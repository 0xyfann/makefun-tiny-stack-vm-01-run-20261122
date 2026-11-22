// Tiny stack VM (make.fun tiny-stack-vm-01, ISA v1). Runs every
// /input/<id>/program.bin with its input.bin; writes
// /output/<id>/stdout.bin + exit.txt. Node builtins only, no clock,
// no network, no env variation: two runs write identical bytes.
const fs = require('node:fs');
const path = require('node:path');
const IN = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR || '/output';

// Binary ops (pop b, then a; push the result). DIV/MOD/DIVU/MODU
// throw 4 on b = 0. All results are signed 32-bit ints.
const BIN = {
  0x10: (a, b) => (a + b) | 0, // ADD (wraps)
  0x11: (a, b) => (a - b) | 0, // SUB (wraps)
  0x12: (a, b) => Math.imul(a, b), // MUL (low 32 bits of the exact product)
  0x13: (a, b) => { if (b === 0) throw 4; return Math.trunc(a / b) | 0; }, // DIV
  0x14: (a, b) => { if (b === 0) throw 4; return (a % b) | 0; }, // MOD, sign of a
  0x15: (a, b) => { if (b === 0) throw 4; return Math.floor((a >>> 0) / (b >>> 0)) | 0; }, // DIVU
  0x16: (a, b) => { if (b === 0) throw 4; return ((a >>> 0) % (b >>> 0)) | 0; }, // MODU
  0x18: (a, b) => a & b, // AND
  0x19: (a, b) => a | b, // OR
  0x1a: (a, b) => a ^ b, // XOR
  0x1c: (a, b) => a << b, // SHL (low 5 bits of b; JS masks the count)
  0x1d: (a, b) => a >> b, // SHR (arithmetic)
  0x1e: (a, b) => (a >>> b) | 0, // SHRU (logical, read back as signed)
  0x20: (a, b) => a === b ? 1 : 0, // EQ
  0x21: (a, b) => a < b ? 1 : 0, // LT (signed)
  0x22: (a, b) => (a >>> 0) < (b >>> 0) ? 1 : 0, // LTU (unsigned)
};

// One program. Returns { out: output bytes, code: exit code 0..255 }.
// A trap throws its exit code; HALT and EXIT return. Output written
// before a trap is kept; the trapping instruction writes nothing.
function run(p, inp) {
  const mem = new Int32Array(256); // 256 words, zero at start
  const st = new Int32Array(257); // data stack, max 256 values
  const cs = new Int32Array(64); // call stack, max 64 return addresses
  let sp = 0, csp = 0, pc = 0, n = 0, ip = 0;
  const out = [];
  const off16 = () => { const o = p[pc + 1] | (p[pc + 2] << 8); return o >= 32768 ? o - 65536 : o; };
  try {
    for (;;) {
      // Step order: step limit, then pc, then opcode, then immediate.
      if (n === 1000000) throw 10;
      if (pc < 0 || pc >= p.length) throw 9;
      const op = p[pc];
      let a, b, v, s;
      n++;
      switch (op) {
        case 0x00: return { out, code: 0 }; // HALT
        case 0x01: // PUSH8: signed 8-bit immediate, sign-extended
          if (pc + 1 >= p.length) throw 9;
          if (sp >= 256) throw 3;
          v = p[pc + 1]; st[sp++] = v >= 128 ? v - 256 : v; pc += 2; break;
        case 0x02: // PUSH32: signed 32-bit little-endian immediate
          if (pc + 4 >= p.length) throw 9;
          if (sp >= 256) throw 3;
          st[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24); pc += 5; break;
        case 0x03: // POP
          if (sp < 1) throw 2; sp--; pc++; break;
        case 0x04: // DUP
          if (sp < 1) throw 2; if (sp >= 256) throw 3; st[sp] = st[sp - 1]; sp++; pc++; break;
        case 0x05: // SWAP
          if (sp < 2) throw 2; v = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = v; pc++; break;
        case 0x06: // OVER
          if (sp < 2) throw 2; if (sp >= 256) throw 3; st[sp] = st[sp - 2]; sp++; pc++; break;
        case 0x07: // ROT ( a b c -- b c a )
          if (sp < 3) throw 2; v = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = v; pc++; break;
        case 0x17: // NEG (wraps: -(-2147483648) is -2147483648)
          if (sp < 1) throw 2; st[sp - 1] = (-st[sp - 1]) | 0; pc++; break;
        case 0x1b: // NOT
          if (sp < 1) throw 2; st[sp - 1] = ~st[sp - 1]; pc++; break;
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
        case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
        case 0x20: case 0x21: case 0x22: // binary ops
          if (sp < 2) throw 2; b = st[--sp]; st[sp - 1] = BIN[op](st[sp - 1], b); pc++; break;
        case 0x30: // JMP: pc = (next instruction) + signed offset
          if (pc + 2 >= p.length) throw 9; pc = pc + 3 + off16(); break;
        case 0x31: // JZ: pop v; jump if v is 0
          if (pc + 2 >= p.length) throw 9; if (sp < 1) throw 2;
          pc = st[--sp] === 0 ? pc + 3 + off16() : pc + 3; break;
        case 0x32: // JNZ: pop v; jump if v is not 0
          if (pc + 2 >= p.length) throw 9; if (sp < 1) throw 2;
          pc = st[--sp] !== 0 ? pc + 3 + off16() : pc + 3; break;
        case 0x33: // CALL: push the next address, pc = unsigned target
          if (pc + 2 >= p.length) throw 9; if (csp >= 64) throw 7;
          cs[csp++] = pc + 3; pc = p[pc + 1] | (p[pc + 2] << 8); break;
        case 0x34: // RET
          if (csp === 0) throw 8; pc = cs[--csp]; break;
        case 0x40: // LOAD
          if (sp < 1) throw 2; a = st[sp - 1];
          if (a < 0 || a > 255) throw 6; st[sp - 1] = mem[a]; pc++; break;
        case 0x41: // STORE ( v addr -- )
          if (sp < 2) throw 2; a = st[sp - 1]; v = st[sp - 2];
          if (a < 0 || a > 255) throw 6; sp -= 2; mem[a] = v; pc++; break;
        case 0x50: // PRINT: decimal ASCII, no newline; over the limit writes nothing
          if (sp < 1) throw 2; v = st[--sp]; s = String(v);
          if (out.length + s.length > 65536) throw 11;
          for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
          pc++; break;
        case 0x51: // PUTC: one byte, v AND 255
          if (sp < 1) throw 2; v = st[--sp];
          if (out.length >= 65536) throw 11; out.push(v & 255); pc++; break;
        case 0x52: // IN: next input byte, or -1 once used up
          if (sp >= 256) throw 3; st[sp++] = ip < inp.length ? inp[ip++] : -1; pc++; break;
        case 0x53: // EXIT: code v AND 255
          if (sp < 1) throw 2; return { out, code: st[--sp] & 255 };
        default: throw 5; // unknown opcode
      }
    }
  } catch (c) { return { out, code: typeof c === 'number' ? c : 9 }; } // a real bug must not corrupt exit.txt's format
}

// The whole set: one answer per instance directory under IN.
for (const id of fs.readdirSync(IN).sort()) {
  const d = path.join(IN, id);
  try { if (!fs.statSync(d).isDirectory()) continue; } catch { continue; }
  let prog = null, inp = Buffer.alloc(0);
  try { prog = fs.readFileSync(path.join(d, 'program.bin')); } catch { prog = null; }
  try { inp = fs.readFileSync(path.join(d, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const r = prog ? run(prog, inp) : { out: [], code: 9 };
  const od = path.join(OUT, id);
  fs.mkdirSync(od, { recursive: true });
  fs.writeFileSync(path.join(od, 'stdout.bin'), Buffer.from(r.out));
  fs.writeFileSync(path.join(od, 'exit.txt'), r.code + '\n');
}
