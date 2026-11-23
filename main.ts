// mend: one patch tool for every AI edit format. My own implementation of
// SPEC.md v1 (kit starter/SPEC.md), written from the specification.
// Node 22, standard library only.
// Run: node main.ts [--format=NAME] [--check] [--strict] [PATCH]

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** A parse/usage error: exit 2 with exactly this line on stdout. */
class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One failed edit: exit 1 with `error: <code> <path>`. */
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') &&
    p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface Split {
  lines: string[];
  br: string;
  final: boolean;
}

/** A file's lines under its own line break, and whether it ends with one. */
function splitFile(text: string): Split {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}

/** The tree as the edits leave it. `now` holds changed paths (null: deleted). */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful moves, in patch order: [old, new]. */
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p) as string | null;
  }

  get(p: string): string | null {
    return this.now.has(p) ? (this.now.get(p) as string | null) : this.original(p);
  }

  set(p: string, v: string | null): void {
    this.now.set(p, v);
  }
}

type Edit = (tree: Tree) => void;

const rtrimWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

function eqTier(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimWs(a) === rtrimWs(b);
  return trimWs(a) === trimWs(b);
}

/** All 0-based positions where O occurs in lines at this tier. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  for (let i = 0; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!eqTier(lines[i + j] as string, o[j] as string, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2 — or only 0 with --strict) at which O occurs, with its positions. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const occ = occurrences(lines, o, tier);
    if (occ.length > 0) return { tier, occ };
  }
  return null;
}

/** One body line of a hunk/chunk: context (in both O and N), deleted, or added. `bs` is set when a `\` line follows it. */
interface Op {
  t: 'ctx' | 'del' | 'add';
  text: string;
  bs: boolean;
}

function opLists(ops: Op[]): { o: string[]; n: string[] } {
  const o: string[] = [];
  const n: string[] = [];
  for (const op of ops) {
    if (op.t === 'ctx') {
      o.push(op.text);
      n.push(op.text);
    } else if (op.t === 'del') o.push(op.text);
    else n.push(op.text);
  }
  return { o, n };
}

/** The replacement lines for N at `pos`: context lines come from the file itself; at tier 2 the other lines are re-indented. */
function mapNew(fileLines: string[], ops: Op[], o: string[], tier: number, pos: number): string[] {
  const out: string[] = [];
  const f = o.length > 0 ? leadWs(fileLines[pos] as string) : '';
  const p = o.length > 0 ? leadWs(o[0] as string) : '';
  let oi = 0;
  for (const op of ops) {
    if (op.t === 'ctx') {
      out.push(fileLines[pos + oi] as string);
      oi += 1;
    } else if (op.t === 'del') {
      oi += 1;
    } else {
      let text = op.text;
      if (tier === 2 && text !== '' && text.trim() !== '' && text.startsWith(p)) {
        text = f + text.slice(p.length);
      }
      out.push(text);
    }
  }
  return out;
}

/** Whether a `\` line follows the hunk's last context or `+` line. */
function lastCtxPlusBs(ops: Op[]): boolean {
  for (let k = ops.length - 1; k >= 0; k--) {
    const op = ops[k] as Op;
    if (op.t === 'ctx' || op.t === 'add') return op.bs;
  }
  return false;
}

/** Format detection (SPEC.md section 4). */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if ((lines[first] as string).trim() === '*** Begin Patch') return 'v4a';
  const c = (lines[first] as string).trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' &&
      (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const norm = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = norm(before);
      const old = norm(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + norm(newStr) + t.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) &&
      typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const cur = splitFile(before);
      if (line < 0 || line > cur.lines.length) throw new Fail('no-match', p);
      const lines = [...cur.lines.slice(0, line), ...add, ...cur.lines.slice(line)];
      tree.set(p, joinFile(lines, cur.br, cur.final));
    };
  }
  return null;
}

function parseJson(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if ((lines[first] as string).trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    if (edits.length === 0) throw new Exit2('error: parse 1');
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

/** SEARCH/REPLACE blocks (SPEC.md section 7). */
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  interface Block {
    path: string;
    oldLines: string[];
    newLines: string[];
  }
  const blocks: Block[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if ((lines[i] as string).trimEnd() === '<<<<<<< SEARCH') {
      let path: string | null = null;
      for (let j = i - 1; j >= prevEnd; j--) {
        const t = (lines[j] as string).trim();
        if (t === '' || t.startsWith('```')) continue;
        path = t;
        break;
      }
      if (path === null) {
        if (prevPath === null) throw new Exit2(`error: parse ${i + 1}`);
        path = prevPath;
      }
      let eq = -1;
      for (let j = i + 1; j < lines.length; j++) {
        const lj = (lines[j] as string).trimEnd();
        if (lj === '=======') {
          eq = j;
          break;
        }
        // SPEC.md section 7: a SEARCH line with no `=======` and then
        // `>>>>>>> REPLACE` after it is `error: parse <the SEARCH line>`.
        // A REPLACE marker reached while still looking for `=======` is
        // that error, even if a `=======` comes later.
        if (lj === '>>>>>>> REPLACE') throw new Exit2(`error: parse ${i + 1}`);
      }
      if (eq < 0) throw new Exit2(`error: parse ${i + 1}`);
      let end = -1;
      for (let j = eq + 1; j < lines.length; j++) {
        if ((lines[j] as string).trimEnd() === '>>>>>>> REPLACE') {
          end = j;
          break;
        }
      }
      if (end < 0) throw new Exit2(`error: parse ${i + 1}`);
      blocks.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, end) });
      prevPath = path;
      prevEnd = end + 1;
      i = end + 1;
    } else {
      i++;
    }
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b): Edit => (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const cur = splitFile(before);
    const found = findTier(cur.lines, b.oldLines, strict);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.occ.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.occ[0] as number;
    const ops: Op[] = [
      ...b.oldLines.map((t): Op => ({ t: 'del', text: t, bs: false })),
      ...b.newLines.map((t): Op => ({ t: 'add', text: t, bs: false })),
    ];
    const rep = mapNew(cur.lines, ops, b.oldLines, found.tier, pos);
    const out = [...cur.lines.slice(0, pos), ...rep, ...cur.lines.slice(pos + b.oldLines.length)];
    tree.set(b.path, joinFile(out, cur.br, cur.final));
  });
}

/** V4A patches (SPEC.md section 8). */
interface VChunk {
  anchor: string;
  ops: Op[];
  eof: boolean;
}

function parseV4A(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if ((lines[first] as string).trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i] as string)) {
      last = i;
      break;
    }
  }
  if ((lines[last] as string).trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i] as string;
    if (blank(l)) {
      i++;
      continue;
    }
    let kind: 'add' | 'del' | 'upd' | null = null;
    let path = '';
    if (l.startsWith('*** Add File: ')) {
      kind = 'add';
      path = l.slice(14).trim();
    } else if (l.startsWith('*** Delete File: ')) {
      kind = 'del';
      path = l.slice(17).trim();
    } else if (l.startsWith('*** Update File: ')) {
      kind = 'upd';
      path = l.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const headerNo = i + 1;
    const raw: Array<{ text: string; no: number }> = [];
    let j = i + 1;
    while (j < last) {
      const lj = lines[j] as string;
      if (isSectionStart(lj)) break;
      raw.push({ text: lj, no: j + 1 });
      j++;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    if (kind === 'add') {
      const addLines: string[] = [];
      for (const r of raw) {
        if (r.text === '') addLines.push('');
        else if (r.text.startsWith('+')) addLines.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.no}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.set(path, addLines.length === 0 ? '' : addLines.join('\n') + '\n');
      });
    } else if (kind === 'del') {
      for (const r of raw) {
        if (!blank(r.text)) throw new Exit2(`error: parse ${r.no}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.set(path, null);
      });
    } else {
      let moveTo: string | null = null;
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      let curEnded = false;
      for (const r of raw) {
        if (r.text.startsWith('*** Move to: ') && cur === null && moveTo === null) {
          moveTo = r.text.slice(13).trim();
          continue;
        }
        if (r.text.startsWith('@@')) {
          cur = { anchor: r.text.slice(2).trim(), ops: [], eof: false };
          chunks.push(cur);
          curEnded = false;
          continue;
        }
        if (r.text === '*** End of File') {
          if (cur === null) {
            cur = { anchor: '', ops: [], eof: true };
            chunks.push(cur);
          } else {
            cur.eof = true;
          }
          curEnded = true;
          continue;
        }
        if (r.text === '' || r.text.startsWith(' ') || r.text.startsWith('-') || r.text.startsWith('+')) {
          if (cur !== null && curEnded) throw new Exit2(`error: parse ${r.no}`);
          if (cur === null) {
            cur = { anchor: '', ops: [], eof: false };
            chunks.push(cur);
          }
          const t = r.text === '' ? 'ctx' : r.text[0] === ' ' ? 'ctx' : r.text[0] === '-' ? 'del' : 'add';
          cur.ops.push({ t, text: r.text === '' ? '' : r.text.slice(1), bs: false });
          continue;
        }
        throw new Exit2(`error: parse ${r.no}`);
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headerNo}`);
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
        const before = tree.get(path);
        if (before === null) throw new Fail('missing', path);
        if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
        let cur = splitFile(before);
        let cursor = 0;
        for (const chunk of chunks) {
          if (chunk.anchor !== '') {
            let foundIdx = -1;
            const tiers = strict ? [0] : [0, 1, 2];
            for (const tier of tiers) {
              for (let k = cursor; k < cur.lines.length; k++) {
                if (eqTier(cur.lines[k] as string, chunk.anchor, tier)) {
                  foundIdx = k;
                  break;
                }
              }
              if (foundIdx >= 0) break;
            }
            if (foundIdx < 0) throw new Fail('no-match', path);
            cursor = foundIdx + 1;
          }
          const { o, n } = opLists(chunk.ops);
          if (o.length === 0) {
            const pos = chunk.eof ? cur.lines.length : cursor;
            const out = [...cur.lines.slice(0, pos), ...n, ...cur.lines.slice(pos)];
            cur = { lines: out, br: cur.br, final: cur.final };
            cursor = pos + n.length;
          } else {
            let hit: { tier: number; pos: number } | null = null;
            const tiers = strict ? [0] : [0, 1, 2];
            for (const tier of tiers) {
              const occs = occurrences(cur.lines, o, tier).filter(
                (p) => p >= cursor && (!chunk.eof || p + o.length === cur.lines.length),
              );
              if (occs.length > 0) {
                hit = { tier, pos: occs[0] as number };
                break;
              }
            }
            if (hit === null) throw new Fail('no-match', path);
            const rep = mapNew(cur.lines, chunk.ops, o, hit.tier, hit.pos);
            const out = [...cur.lines.slice(0, hit.pos), ...rep, ...cur.lines.slice(hit.pos + o.length)];
            cur = { lines: out, br: cur.br, final: cur.final };
            cursor = hit.pos + rep.length;
          }
        }
        const text = joinFile(cur.lines, cur.br, cur.final);
        if (moveTo !== null) {
          tree.set(path, null);
          tree.set(moveTo, text);
          tree.moves.push([path, moveTo]);
        } else {
          tree.set(path, text);
        }
      });
    }
    i = j;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

/** Unified diffs (SPEC.md section 6). */
interface UHunk {
  a: number;
  ops: Op[];
}

interface USection {
  gitOld: string | null;
  gitNew: string | null;
  pairOld: string | null;
  pairNew: string | null;
  /** True once a `---`/`+++` pair has named this section's paths. */
  hasPair: boolean;
  renameOld: string | null;
  renameNew: string | null;
  isNew: boolean;
  isDeleted: boolean;
  hunks: UHunk[];
}

function headerPath(l: string): string {
  return l.slice(4).split('\t')[0]!.trim();
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let sec: USection | null = null;
  let inHeader = false;
  const fresh = (go: string | null, gn: string | null): USection => ({
    gitOld: go,
    gitNew: gn,
    pairOld: null,
    pairNew: null,
    hasPair: false,
    renameOld: null,
    renameNew: null,
    isNew: false,
    isDeleted: false,
    hunks: [],
  });
  let i = 0;
  while (i < lines.length) {
    const l = lines[i] as string;
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.*) b\/(.*)$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      sec = fresh(m[1] as string, m[2] as string);
      sections.push(sec);
      inHeader = true;
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      // SPEC.md section 6: a section starts at a `---`/`+++` pair that is
      // not already part of a section's header. The first pair names the
      // current section (opened by `diff --git`, or by the pair itself);
      // a second pair starts a new section instead of overwriting the first.
      if (sec === null || !inHeader || sec.hasPair) {
        sec = fresh(null, null);
        sections.push(sec);
        inHeader = true;
      }
      sec.pairOld = headerPath(l);
      sec.pairNew = headerPath(lines[i + 1] as string);
      sec.hasPair = true;
      i += 2;
      continue;
    }
    if (l.startsWith('--- ')) {
      if (sec !== null && inHeader) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (l.startsWith('@@')) {
      if (sec === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(m[1] as string, 10);
      const body: string[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j] as string;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bl);
          j++;
        } else break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      const ops: Op[] = [];
      for (const bl of body) {
        if (bl.startsWith('\\')) {
          if (ops.length > 0) (ops[ops.length - 1] as Op).bs = true;
          continue;
        }
        if (bl === '') ops.push({ t: 'ctx', text: '', bs: false });
        else if (bl[0] === ' ') ops.push({ t: 'ctx', text: bl.slice(1), bs: false });
        else if (bl[0] === '-') ops.push({ t: 'del', text: bl.slice(1), bs: false });
        else ops.push({ t: 'add', text: bl.slice(1), bs: false });
      }
      sec.hunks.push({ a, ops });
      inHeader = false;
      i = j;
      continue;
    }
    if (sec !== null && inHeader) {
      if (l.startsWith('rename from ')) sec.renameOld = l.slice(12).trim();
      else if (l.startsWith('rename to ')) sec.renameNew = l.slice(10).trim();
      else if (l.startsWith('new file mode')) sec.isNew = true;
      else if (l.startsWith('deleted file mode')) sec.isDeleted = true;
      else if (l.startsWith('+++ ')) sec.pairNew = headerPath(l);
      i++;
      continue;
    }
    i++;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedEdit(s, strict));
}

function unifiedEdit(s: USection, strict: boolean): Edit {
  const clean = (p: string | null): string | null => {
    if (p === null) return null;
    if (p.startsWith('a/')) return p.slice(2);
    if (p.startsWith('b/')) return p.slice(2);
    return p;
  };
  const oldP = clean(s.pairOld ?? s.renameOld ?? s.gitOld);
  const newP = clean(s.pairNew ?? s.renameNew ?? s.gitNew);
  const isCreate = s.isNew || oldP === '/dev/null';
  const isDelete = s.isDeleted || newP === '/dev/null';
  const isMove = !isCreate && !isDelete && oldP !== null && newP !== null && oldP !== newP;
  return (tree: Tree): void => {
    if (isCreate) {
      const np = newP as string;
      if (!safe(np)) throw new Fail('unsafe', np);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plus: string[] = [];
      let bs = false;
      for (const h of s.hunks) {
        for (const op of h.ops) {
          if (op.t === 'add') {
            plus.push(op.text);
            bs = op.bs;
          }
        }
      }
      tree.set(np, plus.length === 0 ? '' : plus.join('\n') + (bs ? '' : '\n'));
      return;
    }
    if (isDelete) {
      const op = oldP as string;
      if (!safe(op)) throw new Fail('unsafe', op);
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.set(op, null);
      return;
    }
    const op = oldP as string;
    if (!safe(op)) throw new Fail('unsafe', op);
    const np = isMove ? (newP as string) : op;
    if (isMove && !safe(np)) throw new Fail('unsafe', np);
    const before = tree.get(op);
    if (before === null) throw new Fail('missing', op);
    if (isMove && tree.get(np) !== null) throw new Fail('exists', np);
    let cur = splitFile(before);
    let d = 0;
    for (const h of s.hunks) {
      const { o, n } = opLists(h.ops);
      if (o.length === 0) {
        const pos = Math.min(h.a + d, cur.lines.length);
        const touchesEnd = pos === cur.lines.length;
        const out = [...cur.lines.slice(0, pos), ...n, ...cur.lines.slice(pos)];
        cur = { lines: out, br: cur.br, final: touchesEnd ? !lastCtxPlusBs(h.ops) : cur.final };
        d += n.length;
      } else {
        const found = findTier(cur.lines, o, strict);
        if (found === null) throw new Fail('no-match', op);
        const target = h.a - 1 + d;
        let pos = found.occ[0] as number;
        let best = Math.abs(pos - target);
        for (const q of found.occ) {
          const dist = Math.abs(q - target);
          if (dist < best) {
            best = dist;
            pos = q;
          }
        }
        const touchesEnd = pos + o.length === cur.lines.length;
        const rep = mapNew(cur.lines, h.ops, o, found.tier, pos);
        const out = [...cur.lines.slice(0, pos), ...rep, ...cur.lines.slice(pos + o.length)];
        cur = { lines: out, br: cur.br, final: touchesEnd ? !lastCtxPlusBs(h.ops) : cur.final };
        d += n.length - o.length;
      }
    }
    const text = joinFile(cur.lines, cur.br, cur.final);
    if (isMove) {
      tree.set(op, null);
      tree.set(np, text);
      tree.moves.push([op, np]);
    } else {
      tree.set(op, text);
    }
  };
}

/** The command line, output and exit codes (SPEC.md sections 1, 2, 10). */
function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
      continue;
    }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : (pos[0] as string);
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = parseJson(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4A(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesLen;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows: Array<{ key: string; line: string; move?: [string, string] }> = [];
  const suppressed = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    const wasOld = tree.original(oldP);
    const nowOld = tree.now.get(oldP);
    const wasNew = tree.original(newP);
    const nowNew = tree.now.get(newP);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: newP, line: `R ${oldP} -> ${newP}`, move: [oldP, newP] });
      suppressed.add(oldP);
      suppressed.add(newP);
    }
  }
  for (const p of tree.now.keys()) {
    if (suppressed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p) as string | null;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const r of rows) {
      const line = r.line;
      if (r.move !== undefined) {
        const [oldP, newP] = r.move;
        rmSync(oldP, { force: true });
        mkdirSync(dirname(newP), { recursive: true });
        writeFileSync(newP, tree.now.get(newP) as string);
      } else if (line.startsWith('D ')) {
        rmSync(line.slice(2), { force: true });
      } else {
        const p = line.slice(2);
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, tree.now.get(p) as string);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
