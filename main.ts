// mend: one patch tool for every AI edit format.
//
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A patches, JSON text-editor tool calls) and applies it to the tree of
// text files in the working directory, all or nothing, exactly as SPEC.md
// says. Node 22, standard library only; run as `node main.ts [options]
// [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below): keep that
// hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** An exit-2 answer: the one line to print. */
class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One failed edit: its code and the path it concerns. */
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

/** A path is safe when it is not empty, does not start with /, holds no \, and none of its segments is empty, . or .. */
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The leading spaces and tabs of a line. */
function leadingWS(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

/** A line with leading and trailing spaces and tabs removed. */
function trimST(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** A line with trailing spaces and tabs removed. */
function trimTrailST(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

/** A file's text as lines, its line break, and whether it ends with one. */
interface FileText {
  lines: string[];
  br: string;
  eol: boolean;
}

function parseText(text: string): FileText {
  if (text === '') return { lines: [], br: '\n', eol: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const eol = text.endsWith(br);
  const lines = text.split(br);
  if (eol) lines.pop();
  return { lines, br, eol };
}

function serializeText(f: FileText): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.eol ? f.br : '');
}

function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Moves that succeeded, in the patch's order: [old, new]. */
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
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  set(p: string, v: string | null): void {
    this.now.set(p, v);
  }
}

type Edit = (tree: Tree) => void;

/** One line of an old block (O) or a new block (N). A context line is shared: it is written as the file's own matched line. */
interface LineItem {
  text: string;
  /** True for a context line (a line of both O and N). */
  ctx: boolean;
  /** For a context line of N, its index in O. */
  oIdx: number;
}

function ctxItem(text: string, oIdx: number): LineItem {
  return { text, ctx: true, oIdx };
}

function plainItem(text: string): LineItem {
  return { text, ctx: false, oIdx: -1 };
}

/** A line normalised for a matching tier: 0 exact, 1 trailing spaces/tabs off, 2 leading and trailing spaces/tabs off. */
function tierNorm(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return trimTrailST(s);
  return trimST(s);
}

/** Every 0-based position where O's lines match the file's lines at a tier. Occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0 || o.length > lines.length) return out;
  for (let i = 0; i + o.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < o.length; k += 1) {
      if (tierNorm(lines[i + k]!, tier) !== tierNorm(o[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2; only 0 when strict) at which O occurs, with its positions; null when it occurs at no tier. */
function findMatch(lines: string[], o: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const occ = occurrences(lines, o, tier);
    if (occ.length > 0) return { tier, occ };
  }
  return null;
}

/**
 * The lines N writes when it replaces O's match at `pos`: a context line is
 * the file's own matched line; at tier 2 every other line is re-indented
 * (O's first line's leading whitespace replaced by the file's first matched
 * line's); at tiers 0 and 1 the other lines are written as they are.
 */
function buildReplacement(o: LineItem[], n: LineItem[], lines: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  if (o.length > 0 && n.length > 0) {
    const f = leadingWS(lines[pos]!);
    const p = leadingWS(o[0]!.text);
    for (const item of n) {
      if (item.ctx) {
        out.push(lines[pos + item.oIdx]!);
      } else if (item.text === '' || trimST(item.text) === '') {
        out.push(item.text);
      } else if (tier === 2 && item.text.startsWith(p)) {
        out.push(f + item.text.slice(p.length));
      } else {
        out.push(item.text);
      }
    }
  } else {
    for (const item of n) out.push(item.text);
  }
  return out;
}

/** The old and new line items of a hunk/chunk/block body, built from its lines. */
interface BodyParts {
  o: LineItem[];
  n: LineItem[];
  /** Whether a \ line follows the body's last context or + line (unified only). */
  bsAfterLast: boolean;
}

function bodyParts(body: Array<{ kind: string; text: string; bs: boolean }>): BodyParts {
  const o: LineItem[] = [];
  const n: LineItem[] = [];
  for (const b of body) {
    if (b.kind === 'ctx') {
      const item = ctxItem(b.text, o.length);
      o.push(item);
      n.push(item);
    } else if (b.kind === 'old') {
      o.push(plainItem(b.text));
    } else if (b.kind === 'new') {
      n.push(plainItem(b.text));
    }
  }
  // Whether a \ line follows the body's last context or + line.
  let bsAfterLast = false;
  for (let i = body.length - 1; i >= 0; i -= 1) {
    const b = body[i]!;
    if (b.kind === 'ctx' || b.kind === 'new') {
      bsAfterLast = b.bs;
      break;
    }
  }
  return { o, n, bsAfterLast };
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
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
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const f = parseText(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      f.lines.splice(line, 0, ...add);
      tree.set(p, serializeText(f));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
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
  return edits;
}


/** One body line of a unified hunk or a V4A chunk. `bs` is set when a \ line follows it (unified only). */
interface BodyEntry {
  kind: string;
  text: string;
  bs: boolean;
  /** True for a zero-length patch line (an empty line), as opposed to a ` ` line. */
  empty: boolean;
}

interface Hunk {
  a: number;
  body: BodyEntry[];
}

interface UnifiedSection {
  diffOld: string | null;
  diffNew: string | null;
  pairOld: string | null;
  pairNew: string | null;
  renameOld: string | null;
  renameNew: string | null;
  isNew: boolean;
  isDel: boolean;
  hunks: Hunk[];
}

/** The path a ---/+++ line names: after the four characters, up to the first tab, surrounding spaces removed, a leading a/ or b/ removed. */
function headerPath(line: string): string {
  const raw = line.slice(4).split('\t')[0]!;
  const t = raw.trim();
  if (t.startsWith('a/') || t.startsWith('b/')) return t.slice(2);
  return t;
}

const HUNK_RE = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;
const DIFF_GIT_RE = /^diff --git a\/([^ ]+) b\/([^ ]+)$/;

/** Apply a section's hunks in order to a file's lines. Throws Fail('no-match', path) when a hunk finds nothing. */
function applyUnifiedHunks(f: FileText, hunks: Hunk[], strict: boolean, path: string): FileText {
  let lines = [...f.lines];
  let eol = f.eol;
  let d = 0;
  for (const h of hunks) {
    const parts = bodyParts(h.body);
    const oTexts = parts.o.map((x) => x.text);
    if (oTexts.length === 0) {
      const at = Math.min(h.a + d, lines.length);
      const nout = parts.n.map((x) => x.text);
      const atEnd = at === lines.length;
      lines = [...lines.slice(0, at), ...nout, ...lines.slice(at)];
      if (atEnd) eol = !parts.bsAfterLast;
      d += parts.n.length;
      continue;
    }
    const match = findMatch(lines, oTexts, strict);
    if (match === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let pos = match.occ[0]!;
    for (const p of match.occ) {
      if (Math.abs(p - target) < Math.abs(pos - target)) pos = p;
    }
    const nout = buildReplacement(parts.o, parts.n, lines, pos, match.tier);
    const atEnd = pos + oTexts.length === lines.length;
    lines = [...lines.slice(0, pos), ...nout, ...lines.slice(pos + oTexts.length)];
    if (atEnd) eol = !parts.bsAfterLast;
    d += parts.n.length - oTexts.length;
  }
  return { lines, br: f.br, eol };
}

function unifiedSectionEdit(sec: UnifiedSection, strict: boolean): Edit {
  return (tree) => {
    const oldP = (sec.pairOld ?? sec.renameOld ?? sec.diffOld)!;
    const newP = (sec.pairNew ?? sec.renameNew ?? sec.diffNew)!;
    const oldIsNull = oldP === '/dev/null';
    const newIsNull = newP === '/dev/null';
    let kind: string;
    if (oldIsNull || sec.isNew) kind = 'create';
    else if (newIsNull || sec.isDel) kind = 'delete';
    else if (oldP !== newP) kind = 'move';
    else kind = 'change';
    if (!(kind === 'create' && oldIsNull) && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (!(kind === 'delete' && newIsNull) && !safe(newP)) throw new Fail('unsafe', newP);
    if (kind === 'create') {
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const lines: string[] = [];
      let lastBs = false;
      let anyPlus = false;
      for (const h of sec.hunks) {
        for (const b of h.body) {
          if (b.kind === 'new') {
            lines.push(b.text);
            lastBs = b.bs;
            anyPlus = true;
          }
        }
      }
      tree.set(newP, anyPlus ? serializeText({ lines, br: '\n', eol: !lastBs }) : '');
      return;
    }
    if (kind === 'delete') {
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.set(oldP, null);
      return;
    }
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    if (kind === 'move' && tree.get(newP) !== null) throw new Fail('exists', newP);
    const after = serializeText(applyUnifiedHunks(parseText(before), sec.hunks, strict, oldP));
    if (kind === 'move') {
      tree.set(newP, after);
      tree.set(oldP, null);
      tree.moves.push([oldP, newP]);
    } else {
      tree.set(oldP, after);
    }
  };
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let inHeader = false;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { diffOld: m[1]!, diffNew: m[2]!, pairOld: null, pairNew: null, renameOld: null, renameNew: null, isNew: false, isDel: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i += 1;
      continue;
    }
    if (inHeader && cur !== null) {
      if (line.startsWith('@@')) {
        const m = HUNK_RE.exec(line);
        if (m === null) throw new Exit2(`error: parse ${i + 1}`);
        inHeader = false;
        const hunk: Hunk = { a: Number(m[1]), body: [] };
        cur.hunks.push(hunk);
        i += 1;
        i = collectHunkBody(lines, i, hunk);
        continue;
      }
      if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          cur.pairOld = headerPath(line);
          cur.pairNew = headerPath(lines[i + 1]!);
          i += 2;
          continue;
        }
        throw new Exit2(`error: parse ${i + 2}`);
      }
      if (line.startsWith('rename from ')) {
        cur.renameOld = line.slice(12).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameNew = line.slice(10).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.isNew = true;
        i += 1;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.isDel = true;
        i += 1;
        continue;
      }
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = { diffOld: null, diffNew: null, pairOld: headerPath(line), pairNew: headerPath(lines[i + 1]!), renameOld: null, renameNew: null, isNew: false, isDel: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: Number(m[1]), body: [] };
      cur.hunks.push(hunk);
      i += 1;
      i = collectHunkBody(lines, i, hunk);
      continue;
    }
    i += 1;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

/** Collect a hunk's body lines starting at `i`; returns the index after the body. */
function collectHunkBody(lines: string[], i: number, hunk: Hunk): number {
  const n = lines.length;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (line === '') {
      hunk.body.push({ kind: 'ctx', text: '', bs: false, empty: true });
      i += 1;
      continue;
    }
    const c = line[0]!;
    if (c === ' ') {
      hunk.body.push({ kind: 'ctx', text: line.slice(1), bs: false, empty: false });
      i += 1;
      continue;
    }
    if (c === '-') {
      hunk.body.push({ kind: 'old', text: line.slice(1), bs: false, empty: false });
      i += 1;
      continue;
    }
    if (c === '+') {
      hunk.body.push({ kind: 'new', text: line.slice(1), bs: false, empty: false });
      i += 1;
      continue;
    }
    if (c === '\\') {
      if (hunk.body.length > 0) hunk.body[hunk.body.length - 1]!.bs = true;
      i += 1;
      continue;
    }
    break;
  }
  while (hunk.body.length > 0 && hunk.body[hunk.body.length - 1]!.empty) hunk.body.pop();
  return i;
}


function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let searchFrom = 0;
  let prevEnd = 0;
  while (true) {
    let s = -1;
    for (let i = searchFrom; i < lines.length; i += 1) {
      if (lines[i]!.trimEnd() === '<<<<<<< SEARCH') {
        s = i;
        break;
      }
    }
    if (s < 0) break;
    let eq = -1;
    let rep = -1;
    for (let j = s + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${s + 1}`);
    for (let k = eq + 1; k < lines.length; k += 1) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = k;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    let path: string | null = null;
    for (let i = s - 1; i >= prevEnd; i -= 1) {
      const t = lines[i]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    prevPath = path;
    prevEnd = rep + 1;
    const oldLines = lines.slice(s + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    searchFrom = rep + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.set(path, newLines.length === 0 ? '' : serializeText({ lines: [...newLines], br: '\n', eol: true }));
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const f = parseText(before);
    const match = findMatch(f.lines, oldLines, strict);
    if (match === null) throw new Fail('no-match', path);
    if (match.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = match.occ[0]!;
    const items = (ls: string[]): LineItem[] => ls.map((t) => plainItem(t));
    const nout = buildReplacement(items(oldLines), items(newLines), f.lines, pos, match.tier);
    f.lines = [...f.lines.slice(0, pos), ...nout, ...f.lines.slice(pos + oldLines.length)];
    tree.set(path, serializeText(f));
  };
}


interface V4aChunk {
  anchor: string | null;
  eof: boolean;
  body: BodyEntry[];
}

interface V4aSection {
  kind: string;
  path: string;
  moveTo: string | null;
  chunks: V4aChunk[];
  /** 1-based line of the section's header, for parse errors. */
  line: number;
  /** Add File section's lines, once parsed. */
  addLines: string[] | null;
}

function v4aSectionStart(line: string): { kind: string; path: string } | null {
  if (line.startsWith('*** Add File: ')) return { kind: 'add', path: line.slice(14).trim() };
  if (line === '*** Add File:') return { kind: 'add', path: '' };
  if (line.startsWith('*** Delete File: ')) return { kind: 'delete', path: line.slice(17).trim() };
  if (line === '*** Delete File:') return { kind: 'delete', path: '' };
  if (line.startsWith('*** Update File: ')) return { kind: 'update', path: line.slice(17).trim() };
  if (line === '*** Update File:') return { kind: 'update', path: '' };
  return null;
}

/** Apply an Update section's chunks in order, tracking the cursor. Throws Fail('no-match', path) when a chunk finds nothing. */
function applyV4aChunks(f: FileText, chunks: V4aChunk[], strict: boolean, path: string): FileText {
  let lines = [...f.lines];
  let cursor = 0;
  for (const ch of chunks) {
    if (ch.anchor !== null && ch.anchor !== '') {
      let found = -1;
      const tiers = strict ? [0] : [0, 1, 2];
      for (const tier of tiers) {
        for (let i = cursor; i < lines.length; i += 1) {
          if (tierNorm(lines[i]!, tier) === tierNorm(ch.anchor, tier)) {
            found = i;
            break;
          }
        }
        if (found >= 0) break;
      }
      if (found < 0) throw new Fail('no-match', path);
      cursor = found + 1;
    }
    const parts = bodyParts(ch.body);
    const oTexts = parts.o.map((x) => x.text);
    if (oTexts.length === 0) {
      const at = ch.eof ? lines.length : cursor;
      const nout = parts.n.map((x) => x.text);
      lines = [...lines.slice(0, at), ...nout, ...lines.slice(at)];
      cursor = at + nout.length;
      continue;
    }
    const match = findMatchFrom(lines, oTexts, cursor, strict);
    if (match === null) throw new Fail('no-match', path);
    let pos: number;
    if (ch.eof) {
      const want = lines.length - oTexts.length;
      if (want < cursor || !match.occ.includes(want)) throw new Fail('no-match', path);
      pos = want;
    } else {
      pos = match.occ[0]!;
    }
    const nout = buildReplacement(parts.o, parts.n, lines, pos, match.tier);
    lines = [...lines.slice(0, pos), ...nout, ...lines.slice(pos + oTexts.length)];
    cursor = pos + nout.length;
  }
  return { lines, br: f.br, eol: f.eol };
}

/** The first tier at which O occurs at or after `from`, with those positions; null when it occurs at no tier. */
function findMatchFrom(lines: string[], o: string[], from: number, strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const occ = occurrences(lines, o, tier).filter((p) => p >= from);
    if (occ.length > 0) return { tier, occ };
  }
  return null;
}

function v4aSectionEdit(sec: V4aSection, strict: boolean): Edit {
  return (tree) => {
    const path = sec.path;
    if (!safe(path)) throw new Fail('unsafe', path);
    if (sec.kind === 'add') {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      const add = sec.addLines ?? [];
      tree.set(path, add.length === 0 ? '' : serializeText({ lines: [...add], br: '\n', eol: true }));
      return;
    }
    if (sec.kind === 'delete') {
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.set(path, null);
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (sec.moveTo !== null) {
      if (!safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
      if (tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    }
    const after = serializeText(applyV4aChunks(parseText(before), sec.chunks, strict, path));
    if (sec.moveTo !== null) {
      tree.set(sec.moveTo, after);
      tree.set(path, null);
      tree.moves.push([path, sec.moveTo]);
    } else {
      tree.set(path, after);
    }
  };
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4aSection[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i += 1;
      continue;
    }
    const start = v4aSectionStart(line);
    if (start === null) throw new Exit2(`error: parse ${i + 1}`);
    const sec: V4aSection = { kind: start.kind, path: start.path, moveTo: null, chunks: [], line: i + 1, addLines: null };
    i += 1;
    const raw: Array<{ text: string; idx: number }> = [];
    while (i < last) {
      const l = lines[i]!;
      if (v4aSectionStart(l) !== null) break;
      raw.push({ text: l, idx: i });
      i += 1;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    parseV4aSection(sec, raw, strict);
    sections.push(sec);
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => v4aSectionEdit(s, strict));
}

/** Fill a V4A section's lines/chunks from its raw lines (trailing blanks already stripped). */
function parseV4aSection(sec: V4aSection, raw: Array<{ text: string; idx: number }>, _strict: boolean): void {
  if (sec.kind === 'add') {
    const addLines: string[] = [];
    for (const r of raw) {
      if (r.text.startsWith('+')) addLines.push(r.text.slice(1));
      else if (r.text === '') addLines.push('');
      else throw new Exit2(`error: parse ${r.idx + 1}`);
    }
    sec.addLines = addLines;
    return;
  }
  if (sec.kind === 'delete') {
    if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.idx + 1}`);
    return;
  }
  let j = 0;
  if (j < raw.length && raw[j]!.text.startsWith('*** Move to: ')) {
    sec.moveTo = raw[j]!.text.slice(13).trim();
    j += 1;
  } else if (j < raw.length && raw[j]!.text === '*** Move to:') {
    sec.moveTo = '';
    j += 1;
  }
  let cur: V4aChunk | null = null;
  const isBodyLine = (t: string): boolean => t === '' || t.startsWith(' ') || t.startsWith('-') || t.startsWith('+');
  while (j < raw.length) {
    const r = raw[j]!;
    const t = r.text;
    if (t.startsWith('@@')) {
      cur = { anchor: t.slice(2).trim(), eof: false, body: [] };
      sec.chunks.push(cur);
      j += 1;
      continue;
    }
    if (t === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${r.idx + 1}`);
      cur.eof = true;
      cur = null;
      j += 1;
      continue;
    }
    if (isBodyLine(t)) {
      if (cur === null) {
        if (sec.chunks.length > 0) throw new Exit2(`error: parse ${r.idx + 1}`);
        cur = { anchor: null, eof: false, body: [] };
        sec.chunks.push(cur);
      }
      if (t === '') cur.body.push({ kind: 'ctx', text: '', bs: false, empty: true });
      else if (t.startsWith(' ')) cur.body.push({ kind: 'ctx', text: t.slice(1), bs: false, empty: false });
      else if (t.startsWith('-')) cur.body.push({ kind: 'old', text: t.slice(1), bs: false, empty: false });
      else cur.body.push({ kind: 'new', text: t.slice(1), bs: false, empty: false });
      j += 1;
      continue;
    }
    throw new Exit2(`error: parse ${r.idx + 1}`);
  }
  if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${sec.line}`);
}


function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
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
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const beforeNow = new Map(tree.now);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of beforeNow) tree.now.set(k, v);
      tree.moves.length = 0;
      for (const m of beforeMoves) tree.moves.push(m);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: Array<{ key: string; line: string }> = [];
  const handledOld = new Set<string>();
  const handledNew = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, line: `R ${oldP} -> ${newP}` });
      handledOld.add(oldP);
      handledNew.add(newP);
    }
  }
  for (const p of [...tree.now.keys()].sort(byteOrder)) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (handledOld.has(p) || handledNew.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byteOrder)) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
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
