#!/usr/bin/env node
// THE CHECKER. Nothing else can mark a lemma checked or refuted.
//
//   node tools/check-lean.mjs <lean file> <statement file> [check|refute|reduce]
//
// Exit 0 ONLY when all of these hold, each read from the compiled result:
//   1. the file builds in the pinned environment (lean/lean-toolchain, lean/lake-manifest.json);
//   2. the kernel accepts, a second time, every project declaration the theorem rests on;
//   3. the theorem (named after its module, one lemma one file) rests on no `sorry` and on no
//      axiom outside propext, Classical.choice, Quot.sound;
//   4. the theorem is a proof of the recorded statement (of its negation for `refute`), where the
//      statement is read against the pinned library and the definitions root (PEqualNP.Defs)
//      and nothing else of this project, whatever the file imports.
//   For `reduce` (the decomposition door, ships dark): the theorem is T1 → ... → Tk → S with
//   2 ≤ k ≤ 4 non-dependent arrows, S structurally the recorded statement, each Ti a closed
//   proposition of the statement environment, distinct, not S, not False, and the file declares
//   nothing but the theorem. The verifier prints one `CHILD <i> <text>` line per child (Lean's own
//   printing, checked to read back to the same term); they are carried out unchanged.
//   A child with a string or name literal, a text type (String, Char, Lean.Name, ...) among its
//   constants, a constant of Lean's meta namespaces (Lean, Std.Format, IO, ...) under it, a
//   metadata node, or more than 2000 printed characters is refused (reduce-child); one that contains
//   S as a subterm or that `decide` evaluates to false is refused (reduce-waste).
// On acceptance it prints, before the last line, one line recorded with the result:
//   MANIFEST {"rests_on":[{"module","sha256"}...],"defs":[{"module","sha256"}...]}
// the source hash of every project module the theorem rests on and of every module of the
// definitions root, so a later change to a helper or to a definition is visible.
// Steps 2 to 4 are lean/CheckLemma.lean. Any other outcome is a non-zero exit:
//   1 = REJECTED (the last line says why): the checker ran and the file is not a proof it accepts;
//   3 = CHECKER FAULT: the checker could not judge (a missing path, a build that failed for a
//       reason outside the file, a tree whose build configuration is not the committed one).
//       A fault says nothing about the proof.
//
// WHAT IS FIXED BEFORE ANYTHING IS BUILT. The recorded statement is read into memory first and
// the verifier reads a private copy of those bytes; the verifier binary is hashed before the
// judged build and must be the same file after it; the judged tree's lakefile, manifest and
// toolchain must be what its commit holds, with no lakefile.lean beside them; and no build
// setting is inherited from the caller's environment.
//
// SEVERAL TREES. The checker itself, and its verifier, always run from THIS clone;
// PEQUALNP_REPO_ROOT names the tree whose Lean files are being judged. So the author of a proof
// cannot change the checker it is judged by.
//
// A Lean file runs code while it compiles. Run this script on a file you do not trust only
// inside an isolated environment.
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, rmdirSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

export const CHECKER_VERSION = 'check-lean 4';   // 2026-11-24: kind reduce (decomposition door, dark), with the text and waste screens on its children
const DEFS_ROOT = 'PEqualNP.Defs';
const CHECKER_LEAN_DIR = join(dirname(dirname(fileURLToPath(import.meta.url))), 'lean');
const LEAN_DIR = process.env.PEQUALNP_REPO_ROOT ? join(process.env.PEQUALNP_REPO_ROOT, 'lean') : CHECKER_LEAN_DIR;
const LIBRARIES = ['PEqualNP', 'CheckerSuite'];            // the lean_lib roots in lean/lakefile.toml
const BUILD_TIMEOUT_MS = 30 * 60 * 1000;
const LOCK = join(LEAN_DIR, '.lake', 'check.lock');
const LOCK_STALE_MS = 2 * BUILD_TIMEOUT_MS;

// Every byte this script prints is written synchronously. A piped stdout is asynchronous in
// node and process.exit drops what has not drained: an accepted run whose MANIFEST line was
// longer than the pipe buffer (8192 bytes) reached the reader cut short and was not recorded.
const writeAll = (fd, text) => {
  const buf = Buffer.from(text);
  for (let off = 0; off < buf.length;) {
    try { off += writeSync(fd, buf, off, buf.length - off); } catch (e) { if (e.code !== 'EAGAIN') throw e; Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 5); }
  }
};
const out = (line) => writeAll(1, `${line}\n`);
const fault = (msg) => { writeAll(2, `CHECKER FAULT: ${msg}\n`); process.exit(3); };
// Progress, one fixed line per stage on stderr (our words only, never the file's), so a run that
// stops making progress shows where it stood (2026-11-24: eleven runs hung in this step).
const T0 = Date.now();
const stage = (name) => writeAll(2, `checker stage: ${name} t=${Math.round((Date.now() - T0) / 1000)}s\n`);
const reject = (cls, msg) => { out(`REJECTED (${cls}): ${msg}`); process.exit(1); };
// Anything this script did not foresee is a fault of the checker, never a verdict on the proof.
process.on('uncaughtException', (e) => fault(`the checker stopped on an error of its own: ${e?.message ?? e}`));
const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');

const [file, statement, kind = 'check'] = process.argv.slice(2);
if (!file || !statement) fault('usage: node tools/check-lean.mjs <lean file> <statement file> [check|refute|reduce]');
if (kind !== 'check' && kind !== 'refute' && kind !== 'reduce') fault(`kind must be check, refute or reduce, got "${kind}"`);
if (!existsSync(file)) fault(`the lemma file ${file} does not exist`);
if (!existsSync(statement)) fault(`the statement file ${statement} does not exist`);
// The recorded statement, as it is now. Nothing that runs later can change what is judged.
const statementBytes = readFileSync(statement);

if (!existsSync(LEAN_DIR)) fault(`there is no lean/ directory in the tree being judged (${LEAN_DIR})`);

// The module is the file's place under lean/. A file anywhere else is not part of the project.
const rel = relative(realpathSync(LEAN_DIR), realpathSync(file));
const parts = rel.split(sep);
if (rel.startsWith('..') || !rel.endsWith('.lean') || !LIBRARIES.includes(parts[0]) || parts.length < 2
  || !parts.every((p) => /^[A-Za-z][A-Za-z0-9_]*(\.lean)?$/.test(p))) {
  reject('not-a-project-module', `${file} is not a module of ${LIBRARIES.join(' or ')} under lean/`);
}
const module = rel.slice(0, -'.lean'.length).split(sep).join('.');

// The judged tree builds with the configuration its commit holds, and no other.
const TREE = dirname(LEAN_DIR);
const CONFIG = ['lean/lakefile.toml', 'lean/lake-manifest.json', 'lean/lean-toolchain'];
const git = (args) => spawnSync('git', ['-C', TREE, ...args], { encoding: 'utf8', timeout: 60000 });
const configFault = () => {
  if (existsSync(join(LEAN_DIR, 'lakefile.lean'))) return 'lean/lakefile.lean exists; the project is configured by lean/lakefile.toml alone';
  const tracked = git(['ls-files', '--error-unmatch', '--', ...CONFIG]);
  if (tracked.error || tracked.status !== 0) return `not every one of ${CONFIG.join(', ')} is a committed file of this tree`;
  const same = git(['diff', '--quiet', 'HEAD', '--', ...CONFIG]);
  if (same.error || same.status !== 0) return `${CONFIG.join(', ')} are not what this tree's commit holds`;
  return null;
};
const configNow = configFault();
if (configNow) fault(`the build configuration of the judged tree (${TREE}) is not the committed one: ${configNow}. Restore it, then run again.`);

// The pinned library must already be there, prebuilt. The checker never compiles it.
if (!existsSync(join(LEAN_DIR, '.lake', 'packages', 'mathlib', '.lake', 'build', 'lib', 'lean', 'Mathlib.olean'))) {
  fault('the prebuilt Mathlib cache is missing. Run `lake exe cache get` in lean/ (RUNBOOK.md, section 2).');
}

stage('started');
// One build at a time in this directory.
const sleep = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
for (;;) {
  try { mkdirSync(LOCK); break; } catch (e) {
    if (e.code !== 'EEXIST') fault(`cannot take the build lock: ${e.message}`);
    let age = 0; try { age = Date.now() - statSync(LOCK).mtimeMs; } catch { continue; }
    if (age > LOCK_STALE_MS) { try { rmdirSync(LOCK); } catch { /* another run took it */ } } else sleep(500);
  }
}
stage('build lock taken');
const unlock = () => { try { rmdirSync(LOCK); } catch { /* already gone */ } };
process.on('exit', unlock);
for (const s of ['SIGINT', 'SIGTERM']) process.on(s, () => process.exit(3));

// The checker never reads or writes the shared artifact cache (tools/build.sh): what it
// judges is compiled in, or already present in, the judged tree itself, never pulled in from
// another tree's compile.
// Builds wait for a slot of the machine's build queue (this clone's tools/build.sh); the
// verifier's run (step 2) does not, and runs the real lake directly.
// No Lean or Lake setting is inherited from the caller: the search path, the sysroot and the
// toolchain are the judged tree's own, and the shared cache is off
// (LAKE_ARTIFACT_CACHE is false, not unset: unset, Lake still reads its default cache).
const lakeEnv = Object.fromEntries(Object.entries(process.env).filter(([k]) => !/^(LAKE($|_)|LEAN_|ELAN_TOOLCHAIN$)/.test(k)));
lakeEnv.LAKE_ARTIFACT_CACHE = 'false';
const QUEUE = join(dirname(CHECKER_LEAN_DIR), 'tools', 'build.sh');
const opts = (cwd, env) => ({ cwd, encoding: 'utf8', timeout: BUILD_TIMEOUT_MS, maxBuffer: 64 * 1024 * 1024, env });
// The queue is entered through tools/bin/lake, never through `sh`.
const SHIM = join(dirname(CHECKER_LEAN_DIR), 'tools', 'bin', 'lake');
const { PEQUALNP_IN_QUEUE, ...queued } = lakeEnv;
const lakeIn = (cwd, args) => spawnSync(SHIM, args, opts(cwd, queued));
const lake = (args) => lakeIn(LEAN_DIR, args);
const lakeNow = (args) => spawnSync(SHIM, args, opts(LEAN_DIR, { ...lakeEnv, PEQUALNP_IN_QUEUE: '1' }));
const tail = (r, n = 30) => (r.stdout + r.stderr).trim().split('\n').slice(-n).join('\n');

// The verifier is part of the checker: built from this repository, by the pinned toolchain.
stage('building the verifier');
const exe = lakeIn(CHECKER_LEAN_DIR, ['build', 'checklemma']);
if (exe.error || exe.status !== 0) fault(`the verifier did not build.\n${exe.error?.message ?? tail(exe)}`);
// The verifier that judges is the one that was just built: the same bytes before the judged
// build and after it.
const VERIFIER = join(CHECKER_LEAN_DIR, '.lake', 'build', 'bin', 'checklemma');
const verifierHash = sha256(readFileSync(VERIFIER));

// 1. The file builds in the pinned environment, and so does the definitions root.
stage('building the file and the definitions root');
const build = lake(['build', `+${module}`, `+${DEFS_ROOT}`]);
if (build.error) fault(`the build could not run: ${build.error.message}`);
if (build.status !== 0) {
  // "Does not compile" is a verdict on the file only when Lean reported an error in a project
  // source file. A build that failed any other way is a fault, and says nothing of the proof.
  const inSource = new RegExp(`^error: (\\./)?(${LIBRARIES.join('|')})[/A-Za-z0-9_]*\\.lean:`, 'm');
  if (build.status === null || !inSource.test(build.stdout + build.stderr)) fault(`the build failed for a reason that is not an error in a project file.\n${tail(build)}`);
  out(tail(build));
  reject('does-not-compile', `${module} does not build in the pinned environment`);
}
const fixedFault = () => {
  if (sha256(readFileSync(VERIFIER)) !== verifierHash) return 'the verifier binary changed while the judged files were built';
  const c = configFault();
  return c ? `the build configuration of the judged tree changed while the checker ran: ${c}` : null;
};
const moved = fixedFault();
if (moved) fault(`${moved}. Nothing was judged.`);

// 2 to 4. Read the compiled result.
// The checker's own verifier binary, run with the judged tree's search path.
// It reads the statement from a private copy of the bytes read at the start.
const PRIVATE = mkdtempSync(join(tmpdir(), 'pequalnp-check-'));
process.on('exit', () => { try { rmSync(PRIVATE, { recursive: true, force: true }); } catch { /* gone */ } });
const statementCopy = join(PRIVATE, 'statement.lean');
writeFileSync(statementCopy, statementBytes, { mode: 0o400 });
stage('verifier reading the built file');
const verify = lakeNow(['env', VERIFIER, module, statementCopy, kind]);
if (verify.error) fault(`the verifier could not run: ${verify.error.message}`);
if (!readFileSync(statementCopy).equals(statementBytes)) fault('the private copy of the statement changed while the verifier ran. Nothing was judged.');
const movedAfter = fixedFault();
if (movedAfter) fault(`${movedAfter}. Nothing was judged.`);
const lines = verify.stdout.trim().split('\n');
const last = lines.at(-1) ?? '';
const say = (keep) => { writeAll(1, lines.filter(keep).join('\n') + '\n'); writeAll(2, verify.stderr); };
// A REJECTED line anywhere is a rejection, whatever the exit status says.
if (lines.some((l) => l.startsWith('REJECTED'))) { say(() => true); process.exit(1); }
// Neither a REJECTED line nor an acceptance: the verifier did not reach a verdict. A fault.
if (verify.status !== 0 || !last.startsWith('ACCEPTED')) { say(() => true); fault(`the verifier ended without a verdict (exit ${verify.status}).`); }

// Accepted. Hash the source of everything it rests on, then confirm nothing moved since the build.
const listed = (tag) => (lines.find((l) => l.startsWith(`${tag} `)) ?? '').split(' ').slice(1).filter(Boolean);
const hashed = (mods) => mods.sort().map((m) => {
  const src = join(LEAN_DIR, ...m.split('.')) + '.lean';
  if (!existsSync(src)) fault(`the source of ${m}, which the proof rests on, is not in the judged tree (${src}). Run it again on the finished files.`);
  return { module: m, sha256: sha256(readFileSync(src)) };
});
const manifest = { rests_on: hashed(listed('MODULES')), defs: hashed(listed('DEFS')) };
if (!manifest.rests_on.some((m) => m.module === module)) fault('the verifier did not list the lemma module among what it checked');
const fresh = lake(['build', '--no-build', `+${module}`, `+${DEFS_ROOT}`]);
if (fresh.error || fresh.status !== 0) fault('a source file changed while the checker ran. Run it again on the finished files.');
say((l) => !l.startsWith('MODULES ') && !l.startsWith('DEFS ') && l !== last);
out(`MANIFEST ${JSON.stringify(manifest)}`);
out(last);
process.exit(0);
