import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync, writeSync } from 'node:fs';
import { dirname, join } from 'node:path';
const [VERIFIER, python, observer] = process.argv.slice(2);
const LEAN_DIR = '/workspace/pequalnp-proofs/lean';
const TREE = dirname(LEAN_DIR);
const CONFIG = ['lean/lakefile.toml', 'lean/lake-manifest.json', 'lean/lean-toolchain'];
const writeAll = (fd, text) => {
  const buf = Buffer.from(text);
  for (let off = 0; off < buf.length;) {
    try { off += writeSync(fd, buf, off, buf.length - off); } catch (e) { if (e.code !== 'EAGAIN') throw e; Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 5); }
  }
};
const T0 = Date.now();
const stage = name => writeAll(2, `synthetic stage: ${name} t=${Math.round((Date.now() - T0) / 1000)}s\n`);
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const git = args => spawnSync('git', ['-C', TREE, ...args], { encoding: 'utf8', timeout: 60000 });
const configFault = () => {
  if (existsSync(join(LEAN_DIR, 'lakefile.lean'))) return 'unexpected lakefile.lean';
  const tracked = git(['ls-files', '--error-unmatch', '--', ...CONFIG]);
  if (tracked.error || tracked.status !== 0) return 'untracked config';
  const same = git(['diff', '--quiet', 'HEAD', '--', ...CONFIG]);
  if (same.error || same.status !== 0) return 'changed config';
  return null;
};
const configNow = configFault();
if (configNow) throw Error(configNow);
const lakeEnv = Object.fromEntries(Object.entries(process.env).filter(([k]) => !/^(LAKE($|_)|LEAN_|ELAN_TOOLCHAIN$)/.test(k)));
lakeEnv.LAKE_ARTIFACT_CACHE = 'false';
const opts = (cwd, env) => ({ cwd, encoding: 'utf8', timeout: 30 * 60 * 1000, maxBuffer: 64 * 1024 * 1024, env });
const { PEQUALNP_IN_QUEUE, ...queued } = lakeEnv;
const syntheticChild = env => spawnSync(python, [observer, String(process.pid)], opts(LEAN_DIR, env));
stage('building the verifier');
const exe = syntheticChild(queued);
if (exe.error || exe.status !== 0) throw Error('synthetic child failed');
const verifierHash = sha256(readFileSync(VERIFIER));
stage('building the file and the definitions root');
const build = syntheticChild(queued);
if (build.error || build.status !== 0) throw Error('synthetic child failed');
const fixedFault = () => {
  if (sha256(readFileSync(VERIFIER)) !== verifierHash) return 'verifier changed';
  const c = configFault();
  return c ? `configuration changed: ${c}` : null;
};
const moved = fixedFault();
if (moved) throw Error(moved);
const PRIVATE = mkdtempSync('/tmp/oec/pequalnp-pilot-45/node-gc-probe/faithful-statement-');
process.on('exit', () => { try { rmSync(PRIVATE, { recursive: true, force: true }); } catch {} });
const statementCopy = join(PRIVATE, 'statement.lean');
writeFileSync(statementCopy, 'True', { mode: 0o400 });
stage('verifier reading the built file');
const verify = syntheticChild({ ...lakeEnv, PEQUALNP_IN_QUEUE: '1' });
if (verify.error || verify.status !== 0) throw Error('synthetic child failed');
writeAll(1, JSON.stringify({stage: 'faithful_second_hash_then_verify', verifierHash, ...JSON.parse(verify.stdout)}) + '\n');
