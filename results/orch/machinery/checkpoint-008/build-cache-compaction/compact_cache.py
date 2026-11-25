#!/usr/bin/env python3
"""Reversible pruning and generation staging; never activates or deletes old packs."""
import argparse
import contextlib
import fcntl
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def read_json(path):
    op = gzip.open if str(path).endswith('.gz') else open
    with op(path, 'rt') as f:
        return json.load(f)


def syncdir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def discard_owned_temp(path):
    try:
        st = path.lstat()
    except FileNotFoundError:
        return
    if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1:
        raise RuntimeError(f'unsafe transaction temporary: {path}')
    path.unlink()


def atomic(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + '.new')
    discard_owned_temp(tmp)
    with tmp.open('x') as f:
        json.dump(value, f, separators=(',', ':'))
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)
    syncdir(path.parent)


def gzjson(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + '.new')
    discard_owned_temp(tmp)
    with tmp.open('xb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as compressed:
            compressed.write(json.dumps(value, separators=(',', ':')).encode())
            compressed.write(b'\n')
        raw.flush()
        os.fsync(raw.fileno())
    os.replace(tmp, path)
    syncdir(path.parent)


def copy_durable(source, target):
    if Path(target).exists():
        if Path(target).is_symlink() or sha(source) != sha(target):
            raise RuntimeError('snapshot copy differs from original')
        return
    with open(source, 'rb') as src, open(target, 'xb') as dst:
        shutil.copyfileobj(src, dst, 1024 * 1024)
        dst.flush()
        os.fsync(dst.fileno())
    syncdir(Path(target).parent)


def load_storage(path, expected_sha):
    if sha(path) != expected_sha:
        raise RuntimeError('storage implementation hash changed')
    spec = importlib.util.spec_from_file_location('reviewed_storage', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class Transaction:
    def __init__(self, settings):
        self.settings = settings
        self.directory = Path(settings['transaction_dir'])
        self.generation = Path(settings['generation_dir'])
        self.config_path = Path(settings['source_config'])
        self.config = read_json(self.config_path)
        self.module = load_storage(settings['storage_source'], settings['storage_sha256'])
        self.storage = self.module.Storage(self.config)
        self.status_path = self.directory / 'status.json'
        self.plan_path = self.directory / 'plan.json.gz'
        self.directory.mkdir(parents=True, exist_ok=True)

    @contextlib.contextmanager
    def locked(self):
        with (self.storage.state / 'phase.lock').open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if self.storage.journal.exists():
                if read_json(self.storage.journal).get('status') != 'restored':
                    raise RuntimeError('storage transaction is active')
            yield

    def mark(self, status, **extra):
        old = read_json(self.status_path) if self.status_path.exists() else {}
        atomic(self.status_path, {**old, 'status': status, **extra})

    def plan(self):
        if not self.plan_path.exists():
            raise RuntimeError('no completed plan')
        plan = read_json(self.plan_path)
        if sha(self.plan_path) != read_json(self.status_path)['plan_sha256']:
            raise RuntimeError('immutable transaction plan changed')
        if sha(self.config_path) != plan['source_config_sha256']:
            raise RuntimeError('source configuration changed')
        return plan

    def exact_path(self, path, row):
        p = Path(path)
        if p.is_symlink() or not p.is_file():
            raise RuntimeError(f'not a regular source: {p}')
        before = p.stat()
        if before.st_size != row['size'] or sha(p) != row['sha256']:
            raise RuntimeError(f'source bytes changed: {p}')
        after = p.stat()
        if (before.st_ino, before.st_size, before.st_mtime_ns) != (
                after.st_ino, after.st_size, after.st_mtime_ns):
            raise RuntimeError(f'source moved during read: {p}')
        return before

    def allowed(self, row, build_modules, full_modules):
        name = row['module']
        if name in build_modules or name not in full_modules or not (name == 'Mathlib' or name.startswith('Mathlib.')):
            return False
        relative = Path(*name.split('.'))
        p = Path(row['path'])
        mathlib = self.storage.mathlib
        if p == mathlib / relative.with_suffix('.lean'):
            return True
        prefixes = [mathlib / '.lake/build/lib/lean', mathlib / '.lake/build/ir']
        suffixes = ('.c', '.ilean', '.trace', '.c.hash', '.ilean.hash', '.ir.hash',
                    '.ir.sig.hash', '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.setup.json')
        return any(p == Path(str(prefix / relative) + suffix)
                   for prefix in prefixes for suffix in suffixes)

    def snapshot(self):
        if self.plan_path.exists() or self.status_path.exists() or self.generation.exists():
            raise RuntimeError('transaction or generation already exists')
        for name, expected in self.settings['input_sha256'].items():
            if sha(self.settings[name]) != expected:
                raise RuntimeError(f'input changed: {name}')
        build = read_json(self.settings['build_graph'])['modules']
        full = read_json(self.settings['runtime_graph'])['modules']
        prepared = read_json(self.storage.prepared)['files']
        selected = []
        seen = set()
        with gzip.open(self.settings['candidates'], 'rt') as f:
            for line in f:
                candidate = json.loads(line)
                p = candidate['path']
                if p in seen or not self.allowed(candidate, build, full):
                    raise RuntimeError(f'duplicate or ineligible candidate: {p}')
                seen.add(p)
                row = dict(prepared[p])
                for key in ('size', 'sha256', 'pack', 'offset', 'compressed'):
                    if row.get(key) != candidate.get(key):
                        raise RuntimeError(f'candidate backup metadata changed: {p}')
                st = self.exact_path(p, row)
                self.storage.backup_bytes(row)
                rollback_temp = Path(p).with_name(Path(p).name + '.cache-rollback')
                if rollback_temp.exists() or rollback_temp.is_symlink():
                    raise RuntimeError(f'rollback temporary already exists before transaction: {rollback_temp}')
                row.update(mode=stat.S_IMODE(st.st_mode), mtime_ns=st.st_mtime_ns,
                           allocated=st.st_blocks * 512, module=candidate['module'])
                selected.append(row)
        packs = sorted({r['pack'] for r in prepared.values()})
        sources = [self.config_path, self.storage.prepared, Path(self.config['editor_index']),
                   Path(self.config['editor_manifest']), *map(Path, packs)]
        source_hashes = {str(p): sha(p) for p in sources}
        copy_durable(self.config_path, self.directory / 'original-config.json')
        gzjson(self.directory / 'original-prepared.json.gz', {'files': prepared})
        plan = {'version': 1, 'source_config_sha256': sha(self.config_path),
                'source_hashes': source_hashes, 'files': selected,
                'build_graph_sha256': sha(self.settings['build_graph']),
                'runtime_graph_sha256': sha(self.settings['runtime_graph']),
                'generation': str(self.generation),
                'raw': sum(r['size'] for r in selected),
                'allocated': sum(r['allocated'] for r in selected)}
        gzjson(self.plan_path, plan)
        self.mark('planned', selected=len(selected), plan_sha256=sha(self.plan_path))

    def prune(self, stop_after=None):
        plan = self.plan()
        status = read_json(self.status_path)['status']
        if status not in ('planned', 'pruning'):
            raise RuntimeError('prune requires planned or interrupted pruning state')
        self.mark('pruning')
        count = 0
        for row in plan['files']:
            p = Path(row['path'])
            if status == 'planned' and not p.exists():
                raise RuntimeError(f'planned source vanished before prune: {p}')
            if p.exists() or p.is_symlink():
                st = self.exact_path(p, row)
                if stat.S_IMODE(st.st_mode) != row['mode'] or st.st_mtime_ns != row['mtime_ns']:
                    raise RuntimeError(f'source metadata changed before prune: {p}')
                self.storage.backup_bytes(row)
                p.unlink()
                syncdir(p.parent)
                count += 1
                if stop_after is not None and count == stop_after:
                    raise RuntimeError('injected pruning interruption')
        self.mark('pruned')

    def rollback(self):
        plan = self.plan()
        self.mark('rolling_back')
        for row in plan['files']:
            p = Path(row['path'])
            if p.exists() or p.is_symlink():
                st = self.exact_path(p, row)
                if stat.S_IMODE(st.st_mode) != row['mode'] or st.st_mtime_ns != row['mtime_ns']:
                    raise RuntimeError(f'cannot overwrite changed original metadata: {p}')
                continue
            data = self.storage.backup_bytes(row)
            tmp = p.with_name(p.name + '.cache-rollback')
            discard_owned_temp(tmp)
            with tmp.open('xb') as f:
                f.write(data)
                f.flush()
                os.fchmod(f.fileno(), row['mode'])
                os.utime(f.fileno(), ns=(row['mtime_ns'], row['mtime_ns']))
                os.fsync(f.fileno())
            if sha(tmp) != row['sha256']:
                raise RuntimeError('rollback write failed hash verification')
            os.replace(tmp, p)
            syncdir(p.parent)
        self.mark('rolled_back')

    def gate(self, label):
        if label not in ('after-prune', 'after-stage'):
            raise RuntimeError('invalid gate label')
        plan = self.plan()
        if any(Path(r['path']).exists() or Path(r['path']).is_symlink() for r in plan['files']):
            raise RuntimeError('pruned rows unexpectedly reappeared')
        commands = self.settings['no_build_commands']
        outcomes = []
        for i, argv in enumerate(commands):
            if '--no-build' not in argv or 'build' not in argv:
                raise RuntimeError('only explicit no-build commands are allowed')
            stdout = self.directory / f'{label}-{i}.stdout'
            stderr = self.directory / f'{label}-{i}.stderr'
            with stdout.open('xb') as out, stderr.open('xb') as err:
                result = subprocess.run(argv, cwd=self.settings['workdir'], stdout=out, stderr=err)
            outcomes.append({'argv': argv, 'status': result.returncode,
                             'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)})
            if result.returncode:
                atomic(self.directory / f'{label}.json', {'passed': False, 'commands': outcomes})
                self.rollback()
                raise RuntimeError('no-build failed; original files restored')
        atomic(self.directory / f'{label}.json', {'passed': True, 'commands': outcomes})

    def compact(self):
        plan = self.plan()
        if read_json(self.status_path)['status'] != 'pruned':
            raise RuntimeError('generation requires successfully pruned state')
        if not read_json(self.directory / 'after-prune.json')['passed']:
            raise RuntimeError('missing successful original no-build gate')
        if self.generation.exists():
            raise RuntimeError('generation already exists; inspect incomplete generation separately')
        for path, expected in plan['source_hashes'].items():
            if sha(path) != expected:
                raise RuntimeError(f'original backup metadata changed: {path}')
        removed = {row['path'] for row in plan['files']}
        old = read_json(self.storage.prepared)['files']
        retained = {p: dict(row) for p, row in old.items() if p not in removed}
        editor = self.generation / 'editor'
        state = self.generation / 'state'
        editor.mkdir(parents=True)
        state.mkdir()
        os.link(self.storage.state / 'phase.lock', state / 'phase.lock')
        outputs = {self.config['editor_pack']: editor / 'data.zstpack',
                   str(self.storage.extra_pack): state / 'extra.zstpack'}
        unknown = {r['pack'] for r in retained.values()} - set(outputs)
        if unknown:
            raise RuntimeError('unrecognized backup packs; refuse to discard')
        for source, target in outputs.items():
            records = sorted((r for r in retained.values() if r['pack'] == source),
                             key=lambda r: (r['offset'], r['path']))
            seen = {}
            with open(source, 'rb') as src, target.open('xb') as dst:
                for row in records:
                    key = (row['offset'], row['compressed'], row['size'], row['sha256'])
                    if key not in seen:
                        self.storage.backup_bytes(row)
                        src.seek(row['offset'])
                        data = src.read(row['compressed'])
                        if len(data) != row['compressed']:
                            raise RuntimeError('short backup frame')
                        seen[key] = dst.tell()
                        dst.write(data)
                    row.update(offset=seen[key], pack=str(target))
                dst.flush()
                os.fsync(dst.fileno())
        baseline = self.storage.baseline()
        with open(self.config['editor_manifest']) as f:
            virtuals = {r['path']: r['virtual'] for r in map(json.loads, f)}
        with (editor / 'index.tsv').open('x') as index, (editor / 'manifest.jsonl').open('x') as manifest:
            for p, original in baseline.items():
                if p in removed:
                    continue
                row = retained[p]
                # Baseline may have been superseded by a later extra-pack version.
                # Excluding that baseline row is safe: prepared remains authoritative.
                if row['pack'] != str(editor / 'data.zstpack'):
                    continue
                virtual = virtuals[p]
                index.write(f"{virtual}\t{row['mode']:o}\t{row['size']}\t{row['mtime_ns']}\t{row['offset']}\t{row['compressed']}\n")
                manifest.write(json.dumps({k: row[k] for k in ('path', 'size', 'mode', 'mtime_ns', 'sha256')} | {'virtual': virtual}, separators=(',', ':')) + '\n')
            for f in (index, manifest):
                f.flush()
                os.fsync(f.fileno())
        atomic(state / 'prepared.json', {'files': retained})
        config = dict(self.config)
        config.update(state_dir=str(state), editor_index=str(editor / 'index.tsv'),
                      editor_manifest=str(editor / 'manifest.jsonl'), editor_pack=str(editor / 'data.zstpack'))
        atomic(self.generation / 'storage_config.json', config)
        self.verify_generation()
        self.mark('staged', generation=str(self.generation))

    def verify_generation(self):
        plan = self.plan()
        removed = {row['path'] for row in plan['files']}
        before = read_json(self.directory / 'original-prepared.json.gz')['files']
        config = read_json(self.generation / 'storage_config.json')
        fresh = self.module.Storage(config)
        rows = read_json(fresh.prepared)['files']
        if set(rows) != set(before) - removed:
            raise RuntimeError('generation rows differ from exact retained set')
        baseline = fresh.baseline()
        if set(baseline) - set(rows):
            raise RuntimeError('baseline resurrects discarded paths')
        for p, row in rows.items():
            for key in ('size', 'sha256', 'mode', 'mtime_ns'):
                if row[key] != before[p][key]:
                    raise RuntimeError('retained metadata changed')
            fresh.backup_bytes(row)
        a = (self.storage.state / 'phase.lock').stat()
        b = (fresh.state / 'phase.lock').stat()
        if (a.st_dev, a.st_ino) != (b.st_dev, b.st_ino):
            raise RuntimeError('phase lock inode differs')
        files = [fresh.prepared, fresh.extra_pack, self.generation / 'storage_config.json',
                 *[Path(config[k]) for k in ('editor_index', 'editor_manifest', 'editor_pack')]]
        atomic(self.directory / 'generation-verification.json',
               {'passed': True, 'rows': len(rows), 'removed': len(removed),
                'files': {str(p): {'sha256': sha(p), 'size': p.stat().st_size} for p in files},
                'activation': 'not performed', 'old_backups': 'all retained'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--settings', required=True)
    parser.add_argument('action', choices=['snapshot', 'prune', 'gate-prune', 'compact', 'verify', 'gate-stage', 'rollback'])
    args = parser.parse_args()
    transaction = Transaction(read_json(args.settings))
    with transaction.locked():
        actions = {'snapshot': transaction.snapshot, 'prune': transaction.prune,
                   'gate-prune': lambda: transaction.gate('after-prune'), 'compact': transaction.compact,
                   'verify': transaction.verify_generation, 'gate-stage': lambda: transaction.gate('after-stage'),
                   'rollback': transaction.rollback}
        actions[args.action]()
    print(json.dumps({'action': args.action, 'status': 'complete'}), file=sys.stderr)


if __name__ == '__main__':
    main()
