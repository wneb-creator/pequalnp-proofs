#!/usr/bin/env python3
"""Activate a coherent replacement and retire exactly five audited obsolete files."""
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
import sys

import compact_cache as cc


def identity(path):
    st = Path(path).lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise RuntimeError(f'not a unique regular obsolete file: {path}')
    return {'dev': st.st_dev, 'ino': st.st_ino, 'size': st.st_size,
            'mtime_ns': st.st_mtime_ns, 'mode': stat.S_IMODE(st.st_mode)}


def gzip_digest(path):
    h = hashlib.sha256()
    count = 0
    with gzip.open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            count += len(block)
            h.update(block)
    return count, h.hexdigest()


class Retirement:
    def __init__(self, settings):
        self.s = settings
        self.directory = Path(settings['retirement_dir'])
        self.directory.mkdir(parents=True, exist_ok=True)
        self.journal = self.directory / 'retirement.json'
        self.original = cc.read_json(settings['original_config'])
        self.generation = cc.read_json(settings['generation_config'])
        self.plan = cc.read_json(settings['prune_plan'])
        self.expected_paths = {
            self.original['editor_pack'], self.original['editor_index'],
            self.original['editor_manifest'],
            str(Path(self.original['state_dir']) / 'extra.zstpack'),
            str(Path(self.original['state_dir']) / 'prepared.json')}
        if set(settings['obsolete']) != self.expected_paths or len(self.expected_paths) != 5:
            raise RuntimeError('retirement must cover exactly the five original data paths')
        if self.expected_paths.intersection(settings['pinned_files']):
            raise RuntimeError('obsolete file also marked as retained')
        source = settings['storage_source']
        self.storage_module = cc.load_storage(source, settings['pinned_files'][source])
        self.storage = self.storage_module.Storage(self.generation)

    @contextlib.contextmanager
    def locked(self):
        path = Path(self.s['phase_lock'])
        with path.open('r+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            left = os.fstat(lock.fileno())
            right = (Path(self.generation['state_dir']) / 'phase.lock').stat()
            if (left.st_dev, left.st_ino) != (right.st_dev, right.st_ino):
                raise RuntimeError('generation does not share original phase lock')
            yield

    def write_journal(self, value):
        cc.atomic(self.journal, value)

    def guard_context(self):
        for path, expected in self.s['pinned_files'].items():
            if Path(path).is_symlink() or cc.sha(path) != expected:
                raise RuntimeError(f'pinned retained input changed: {path}')
        for path in self.s['journals']:
            p = Path(path)
            if p.exists() and cc.read_json(p).get('status') != 'restored':
                raise RuntimeError(f'active storage journal: {path}')
        for path in self.s['review_reports']:
            if cc.read_json(path).get('status') != 'PASS':
                raise RuntimeError('independent replacement review did not pass')
        for gate in self.s['gates']:
            outcome = cc.read_json(gate['path'])
            if not outcome.get('passed'):
                raise RuntimeError('required no-build gate did not pass')
            if [c['argv'] for c in outcome['commands']] != self.s['no_build_commands']:
                raise RuntimeError('no-build command changed')
            for index, command in enumerate(outcome['commands']):
                if command['status'] != 0:
                    raise RuntimeError('no-build command failed')
                for stream in ('stdout', 'stderr'):
                    p = Path(gate['path']).with_name(Path(gate['path']).stem + f'-{index}.{stream}')
                    if cc.sha(p) != command[stream + '_sha256']:
                        raise RuntimeError('no-build evidence changed')
        core = cc.read_json(self.s['core_config'])
        if core['base_journal'] != str(Path(self.generation['state_dir']) / 'transaction.json'):
            raise RuntimeError('core phase uses a different base journal')
        if core['phase_lock'] != self.s['phase_lock'] or self.generation['phase_lock'] != self.s['phase_lock']:
            raise RuntimeError('configuration does not share the phase lock')
        commands = cc.read_json(self.s['commands'])
        for item in commands['required_files']:
            if self.s['pinned_files'].get(item['path']) != item['sha256']:
                raise RuntimeError('launcher input is not identically pinned')
        base_args = commands['base_command']
        core_args = commands['core_command']
        if base_args[base_args.index('--config') + 1] != self.s['generation_config']:
            raise RuntimeError('launcher uses a different base configuration')
        if core_args[core_args.index('--config') + 1] != self.s['core_config']:
            raise RuntimeError('launcher uses a different core configuration')
        staged = cc.read_json(self.s['staged_handoff'])
        for action in ('enter', 'restore'):
            argv = staged['phase_' + action]
            if argv[argv.index('--commands') + 1] != self.s['commands']:
                raise RuntimeError('handoff uses a different command bundle')
            if argv[argv.index('--commands-sha256') + 1] != self.s['pinned_files'][self.s['commands']]:
                raise RuntimeError('handoff command hash differs')
            if argv[-1] != action:
                raise RuntimeError('handoff action differs')

    def guard_old(self, path):
        expected = self.s['obsolete'][path]
        if identity(path) != expected['identity'] or cc.sha(path) != expected['sha256']:
            raise RuntimeError(f'original file changed: {path}')
        if self.plan['source_hashes'][path] != expected['sha256']:
            raise RuntimeError('original differs from immutable prune provenance')

    def verify_replacement(self):
        old = cc.read_json(self.s['original_prepared_gzip'])['files']
        removed = {r['path'] for r in self.plan['files']}
        rows = cc.read_json(Path(self.generation['state_dir']) / 'prepared.json')['files']
        libraries = {r['path']: r for r in self.generation['shared_library_whitelist']}
        if len(libraries) != 2 or set(rows) != (set(old) - removed) | set(libraries):
            raise RuntimeError('replacement is not exact retained set plus two libraries')
        for path, row in rows.items():
            expected = libraries[path] if path in libraries else old[path]
            for key in ('size', 'mode', 'mtime_ns', 'sha256'):
                if row[key] != expected[key]:
                    raise RuntimeError('replacement content metadata changed')
            if row['pack'] not in (self.generation['editor_pack'], str(self.storage.extra_pack)):
                raise RuntimeError('replacement still refers to an obsolete pack')
            self.storage.backup_bytes(row)
        baseline = self.storage.baseline()
        if set(baseline) - set(rows):
            raise RuntimeError('replacement baseline resurrects removed rows')
        for path, row in baseline.items():
            if row != rows[path]:
                raise RuntimeError('replacement baseline and prepared disagree')
        return len(rows)

    def archive_metadata(self, source, target):
        expected = self.s['obsolete'][str(source)]
        if target.exists():
            if target.is_symlink() or gzip_digest(target) != (expected['identity']['size'], expected['sha256']):
                raise RuntimeError('existing compressed metadata snapshot differs')
            return
        temp = target.with_name(target.name + '.new')
        cc.discard_owned_temp(temp)
        with open(source, 'rb') as src, temp.open('xb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as compressed:
                shutil.copyfileobj(src, compressed, 1024 * 1024)
            raw.flush()
            os.fsync(raw.fileno())
        if gzip_digest(temp) != (expected['identity']['size'], expected['sha256']):
            raise RuntimeError('compressed metadata failed exact reconstruction')
        os.replace(temp, target)
        cc.syncdir(target.parent)

    def prepare(self):
        self.guard_context()
        if self.journal.exists():
            raise RuntimeError('retirement already prepared; use run to resume')
        for path in self.expected_paths:
            self.guard_old(path)
        rows = self.verify_replacement()
        archives = {}
        for key, label in (('editor_index', 'old-index.tsv.gz'), ('editor_manifest', 'old-manifest.jsonl.gz')):
            source = Path(self.original[key])
            target = self.directory / label
            self.archive_metadata(source, target)
            archives[str(source)] = {'path': str(target), 'sha256': cc.sha(target)}
        prepared = str(Path(self.original['state_dir']) / 'prepared.json')
        snapshot = Path(self.s['original_prepared_gzip'])
        expected = self.s['obsolete'][prepared]
        if gzip_digest(snapshot) != (expected['identity']['size'], expected['sha256']):
            snapshot = self.directory / 'old-prepared.json.gz'
            self.archive_metadata(Path(prepared), snapshot)
        archives[prepared] = {'path': str(snapshot), 'sha256': cc.sha(snapshot)}
        active = Path(self.s['active_handoff'])
        if active.is_symlink() or cc.sha(active) != self.s['old_handoff_sha256']:
            raise RuntimeError('active handoff differs from expected original')
        backup = self.directory / 'original-handoff.json'
        if backup.is_symlink() or (backup.exists() and not backup.is_file()):
            raise RuntimeError('unsafe original handoff backup')
        if not backup.exists():
            temporary = backup.with_name(backup.name + '.new')
            cc.discard_owned_temp(temporary)
            cc.copy_durable(active, temporary)
            os.replace(temporary, backup)
            cc.syncdir(backup.parent)
        if cc.sha(backup) != self.s['old_handoff_sha256']:
            raise RuntimeError('handoff snapshot differs')
        self.write_journal({'status': 'prepared', 'settings_sha256': self.s['settings_sha256'],
                            'replacement_rows': rows, 'archives': archives,
                            'original_handoff_mode': stat.S_IMODE(active.stat().st_mode),
                            'files': {p: 'pending' for p in sorted(self.expected_paths)}})

    def verify_archives(self, journal):
        backup = self.directory / 'original-handoff.json'
        if backup.is_symlink() or not backup.is_file() or cc.sha(backup) != self.s['old_handoff_sha256']:
            raise RuntimeError('original handoff backup changed')
        for original, archive in journal['archives'].items():
            expected = self.s['obsolete'][original]
            if cc.sha(archive['path']) != archive['sha256'] or gzip_digest(archive['path']) != (
                    expected['identity']['size'], expected['sha256']):
                raise RuntimeError('metadata recovery snapshot changed')

    def run(self, interrupt=None):
        self.guard_context()
        journal = cc.read_json(self.journal)
        if journal['settings_sha256'] != self.s['settings_sha256']:
            raise RuntimeError('retirement settings changed after preparation')
        if set(journal['files']) != self.expected_paths:
            raise RuntimeError('retirement journal path set changed')
        self.verify_archives(journal)
        self.verify_replacement()
        # Check every remaining original before activating anything.
        for path, status in journal['files'].items():
            if Path(path).exists() or Path(path).is_symlink():
                self.guard_old(path)
            elif status not in ('unlinking', 'removed'):
                raise RuntimeError('original vanished without a durable unlink plan')
        active = Path(self.s['active_handoff'])
        if active.is_symlink():
            raise RuntimeError('active handoff is a symlink')
        current = cc.sha(active)
        desired = self.s['pinned_files'][self.s['staged_handoff']]
        if current == self.s['old_handoff_sha256']:
            if journal['status'] not in ('prepared', 'activating'):
                raise RuntimeError('old handoff reappeared after retirement activation')
            journal['status'] = 'activating'
            self.write_journal(journal)
            temporary = active.with_name(active.name + '.retirement-new')
            cc.discard_owned_temp(temporary)
            with open(self.s['staged_handoff'], 'rb') as src, temporary.open('xb') as dst:
                shutil.copyfileobj(src, dst)
                dst.flush()
                os.fchmod(dst.fileno(), journal['original_handoff_mode'])
                os.fsync(dst.fileno())
            if cc.sha(temporary) != desired:
                raise RuntimeError('handoff copy hash differs')
            os.replace(temporary, active)
            cc.syncdir(active.parent)
        elif current != desired or journal['status'] not in ('activating', 'active', 'retiring', 'complete'):
            raise RuntimeError('active handoff changed unexpectedly')
        cc.syncdir(active.parent)
        journal['status'] = 'active'
        self.write_journal(journal)
        if interrupt == 'after-activation':
            raise RuntimeError('injected interruption after activation')
        for path in sorted(self.expected_paths):
            if journal['files'][path] == 'removed':
                if Path(path).exists() or Path(path).is_symlink():
                    raise RuntimeError('retired original path reappeared')
                continue
            journal['status'] = 'retiring'
            journal['files'][path] = 'unlinking'
            self.write_journal(journal)
            p = Path(path)
            if p.exists() or p.is_symlink():
                self.guard_old(path)
                p.unlink()
                if interrupt == 'after-first-unlink':
                    raise RuntimeError('injected interruption after unlink')
            cc.syncdir(p.parent)
            journal['files'][path] = 'removed'
            self.write_journal(journal)
        journal['status'] = 'complete'
        self.write_journal(journal)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--settings', required=True)
    parser.add_argument('--settings-sha256', required=True)
    parser.add_argument('action', choices=('prepare', 'run'))
    args = parser.parse_args()
    if cc.sha(args.settings) != args.settings_sha256:
        raise RuntimeError('retirement settings pin differs')
    settings = cc.read_json(args.settings)
    settings['settings_sha256'] = args.settings_sha256
    obj = Retirement(settings)
    with obj.locked():
        getattr(obj, args.action)()
    print(json.dumps({'action': args.action, 'status': 'complete'}), file=sys.stderr)


if __name__ == '__main__':
    main()
