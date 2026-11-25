#!/usr/bin/python3
"""Pinned, restartable activation and separately authorized obsolete-data retirement."""
import argparse
import contextlib
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import signal
import stat
import tempfile
import time

ROOT = Path('/tmp/oec/pequalnp-pilot-45')
PROTECTED_PID = 42728


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def identity(path, unique=True):
    s = Path(path).lstat()
    if not stat.S_ISREG(s.st_mode) or (unique and s.st_nlink != 1):
        raise RuntimeError(f'not a unique regular file: {path}')
    return dict(dev=s.st_dev, ino=s.st_ino, size=s.st_size,
                mode=stat.S_IMODE(s.st_mode), mtime_ns=s.st_mtime_ns)


def confined(path):
    p = Path(path)
    if not p.is_absolute() or '..' in p.parts or not p.is_relative_to(ROOT):
        raise RuntimeError('path outside job scratch')
    for parent in (p, *p.parents):
        if parent == ROOT.parent:
            break
        if parent.is_symlink():
            raise RuntimeError(f'symlink is not allowed: {parent}')
    return p


def syncdir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_bytes(path, data, mode=0o600, mtime_ns=None):
    p = confined(path)
    if p.exists():
        identity(p)
    fd, temp = tempfile.mkstemp(prefix=p.name + '.new-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
            stream.flush()
            os.fchmod(stream.fileno(), mode)
            if mtime_ns is not None:
                os.utime(stream.fileno(), ns=(mtime_ns, mtime_ns))
            os.fsync(stream.fileno())
        os.replace(temp, p)
        syncdir(p.parent)
    finally:
        if os.path.lexists(temp):
            os.unlink(temp)


def read_json(path):
    identity(path)
    with open(path) as stream:
        return json.load(stream)


def gzip_raw_digest(path):
    identity(path)
    h, size = hashlib.sha256(), 0
    with gzip.open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
            size += len(block)
    return size, h.hexdigest()


def process_start(pid):
    # stat is public process metadata; no argv or environment is read.
    return int(Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19])


def no_live_lean():
    count = 0
    for entry in os.scandir('/proc'):
        if not entry.name.isdigit():
            continue
        count += 1
        if count > 16384:
            raise RuntimeError('process census exceeded bound')
        try:
            comm = (Path(entry.path) / 'comm').read_text().strip()
            state = (Path(entry.path) / 'stat').read_text().rsplit(')', 1)[1].split()[0]
        except FileNotFoundError:
            continue
        if state != 'Z' and comm in ('lean', 'lake', 'checklemma', 'nativeCheckLemm', 'nativeCheckLemma'):
            raise RuntimeError(f'live Lean/Lake/native process: {entry.name}')


class Cutover:
    def __init__(self, settings_path, settings_sha256):
        if not all((hasattr(fcntl, 'F_GET_SEALS'), hasattr(os, 'pidfd_open'), hasattr(signal, 'pidfd_send_signal'))):
            raise RuntimeError('use installed /usr/bin/python3 with Linux pidfd/seal support')
        self.settings_path = confined(settings_path)
        identity(self.settings_path)
        if digest(self.settings_path) != settings_sha256:
            raise RuntimeError('settings pin differs')
        self.s = read_json(self.settings_path)
        self.settings_sha = settings_sha256
        if self.s['version'] != 1:
            raise RuntimeError('settings version differs')
        self.directory = confined(self.s['transaction_dir'])
        self.directory.mkdir(parents=True, exist_ok=True)
        self.journal = self.directory / 'transaction.json'
        self.backup = self.directory / 'original-handoff.json'
        self.active = confined(self.s['active_handoff'])
        self.staged = confined(self.s['new_handoff'])
        self.old_config = read_json(confined(self.s['old_base_config']))
        self.new_config = read_json(confined(self.s['new_base_config']))
        self.new_core = read_json(confined(self.s['new_core_config']))
        expected = {self.old_config[k] for k in ('editor_pack', 'editor_index', 'editor_manifest')}
        expected.update(str(Path(self.old_config['state_dir']) / n) for n in ('extra.zstpack', 'prepared.json'))
        self.obsolete = self.s['obsolete']
        if len(expected) != 5 or set(self.obsolete) != expected:
            raise RuntimeError('obsolete set must be exactly the five old generation files')
        self.metadata = {self.old_config['editor_index'], self.old_config['editor_manifest'],
                         str(Path(self.old_config['state_dir']) / 'prepared.json')}
        for p in self.obsolete:
            confined(p)
        if set(self.obsolete).intersection(self.s['required_pins']):
            raise RuntimeError('obsolete file also retained')
        mandatory = {str(self.staged), self.s['old_base_config'], self.s['new_base_config'],
                     self.s['new_core_config'], self.s['new_commands']}
        mandatory.update(self.new_config[k] for k in ('editor_pack', 'editor_index', 'editor_manifest'))
        mandatory.update(str(Path(self.new_config['state_dir']) / n) for n in ('extra.zstpack', 'prepared.json'))
        mandatory.update(str(Path(self.new_core['state_dir']) / n) for n in ('excluded.zstpack', 'prepared.json'))
        if not mandatory.issubset(self.s['required_pins']):
            raise RuntimeError('required generation input is not pinned')
        if len(self.s['review_reports']) < 2:
            raise RuntimeError('independent base and core review reports required')

    @contextlib.contextmanager
    def locked(self):
        p = confined(self.s['phase_lock'])
        identity(p, unique=False)
        with p.open('r+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            a = os.fstat(lock.fileno())
            for alias in self.s['lock_aliases']:
                b = confined(alias).stat()
                if (a.st_dev, a.st_ino) != (b.st_dev, b.st_ino):
                    raise RuntimeError('phase lock aliases differ')
            yield

    def save(self, journal):
        atomic_bytes(self.journal, (json.dumps(journal, indent=2) + '\n').encode())

    def guard_context(self):
        if digest(self.settings_path) != self.settings_sha:
            raise RuntimeError('settings changed')
        for path, sha in self.s['required_pins'].items():
            p = confined(path)
            identity(p)
            if digest(p) != sha:
                raise RuntimeError(f'required pin changed: {p}')
        for path in self.s['journals']:
            p = confined(path)
            if p.exists() and read_json(p).get('status') != 'restored':
                raise RuntimeError(f'active phase journal: {p}')
        for report in self.s['review_reports']:
            if report['path'] not in self.s['required_pins']:
                raise RuntimeError('review report is not pinned')
            value = read_json(report['path'])
            for key in report['keys']:
                value = value[key]
            if value != report['equals']:
                raise RuntimeError('review report did not pass')
        if self.new_config['phase_lock'] != self.s['phase_lock'] or self.new_core['phase_lock'] != self.s['phase_lock']:
            raise RuntimeError('new configuration phase lock differs')
        if self.new_core['base_journal'] != str(Path(self.new_config['state_dir']) / 'transaction.json'):
            raise RuntimeError('new core base journal differs')
        bundle = read_json(self.s['new_commands'])
        for key, config in [('base_command', 'new_base_config'), ('core_command', 'new_core_config')]:
            args = bundle[key]
            if args[args.index('--config') + 1] != self.s[config]:
                raise RuntimeError('command bundle points at another generation')
        for row in bundle['required_files']:
            if self.s['required_pins'].get(row['path']) != row['sha256']:
                raise RuntimeError('command input pin differs')
        handoff = read_json(self.staged)
        for action in ('enter', 'restore'):
            args = handoff['phase_' + action]
            if args[args.index('--commands') + 1] != self.s['new_commands'] or args[-1] != action:
                raise RuntimeError('handoff command path/action differs')
            if args[args.index('--commands-sha256') + 1] != self.s['required_pins'][self.s['new_commands']]:
                raise RuntimeError('handoff command pin differs')

    def guard_old(self, path):
        row = self.obsolete[path]
        if identity(path) != row['identity'] or digest(path) != row['sha256']:
            raise RuntimeError(f'obsolete file changed: {path}')

    def archive(self, path, number):
        expected = self.obsolete[path]
        target = confined(self.directory / f'old-metadata-{number}.gz')
        if not target.exists():
            fd, temp = tempfile.mkstemp(prefix='metadata-new-', dir=self.directory)
            try:
                with os.fdopen(fd, 'wb') as out, open(path, 'rb') as src:
                    with gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as packed:
                        for block in iter(lambda: src.read(1024 * 1024), b''):
                            packed.write(block)
                    out.flush()
                    os.fsync(out.fileno())
                os.replace(temp, target)
                syncdir(self.directory)
            finally:
                if os.path.lexists(temp):
                    os.unlink(temp)
        if gzip_raw_digest(target) != (expected['identity']['size'], expected['sha256']):
            raise RuntimeError('metadata archive reconstruction differs')
        return {'path': str(target), 'sha256': digest(target), 'raw_identity': expected['identity'],
                'raw_sha256': expected['sha256']}

    def load_journal(self):
        j = read_json(self.journal)
        if j['settings_sha256'] != self.settings_sha or set(j['files']) != set(self.obsolete):
            raise RuntimeError('transaction settings/path set differs')
        if identity(self.backup)['mode'] != j['old_handoff_identity']['mode'] or digest(self.backup) != self.s['old_handoff_sha256']:
            raise RuntimeError('durable original handoff differs')
        if self.backup.stat().st_mtime_ns != j['old_handoff_identity']['mtime_ns']:
            raise RuntimeError('durable original handoff metadata differs')
        if set(j['archives']) != self.metadata:
            raise RuntimeError('metadata snapshot set differs')
        for source, row in j['archives'].items():
            expected = self.obsolete[source]
            if digest(row['path']) != row['sha256'] or gzip_raw_digest(row['path']) != (expected['identity']['size'], expected['sha256']):
                raise RuntimeError('metadata snapshot differs')
            if row['raw_identity'] != expected['identity'] or row['raw_sha256'] != expected['sha256']:
                raise RuntimeError('metadata reconstruction attributes differ')
        return j

    def activate(self, interrupt=None):
        self.guard_context()
        if not self.journal.exists():
            for path in self.obsolete:
                self.guard_old(path)
            old = identity(self.active)
            if digest(self.active) != self.s['old_handoff_sha256']:
                raise RuntimeError('active handoff is not expected old version')
            if not self.backup.exists():
                atomic_bytes(self.backup, self.active.read_bytes(), old['mode'], old['mtime_ns'])
            if digest(self.backup) != self.s['old_handoff_sha256']:
                raise RuntimeError('old handoff backup differs')
            archives = {p: self.archive(p, n) for n, p in enumerate(sorted(self.metadata))}
            self.save(dict(status='prepared', settings_sha256=self.settings_sha, old_handoff_identity=old,
                           archives=archives, files={p: 'pending' for p in sorted(self.obsolete)}, holder='pending'))
        j = self.load_journal()
        current, desired = digest(self.active), self.s['required_pins'][str(self.staged)]
        if current == self.s['old_handoff_sha256']:
            if j['status'] not in ('prepared', 'activating'):
                raise RuntimeError('old handoff reappeared')
            for path in self.obsolete:
                self.guard_old(path)
            j['status'] = 'activating'
            self.save(j)
            atomic_bytes(self.active, self.staged.read_bytes(), j['old_handoff_identity']['mode'])
            if interrupt == 'after-replace':
                raise RuntimeError('fixture interruption after replace')
        elif current != desired or j['status'] not in ('activating', 'active', 'retiring', 'retired'):
            raise RuntimeError('unexpected active handoff/state')
        if digest(self.active) != desired:
            raise RuntimeError('installed handoff differs')
        if j['status'] in ('prepared', 'activating'):
            j['status'] = 'active'
            self.save(j)

    def active_journal(self):
        self.guard_context()
        j = self.load_journal()
        if j['status'] not in ('active', 'retiring', 'retired') or digest(self.active) != self.s['required_pins'][str(self.staged)]:
            raise RuntimeError('reviewed generation is not active')
        return j

    def retire_files(self, interrupt=None):
        j = self.active_journal()
        for path, state in j['files'].items():
            if os.path.lexists(path):
                if state == 'removed':
                    raise RuntimeError('retired path reappeared')
                self.guard_old(path)
            elif state not in ('unlinking', 'removed'):
                raise RuntimeError('old file vanished without durable plan')
        for path in j['files']:
            if j['files'][path] == 'removed':
                continue
            j['status'], j['files'][path] = 'retiring', 'unlinking'
            self.save(j)
            if os.path.lexists(path):
                self.guard_old(path)
                os.unlink(path)
                if interrupt == 'after-unlink':
                    raise RuntimeError('fixture interruption after unlink')
            syncdir(Path(path).parent)
            j['files'][path] = 'removed'
            self.save(j)
        j['status'] = 'retired'
        self.save(j)

    def retire_holder(self):
        j = self.active_journal()
        h = self.s['holder']
        pid = h['pid']
        if pid == PROTECTED_PID or pid <= 1:
            raise RuntimeError('raw artifact guardian is protected')
        if self.s.get('fixture'):
            if not self.directory.is_relative_to(ROOT / 'recompression-cutover' / 'fixtures'):
                raise RuntimeError('fixture outside isolated fixture directory')
        elif (pid, h['starttime'], h['dev'], h['ino'], h['fd'], h['seals']) != (51759, 1015128, 1, 24087, 4, 15):
            raise RuntimeError('production holder identity is not authorized')
        no_live_lean()
        try:
            start = process_start(pid)
        except FileNotFoundError:
            if j['holder'] not in ('signaling', 'retired'):
                raise RuntimeError('holder disappeared without durable signal plan')
            j['holder'] = 'retired'
            self.save(j)
            return
        if start != h['starttime']:
            raise RuntimeError('holder identity changed/reappeared')
        state = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0]
        if state == 'Z' and j['holder'] in ('signaling', 'retired'):
            j['holder'] = 'retired'
            self.save(j)
            return
        if state == 'Z' or j['holder'] == 'retired':
            raise RuntimeError('holder identity changed/reappeared')
        if self.s.get('fixture'):
            status = Path(f'/proc/{pid}/status').read_text().splitlines()
            parent = int(next(s.split()[1] for s in status if s.startswith('PPid:')))
            if parent != os.getpid():
                raise RuntimeError('fixture holder is not this test process child')
        pidfd = os.pidfd_open(pid)
        try:
            if process_start(pid) != h['starttime']:
                raise RuntimeError('holder changed after pidfd open')
            with open(f'/proc/{pid}/fd/{h["fd"]}', 'rb') as stream:
                s = os.fstat(stream.fileno())
                if (s.st_dev, s.st_ino, s.st_size) != (h['dev'], h['ino'], h['size']):
                    raise RuntimeError('holder backing identity differs')
                if fcntl.fcntl(stream.fileno(), fcntl.F_GET_SEALS) != h['seals']:
                    raise RuntimeError('holder seals differ')
                if digest(f'/proc/{pid}/fd/{h["fd"]}') != h['sha256']:
                    raise RuntimeError('holder backup bytes differ')
            j['holder'] = 'signaling'
            self.save(j)
            signal.pidfd_send_signal(pidfd, signal.SIGTERM)
            # Waiting is deliberately bounded; a retry completes an interrupted retirement.
            for _ in range(20):
                try:
                    if process_start(pid) != h['starttime']:
                        break
                    state = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[0]
                    if state == 'Z':
                        break
                except FileNotFoundError:
                    break
                time.sleep(0.05)
            else:
                raise RuntimeError('holder has not exited yet; retry explicitly')
            j['holder'] = 'retired'
            self.save(j)
        finally:
            os.close(pidfd)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--settings', required=True)
    p.add_argument('--settings-sha256', required=True)
    p.add_argument('action', choices=['activate', 'retire-files', 'retire-holder'])
    a = p.parse_args()
    obj = Cutover(a.settings, a.settings_sha256)
    with obj.locked():
        getattr(obj, a.action.replace('-', '_'))()
    print(json.dumps({'action': a.action, 'status': 'complete'}))


if __name__ == '__main__':
    main()
