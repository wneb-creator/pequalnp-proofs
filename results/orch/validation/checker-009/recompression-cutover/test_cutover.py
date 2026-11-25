import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

import cutover as c


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value) if isinstance(value, dict) else value)
    return str(path)


class Fixture:
    def __init__(self):
        parent = c.ROOT / 'recompression-cutover' / 'fixtures'
        parent.mkdir(exist_ok=True)
        self.root = Path(tempfile.mkdtemp(prefix='case-', dir=parent))
        old, new, core = (self.root / n for n in ('old', 'new', 'core'))
        lock = put(self.root / 'phase.lock', '')
        oldcfg = {k: put(old / name, 'old-' + name) for k, name in
                  [('editor_pack', 'data.zstpack'), ('editor_index', 'index.tsv'), ('editor_manifest', 'manifest.jsonl')]}
        oldcfg.update(state_dir=str(old / 'state'), phase_lock=lock)
        oldfiles = list(oldcfg[k] for k in ('editor_pack', 'editor_index', 'editor_manifest'))
        oldfiles += [put(old / 'state' / n, 'old-' + n) for n in ('extra.zstpack', 'prepared.json')]
        newcfg = {k: put(new / name, 'new-' + name) for k, name in
                  [('editor_pack', 'data.zstpack'), ('editor_index', 'index.tsv'), ('editor_manifest', 'manifest.jsonl')]}
        newcfg.update(state_dir=str(new / 'state'), phase_lock=lock)
        newfiles = list(newcfg[k] for k in ('editor_pack', 'editor_index', 'editor_manifest'))
        newfiles += [put(new / 'state' / n, 'new-' + n) for n in ('extra.zstpack', 'prepared.json')]
        newfiles += [put(core / n, 'core-' + n) for n in ('excluded.zstpack', 'prepared.json')]
        corecfg = dict(state_dir=str(core), phase_lock=lock, base_journal=str(new / 'state' / 'transaction.json'))
        oldpath = put(self.root / 'old-config.json', oldcfg)
        newpath = put(self.root / 'new-config.json', newcfg)
        corepath = put(self.root / 'core-config.json', corecfg)
        report1 = put(self.root / 'base-report.json', {'status': 'PASS'})
        report2 = put(self.root / 'core-report.json', {'status': 'PASS'})
        command = put(self.root / 'commands.json', {'base_command': ['python', '--config', newpath],
                      'core_command': ['python', '--config', corepath], 'required_files': []})
        handoff = {f'phase_{a}': ['python', '--commands', command, '--commands-sha256', c.digest(command), a]
                   for a in ('enter', 'restore')}
        staged = put(self.root / 'new-handoff.json', handoff)
        active = put(self.root / 'active-handoff.json', {'old': True})
        pins = newfiles + [oldpath, newpath, corepath, report1, report2, command, staged]
        journals = [put(self.root / n, {'status': 'restored'}) for n in ('old-journal.json', 'new-journal.json')]
        self.s = dict(version=1, fixture=True, transaction_dir=str(self.root / 'transaction'),
                      phase_lock=lock, lock_aliases=[lock], active_handoff=active,
                      old_handoff_sha256=c.digest(active), old_base_config=oldpath,
                      new_base_config=newpath, new_core_config=corepath, new_commands=command,
                      new_handoff=staged, required_pins={p: c.digest(p) for p in pins}, journals=journals,
                      review_reports=[{'path': p, 'keys': ['status'], 'equals': 'PASS'} for p in (report1, report2)],
                      obsolete={p: {'identity': c.identity(p), 'sha256': c.digest(p)} for p in oldfiles},
                      holder={'pid': 42728})
        self.path = self.root / 'settings.json'
        self.write_settings()

    def write_settings(self):
        put(self.path, self.s)
        self.sha = c.digest(self.path)

    def obj(self):
        return c.Cutover(self.path, self.sha)

    def run(self, method, *args):
        o = self.obj()
        with o.locked():
            return getattr(o, method)(*args)


class Tests(unittest.TestCase):
    def test_normal_and_idempotent(self):
        f = Fixture()
        f.run('activate')
        f.run('activate')
        self.assertEqual(c.digest(f.s['active_handoff']), c.digest(f.s['new_handoff']))
        f.run('retire_files')
        f.run('retire_files')
        f.run('activate')
        self.assertTrue(all(not Path(p).exists() for p in f.s['obsolete']))
        self.assertTrue(all(Path(p).exists() for p in f.s['required_pins']))
        j = c.read_json(f.obj().journal)
        self.assertEqual(j['status'], 'retired')
        for p, row in j['archives'].items():
            self.assertEqual(hashlib.sha256(gzip.decompress(Path(row['path']).read_bytes())).hexdigest(), f.s['obsolete'][p]['sha256'])

    def test_interrupted_activation_retry(self):
        f = Fixture()
        with self.assertRaisesRegex(RuntimeError, 'interruption'):
            f.run('activate', 'after-replace')
        f.run('activate')
        f.run('retire_files')

    def test_interrupted_unlink_retry(self):
        f = Fixture()
        f.run('activate')
        with self.assertRaisesRegex(RuntimeError, 'interruption'):
            f.run('retire_files', 'after-unlink')
        f.run('retire_files')
        self.assertTrue(all(not Path(p).exists() for p in f.s['obsolete']))

    def test_changed_retained_pin(self):
        f = Fixture()
        p = next(iter(f.s['required_pins']))
        Path(p).write_text('tampered')
        with self.assertRaisesRegex(RuntimeError, 'required pin changed'):
            f.run('activate')
        self.assertEqual(c.digest(f.s['active_handoff']), f.s['old_handoff_sha256'])

    def test_changed_settings_pin(self):
        f = Fixture()
        f.path.write_text('{}')
        with self.assertRaisesRegex(RuntimeError, 'settings pin'):
            f.obj()

    def test_changed_old_before_activation(self):
        f = Fixture()
        Path(next(iter(f.s['obsolete']))).write_text('tampered')
        with self.assertRaisesRegex(RuntimeError, 'obsolete file changed'):
            f.run('activate')

    def test_changed_old_before_retirement(self):
        f = Fixture()
        f.run('activate')
        Path(next(iter(f.s['obsolete']))).write_text('tampered')
        with self.assertRaisesRegex(RuntimeError, 'obsolete file changed'):
            f.run('retire_files')
        self.assertTrue(all(Path(p).exists() for p in f.s['obsolete']))

    def test_entered_old_or_new_journal(self):
        for n in (0, 1):
            f = Fixture()
            put(Path(f.s['journals'][n]), {'status': 'entered'})
            with self.assertRaisesRegex(RuntimeError, 'active phase journal'):
                f.run('activate')

    def test_shared_lock(self):
        f = Fixture()
        with open(f.s['phase_lock'], 'r+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaises(BlockingIOError):
                f.run('activate')

    def test_intentional_hardlink_lock(self):
        f = Fixture()
        alias = f.root / 'same-phase.lock'
        os.link(f.s['phase_lock'], alias)
        f.s['lock_aliases'].append(str(alias))
        f.write_settings()
        f.run('activate')
        f.run('retire_files')

    def test_retire_before_activation(self):
        f = Fixture()
        with self.assertRaises(FileNotFoundError):
            f.run('retire_files')

    def test_tampered_active_handoff(self):
        f = Fixture()
        f.run('activate')
        put(Path(f.s['active_handoff']), {'other': True})
        with self.assertRaisesRegex(RuntimeError, 'not active'):
            f.run('retire_files')

    def test_tampered_archive(self):
        f = Fixture()
        f.run('activate')
        j = c.read_json(f.obj().journal)
        Path(next(iter(j['archives'].values()))['path']).write_bytes(b'bad')
        with self.assertRaisesRegex(RuntimeError, 'snapshot differs'):
            f.run('retire_files')

    def test_raw_guardian_protected(self):
        f = Fixture()
        f.run('activate')
        with self.assertRaisesRegex(RuntimeError, 'guardian is protected'):
            f.run('retire_holder')

    def test_owned_fake_holder_only(self):
        f = Fixture()
        code = ('import fcntl,json,os,signal,time;'
                'fd=os.memfd_create("owned-cutover-fixture",os.MFD_ALLOW_SEALING);'
                'os.write(fd,b"fake pack");fcntl.fcntl(fd,fcntl.F_ADD_SEALS,15);'
                's=os.fstat(fd);'
                'print(json.dumps(dict(pid=os.getpid(),fd=fd,dev=s.st_dev,ino=s.st_ino,size=s.st_size)),flush=True);'
                'signal.pause()')
        child = subprocess.Popen([sys.executable, '-c', code], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, env={'PATH': '/usr/bin:/bin'})
        try:
            line = child.stdout.readline()
            if not line:
                raise RuntimeError(child.stderr.read())
            h = json.loads(line)
            h.update(starttime=c.process_start(child.pid), seals=15,
                     sha256=hashlib.sha256(b'fake pack').hexdigest())
            f.s['holder'] = h
            f.write_settings()
            f.run('activate')
            f.run('retire_holder')
            child.wait(timeout=3)
            self.assertEqual(child.returncode, -15)
            f.run('retire_holder')
            self.assertEqual(c.read_json(f.obj().journal)['holder'], 'retired')
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait(timeout=3)
            child.stdout.close()
            child.stderr.close()

    def test_holder_signal_interruption_zombie_retry(self):
        f = Fixture()
        code = ('import fcntl,json,os,signal;'
                'fd=os.memfd_create("owned-cutover-retry-fixture",os.MFD_ALLOW_SEALING);'
                'os.write(fd,b"fake pack");fcntl.fcntl(fd,fcntl.F_ADD_SEALS,15);'
                's=os.fstat(fd);'
                'print(json.dumps(dict(pid=os.getpid(),fd=fd,dev=s.st_dev,ino=s.st_ino,size=s.st_size)),flush=True);'
                'signal.pause()')
        child = subprocess.Popen([sys.executable, '-c', code], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, env={'PATH': '/usr/bin:/bin'})
        try:
            line = child.stdout.readline()
            if not line:
                raise RuntimeError(child.stderr.read())
            h = json.loads(line)
            h.update(starttime=c.process_start(child.pid), seals=15, sha256=hashlib.sha256(b'fake pack').hexdigest())
            f.s['holder'] = h
            f.write_settings()
            f.run('activate')
            obj = f.obj()
            j = c.read_json(obj.journal)
            j['holder'] = 'signaling'
            obj.save(j)
            child.terminate()
            for _ in range(100):
                state = Path(f'/proc/{child.pid}/stat').read_text().rsplit(')', 1)[1].split()[0]
                if state == 'Z':
                    break
                time.sleep(0.01)
            self.assertEqual(state, 'Z')
            f.run('retire_holder')
            f.run('retire_holder')
            self.assertEqual(c.read_json(obj.journal)['holder'], 'retired')
            child.wait(timeout=3)
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait(timeout=3)
            child.stdout.close()
            child.stderr.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
