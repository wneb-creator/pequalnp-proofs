"""Independent isolated recovery checks; never loads production settings."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
from unittest.mock import patch

import cutover as c
from test_cutover import Fixture


class RecoveryTests(unittest.TestCase):
    def fixture(self):
        f = Fixture()
        self.addCleanup(shutil.rmtree, f.root)
        return f

    def holder(self, f, seals=15):
        code = ('import fcntl,json,os,signal;'
                'fd=os.memfd_create("independent-cutover-fixture",os.MFD_ALLOW_SEALING);'
                'os.write(fd,b"independent fixture");'
                f'fcntl.fcntl(fd,fcntl.F_ADD_SEALS,{seals});'
                's=os.fstat(fd);'
                'print(json.dumps(dict(pid=os.getpid(),fd=fd,dev=s.st_dev,ino=s.st_ino,size=s.st_size)),flush=True);'
                'signal.pause()')
        child = subprocess.Popen(['/usr/bin/python3', '-c', code], stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, env={'PATH': '/usr/bin:/bin'})
        def cleanup():
            if child.poll() is None:
                child.terminate()
                child.wait(timeout=3)
            child.stdout.close()
            child.stderr.close()
        self.addCleanup(cleanup)
        line = child.stdout.readline()
        self.assertTrue(line)
        row = json.loads(line)
        row.update(starttime=c.process_start(child.pid), seals=15,
                   sha256=hashlib.sha256(b'independent fixture').hexdigest())
        f.s['holder'] = row
        f.write_settings()
        return child

    def test_replacement_visible_before_directory_fsync_retry(self):
        f = self.fixture()
        original = c.syncdir
        failed = []
        def interrupted(path):
            if (Path(path) == Path(f.s['active_handoff']).parent and not failed
                    and c.digest(f.s['active_handoff']) == c.digest(f.s['new_handoff'])):
                failed.append(True)
                raise OSError('injected directory fsync interruption')
            return original(path)
        with patch.object(c, 'syncdir', interrupted):
            with self.assertRaisesRegex(OSError, 'injected'):
                f.run('activate')
        self.assertEqual(c.read_json(f.obj().journal)['status'], 'activating')
        self.assertTrue(all(Path(p).exists() for p in f.s['obsolete']))
        f.run('activate')
        self.assertEqual(c.read_json(f.obj().journal)['status'], 'active')

    def test_unlink_intent_durable_before_unlink_retry(self):
        f = self.fixture()
        f.run('activate')
        original = c.os.unlink
        failed = []
        def interrupted(path, *args, **kwargs):
            if str(path) in f.s['obsolete'] and not failed:
                failed.append(str(path))
                raise OSError('injected before unlink')
            return original(path, *args, **kwargs)
        with patch.object(c.os, 'unlink', interrupted):
            with self.assertRaisesRegex(OSError, 'injected'):
                f.run('retire_files')
        self.assertEqual(c.read_json(f.obj().journal)['files'][failed[0]], 'unlinking')
        self.assertTrue(Path(failed[0]).exists())
        f.run('retire_files')
        self.assertTrue(all(not Path(p).exists() for p in f.s['obsolete']))

    def test_wrong_holder_start_is_never_signaled(self):
        f = self.fixture()
        child = self.holder(f)
        f.s['holder']['starttime'] += 1
        f.write_settings()
        f.run('activate')
        with patch.object(c.signal, 'pidfd_send_signal') as send:
            with self.assertRaisesRegex(RuntimeError, 'identity changed'):
                f.run('retire_holder')
            send.assert_not_called()
        self.assertIsNone(child.poll())

    def test_wrong_holder_seals_is_never_signaled(self):
        f = self.fixture()
        child = self.holder(f, seals=0)
        f.run('activate')
        with patch.object(c.signal, 'pidfd_send_signal') as send:
            with self.assertRaisesRegex(RuntimeError, 'seals differ'):
                f.run('retire_holder')
            send.assert_not_called()
        self.assertIsNone(child.poll())

    def test_signal_intent_durable_before_signal_retry(self):
        f = self.fixture()
        child = self.holder(f)
        f.run('activate')
        with patch.object(c.signal, 'pidfd_send_signal', side_effect=OSError('injected before signal')):
            with self.assertRaisesRegex(OSError, 'injected'):
                f.run('retire_holder')
        self.assertEqual(c.read_json(f.obj().journal)['holder'], 'signaling')
        self.assertIsNone(child.poll())
        f.run('retire_holder')
        child.wait(timeout=3)
        self.assertEqual(child.returncode, -15)
        f.run('retire_holder')
        self.assertEqual(c.read_json(f.obj().journal)['holder'], 'retired')


if __name__ == '__main__':
    unittest.main(verbosity=2)
