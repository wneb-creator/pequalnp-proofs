"""Independent tiny-fixture retirement tests; never runs concrete settings."""
import gzip
import hashlib
import os
from pathlib import Path
import stat

import compact_cache as cc
from test_retire_generation import RetireFixture, fails

HERE = Path(__file__).resolve().parent
EXPECTED = 'b118db721842c6513bbec64ef80b0ac013ffb67ccee600dc2d43cd4c5c5c9ca4'
assert hashlib.sha256((HERE / 'retire_generation.py').read_bytes()).hexdigest() == EXPECTED


def unlink_intent_before_failure():
    f = RetireFixture()
    unlink = Path.unlink
    try:
        f.retire.prepare()
        target = Path(sorted(f.retire.expected_paths)[0])
        fired = False
        def fail_first(path, *args, **kwargs):
            nonlocal fired
            if path == target and not fired:
                fired = True
                raise RuntimeError('injected failure before unlink')
            return unlink(path, *args, **kwargs)
        Path.unlink = fail_first
        fails(f.retire.run)
        Path.unlink = unlink
        journal = cc.read_json(f.retire.journal)
        assert fired and journal['files'][str(target)] == 'unlinking'
        assert all(Path(p).exists() for p in f.retire.expected_paths)
        assert cc.sha(f.retire_settings['active_handoff']) == cc.sha(f.retire_settings['staged_handoff'])
        f.retire.run()
        f.validate_complete()
    finally:
        Path.unlink = unlink
        f.close()


def interrupted_activation_sync():
    f = RetireFixture()
    sync = cc.syncdir
    try:
        f.retire.prepare()
        active = Path(f.retire_settings['active_handoff'])
        desired = cc.sha(f.retire_settings['staged_handoff'])
        fired = False
        def fail_once(path):
            nonlocal fired
            if Path(path) == active.parent and cc.sha(active) == desired and not fired:
                fired = True
                raise RuntimeError('injected interruption after handoff rename')
            return sync(path)
        cc.syncdir = fail_once
        fails(f.retire.run)
        cc.syncdir = sync
        assert fired and cc.read_json(f.retire.journal)['status'] == 'activating'
        assert all(Path(p).exists() for p in f.retire.expected_paths)
        f.retire.run()
        f.validate_complete()
    finally:
        cc.syncdir = sync
        f.close()


def shared_lock_identity():
    f = RetireFixture()
    try:
        lock = f.tx.generation / 'state/phase.lock'
        lock.unlink()
        lock.touch()
        try:
            with f.retire.locked():
                raise AssertionError('different lock inode accepted')
        except RuntimeError as error:
            assert 'share original phase lock' in str(error)
        assert all(Path(p).exists() for p in f.retire.expected_paths)
    finally:
        f.close()


def metadata_reconstruction_after_retire():
    f = RetireFixture()
    try:
        f.retire.prepare()
        journal = cc.read_json(f.retire.journal)
        originals = {p: Path(p).read_bytes() for p in journal['archives']}
        f.retire.run()
        f.validate_complete()
        destination = f.root / 'reconstructed-metadata'
        destination.mkdir()
        for i, (original, archive) in enumerate(journal['archives'].items()):
            metadata = f.retire_settings['obsolete'][original]['identity']
            with gzip.open(archive['path'], 'rb') as stream:
                raw = stream.read()
            assert raw == originals[original]
            p = destination / str(i)
            p.write_bytes(raw)
            p.chmod(metadata['mode'])
            os.utime(p, ns=(metadata['mtime_ns'],) * 2)
            st = p.stat()
            assert (st.st_size, stat.S_IMODE(st.st_mode), st.st_mtime_ns) == (
                metadata['size'], metadata['mode'], metadata['mtime_ns'])
    finally:
        f.close()


for test in (unlink_intent_before_failure, interrupted_activation_sync,
             shared_lock_identity, metadata_reconstruction_after_retire):
    test()
    print(test.__name__, 'PASS')
assert hashlib.sha256((HERE / 'retire_generation.py').read_bytes()).hexdigest() == EXPECTED
print('PASS 4 independent tiny recovery fixtures; production actions 0')
