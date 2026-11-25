"""Only tiny newly-created fixtures; real journal files are never accessed."""
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile

import indexed_archive as a

HERE = Path(__file__).resolve().parent


class Fixture:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='outer-fixture-', dir=HERE)
        self.root = Path(self.temp.name)
        self.source = self.root / 'sources'
        self.source.mkdir()
        self.output = self.root / 'outer'
        self.originals, self.sidecars = {}, {}
        for i, name in enumerate(a.NAMES):
            raw = json.dumps({'status': 'restored', 'fixture': i, 'repeated': 'abcdef' * 100}).encode()
            r = subprocess.run(['zstd', '-q', '-c'], input=raw, capture_output=True, check=True)
            p = self.source / name
            p.write_bytes(r.stdout)
            p.chmod(0o640)
            os.utime(p, ns=(1700000000000000000 + i,) * 2)
            m = {'archive': str(p), 'status': 'restored', 'archive_bytes': len(r.stdout),
                 'archive_sha256': hashlib.sha256(r.stdout).hexdigest(),
                 'uncompressed_bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
            sidecar = p.with_name(p.name + '.metadata.json')
            sidecar.write_text(json.dumps(m))
            self.originals[name] = (r.stdout, p.stat().st_mtime_ns)
            self.sidecars[sidecar.name] = sidecar.read_bytes()
        self.active = self.source / 'transaction.json'
        self.active.write_bytes(b'active journal must not be read or changed')
        self.result = a.create(self.source, self.output)
        self.index = Path(self.result['index'])
        self.pin = self.result['index_sha256']

    def check_sources(self):
        for name, (raw, mtime) in self.originals.items():
            p = self.source / name
            assert p.read_bytes() == raw and p.stat().st_mtime_ns == mtime
            assert stat.S_IMODE(p.stat().st_mode) == 0o640

    def check_provenance(self):
        for name, raw in self.sidecars.items():
            assert (self.source / name).read_bytes() == raw
        assert self.active.read_bytes() == b'active journal must not be read or changed'

    def close(self):
        self.temp.cleanup()


def fails(call):
    try:
        call()
    except RuntimeError:
        return
    raise AssertionError('expected refusal')


def roundtrip():
    f = Fixture()
    try:
        f.check_sources()
        assert a.verify(f.index, f.pin)['verified_files'] == 7
        restored = f.root / 'reconstructed'
        a.restore(f.index, f.pin, restored)
        for name, (raw, mtime) in f.originals.items():
            p = restored / name
            assert p.read_bytes() == raw and p.stat().st_mtime_ns == mtime
            assert stat.S_IMODE(p.stat().st_mode) == 0o640
        assert a.retire(f.index, f.pin)['retired_files'] == 7
        assert a.retire(f.index, f.pin)['retired_files'] == 7
        assert all(not (f.source / name).exists() for name in a.NAMES)
        f.check_provenance()
    finally:
        f.close()


def corrupt_outer():
    f = Fixture()
    try:
        p = f.output / 'completed-journals.outer.zst'
        p.write_bytes(b'corrupt')
        fails(lambda: a.retire(f.index, f.pin))
        f.check_sources()
        f.check_provenance()
    finally:
        f.close()


def changed_source():
    f = Fixture()
    try:
        p = f.source / a.NAMES[-1]
        p.write_bytes(p.read_bytes() + b'changed')
        fails(lambda: a.retire(f.index, f.pin))
        assert all((f.source / name).exists() for name in a.NAMES)
        f.check_provenance()
    finally:
        f.close()


def partial_retirement():
    f = Fixture()
    original = Path.unlink
    try:
        failed = False
        def interrupted(path, *args, **kwargs):
            nonlocal failed
            if path == f.source / a.NAMES[1] and not failed:
                failed = True
                raise RuntimeError('injected retirement interruption')
            return original(path, *args, **kwargs)
        Path.unlink = interrupted
        fails(lambda: a.retire(f.index, f.pin))
        Path.unlink = original
        assert failed and not (f.source / a.NAMES[0]).exists()
        assert a.retire(f.index, f.pin)['retired_files'] == 7
        f.check_provenance()
    finally:
        Path.unlink = original
        f.close()


def rejects_active_name():
    f = Fixture()
    try:
        data = json.loads(f.index.read_text())
        data['files'][0]['name'] = 'transaction.json'
        f.index.write_text(json.dumps(data))
        fails(lambda: a.retire(f.index, a.digest(f.index)))
        f.check_sources()
        f.check_provenance()
    finally:
        f.close()


for test in (roundtrip, corrupt_outer, changed_source, partial_retirement, rejects_active_name):
    test()
    print(test.__name__, 'PASS')
print('PASS 5 tiny fixture cases; real journal mutations 0')
