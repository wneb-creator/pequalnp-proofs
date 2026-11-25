#!/usr/bin/env python3
import gzip
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import tempfile

import compact_cache as cc

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'resource-wrapper/storage_phase.py'


def write_json(path, value):
    path.write_text(json.dumps(value))


class Fixture:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='fixture-', dir=HERE)
        self.root = Path(self.temp.name)
        self.state = self.root / 'old-state'
        self.state.mkdir()
        (self.state / 'phase.lock').touch()
        self.editor = self.root / 'old-editor'
        self.editor.mkdir()
        self.pkg = self.root / 'packages/mathlib'
        self.pkg.mkdir(parents=True)
        self.config = {
            'state_dir': str(self.state), 'packages_root': str(self.root / 'packages'),
            'project_build_root': str(self.root / 'project/.lake/build'),
            'toolchain_root': str(self.root / 'toolchain'),
            'editor_index': str(self.editor / 'index.tsv'),
            'editor_manifest': str(self.editor / 'manifest.jsonl'),
            'editor_pack': str(self.editor / 'data.zstpack'),
            'disk_reserve_bytes': 0, 'ram_limit_bytes': 0, 'ram_manifests': []}
        self.mod = cc.load_storage(str(SOURCE), cc.sha(SOURCE))
        codec = self.mod.Codec()
        self.rows = {}
        self.selected = []
        self.originals = {}
        baseline = []
        paths = [('Mathlib.Keep', '.lake/build/ir/Mathlib/Keep.c', True),
                 ('Mathlib.Drop', '.lake/build/ir/Mathlib/Drop.c', True),
                 ('Mathlib.Keep', 'Mathlib/Keep.lean', False),
                 ('Mathlib.Drop', 'Mathlib/Drop.lean', False),
                 ('Mathlib.Drop', '.lake/build/lib/lean/Mathlib/Drop.olean.hash', False)]
        with (self.editor / 'data.zstpack').open('wb') as old, (self.state / 'extra.zstpack').open('wb') as extra:
            for i, (module, relative, is_baseline) in enumerate(paths):
                p = self.pkg / relative
                p.parent.mkdir(parents=True, exist_ok=True)
                raw = (f'file {relative} byte payload\n' * 5).encode()
                p.write_bytes(raw)
                p.chmod(0o640)
                os.utime(p, ns=(123000000000 + i, 123000000000 + i))
                packed = codec.compress(raw)
                stream = old if is_baseline else extra
                row = {'path': str(p), 'size': len(raw), 'mode': 0o640,
                       'mtime_ns': p.stat().st_mtime_ns,
                       'sha256': hashlib.sha256(raw).hexdigest(),
                       'pack': stream.name, 'offset': stream.tell(), 'compressed': len(packed)}
                stream.write(packed)
                self.rows[str(p)] = row
                self.originals[str(p)] = (raw, p.stat().st_mtime_ns)
                if module == 'Mathlib.Drop':
                    self.selected.append(dict(row, module=module))
                if is_baseline:
                    baseline.append(dict(row, virtual=relative))
        with (self.editor / 'index.tsv').open('w') as index, (self.editor / 'manifest.jsonl').open('w') as manifest:
            for row in baseline:
                index.write(f"{row['virtual']}\t{row['mode']:o}\t{row['size']}\t{row['mtime_ns']}\t{row['offset']}\t{row['compressed']}\n")
                manifest.write(json.dumps(row) + '\n')
        write_json(self.state / 'prepared.json', {'files': self.rows})
        write_json(self.root / 'config.json', self.config)
        write_json(self.root / 'build.json', {'modules': {'Mathlib.Keep': {}}})
        write_json(self.root / 'full.json', {'modules': {'Mathlib.Keep': {}, 'Mathlib.Drop': {}}})
        with gzip.open(self.root / 'candidates.jsonl.gz', 'wt') as f:
            for row in self.selected:
                f.write(json.dumps(row) + '\n')
        self.runtime = self.pkg / '.lake/build/lib/lean/Mathlib/Drop.olean'
        self.runtime.write_bytes(b'runtime must survive')
        gate = self.root / 'gate.py'
        gate.write_text('import pathlib,sys\np=pathlib.Path(__file__).parent\nassert (p/"packages/mathlib/.lake/build/lib/lean/Mathlib/Drop.olean").read_bytes()==b"runtime must survive"\nsys.exit(1 if (p/"fail-gate").exists() else 0)\n')
        self.settings = {'transaction_dir': str(self.root / 'transaction'),
                         'generation_dir': str(self.root / 'generation'),
                         'source_config': str(self.root / 'config.json'),
                         'storage_source': str(SOURCE), 'storage_sha256': cc.sha(SOURCE),
                         'build_graph': str(self.root / 'build.json'),
                         'runtime_graph': str(self.root / 'full.json'),
                         'candidates': str(self.root / 'candidates.jsonl.gz'),
                         'workdir': str(self.root),
                         'no_build_commands': [[sys.executable, str(gate), 'build', '--no-build']]}
        self.settings['input_sha256'] = {k: cc.sha(self.settings[k]) for k in
            ('build_graph', 'runtime_graph', 'candidates', 'source_config')}
        self.tx = cc.Transaction(self.settings)

    def check_originals(self):
        for p, (raw, mtime) in self.originals.items():
            path = Path(p)
            assert path.read_bytes() == raw
            assert path.stat().st_mtime_ns == mtime
            assert stat.S_IMODE(path.stat().st_mode) == 0o640
        assert self.runtime.read_bytes() == b'runtime must survive'

    def close(self):
        self.temp.cleanup()


def fails(function):
    try:
        function()
    except RuntimeError:
        return
    raise AssertionError('operation unexpectedly succeeded')


def test_complete():
    f = Fixture()
    try:
        old_hashes = {str(p): cc.sha(p) for p in (f.editor / 'data.zstpack', f.state / 'extra.zstpack')}
        with f.tx.locked():
            f.tx.snapshot()
            f.tx.prune()
            f.tx.gate('after-prune')
            f.tx.compact()
            f.tx.gate('after-stage')
            fresh = f.mod.Storage(cc.read_json(f.tx.generation / 'storage_config.json'))
            before = cc.read_json(fresh.prepared)
            fresh.prepare()
            assert cc.read_json(fresh.prepared) == before
            f.tx.verify_generation()
            assert all(cc.sha(p) == expected for p, expected in old_hashes.items())
            f.tx.rollback()
            f.check_originals()
        assert cc.read_json(f.root / 'config.json') == f.config
    finally:
        f.close()


def test_partial():
    f = Fixture()
    try:
        f.tx.snapshot()
        fails(lambda: f.tx.prune(stop_after=1))
        f.tx.rollback()
        f.check_originals()
    finally:
        f.close()


def test_changed_source():
    f = Fixture()
    try:
        f.tx.snapshot()
        p = Path(f.selected[0]['path'])
        p.write_bytes(b'changed')
        fails(f.tx.prune)
        assert p.read_bytes() == b'changed'
    finally:
        f.close()


def test_corrupt_backup():
    f = Fixture()
    try:
        p = f.editor / 'data.zstpack'
        p.write_bytes(b'bad')
        fails(f.tx.snapshot)
        f.check_originals()
    finally:
        f.close()


def test_gate_failure():
    f = Fixture()
    try:
        f.tx.snapshot()
        f.tx.prune()
        (f.root / 'fail-gate').touch()
        fails(lambda: f.tx.gate('after-prune'))
        f.check_originals()
    finally:
        f.close()


def test_regenerated():
    f = Fixture()
    try:
        f.tx.snapshot()
        f.tx.prune()
        f.tx.gate('after-prune')
        f.tx.compact()
        fresh = f.mod.Storage(cc.read_json(f.tx.generation / 'storage_config.json'))
        p = Path(f.selected[0]['path'])
        p.write_bytes(b'new regenerated bytes')
        fresh.prepare()
        row = cc.read_json(fresh.prepared)['files'][str(p)]
        assert fresh.backup_bytes(row) == b'new regenerated bytes'
        assert row['pack'] == str(fresh.extra_pack)
        assert str(p) not in fresh.baseline()
    finally:
        f.close()


def test_runtime_candidate_refused():
    f = Fixture()
    try:
        row = dict(f.selected[0], path=str(f.runtime))
        with gzip.open(f.root / 'candidates.jsonl.gz', 'wt') as stream:
            stream.write(json.dumps(row) + '\n')
        fails(f.tx.snapshot)
        f.check_originals()
    finally:
        f.close()


def test_lock():
    f = Fixture()
    try:
        with f.tx.locked():
            try:
                with f.tx.locked():
                    raise AssertionError('lock unexpectedly acquired twice')
            except BlockingIOError:
                pass
    finally:
        f.close()


def test_interrupted_rollback_temp():
    f = Fixture()
    try:
        f.tx.snapshot()
        f.tx.prune()
        p = Path(f.selected[0]['path'])
        p.with_name(p.name + '.cache-rollback').write_bytes(b'interrupted partial write')
        f.tx.status_path.with_name('status.json.new').write_bytes(b'{incomplete')
        f.tx.rollback()
        f.check_originals()
        assert not p.with_name(p.name + '.cache-rollback').exists()
    finally:
        f.close()


def test_temporary_symlink_rejected():
    f = Fixture()
    try:
        f.tx.snapshot()
        f.tx.prune()
        p = Path(f.selected[0]['path'])
        tmp = p.with_name(p.name + '.cache-rollback')
        tmp.symlink_to(f.runtime)
        fails(f.tx.rollback)
        assert f.runtime.read_bytes() == b'runtime must survive'
    finally:
        f.close()


def test_pinned_inputs():
    f = Fixture()
    try:
        (f.root / 'build.json').write_text('{"modules":{}}')
        fails(f.tx.snapshot)
        f.check_originals()
    finally:
        f.close()


def test_interrupted_metadata():
    f = Fixture()
    try:
        f.tx.plan_path.with_name('plan.json.gz.new').write_bytes(b'partial gzip')
        f.tx.snapshot()
        f.tx.prune()
        f.tx.gate('after-prune')
        f.tx.compact()
        f.tx.verify_generation()
        f.tx.rollback()
        f.check_originals()
    finally:
        f.close()


if __name__ == '__main__':
    tests = [test_complete, test_partial, test_changed_source, test_corrupt_backup,
             test_gate_failure, test_regenerated, test_runtime_candidate_refused, test_lock,
             test_interrupted_rollback_temp, test_temporary_symlink_rejected,
             test_pinned_inputs, test_interrupted_metadata]
    for test in tests:
        test()
        print(test.__name__, 'PASS')
    print(json.dumps({'passed': len(tests)}))
