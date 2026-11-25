#!/usr/bin/env python3
import gzip
import hashlib
import json
from pathlib import Path
import sys

import compact_cache as cc
import retire_generation as rg
from test_compact_cache import Fixture, fails, write_json


class RetireFixture(Fixture):
    def __init__(self):
        super().__init__()
        self.tx.snapshot()
        self.tx.prune()
        self.tx.gate('after-prune')
        self.tx.compact()
        self.tx.gate('after-stage')
        cfg = cc.read_json(self.tx.generation / 'storage_config.json')
        cfg['phase_lock'] = str(self.state / 'phase.lock')
        cfg['shared_library_whitelist'] = []
        prep_path = self.tx.generation / 'state/prepared.json'
        prep = cc.read_json(prep_path)
        pack_path = self.tx.generation / 'state/extra.zstpack'
        with pack_path.open('ab') as f:
            for name in ('libleanshared.so', 'libLake_shared.so'):
                raw = ('library' + name).encode()
                path = self.root / 'toolchain/lib/lean' / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
                row = {'path': str(path), 'size': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                       'mode': path.stat().st_mode & 0o777, 'mtime_ns': path.stat().st_mtime_ns}
                cfg['shared_library_whitelist'].append(row)
                data = self.mod.Codec().compress(raw)
                prep['files'][str(path)] = dict(row, pack=str(pack_path), offset=f.tell(), compressed=len(data))
                f.write(data)
        write_json(prep_path, prep)
        new_cfg = self.root / 'new-config.json'
        write_json(new_cfg, cfg)
        core_cfg = self.root / 'core-config.json'
        write_json(core_cfg, {'base_journal': str(self.tx.generation / 'state/transaction.json'),
                             'phase_lock': cfg['phase_lock']})
        report = self.root / 'review.json'
        write_json(report, {'status': 'PASS'})
        old_handoff = self.root / 'handoff.json'
        write_json(old_handoff, {'old': True})
        required = [{'path': self.settings['storage_source'], 'sha256': self.settings['storage_sha256']}]
        commands = self.root / 'commands.json'
        write_json(commands, {'required_files': required,
                              'base_command': [sys.executable, 'base', '--config', str(new_cfg)],
                              'core_command': [sys.executable, 'core', '--config', str(core_cfg)]})
        staged = self.root / 'staged-handoff.json'
        argv = [sys.executable, 'launcher', '--commands', str(commands), '--commands-sha256', cc.sha(commands)]
        write_json(staged, {'phase_enter': argv + ['enter'], 'phase_restore': argv + ['restore']})
        pins = [new_cfg, core_cfg, report, commands, staged,
                prep_path, pack_path, self.tx.generation / 'editor/data.zstpack',
                self.tx.generation / 'editor/index.tsv', self.tx.generation / 'editor/manifest.jsonl',
                self.root / 'config.json', self.tx.plan_path,
                Path(self.settings['storage_source']),
                self.tx.directory / 'after-prune.json', self.tx.directory / 'after-stage.json']
        obsolete = [self.editor / 'data.zstpack', self.editor / 'index.tsv', self.editor / 'manifest.jsonl',
                    self.state / 'extra.zstpack', self.state / 'prepared.json']
        self.retire_settings = {'retirement_dir': str(self.root / 'retirement'),
            'original_config': str(self.root / 'config.json'), 'generation_config': str(new_cfg),
            'prune_plan': str(self.tx.plan_path), 'storage_source': self.settings['storage_source'],
            'obsolete': {str(p): {'identity': rg.identity(p), 'sha256': cc.sha(p)} for p in obsolete},
            'pinned_files': {str(p): cc.sha(p) for p in pins},
            'phase_lock': cfg['phase_lock'], 'journals': [str(self.state / 'transaction.json'), str(self.tx.generation / 'state/transaction.json')],
            'review_reports': [str(report)],
            'gates': [{'path': str(self.tx.directory / f'{name}.json')} for name in ('after-prune', 'after-stage')],
            'no_build_commands': self.settings['no_build_commands'],
            'core_config': str(core_cfg), 'commands': str(commands), 'staged_handoff': str(staged),
            'original_prepared_gzip': str(self.tx.directory / 'original-prepared.json.gz'),
            'active_handoff': str(old_handoff), 'old_handoff_sha256': cc.sha(old_handoff),
            'settings_sha256': 'fixture-pin'}
        self.retire = rg.Retirement(self.retire_settings)

    def validate_complete(self):
        assert all(not Path(p).exists() for p in self.retire_settings['obsolete'])
        assert cc.sha(self.retire_settings['active_handoff']) == cc.sha(self.retire_settings['staged_handoff'])
        assert cc.read_json(self.retire.journal)['status'] == 'complete'
        assert self.runtime.read_bytes() == b'runtime must survive'
        assert (self.state / 'phase.lock').exists()
        assert (self.root / 'config.json').exists()


def run_test(test):
    f = RetireFixture()
    try:
        test(f)
        print(test.__name__, 'PASS')
    finally:
        f.close()


def complete(f):
    with f.retire.locked():
        f.retire.prepare()
        f.retire.run()
        f.retire.run()
    f.validate_complete()


def activation_retry(f):
    f.retire.prepare()
    fails(lambda: f.retire.run(interrupt='after-activation'))
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])
    f.retire.run()
    f.validate_complete()


def unlink_retry(f):
    f.retire.prepare()
    fails(lambda: f.retire.run(interrupt='after-first-unlink'))
    assert sum(not Path(p).exists() for p in f.retire_settings['obsolete']) == 1
    f.retire.run()
    f.validate_complete()


def corrupt_replacement(f):
    f.retire.prepare()
    p = f.tx.generation / 'state/extra.zstpack'
    p.write_bytes(b'corrupt')
    fails(f.retire.run)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


def changed_old(f):
    f.retire.prepare()
    p = f.state / 'prepared.json'
    p.write_bytes(b'changed')
    fails(f.retire.run)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


def active_journal(f):
    write_json(f.state / 'transaction.json', {'status': 'entering'})
    fails(f.retire.prepare)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


def corrupt_archive(f):
    f.retire.prepare()
    (f.retire.directory / 'old-index.tsv.gz').write_bytes(b'bad gzip')
    fails(f.retire.run)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


def unrelated_path(f):
    s = dict(f.retire_settings)
    s['obsolete'] = dict(s['obsolete'], **{str(f.runtime): {'sha256': cc.sha(f.runtime)}})
    fails(lambda: rg.Retirement(s))
    assert f.runtime.read_bytes() == b'runtime must survive'


def interrupted_copy_preparation(f):
    (f.retire.directory / 'old-index.tsv.gz.new').write_bytes(b'partial compressed stream')
    (f.retire.directory / 'original-handoff.json.new').write_bytes(b'partial handoff copy')
    (f.retire.directory / 'retirement.json.new').write_bytes(b'partial journal')
    f.retire.prepare()
    f.retire.run()
    f.validate_complete()


def unsafe_handoff_backup(f):
    (f.retire.directory / 'original-handoff.json').symlink_to(f.retire_settings['active_handoff'])
    fails(f.retire.prepare)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


def changed_handoff_backup(f):
    f.retire.prepare()
    (f.retire.directory / 'original-handoff.json').write_bytes(b'changed backup')
    fails(f.retire.run)
    assert all(Path(p).exists() for p in f.retire_settings['obsolete'])


if __name__ == '__main__':
    tests = [complete, activation_retry, unlink_retry, corrupt_replacement, changed_old,
             active_journal, corrupt_archive, unrelated_path, interrupted_copy_preparation,
             unsafe_handoff_backup, changed_handoff_backup]
    for test in tests:
        run_test(test)
    print(json.dumps({'passed': len(tests)}))
