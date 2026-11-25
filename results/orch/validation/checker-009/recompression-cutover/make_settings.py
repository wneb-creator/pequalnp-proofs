import hashlib
import json
import os
import stat
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')
HERE = BASE / 'recompression-cutover'
OLD = BASE / 'resource-wrapper/shared-library-fallback'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def identity(path):
    s = path.stat()
    return {'dev': s.st_dev, 'ino': s.st_ino, 'size': s.st_size,
            'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}


old_path = OLD / 'generation-001-config.json'
old = json.loads(old_path.read_text())
new = json.loads((HERE / 'base-config.json').read_text())
core = json.loads((HERE / 'core-config.json').read_text())
commands = json.loads((HERE / 'commands.json').read_text())
required = {row['path']: row['sha256'] for row in commands['required_files']}
for p in [old_path, HERE / 'base-config.json', HERE / 'core-config.json', HERE / 'commands.json',
          HERE / 'handoff-config.json', HERE / 'cutover.py',
          Path(new['editor_pack']), Path(new['editor_index']), Path(new['editor_manifest']),
          Path(new['state_dir']) / 'extra.zstpack', Path(new['state_dir']) / 'prepared.json',
          Path(core['state_dir']) / 'excluded.zstpack', Path(core['state_dir']) / 'prepared.json',
          Path(core['state_dir']) / 'ready.json', Path(new['state_dir']).parent / 'staging-report.json']:
    required[str(p)] = sha(p)
reports = []
for name in ('review-generation002.stdout', 'review-disk-core.stdout', 'review-staged-configs.stdout'):
    p = HERE / name
    if json.loads(p.read_text())['status'] != 'PASS':
        raise RuntimeError('independent report has not passed')
    required[str(p)] = sha(p)
    reports.append({'path': str(p), 'keys': ['status'], 'equals': 'PASS'})
obsolete = {}
for p in [Path(old[k]) for k in ('editor_pack', 'editor_index', 'editor_manifest')] + [
        Path(old['state_dir']) / n for n in ('extra.zstpack', 'prepared.json')]:
    obsolete[str(p)] = {'identity': identity(p), 'sha256': sha(p)}
active = BASE / 'resource-wrapper/handoff-prototype/config.json'
settings = {'version': 1, 'transaction_dir': str(HERE / 'transaction-001'),
            'phase_lock': new['phase_lock'],
            'lock_aliases': [new['phase_lock'], str(Path(new['state_dir']) / 'phase.lock')],
            'active_handoff': str(active), 'old_handoff_sha256': sha(active),
            'old_base_config': str(old_path), 'new_base_config': str(HERE / 'base-config.json'),
            'new_core_config': str(HERE / 'core-config.json'), 'new_commands': str(HERE / 'commands.json'),
            'new_handoff': str(HERE / 'handoff-config.json'), 'required_pins': required,
            'journals': [str(Path(old['state_dir']) / 'transaction.json'),
                         str(Path(new['state_dir']) / 'transaction.json'),
                         str(BASE / 'core-phase/state/transaction.json'),
                         str(Path(core['state_dir']) / 'transaction.json')],
            'review_reports': reports, 'obsolete': obsolete,
            'holder': {'pid': 51759, 'starttime': 1015128, 'dev': 1, 'ino': 24087,
                       'fd': 4, 'seals': 15, 'size': 119486056,
                       'sha256': '7fcdf47496bd22445fc923c340eb0f816a51036bbba9b646ca4baff13eb2d295'}}
path = HERE / 'settings.json'
with path.open('x') as stream:
    json.dump(settings, stream, indent=2)
    stream.write('\n')
    stream.flush()
    os.fsync(stream.fileno())
fd = os.open(HERE, os.O_DIRECTORY)
try:
    os.fsync(fd)
finally:
    os.close(fd)
print(json.dumps({'settings': str(path), 'sha256': sha(path), 'obsolete_files': len(obsolete),
                  'obsolete_allocated': sum(Path(p).stat().st_blocks * 512 for p in obsolete),
                  'required_pins': len(required)}), flush=True)
