import argparse
import hashlib
import json
import os
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')
HERE = BASE / 'recompression-cutover'
OLD = BASE / 'resource-wrapper/shared-library-fallback'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def write(path, value):
    raw = (json.dumps(value, indent=2) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    return sha(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reserve-bytes', type=int, required=True)
    args = parser.parse_args()
    if args.reserve_bytes < 24 * 1024 * 1024:
        raise RuntimeError('reserve below reviewed proposed range')
    base_state = BASE / 'build-cache-compaction/generation-002/state'
    core_state = BASE / 'core-phase/disk-state-001'
    disk_report = json.loads((base_state.parent / 'staging-report.json').read_text())
    core_report = json.loads((core_state / 'ready.json').read_text())
    for name, pin in disk_report['files'].items():
        if sha(Path(name)) != pin['sha256']:
            raise RuntimeError('staged disk generation pin mismatch')
    for key in ('prepared', 'pack'):
        if sha(Path(core_report[key])) != core_report[key + '_sha256']:
            raise RuntimeError('staged core pin mismatch')
    base = json.loads((OLD / 'generation-001-config.json').read_text())
    base.update(state_dir=str(base_state),
                editor_index=str(base_state.parent / 'editor/index.tsv'),
                editor_manifest=str(base_state.parent / 'editor/manifest.jsonl'),
                editor_pack=str(base_state.parent / 'editor/data.zstpack'),
                disk_reserve_bytes=args.reserve_bytes,
                excluded_core_manifests=[{'path': str(core_state / 'prepared.json'),
                    'sha256': core_report['prepared_sha256']}])
    base_sha = write(HERE / 'base-config.json', base)
    core = json.loads((OLD / 'generation-001-core-config.json').read_text())
    core.update(state_dir=str(core_state), base_journal=str(base_state / 'transaction.json'))
    core_sha = write(HERE / 'core-config.json', core)
    commands = json.loads((OLD / 'generation-001-commands.json').read_text())
    commands['base_command'][3] = str(HERE / 'base-config.json')
    commands['base_command'][5] = base_sha
    commands['core_command'][3] = str(HERE / 'core-config.json')
    for row in commands['required_files']:
        if row['path'] == str(OLD / 'generation-001-config.json'):
            row.update(path=str(HERE / 'base-config.json'), sha256=base_sha)
        elif row['path'] == str(OLD / 'generation-001-core-config.json'):
            row.update(path=str(HERE / 'core-config.json'), sha256=core_sha)
        elif sha(Path(row['path'])) != row['sha256']:
            raise RuntimeError('original source pin changed')
    command_sha = write(HERE / 'commands.json', commands)
    handoff = json.loads((OLD / 'generation-001-handoff-config.json').read_text())
    for key in ('phase_enter', 'phase_restore'):
        handoff[key][3] = str(HERE / 'commands.json')
        handoff[key][5] = command_sha
    handoff_sha = write(HERE / 'handoff-config.json', handoff)
    directory = os.open(HERE, os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    print(json.dumps({'status': 'staged_only', 'reserve_bytes': args.reserve_bytes,
                      'base_config_sha256': base_sha, 'core_config_sha256': core_sha,
                      'commands_sha256': command_sha, 'handoff_sha256': handoff_sha}), flush=True)


if __name__ == '__main__':
    main()
