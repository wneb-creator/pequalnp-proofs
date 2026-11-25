import argparse
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')


def checked_json(path, expected):
    path = Path(path)
    if not path.is_absolute() or not path.is_relative_to(BASE):
        raise RuntimeError('commands must stay in task scratch')
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError('reviewed phase commands changed')
    return json.loads(data)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--commands', required=True)
    parser.add_argument('--commands-sha256', required=True)
    parser.add_argument('action', choices=('enter', 'restore'))
    args = parser.parse_args()
    commands = checked_json(args.commands, args.commands_sha256)
    pins = {}
    for item in commands['required_files']:
        path = Path(item['path'])
        if not path.is_absolute() or not path.is_relative_to(BASE):
            raise RuntimeError('phase input outside task scratch')
        if hashlib.sha256(path.read_bytes()).hexdigest() != item['sha256']:
            raise RuntimeError('reviewed phase input changed')
        pins[str(path)] = item['sha256']
    sequence = Path(commands['sequence_source'])
    if str(sequence) not in pins:
        raise RuntimeError('sequence source is not pinned')
    for key in ('base_command', 'core_command'):
        if not isinstance(commands[key], list) or not commands[key] or not all(isinstance(value, str) for value in commands[key]):
            raise RuntimeError('invalid phase argv')
    spec = importlib.util.spec_from_file_location('reviewed_sequence', sequence)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Sequence(args.action, commands['base_command'], commands['core_command']).run()


if __name__ == '__main__':
    sys.exit(main())
