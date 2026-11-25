"""Validate RUP learned-clause checkpoints and stitch restarts to the original CNF.

No learned clause is an assumption in the stitched proof. Both subcommands reject
all RAT/negative hints, malformed/truncated records, and changed source files.
Original traces are never modified. Output paths must not already exist.
"""

import argparse
import gzip
import hashlib
import json
import sys
from contextlib import contextmanager
from pathlib import Path

from lrat_pack import read_cnf, read_signed_varint, read_zero_terminated


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def signature(path):
    info = path.stat()
    return info.st_size, info.st_mtime_ns


@contextmanager
def proof_stream(path):
    with path.open('rb') as raw:
        compressed = raw.read(2) == b'\x1f\x8b'
    with (gzip.open(path, 'rb') if compressed else path.open('rb')) as stream:
        first = stream.read(1)
        stream.seek(0)
        yield stream, first in (b'a', b'd')


def records(path):
    with proof_stream(path) as (stream, binary):
        while True:
            if binary:
                tag = stream.read(1)
                if not tag:
                    return
                if tag == b'd':
                    deleted = read_zero_terminated(stream)
                    if any(identifier <= 0 for identifier in deleted):
                        raise ValueError('nonpositive deletion identifier')
                    yield 'd', 0, deleted, []
                elif tag == b'a':
                    identifier = read_signed_varint(stream)
                    clause = read_zero_terminated(stream)
                    hints = read_zero_terminated(stream)
                    yield 'a', identifier, clause, hints
                else:
                    raise ValueError('unknown binary LRAT record tag')
                continue
            line = stream.readline()
            if not line:
                return
            fields = line.split()
            if not fields or fields[0] == b'c':
                continue
            identifier = int(fields[0])
            if len(fields) > 1 and fields[1] == b'd':
                deleted = list(map(int, fields[2:]))
                if not deleted or deleted[-1] != 0 or any(i <= 0 for i in deleted[:-1]):
                    raise ValueError('invalid deletion record')
                yield 'd', identifier, deleted[:-1], []
                continue
            values = list(map(int, fields[1:]))
            if not values or values[-1] != 0:
                raise ValueError('incomplete LRAT addition')
            split = values.index(0)
            clause, hints = values[:split], values[split + 1:-1]
            if 0 in hints:
                raise ValueError('unexpected zero inside hint list')
            yield 'a', identifier, clause, hints


class RupState:
    def __init__(self, initial):
        self.initial_count = len(initial)
        self.database = {identifier: tuple(clause) for identifier, clause in initial.items()}
        self.last = self.initial_count
        self.additions = 0
        self.deletions = 0
        self.empty = None

    def consume(self, record):
        kind, identifier, clause, hints = record
        if kind == 'd':
            for deleted in clause:
                if deleted > self.initial_count:
                    self.database.pop(deleted, None)
            self.deletions += len(clause)
            return
        if identifier <= self.last:
            raise ValueError('addition identifiers must strictly increase above initial IDs')
        if any(hint <= 0 for hint in hints):
            raise ValueError('RAT/negative or zero hints are not supported')
        if any(hint >= identifier for hint in hints):
            raise ValueError('hint does not refer to an earlier clause')
        falsified = set(clause)
        conflict = False
        for hint in hints:
            if hint not in self.database:
                raise ValueError(f'unknown or deleted hint {hint} in addition {identifier}')
            unit = None
            for lit in self.database[hint]:
                if lit not in falsified:
                    if unit is not None and unit != lit:
                        raise ValueError(f'non-unit hint {hint} in addition {identifier}')
                    unit = lit
            if unit is None:
                conflict = True
                break
            falsified.add(-unit)
        if not conflict:
            raise ValueError(f'no RUP conflict for addition {identifier}')
        self.database[identifier] = tuple(clause)
        self.last = identifier
        self.additions += 1
        if not clause:
            self.empty = identifier


def scan(path, initial, output=None):
    state = RupState(initial)
    events = 0
    for record in records(path):
        state.consume(record)
        if output is not None and record[0] == 'a':
            emit(output, *record[1:])
        events += 1
        if events % 100000 == 0:
            print(json.dumps({'events': events, 'additions': state.additions,
                              'active_derived': len(state.database) - state.initial_count}),
                  file=sys.stderr, flush=True)
    return state, events


def varint(value):
    value = 2 * abs(value) + int(value < 0)
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return result


def emit(stream, identifier, clause, hints):
    stream.write(b'a')
    stream.write(varint(identifier))
    for values in (clause, hints):
        for value in values:
            stream.write(varint(value))
        stream.write(b'\x00')


def require_new(*paths):
    if len({str(p.resolve()) for p in paths}) != len(paths):
        raise ValueError('output paths must be distinct')
    for path in paths:
        if path.exists():
            raise ValueError(f'output path already exists: {path}')


def checkpoint(args):
    require_new(args.output_cnf, args.manifest)
    initial = read_cnf(args.cnf)
    source_sig = signature(args.prefix)
    source_hash = digest(args.prefix)
    state, events = scan(args.prefix, initial)
    if signature(args.prefix) != source_sig:
        raise ValueError('prefix changed during validation')
    if state.empty is not None:
        raise ValueError('prefix already contains an empty clause; pack it directly')
    learned = sorted(identifier for identifier in state.database if identifier > len(initial))
    if args.max_length is not None:
        learned = [identifier for identifier in learned
                   if len(state.database[identifier]) <= args.max_length]
    if args.max_learned is not None:
        # Short clauses first; keep final order by original proof identifier.
        learned = sorted(sorted(learned, key=lambda i: (len(state.database[i]), -i))[:args.max_learned])
    selected = [*initial.values(), *(state.database[identifier] for identifier in learned)]
    max_var = max((abs(lit) for clause in selected for lit in clause), default=0)
    with args.output_cnf.open('x') as stream:
        stream.write(f'p cnf {max_var} {len(selected)}\n')
        for clause in selected:
            stream.write(' '.join(map(str, clause)) + (' ' if clause else '') + '0\n')
    manifest = {
        'format': 'rup-restart-v1',
        'original_cnf_sha256': digest(args.cnf),
        'prefix_sha256': source_hash,
        'checkpoint_cnf_sha256': digest(args.output_cnf),
        'original_clauses': len(initial),
        'prefix_events': events,
        'prefix_additions': state.additions,
        'prefix_last_id': state.last,
        'learned_ids': learned,
        'restart_initial_clauses': len(selected),
    }
    with args.manifest.open('x') as stream:
        json.dump(manifest, stream, separators=(',', ':'))
    print(json.dumps({k: v for k, v in manifest.items() if k != 'learned_ids'} | {'retained_learned': len(learned)}, indent=2))


def stitch(args):
    temporary = args.output.with_name(args.output.name + '.partial')
    require_new(args.output, temporary)
    manifest = json.loads(args.manifest.read_text())
    if manifest.get('format') != 'rup-restart-v1':
        raise ValueError('unknown checkpoint manifest format')
    for key, path in [('original_cnf_sha256', args.cnf), ('prefix_sha256', args.prefix),
                      ('checkpoint_cnf_sha256', args.checkpoint_cnf)]:
        if digest(path) != manifest[key]:
            raise ValueError(f'source hash mismatch: {key}')
    prefix_sig = signature(args.prefix)
    resumed_sig = signature(args.resumed)
    initial = read_cnf(args.cnf)
    restarted = read_cnf(args.checkpoint_cnf)
    count = len(initial)
    learned = manifest['learned_ids']
    if (len(restarted) != count + len(learned) or
            count != manifest['original_clauses'] or
            len(restarted) != manifest['restart_initial_clauses'] or
            learned != sorted(set(learned))):
        raise ValueError('invalid checkpoint counts or learned IDs')
    for identifier, clause in initial.items():
        if restarted[identifier] != clause:
            raise ValueError('checkpoint does not preserve the original clauses exactly')
    with temporary.open('xb') as output:
        prefix, events = scan(args.prefix, initial, output)
        if (events != manifest['prefix_events'] or prefix.last != manifest['prefix_last_id'] or
                prefix.additions != manifest['prefix_additions']):
            raise ValueError('validated prefix does not match manifest')
        for slot, identifier in enumerate(learned, count + 1):
            if identifier <= count or identifier not in prefix.database:
                raise ValueError('retained learned clause is not active in prefix')
            if tuple(restarted[slot]) != prefix.database[identifier]:
                raise ValueError('checkpoint learned clause content mismatch')
        prefix_last = prefix.last
        del prefix
        resumed_count = len(restarted)
        remap = {**{i: i for i in initial},
                 **{slot: identifier for slot, identifier in enumerate(learned, count + 1)}}
        resumed = RupState(restarted)
        for record in records(args.resumed):
            resumed.consume(record)
            if record[0] == 'd':
                continue
            _, identifier, clause, hints = record
            mapped = prefix_last + identifier - resumed_count
            remap[identifier] = mapped
            emit(output, mapped, clause, [remap[hint] for hint in hints])
        if resumed.empty is None:
            raise ValueError('resumed trace does not contain a completed empty-clause refutation')
    if signature(args.prefix) != prefix_sig or signature(args.resumed) != resumed_sig:
        raise ValueError('source trace changed during stitching')
    temporary.rename(args.output)
    print(json.dumps({'original_clauses': count, 'retained_learned': len(learned),
                      'prefix_additions': manifest['prefix_additions'],
                      'resumed_additions': resumed.additions,
                      'stitched_final_id': remap[resumed.empty],
                      'stitched_sha256': digest(args.output)}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    cp = commands.add_parser('checkpoint')
    cp.add_argument('cnf', type=Path)
    cp.add_argument('prefix', type=Path)
    cp.add_argument('output_cnf', type=Path)
    cp.add_argument('manifest', type=Path)
    cp.add_argument('--max-length', type=int)
    cp.add_argument('--max-learned', type=int)
    cp.set_defaults(run=checkpoint)
    st = commands.add_parser('stitch')
    st.add_argument('cnf', type=Path)
    st.add_argument('prefix', type=Path)
    st.add_argument('checkpoint_cnf', type=Path)
    st.add_argument('manifest', type=Path)
    st.add_argument('resumed', type=Path)
    st.add_argument('output', type=Path)
    st.set_defaults(run=stitch)
    args = parser.parse_args()
    if getattr(args, 'max_length', 0) is not None and getattr(args, 'max_length', 0) < 0:
        parser.error('--max-length must be nonnegative')
    if getattr(args, 'max_learned', 0) is not None and getattr(args, 'max_learned', 0) < 0:
        parser.error('--max-learned must be nonnegative')
    args.run(args)


if __name__ == '__main__':
    main()
