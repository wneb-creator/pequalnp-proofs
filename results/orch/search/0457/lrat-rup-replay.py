import argparse
import gzip
import hashlib
import json
from pathlib import Path
import resource
import time


def text_input(path):
    return gzip.open(path, 'rt') if path.suffix == '.gz' else path.open('r')


def binary_input(path):
    return gzip.open(path, 'rb') if path.suffix == '.gz' else path.open('rb')


def header(path):
    with text_input(path) as stream:
        for line in stream:
            words = line.split()
            if not words or words[0] == 'c':
                continue
            assert len(words) == 4 and words[:2] == ['p', 'cnf']
            return int(words[2]), int(words[3])
    raise ValueError('Missing DIMACS header')


def main():
    parser = argparse.ArgumentParser(description='Independent memory-capped binary-LRAT dependency trim and RUP-only replay; no Lean-kernel claim.')
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--proof', type=Path, required=True)
    parser.add_argument('--outdir', type=Path, required=True)
    parser.add_argument('--max-address-space-mib', type=int, default=1024)
    args = parser.parse_args()
    assert args.max_address_space_mib >= 128
    limit = args.max_address_space_mib*2**20
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    args.outdir.mkdir(exist_ok=False)
    started = time.monotonic()
    variables, original_count = header(args.cnf)
    assert variables >= 0 and original_count >= 0
    with binary_input(args.proof) as stream:
        data = stream.read()
    live = bytearray(b'\x01')*(original_count+1)
    live[0] = 0
    position = 0
    additions = {}
    order = []
    last_id = original_count
    final_empty = None
    deletions = 0

    def number():
        nonlocal position
        unsigned = shift = 0
        while True:
            assert position < len(data), 'Truncated binary integer'
            byte = data[position]
            position += 1
            unsigned |= (byte & 127) << shift
            if byte < 128:
                return -(unsigned >> 1) if unsigned & 1 else unsigned >> 1
            shift += 7
            assert shift <= 63, 'Oversized binary integer'

    def sequence():
        result = []
        while True:
            item = number()
            if item == 0:
                return tuple(result)
            result.append(item)

    while position < len(data):
        begin = position
        tag = data[position]
        position += 1
        if tag == ord('a'):
            ident = number()
            assert ident > last_id, 'Nonfresh or nonmonotone clause ID'
            clause = sequence()
            hints = sequence()
            assert all(1 <= abs(x) <= variables for x in clause)
            for hint in hints:
                source = abs(hint)
                assert source < len(live) and live[source], ('Unavailable hint', ident, hint)
            if ident >= len(live):
                live.extend(b'\x00'*(ident+1-len(live)))
            live[ident] = 1
            additions[ident] = (clause, hints, begin, position)
            order.append(ident)
            last_id = ident
            if not clause:
                final_empty = ident
        elif tag == ord('d'):
            for ident in sequence():
                assert ident > 0
                if ident < len(live):
                    live[ident] = 0
                deletions += 1
        else:
            raise ValueError(('Unsupported binary LRAT record', tag, position-1))
    assert final_empty is not None, 'No empty-clause addition'
    needed = set()
    originals = set()
    pending = [final_empty]
    while pending:
        ident = pending.pop()
        if ident <= original_count:
            assert ident > 0
            originals.add(ident)
            continue
        if ident in needed:
            continue
        clause, hints, _, _ = additions[ident]
        assert all(hint > 0 for hint in hints), ('Needed RAT record unsupported', ident)
        needed.add(ident)
        pending.extend(hints)
    del live
    print('PARSED', json.dumps({'proof_bytes': len(data), 'additions': len(additions),
                               'needed_additions': len(needed), 'needed_originals': len(originals)}), flush=True)
    clauses = {}
    count = 0
    current = []
    saw_header = False
    with text_input(args.cnf) as stream:
        for line in stream:
            words = line.split()
            if not words or words[0] == 'c':
                continue
            if words[0] == 'p':
                assert not saw_header and words == ['p', 'cnf', str(variables), str(original_count)]
                saw_header = True
                continue
            assert saw_header
            for word in words:
                literal = int(word)
                if literal:
                    assert 1 <= abs(literal) <= variables
                    current.append(literal)
                else:
                    count += 1
                    if count in originals:
                        clauses[count] = tuple(current)
                    current = []
    assert saw_header and not current and count == original_count
    assert set(clauses) == originals
    with (args.outdir/'needed-original-clauses.txt').open('x') as output:
        for ident in sorted(originals):
            output.write(str(ident)+' '+' '.join(map(str, clauses[ident]))+' 0\n')
    replayed = 0
    for ident in order:
        if ident not in needed:
            continue
        clause, hints, _, _ = additions[ident]
        assigned = {}
        conflict = False
        for literal in clause:
            variable, truth = abs(literal), literal < 0
            if variable in assigned and assigned[variable] != truth:
                conflict = True
                break
            assigned[variable] = truth
        if not conflict:
            for hint in hints:
                assert hint in clauses and hint < ident
                unit = set()
                satisfied = False
                for literal in clauses[hint]:
                    variable = abs(literal)
                    if variable not in assigned:
                        unit.add(literal)
                    elif assigned[variable] == (literal > 0):
                        satisfied = True
                        break
                if satisfied:
                    continue
                if not unit:
                    conflict = True
                    break
                assert len(unit) == 1, ('Nonunit RUP hint', ident, hint)
                literal = next(iter(unit))
                assigned[abs(literal)] = literal > 0
        assert conflict, ('RUP failed to derive conflict', ident)
        clauses[ident] = clause
        replayed += 1
    assert clauses[final_empty] == ()
    trimmed = args.outdir/'trimmed.lrat'
    with trimmed.open('xb') as output:
        for ident in order:
            if ident in needed:
                _, _, begin, end = additions[ident]
                output.write(data[begin:end])
    result = {'status': 'INDEPENDENT_RUP_REPLAY_PASSED',
              'scope': 'external computational certificate replay, not Lean-kernel verification',
              'original_variables': variables, 'original_clauses': original_count,
              'proof_bytes': len(data), 'proof_sha256': hashlib.sha256(data).hexdigest(),
              'additions': len(additions), 'deletions': deletions,
              'needed_originals': len(originals), 'replayed_additions': replayed,
              'final_empty_id': final_empty, 'trimmed_bytes': trimmed.stat().st_size,
              'temporal_hint_availability_checked': True,
              'max_address_space_mib': args.max_address_space_mib,
              'max_RSS_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'elapsed_seconds': time.monotonic()-started}
    (args.outdir/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
