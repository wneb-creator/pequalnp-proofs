#!/usr/bin/env python3
"""Coalesce consecutive equal-arity spans into bounded depth-zero batches.

The source's generic spansBlock theorem continues to justify the certificate.
Every transformed numerical check must still be replayed by Lean.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


PATTERN = re.compile(
    r'(spansBlock ([A-Za-z_][\w.]*) ([0-9]+) ([0-9]+) )'
    r'\[([ \t\n0-9(),]+)\]'
)


def transform(source, cap):
    records = []

    def replace(match):
        payload = match.group(5)
        triples = [(int(n), int(a), int(d)) for n, a, d in re.findall(
            r'\(([0-9]+),\s*([0-9]+),\s*([0-9]+)\)', payload)]
        assert triples
        assert re.sub(r'\(([0-9]+),\s*([0-9]+),\s*([0-9]+)\)|[\s,]', '', payload) == ''
        runs = []
        for count, arity, _ in triples:
            assert count > 0
            if runs and runs[-1][1] == arity:
                runs[-1] = (runs[-1][0] + count, arity)
            else:
                runs.append((count, arity))
        merged = []
        for count, arity in runs:
            while count:
                size = min(cap, count)
                merged.append((size, arity, 0))
                count -= size
        assert [a for n, a, _ in triples for _ in range(n)] == [a for n, a, _ in merged for _ in range(n)]
        if merged != triples:
            records.append({
                'forest': match.group(2), 'level': int(match.group(3)),
                'start': int(match.group(4)), 'before': triples, 'after': merged,
                'coveredStates': sum(n for n, _, _ in triples),
                'oldLeaves': sum(2**d for _, _, d in triples),
                'newLeaves': len(merged),
            })
        return match.group(1) + '[' + ','.join(f'({n},{a},{d})' for n, a, d in merged) + ']'

    output = PATTERN.sub(replace, source)
    assert re.findall(r'\b0x[0-9a-fA-F]+', source) == re.findall(r'\b0x[0-9a-fA-F]+', output)
    return output, records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cap', type=int, default=64)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    assert args.cap > 0
    source = args.source.read_text()
    output, records = transform(source, args.cap)
    args.output.write_text(output)
    report = {
        'source': str(args.source), 'output': str(args.output), 'cap': args.cap,
        'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
        'outputSha256': hashlib.sha256(output.encode()).hexdigest(),
        'sourceBytes': len(source.encode()), 'outputBytes': len(output.encode()),
        'changedCalls': len(records),
        'oldLeaves': sum(r['oldLeaves'] for r in records),
        'newLeaves': sum(r['newLeaves'] for r in records),
        'hexLiteralsUnchanged': True, 'records': records,
    }
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}))


if __name__ == '__main__':
    main()
