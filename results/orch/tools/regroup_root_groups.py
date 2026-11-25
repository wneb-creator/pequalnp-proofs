#!/usr/bin/env python3
"""Merge adjacent equal-arity checker groups; preserve every covered state.

This changes proof-check scheduling only. Every resulting file needs a fresh
Lean replay; this script does not assert that any numeric check succeeds.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


PATTERN = re.compile(
    r'(apply rootGroupsBlock ([A-Za-z_][\w.]*) ([0-9]+) ([0-9]+) )'
    r'\[([ \t\n0-9(),]+)\]'
)


def transform(source, cap):
    records = []

    def replace(match):
        payload = match.group(5)
        pairs = [(int(a), int(n)) for a, n in re.findall(
            r'\(([0-9]+),\s*([0-9]+)\)', payload)]
        assert pairs
        assert re.sub(r'\(([0-9]+),\s*([0-9]+)\)|[\s,]', '', payload) == ''
        merged = []
        for arity, count in pairs:
            assert count > 0
            if merged and merged[-1][0] == arity and merged[-1][1] + count <= cap:
                merged[-1] = (arity, merged[-1][1] + count)
            else:
                merged.append((arity, count))
        assert sum(n for _, n in pairs) == sum(n for _, n in merged)
        # Full expanded arity sequences give an independent coverage check.
        assert [a for a, n in pairs for _ in range(n)] == [a for a, n in merged for _ in range(n)]
        if merged != pairs:
            records.append({
                'forest': match.group(2), 'level': int(match.group(3)),
                'start': int(match.group(4)), 'before': pairs, 'after': merged,
                'coveredStates': sum(n for _, n in pairs),
            })
        return match.group(1) + '[' + ','.join(f'({a},{n})' for a, n in merged) + ']'

    output = PATTERN.sub(replace, source)
    # Proof-group edits must not touch a hexadecimal data literal.
    assert re.findall(r'\b0x[0-9a-fA-F]+', source) == re.findall(r'\b0x[0-9a-fA-F]+', output)
    return output, records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cap', type=int, default=96)
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
        'groupsBefore': sum(len(r['before']) for r in records),
        'groupsAfter': sum(len(r['after']) for r in records),
        'hexLiteralsUnchanged': True, 'records': records,
    }
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}))


if __name__ == '__main__':
    main()
