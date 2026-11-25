"""Add an exact operation-count restriction to the frozen full-4970 encoder."""
import argparse
import hashlib
import itertools
import json
import resource
from pathlib import Path

import serve_sat


def add_at_most(cnf, literals, count):
    """Forbid every (count+1)-subset of true literals; small controls only."""
    assert count >= 0
    for subset in itertools.combinations(literals, count + 1):
        cnf.clause(*(-literal for literal in subset))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--graph', required=True)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--operator', choices=['AND', 'OR'], required=True)
    parser.add_argument('--maximum', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--memory-mib', type=int, default=512)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    args.output_before_last = False
    args.generate_only = False
    limit = args.memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    frozen = serve_sat.make_problem

    def with_count(*positional, **keywords):
        encoded = frozen(*positional, **keywords)
        cnf, ops = encoded[:2]
        # op=true means OR, op=false means AND.
        literals = ops if args.operator == 'OR' else [-op for op in ops]
        add_at_most(cnf, literals, args.maximum)
        return encoded

    serve_sat.make_problem = with_count
    result = serve_sat.main(args)
    result['operator_restriction'] = {
        'operator': args.operator, 'maximum': args.maximum,
        'all_posted_hypotheses_enforced': True, 'memory_limit_mib': args.memory_mib,
        'base_encoder_sha256': hashlib.sha256(Path(serve_sat.__file__).read_bytes()).hexdigest()}
    if result['status'] == 'SAT':
        and_count = sum(not op for op, _, _ in result['circuit'])
        or_count = args.gates - and_count
        actual = and_count if args.operator == 'AND' else or_count
        assert actual <= args.maximum
        result['operation_counts'] = {'AND': and_count, 'OR': or_count}
        expected_lower_bound = result['cover_number'] if args.operator == 'AND' else len(result['edges']) - 1
        result['violates_proposed_count_bound'] = actual < expected_lower_bound
    Path(args.output).with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
