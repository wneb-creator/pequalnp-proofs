#!/usr/bin/env python3
"""Refine a partial monotone synthesis specification using false independent sets."""
import argparse
import json
import math
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import synthesize


def bipartition_rows(info):
    n = info['n']
    adjacency = [set() for _ in range(n)]
    for a, b in info['edges']:
        adjacency[a].add(b)
        adjacency[b].add(a)
    colors = [None] * n
    for root in range(n):
        if colors[root] is not None:
            continue
        colors[root] = 0
        stack = [root]
        while stack:
            a = stack.pop()
            for b in adjacency[a]:
                if colors[b] is None:
                    colors[b] = 1 - colors[a]
                    stack.append(b)
                else:
                    assert colors[b] != colors[a], 'graph must be bipartite'
    isolated = sum(1 << v for v in range(n) if not adjacency[v])
    return sorted({isolated | sum(1 << v for v in range(n)
                                 if colors[v] == color)
                   for color in (0, 1)})


def extend_independent(info, mask):
    assert all(not (mask >> a & 1 and mask >> b & 1)
               for a, b in info['edges'])
    for v in range(info['n']):
        candidate = mask | (1 << v)
        if all(not (candidate >> a & 1 and candidate >> b & 1)
               for a, b in info['edges']):
            mask = candidate
    return mask


def evaluate(n, gates, mask):
    values = [bool(mask & (1 << v)) for v in range(n)]
    for g in gates:
        assert 0 <= g['left'] < len(values)
        assert 0 <= g['right'] < len(values)
        a, b = values[g['left']], values[g['right']]
        assert g['op'] in ('and', 'or')
        values.append(a and b if g['op'] == 'and' else a or b)
    return values[-1]


def check_every_input(info, gates):
    false_positives = []
    false_negatives = []
    for mask in range(1 << info['n']):
        expected = any(mask >> a & 1 and mask >> b & 1
                       for a, b in info['edges'])
        actual = evaluate(info['n'], gates, mask)
        if actual and not expected:
            false_positives.append(mask)
        if expected and not actual:
            false_negatives.append(mask)
    assert not false_negatives, ('edge constraints or decoding failed', false_negatives)
    return false_positives


def check_essential_inputs(info, negative_masks):
    # This witnesses why the encoder's unconditional input-read clauses remain
    # valid on our relaxed sample. An edge containing u is positive; deleting u
    # leaves a neighbor contained in a negative sampled independent set.
    for a, b in info['edges']:
        for u, v in ((a, b), (b, a)):
            assert any(mask >> v & 1 and not mask >> u & 1
                       for mask in negative_masks), (u, v)


def initial_negatives(info, mode):
    if mode == 'bipartition':
        return set(bipartition_rows(info))
    if mode == 'all':
        return {mask for mask, target in info['rows'] if not target}
    edge_masks = {mask for mask, target in info['rows'] if target}
    return {1 << v for v in range(info['n'])} | {
        (1 << a) | (1 << b)
        for a in range(info['n']) for b in range(a + 1, info['n'])
        if ((1 << a) | (1 << b)) not in edge_masks}


def run(info, name, k, args):
    directory = ROOT / 'synthesis' / (
        f'cegar-{name}-k{k}-{args.initial}-{args.add}-s{args.seed}-{time.time_ns()}')
    directory.mkdir(parents=True)
    negative_masks = initial_negatives(info, args.initial)
    check_essential_inputs(info, negative_masks)
    positives = [(mask, True) for mask, target in info['rows'] if target]
    all_maximal_negatives = {mask for mask, target in info['rows'] if not target}
    (directory / 'configuration.json').write_text(json.dumps({
        'graph': name, 'k': k, 'info': info, 'args': vars(args),
        'graph_symmetry': False,
    }, indent=2, default=str))
    started = time.monotonic()
    history = []
    final_status = 'UNKNOWN'
    for round_number in range(args.max_rounds):
        remaining = args.total_seconds - (time.monotonic() - started)
        if remaining <= 0:
            break
        seconds = min(args.seconds_per_round, max(1, math.ceil(remaining)))
        sample = dict(info)
        sample['rows'] = positives + [(mask, False) for mask in sorted(negative_masks)]
        cnf, mapping = synthesize.encode(
            sample, k, normalized=not args.plain, symmetry=None,
            distinct=args.distinct, undominated=args.undominated,
            oriented=args.oriented)
        step = directory / f'round-{round_number:03d}'
        step.mkdir()
        cnf.write(step / 'input.cnf')
        (step / 'encoding.json').write_text(json.dumps({
            'info': sample, 'mapping': mapping, 'graph_symmetry': None,
            'normalized': not args.plain, 'distinct': args.distinct,
            'undominated': args.undominated, 'oriented': args.oriented,
        }, indent=2))
        round_started = time.monotonic()
        with (step / 'solver.stdout').open('w') as stdout, \
                (step / 'solver.stderr').open('w') as stderr:
            process = subprocess.Popen([
                str(args.solver), f'--time={seconds}', f'--seed={args.seed}',
                str(step / 'input.cnf')], stdout=stdout, stderr=stderr)
            print(json.dumps({'round': round_number, 'solver_pid': process.pid,
                              'directory': str(step), 'time_limit': seconds}), flush=True)
            process.wait()
        output = (step / 'solver.stdout').read_text()
        result = {
            'round': round_number, 'sample_rows': len(sample['rows']),
            'negative_rows': len(negative_masks), 'vars': cnf.nvars,
            'clauses': len(cnf.clauses), 'exit': process.returncode,
            'seconds': time.monotonic() - round_started,
        }
        if process.returncode == 20:
            assert 's UNSATISFIABLE' in output
            result['status'] = 'UNSAT_RELAXATION'
            final_status = 'UNSAT'
        elif process.returncode == 10:
            assert 's SATISFIABLE' in output
            gates = synthesize.decode(output, mapping)
            assert all(evaluate(info['n'], gates, mask) == target
                       for mask, target in sample['rows']), 'decoded sample mismatch'
            false_positives = check_every_input(info, gates)
            result.update(gates=gates, truth_rows_checked=1 << info['n'],
                          false_positive_count=len(false_positives),
                          actual_gates=sum(not g['pad'] for g in gates))
            if not false_positives:
                result['status'] = 'SAT_EXACT'
                final_status = 'SAT'
            else:
                if args.add == 'one':
                    false_positives = [max(false_positives, key=int.bit_count)]
                added = {extend_independent(info, mask) for mask in false_positives}
                assert added <= all_maximal_negatives
                assert all(evaluate(info['n'], gates, mask) for mask in added)
                assert not added & negative_masks, 'refinement did not add fresh rows'
                negative_masks.update(added)
                result['status'] = 'SAT_REFINED'
                result['added_negative_masks'] = sorted(added)
        else:
            result['status'] = 'UNKNOWN'
        (step / 'result.json').write_text(json.dumps(result, indent=2))
        history.append(result)
        print(json.dumps({key: value for key, value in result.items()
                          if key != 'gates'}), flush=True)
        if result['status'] != 'SAT_REFINED':
            break
    final = {'graph': name, 'k': k, 'status': final_status,
             'seconds': time.monotonic() - started, 'directory': str(directory),
             'rounds': history}
    (directory / 'result.json').write_text(json.dumps(final, indent=2))
    print(json.dumps({key: value for key, value in final.items()
                      if key != 'rounds'}), flush=True)
    return final


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph', default='Heawood')
    parser.add_argument('--k', type=int)
    parser.add_argument('--candidates', type=Path,
                        default=ROOT / 'candidates.json')
    parser.add_argument('--solver', type=Path, default=synthesize.DEFAULT_SOLVER)
    parser.add_argument('--initial', choices=('bipartition', 'pairs', 'all'),
                        default='bipartition')
    parser.add_argument('--add', choices=('one', 'all'), default='one')
    parser.add_argument('--seconds-per-round', type=int, default=60)
    parser.add_argument('--total-seconds', type=int, default=600)
    parser.add_argument('--max-rounds', type=int, default=100)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--plain', action='store_true')
    parser.add_argument('--distinct', action='store_true')
    parser.add_argument('--undominated', action='store_true')
    parser.add_argument('--oriented', action='store_true')
    args = parser.parse_args()
    if args.solver is None:
        parser.error('Kissat was not found; provide --solver PATH')
    assert args.seconds_per_round > 0 and args.total_seconds > 0 and args.max_rounds > 0
    if args.plain and args.oriented:
        parser.error('--oriented requires normalization')
    if args.graph.startswith('C') and args.graph[1:].isdigit():
        n = int(args.graph[1:])
        edges = [(v, (v + 1) % n) for v in range(n)]
    else:
        candidates = json.loads(args.candidates.read_text())
        graph = next(candidate for candidate in candidates
                     if candidate['name'] == args.graph)
        n, edges = graph['n'], graph['edges']
    info = synthesize.graph_info(n, edges)
    k = args.k if args.k is not None else info['standard_bound'] - 1
    run(info, args.graph, k, args)


if __name__ == '__main__':
    main()
