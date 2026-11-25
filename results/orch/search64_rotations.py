#!/usr/bin/env python3
"""Search semantic-equivalent associative variants before deleting one gate."""
import argparse
import importlib.util
import json
import time
from pathlib import Path

spec = importlib.util.spec_from_file_location('search64', Path(__file__).with_name('search64.py'))
search64 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(search64)


def rotations(gates, output):
    readers = [0] * (26 + len(gates))
    readers[output] += 1
    for _, a, b in gates:
        readers[a] += 1
        readers[b] += 1
    answers = []
    for j, (op, a, b) in enumerate(gates):
        for child, other in ((a, b), (b, a)):
            if child < 26 or readers[child] != 1 or other >= child:
                continue
            child_j = child - 26
            child_op, c, d = gates[child_j]
            if child_op != op:
                continue
            for keep, shift in ((c, d), (d, c)):
                if keep == other:
                    continue
                candidate = list(gates)
                candidate[child_j] = (op, min(keep, other), max(keep, other))
                candidate[j] = (op, min(child, shift), max(child, shift))
                answers.append(candidate)
    return answers


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds', type=int, default=1200)
    parser.add_argument('--seed', type=int, default=12602)
    parser.add_argument('--repair-per-round', type=int, default=3)
    args = parser.parse_args()
    data = json.loads((search64.JOB / 'tight-circuit.json').read_text())
    search64.JOB = search64.JOB / 'search64-rotations'
    search64.JOB.mkdir(exist_ok=True)
    initial = [tuple(g) for g in data['gates']]
    output = data['output']
    search = search64.Search(args.seconds, args.seed)
    gates = initial
    seen = set()
    rounds = 0
    search.report('rotations_start')
    while time.monotonic() < search.deadline:
        for _ in range(20):
            variants = rotations(gates, output)
            if not variants:
                break
            gates = search.rng.choice(variants)
        key = tuple(gates)
        if key in seen:
            gates = initial
            continue
        seen.add(key)
        assert search64.valid(gates, output)
        assert search64.score(search64.evaluate(gates, output)[0]) == (0, 0, 0)
        rounds += 1
        old_near = len(search.near)
        if search.deletion_sweep(gates, output, f'rotation{rounds}'):
            return
        candidates = search.near[old_near:]
        search.rng.shuffle(candidates)
        candidates.sort(key=lambda row: sum(row[2]))
        for i, (candidate, out, errors) in enumerate(candidates[:args.repair_per_round]):
            if search.mutation_sweep(candidate, out, f'rotation{rounds}-repair{i}'):
                return
            if time.monotonic() >= search.deadline:
                break
        if rounds % 5 == 0:
            search.report('rotation_progress', rounds=rounds, near=len(search.near))
    search.report('rotations_finished', rounds=rounds, found=False)


if __name__ == '__main__':
    main()
