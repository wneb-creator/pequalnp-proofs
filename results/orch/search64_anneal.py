#!/usr/bin/env python3
"""Unrestricted local stochastic search on proper 64-gate AND/OR DAGs."""
import argparse
import importlib.util
import json
import math
import random
import time
from datetime import datetime, timezone
from pathlib import Path

spec = importlib.util.spec_from_file_location('search64', Path(__file__).with_name('search64.py'))
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def fitness(signature):
    errors = s.score(signature)
    return errors[0] + errors[1] + 4 * errors[2], errors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--seed', type=int, default=22602)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    output_dir = s.JOB / 'search64-anneal'
    output_dir.mkdir(exist_ok=True)
    data = json.loads((s.JOB / 'tight-circuit.json').read_text())
    initial = [tuple(g) for g in data['gates']]
    seeds = []
    seen = set()
    for j in range(len(initial)):
        for replacement in range(26 + j):
            gates, output = s.normalize(initial, data['output'], (j, replacement))
            if len(gates) != 64:
                continue
            signature, _ = s.evaluate(gates, output)
            cost, errors = fitness(signature)
            key = tuple(gates), output
            if cost <= 2 and key not in seen:
                seen.add(key)
                seeds.append((gates, output))
    assert seeds
    start = time.monotonic()
    deadline = start + args.seconds
    last_report = 0
    iteration = 0
    accepted = 0
    restart = 0
    best_cost = float('inf')
    best = None

    def report(phase, cost, errors):
        row = dict(utc=datetime.now(timezone.utc).isoformat(), phase=phase,
                   elapsed=round(time.monotonic() - start, 3), iterations=iteration,
                   accepted=accepted, restarts=restart, current_cost=cost,
                   current_errors=errors, best=best_cost, seeds=len(seeds))
        print(json.dumps(row), flush=True)
        (output_dir / 'progress.json').write_text(json.dumps(row, indent=2))

    while time.monotonic() < deadline:
        gates, output = rng.choice(seeds)
        gates = list(gates)
        signature, values = s.evaluate(gates, output)
        cost, errors = fitness(signature)
        restart += 1
        for local in range(30000):
            iteration += 1
            j = rng.randrange(64)
            op, a, b = gates[j]
            kind = rng.randrange(100)
            if kind < 45:
                if rng.randrange(2):
                    a = rng.randrange(26 + j)
                else:
                    b = rng.randrange(26 + j)
            elif kind < 60:
                op = 'and' if op == 'or' else 'or'
            else:
                op = rng.choice(('and', 'or'))
                a = rng.randrange(26 + j)
                b = rng.randrange(26 + j)
            if a == b:
                continue
            replacement = (op, min(a, b), max(a, b))
            if replacement == gates[j]:
                continue
            candidate = gates[:j] + [replacement] + gates[j + 1:]
            new_signature, new_values = s.evaluate(candidate, output, values, j)
            new_cost, new_errors = fitness(new_signature)
            temperature = 0.15 + 3.5 * (1 - local / 30000)
            if new_cost <= cost or rng.random() < math.exp((cost - new_cost) / temperature):
                gates, values, cost, errors = candidate, new_values, new_cost, new_errors
                accepted += 1
            if new_cost < best_cost:
                best_cost = new_cost
                best = dict(gates=candidate, output=output, errors=new_errors, cost=new_cost)
                (output_dir / 'best.json').write_text(json.dumps(best, indent=2))
                report('best', new_cost, new_errors)
            if new_errors == (0, 0, 0):
                assert s.valid(candidate, output)
                assert s.independent_verify(candidate, output)
                (output_dir / 'WITNESS.json').write_text(json.dumps(
                    dict(gates=candidate, output=output, derivatives=[0, 0],
                         verification='all 52 edges and all 8192 canonical negative rows'), indent=2))
                report('WITNESS', new_cost, new_errors)
                return
            now = time.monotonic()
            if now > last_report + 30:
                report('running', cost, errors)
                last_report = now
            if now >= deadline:
                break
    report('finished', cost, errors)


if __name__ == '__main__':
    main()
