#!/usr/bin/env python3
"""Exact-test heuristic search around the 65-gate order-three-plane circuit."""

import argparse
import hashlib
import json
import random
import time
from datetime import datetime, timezone
from pathlib import Path

N = 26
JOB = Path('/tmp/oec/pequalnp-pilot-60')
FULL13 = (1 << 13) - 1
EDGES = [(p, l) for l in range(13) for p in range(13)
         if (p - l) % 13 in (0, 1, 3, 9)]
POINT_NEIGHBORS = [sum(1 << l for q, l in EDGES if q == p) for p in range(13)]
LINE_NEIGHBORS = [sum(1 << p for p, q in EDGES if q == l) for l in range(13)]


def independent_rows():
    maximal = set()
    canonical = []
    for points in range(1 << 13):
        neighbors = 0
        for p in range(13):
            if points >> p & 1:
                neighbors |= POINT_NEIGHBORS[p]
        lines = FULL13 ^ neighbors
        canonical.append(points | (lines << 13))
        forbidden_points = 0
        for l in range(13):
            if lines >> l & 1:
                forbidden_points |= LINE_NEIGHBORS[l]
        closed_points = FULL13 ^ forbidden_points
        maximal.add(closed_points | (lines << 13))
    return sorted(maximal), canonical


NEGATIVE, CANONICAL_NEGATIVE = independent_rows()
ROWS = [(1 << p) | (1 << (13 + l)) for p, l in EDGES] + NEGATIVE + [1, 1 << 13]
BASE_POINT = len(ROWS) - 2
BASE_LINE = len(ROWS) - 1
TARGET = (1 << len(EDGES)) - 1
INPUTS = [(sum(1 << k for k, x in enumerate(ROWS) if x >> i & 1),
           int(i == 13), int(i == 0)) for i in range(N)]


def gate_value(op, a, b):
    ta, da, ea = a
    tb, db, eb = b
    if op == 'or':
        return ta | tb, da | db, ea | eb
    return (ta & tb,
            (((ta >> BASE_POINT) & 1) & db) | (da & ((tb >> BASE_POINT) & 1)),
            (((ta >> BASE_LINE) & 1) & eb) | (ea & ((tb >> BASE_LINE) & 1)))


def evaluate(gates, output, prefix=None, start=0):
    values = list(INPUTS if prefix is None else prefix[:N + start])
    for op, a, b in gates[start:]:
        values.append(gate_value(op, values[a], values[b]))
    return values[output], values


def score(signature):
    truth, dl, dp = signature
    delta = truth ^ TARGET
    return (delta & TARGET).bit_count(), (delta & ~TARGET).bit_count(), dl + dp


def valid(gates, output):
    return output < N + len(gates) and all(
        op in ('and', 'or') and 0 <= a < N + j and 0 <= b < N + j and a != b
        for j, (op, a, b) in enumerate(gates))


def normalize(gates, output, alias=None):
    remap = list(range(N))
    temporary = []
    memo = {}
    for j, (op, a, b) in enumerate(gates):
        if alias is not None and j == alias[0]:
            remap.append(remap[alias[1]])
            continue
        a, b = sorted((remap[a], remap[b]))
        if a == b:
            remap.append(a)
            continue
        key = (op, a, b)
        if key in memo:
            remap.append(memo[key])
            continue
        remap.append(N + len(temporary))
        memo[key] = N + len(temporary)
        temporary.append(key)
    output = remap[output]
    used = set()

    def visit(w):
        if w < N or w in used:
            return
        used.add(w)
        _, a, b = temporary[w - N]
        visit(a)
        visit(b)

    visit(output)
    final = []
    remap = list(range(N))
    for j, (op, a, b) in enumerate(temporary):
        if N + j in used:
            remap.append(N + len(final))
            final.append((op, remap[a], remap[b]))
        else:
            remap.append(-1)
    return final, remap[output]


def independent_verify(gates, output):
    for row in CANONICAL_NEGATIVE:
        wires = [bool(row >> i & 1) for i in range(N)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == 'and' else wires[a] or wires[b])
        if wires[output]:
            return False
    for p, l in EDGES:
        row = (1 << p) | (1 << (13 + l))
        wires = [bool(row >> i & 1) for i in range(N)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == 'and' else wires[a] or wires[b])
        if not wires[output]:
            return False
    return score(evaluate(gates, output)[0]) == (0, 0, 0)


class Search:
    def __init__(self, seconds, seed):
        self.start = time.monotonic()
        self.deadline = self.start + seconds
        self.rng = random.Random(seed)
        self.tested = 0
        self.neutrals = 0
        self.report_at = self.start
        self.best = None
        self.best_data = None
        self.seen = set()
        self.queue = []
        self.near = []
        self.near_seen = set()
        self.found = False

    def report(self, phase, **extra):
        row = dict(utc=datetime.now(timezone.utc).isoformat(), phase=phase,
                   elapsed=round(time.monotonic() - self.start, 3), tested=self.tested,
                   neutral=self.neutrals, best=self.best, **extra)
        print(json.dumps(row), flush=True)
        (JOB / 'search64-progress.json').write_text(json.dumps(row, indent=2))
        self.report_at = time.monotonic() + 30

    def consider(self, gates, output, label, signature=None):
        self.tested += 1
        if signature is None:
            signature = evaluate(gates, output)[0]
        errors = score(signature)
        cost = errors[0] + errors[1] + 20 * errors[2]
        key = (cost, sum(errors), len(gates))
        if len(gates) <= 64 and errors[2] == 0 and errors[0] + errors[1] <= 2:
            near_key = (tuple(tuple(g) for g in gates), output)
            if near_key not in self.near_seen:
                self.near_seen.add(near_key)
                self.near.append((gates, output, errors))
        if len(gates) <= 64 and (self.best is None or key < self.best):
            self.best = key
            self.best_data = dict(gates=gates, output=output, score=errors, label=label)
            (JOB / 'search64-best.json').write_text(json.dumps(self.best_data, indent=2))
            self.report('best', label=label, errors=errors, gates=len(gates))
        if errors == (0, 0, 0):
            gates, output = normalize(gates, output)
            if not valid(gates, output) or score(evaluate(gates, output)[0]) != (0, 0, 0):
                return False
            if len(gates) <= 64:
                assert independent_verify(gates, output)
                witness = dict(gates=gates, output=output, label=label,
                               verification='all 52 edges and all 8192 canonical negative rows',
                               derivatives=[0, 0], seconds=time.monotonic() - self.start)
                (JOB / 'search64-WITNESS.json').write_text(json.dumps(witness, indent=2))
                self.found = True
                self.report('WITNESS', gates=len(gates), label=label)
                return True
            key = (tuple(gates), output)
            if key not in self.seen:
                self.seen.add(key)
                self.neutrals += 1
                if len(self.queue) < 2000:
                    self.queue.append((gates, output))
        return False

    def deletion_sweep(self, gates, output, label):
        for j in range(len(gates)):
            for replacement in range(N + j):
                new, out = normalize(gates, output, (j, replacement))
                if self.consider(new, out, f'{label}:delete:{j}:{replacement}'):
                    return True
            if time.monotonic() >= self.deadline:
                return False
        self.report('deletion_done', label=label)
        return False

    def mutation_sweep(self, gates, output, label, exhaustive=True):
        _, prefix = evaluate(gates, output)
        indices = list(range(len(gates)))
        self.rng.shuffle(indices)
        for j in indices:
            options = [(op, a, b) for op in ('and', 'or')
                       for a in range(N + j) for b in range(a + 1, N + j)]
            self.rng.shuffle(options)
            if not exhaustive:
                options = options[:min(150, len(options))]
            for replacement in options:
                if replacement == gates[j]:
                    continue
                new = gates[:j] + [replacement] + gates[j + 1:]
                signature, _ = evaluate(new, output, prefix, j)
                if self.consider(new, output, f'{label}:mutate:{j}:{replacement}', signature):
                    return True
            now = time.monotonic()
            if now >= self.report_at:
                self.report('mutation', label=label, gate=j, queue=len(self.queue))
            if now >= self.deadline:
                return False
        self.report('mutation_done', label=label, queue=len(self.queue))
        return False

    def run(self, gates, output):
        assert valid(gates, output)
        assert score(evaluate(gates, output)[0]) == (0, 0, 0)
        self.report('start', initial_gates=len(gates), maximal_negative=len(NEGATIVE),
                    rows=len(ROWS), canonical_negative=len(CANONICAL_NEGATIVE))
        self.consider(gates, output, 'initial')
        if self.deletion_sweep(gates, output, 'initial'):
            return
        if self.mutation_sweep(gates, output, 'initial'):
            return
        self.report('repair_start', near_candidates=len(self.near))
        initial_near = list(self.near)
        initial_near.sort(key=lambda row: sum(row[2]))
        for k, (candidate, out, errors) in enumerate(initial_near):
            if self.mutation_sweep(candidate, out, f'repair{k}', exhaustive=True):
                return
            if time.monotonic() >= self.deadline:
                break
        steps = 0
        while self.queue and time.monotonic() < self.deadline:
            i = self.rng.randrange(len(self.queue))
            candidate, out = self.queue.pop(i)
            steps += 1
            if self.deletion_sweep(candidate, out, f'neutral{steps}'):
                return
            if self.mutation_sweep(candidate, out, f'neutral{steps}', exhaustive=False):
                return
        self.report('finished', neutral_states_examined=steps, queue=len(self.queue),
                    found=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds', type=int, default=900)
    parser.add_argument('--seed', type=int, default=2602)
    parser.add_argument('--initial', type=Path, default=JOB / 'tight-circuit.json')
    args = parser.parse_args()
    data = json.loads(args.initial.read_text())
    gates = [tuple(g) for g in data['gates']]
    Search(args.seconds, args.seed).run(gates, data['output'])
    print('program_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)


if __name__ == '__main__':
    main()
