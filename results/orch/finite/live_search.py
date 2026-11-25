import ast
import json
import sys
import time
from collections import Counter
from pathlib import Path


FULL = (1 << 512) - 1
PAIRS = (1 << 768) - 1
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
         (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
INPUTS = [sum(1 << row for row in range(512) if (row >> j) & 1) for j in range(9)]
TARGET = sum(1 << row for row in range(512)
             if any((row >> a) & 1 and (row >> b) & 1 for a, b in EDGES))


def binop(op, a, b):
    if op == 0:
        return a & b
    if op == 1:
        return a | b
    if op == 2:
        return a & ~b
    return ~a & b


def source_data():
    source = Path('lean/PEqualNP/Outside/L_meta_5236.lean').read_text().splitlines()
    def extract(prefix):
        line = next(line for line in source if line.startswith(prefix))
        return ast.literal_eval(line.split(':=', 1)[1].strip().replace('#[', '['))
    columns = extract('def rootSCols ')
    samples = [(a & PAIRS, b & PAIRS) for a, b in extract('def rootSSamples ')]
    swaps = extract('def rootSAutos ')
    permutations = []
    for sequence in swaps:
        p = list(range(9))
        for step in reversed(sequence):
            a, b = step & 15, step >> 4
            p = [b if v == a else a if v == b else v for v in p]
        assert {tuple(sorted((p[a], p[b]))) for a, b in EDGES} == {
            tuple(sorted(edge)) for edge in EDGES}
        permutations.append(p)
    for bit in range(768):
        pos = sum(((a >> bit) & 1) << j for j, (a, b) in enumerate(samples))
        neg = sum(((b >> bit) & 1) << j for j, (a, b) in enumerate(samples))
        assert (TARGET >> pos) & 1 and not (TARGET >> neg) & 1
    domains = [sum(1 << row for row in range(512)
                   if row & z == 0 and row & o == o) for z, o, _, _, _ in columns]
    return columns, samples, swaps, permutations, domains


class Wire:
    __slots__ = ('value', 'pos', 'neg', 'autos', 'masked', 'index', 'constant')

    def __init__(self, value, pos, neg, autos, masked, index, domains):
        self.value, self.pos, self.neg = value, pos, neg
        self.autos, self.masked, self.index = autos, masked, index
        self.constant = tuple(v == 0 or v == d for v, d in zip(masked, domains))


class Search:
    def __init__(self, cap, seconds):
        self.columns, self.samples, self.swaps, self.perms, self.domains = source_data()
        self.cap, self.seconds, self.start = cap, seconds, time.monotonic()
        self.stats = Counter()
        self.memo, self.records = {}, []
        self.root = [Wire(v, *self.samples[j], tuple(INPUTS[p[j]] for p in self.perms),
                          tuple(v & d for d in self.domains), j, self.domains)
                     for j, v in enumerate(INPUTS)]
        self.pools = [frozenset([0] + [min(w.masked[i], d ^ w.masked[i]) for w in self.root])
                      for i, d in enumerate(self.domains)]
        self.order = sorted(range(len(self.columns)), key=lambda i: -self.columns[i][-1])

    def canonical(self, wires):
        return min(tuple(sorted(w.autos[p] for w in wires)) for p in range(len(self.perms)))

    def search(self, k, wires, prefix, pools, paid):
        self.stats['entered'] += 1
        if self.stats['entered'] % 100 == 0:
            elapsed = time.monotonic() - self.start
            print(json.dumps(dict(elapsed=round(elapsed, 2), states=len(self.records),
                                  depth=len(prefix), remaining=k, stats=dict(self.stats))), flush=True)
            if elapsed >= self.seconds:
                raise TimeoutError
        if any(w.value == TARGET for w in wires):
            return prefix, next(w.index for w in wires if w.value == TARGET)
        key = (k, self.canonical(wires))
        if key in self.memo:
            self.stats['memo'] += 1
            return None
        if k == 0 or len(wires) == 1:
            self.memo[key] = len(self.records)
            self.records.append(dict(k=k, prefix=prefix, live=[w.index for w in wires], rules=[]))
            return None
        counts = [sum(w.constant[i] for w in wires) for i in range(len(self.columns))]
        used_rules = set()
        for ia in range(len(wires)):
            a = wires[ia]
            for ib in range(ia + 1, len(wires)):
                b = wires[ib]
                rest = [w for j, w in enumerate(wires) if j not in (ia, ib)]
                rest_cov = 0
                for w in rest:
                    rest_cov |= w.pos ^ w.neg
                for op in range(4):
                    self.stats['operations'] += 1
                    value = binop(op, a.value, b.value)
                    if value in (0, FULL) or any(w.value == value for w in wires):
                        self.stats['trivial'] += 4
                        continue
                    zp, zn = binop(op, a.pos, b.pos), binop(op, a.neg, b.neg)
                    coverage = (zp ^ zn) | rest_cov
                    survivors = []
                    for ka, kb in ((False, False), (True, False), (False, True), (True, True)):
                        if len(rest) + 1 + ka + kb > k:
                            self.stats['mass'] += 1
                            continue
                        cov = coverage | ((a.pos ^ a.neg) if ka else 0) | ((b.pos ^ b.neg) if kb else 0)
                        if cov != PAIRS:
                            self.stats['coverage'] += 1
                            continue
                        survivors.append((ka, kb))
                    if not survivors:
                        continue
                    masked = tuple(binop(op, x, y) for x, y in zip(a.masked, b.masked))
                    canonical = tuple(min(v, d ^ v) for v, d in zip(masked, self.domains))
                    extras = tuple(v not in pool for v, pool in zip(canonical, pools))
                    constants = tuple(v == 0 for v in canonical)
                    for ka, kb in survivors:
                        cut = None
                        for i in self.order:
                            const = counts[i] - ((not ka) and a.constant[i]) - ((not kb) and b.constant[i]) + constants[i]
                            if k - 1 + paid[i].bit_count() + extras[i] < self.columns[i][-1] + const:
                                cut = i
                                break
                        if cut is not None:
                            self.stats['restriction'] += 1
                            used_rules.add((cut, paid[cut]))
                            continue
                        z = Wire(value, zp, zn, tuple(binop(op, x, y) for x, y in zip(a.autos, b.autos)),
                                 masked, 9 + len(prefix), self.domains)
                        child = [z] + rest + ([a] if ka else []) + ([b] if kb else [])
                        child_pools = [pool | {v} if extra else pool
                                       for pool, v, extra in zip(pools, canonical, extras)]
                        child_paid = [bits | (1 << len(prefix)) if extra else bits
                                      for bits, extra in zip(paid, extras)]
                        self.stats['expanded'] += 1
                        result = self.search(k - 1, child, prefix + [(op, a.index, b.index)],
                                             child_pools, child_paid)
                        if result is not None:
                            return result
        self.memo[key] = len(self.records)
        self.records.append(dict(k=k, prefix=prefix, live=[w.index for w in wires],
                                 rules=sorted(used_rules)))
        return None

    def run(self, output):
        verdict, result = 'UNKNOWN', None
        try:
            result = self.search(self.cap, self.root, [], self.pools, [0] * len(self.columns))
            verdict = 'SAT' if result is not None else 'UNSAT'
        except TimeoutError:
            pass
        report = dict(verdict=verdict, result=result, cap=self.cap,
                      elapsed=time.monotonic() - self.start, stats=dict(self.stats),
                      nodes=len(self.records), columns=len(self.columns), records=self.records)
        Path(output).write_text(json.dumps(report))
        print(json.dumps({k: v for k, v in report.items() if k != 'records'}), flush=True)


if __name__ == '__main__':
    Search(int(sys.argv[1]), float(sys.argv[2])).run(sys.argv[3])
