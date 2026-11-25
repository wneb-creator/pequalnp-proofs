import argparse
import itertools
import json
import random
import subprocess
import time
from pathlib import Path


N = 13
NINPUT = 26
LINES = [{l, (l + 1) % N, (l + 3) % N, (l + 9) % N} for l in range(N)]
EDGES = [(p, N + l) for l, points in enumerate(LINES) for p in sorted(points)]
POSITIVE = [(1 << p) | (1 << l) for p, l in EDGES]
assert all(len(points) == 4 for points in LINES)
assert all(sum(p in points and p2 in points for points in LINES) == 1
           for p in range(N) for p2 in range(p))


def maximal_independent():
    result = []
    closures = []
    for a in range(1 << N):
        b = sum(1 << l for l, points in enumerate(LINES)
                if not any((a >> p) & 1 for p in points))
        aa = sum(1 << p for p in range(N)
                 if not any((b >> l) & 1 and p in points for l, points in enumerate(LINES)))
        if aa == a:
            result.append(a | (b << N))
        closures.append((a | (b << N), aa | (b << N)))
    target_set = set(result)
    for smaller, larger in closures:
        assert smaller & ~larger == 0 and larger in target_set
    assert len(result) == 704
    return result


NEGATIVE = maximal_independent()


def star_circuit(order):
    gates, stars = [], []
    for l in order:
        a, b, c, d = sorted(LINES[l])
        j = len(gates)
        gates += [(False, a, b), (False, NINPUT + j, c),
                  (False, NINPUT + j + 1, d), (True, NINPUT + j + 2, N + l)]
        stars.append(NINPUT + j + 3)
    output = stars[0]
    for star in stars[1:]:
        gates.append((False, output, star))
        output = NINPUT + len(gates) - 1
    assert len(gates) == 64
    return gates


def evaluate(circuit, patterns):
    words = [sum(1 << t for t, mask in enumerate(patterns) if (mask >> i) & 1)
             for i in range(NINPUT)]
    for op, a, b in circuit:
        words.append(words[a] & words[b] if op else words[a] | words[b])
    return words[-1]


class Encoding:
    def __init__(self, seed, free, patterns):
        self.seed, self.free, self.patterns = seed, set(free), patterns
        self.count = 0
        self.clauses = []
        self.ops, self.lhs, self.rhs = {}, {}, {}
        self.lv, self.rv = {}, {}
        self.values = [[self.var() for _ in patterns] for _ in seed]
        for i in free:
            self.ops[i] = self.var()
            self.lhs[i] = [self.var() for _ in range(NINPUT + i)]
            self.rhs[i] = [self.var() for _ in range(NINPUT + i)]
            self.lv[i] = [self.var() for _ in patterns]
            self.rv[i] = [self.var() for _ in patterns]
            self.one(self.lhs[i])
            self.one(self.rhs[i])
            for a in range(NINPUT + i):
                for b in range(a):
                    self.add(-self.lhs[i][a], -self.rhs[i][b])
        self.truth = self.var()
        self.add(self.truth)
        for i, (op, a, b) in enumerate(seed):
            for t, mask in enumerate(patterns):
                v = self.values[i][t]
                if i not in self.free:
                    l, r = self.wire(a, t), self.wire(b, t)
                    if op:
                        self.add(-v, l); self.add(-v, r); self.add(v, -l, -r)
                    else:
                        self.add(v, -l); self.add(v, -r); self.add(-v, l, r)
                    continue
                l, r, o = self.lv[i][t], self.rv[i][t], self.ops[i]
                for selections, bit in ((self.lhs[i], l), (self.rhs[i], r)):
                    for j, sel in enumerate(selections):
                        w = self.wire(j, t)
                        self.add(-sel, -bit, w); self.add(-sel, bit, -w)
                self.add(-o, -v, l); self.add(-o, -v, r); self.add(-o, v, -l, -r)
                self.add(o, v, -l); self.add(o, v, -r); self.add(o, -v, l, r)
        for t in range(len(patterns)):
            self.add(self.values[-1][t] if t < len(POSITIVE) else -self.values[-1][t])

    def var(self):
        self.count += 1
        return self.count

    def add(self, *lits):
        self.clauses.append(lits)

    def one(self, vs):
        self.add(*vs)
        for i, v in enumerate(vs):
            for w in vs[:i]:
                self.add(-v, -w)

    def wire(self, j, t):
        if j < NINPUT:
            return self.truth if (self.patterns[t] >> j) & 1 else -self.truth
        return self.values[j - NINPUT][t]

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.count} {len(self.clauses)}\n')
            for c in self.clauses:
                f.write(' '.join(map(str, c)) + ' 0\n')

    def decode(self, text):
        assignment = {abs(v): v > 0 for line in text.splitlines() if line.startswith('v ')
                      for v in map(int, line[2:].split()) if v}
        result = list(self.seed)
        for i in self.free:
            left = [j for j, v in enumerate(self.lhs[i]) if assignment[v]]
            right = [j for j, v in enumerate(self.rhs[i]) if assignment[v]]
            assert len(left) == len(right) == 1
            result[i] = (assignment[self.ops[i]], left[0], right[0])
        return result

    def known_assignment(self):
        assignment = {self.truth: True}
        for i in self.free:
            op, a, b = self.seed[i]
            a, b = sorted((a, b))
            assignment[self.ops[i]] = op
            for j, v in enumerate(self.lhs[i]): assignment[v] = j == a
            for j, v in enumerate(self.rhs[i]): assignment[v] = j == b
        for t, mask in enumerate(self.patterns):
            ws = [bool(mask >> j & 1) for j in range(NINPUT)]
            for i, (op, a, b) in enumerate(self.seed):
                if i in self.free:
                    a, b = sorted((a, b))
                    assignment[self.lv[i][t]], assignment[self.rv[i][t]] = ws[a], ws[b]
                v = ws[a] and ws[b] if op else ws[a] or ws[b]
                ws.append(v)
                assignment[self.values[i][t]] = v
        return assignment

    def verify_known(self):
        assignment = self.known_assignment()
        for index, c in enumerate(self.clauses):
            assert any(assignment[abs(v)] == (v > 0) for v in c), (index, c)

    def write_phases(self, path):
        assignment = self.known_assignment()
        path.write_text(' '.join(str(v if b else -v) for v,b in sorted(assignment.items())) + '\n')

    def least_singleton(self):
        lookup={mask:t for t,mask in enumerate(self.patterns)}
        for i in range(len(self.seed)):
            for vertex in range(NINPUT):
                t=lookup[1<<vertex]
                away=[self.values[i][k] for k,(a,b) in enumerate(EDGES) if vertex not in (a,b)]
                self.add(-self.values[i][t],*away)

    def least_or_strict(self):
        for i, (op, a, b) in enumerate(self.seed):
            self.add(*self.values[i][:len(POSITIVE)])
            if i not in self.free and op:
                continue
            witnesses = ([], [])
            for t in range(len(POSITIVE)):
                left = self.lv[i][t] if i in self.free else self.wire(a,t)
                right = self.rv[i][t] if i in self.free else self.wire(b,t)
                for side, (x,y) in enumerate(((left,right),(right,left))):
                    v = self.var(); witnesses[side].append(v)
                    self.add(-v,x); self.add(-v,-y); self.add(v,-x,y)
            for side in witnesses:
                self.add(*([self.ops[i]] if i in self.free else []), *side)
        for i in range(len(self.seed)-1):
            wire=NINPUT+i
            if any(j not in self.free and wire in pair[1:]
                   for j,pair in enumerate(self.seed) if j>i):
                continue
            uses=[]
            for j in self.free:
                if j>i:
                    uses += [self.lhs[j][wire],self.rhs[j][wire]]
            self.add(*uses)


def neighborhood(rng, trial):
    k = 4 + trial % 3
    candidates = []
    for chosen in itertools.combinations(range(N), k):
        triple = sum(sum(p in LINES[l] for l in chosen) *
                     (sum(p in LINES[l] for l in chosen) - 1) *
                     (sum(p in LINES[l] for l in chosen) - 2) // 6 for p in range(N))
        candidates.append((triple, chosen))
    candidates.sort()
    score, selected = rng.choice(candidates[:max(1, len(candidates) // 4)])
    outside = [l for l in range(N) if l not in selected]
    rng.shuffle(outside)
    selected = list(selected)
    rng.shuffle(selected)
    order = outside + selected
    seed = star_circuit(order)
    block = rng.randrange(len(outside), N)
    remove = 4 * block + rng.randrange(3)
    replacement = seed[remove][1] if remove % 4 else rng.choice(seed[remove][1:])
    shift = lambda w: (replacement if w == NINPUT + remove else w) - (w > NINPUT + remove)
    new_seed = [(op, shift(a), shift(b)) for i, (op, a, b) in enumerate(seed) if i != remove]
    old_free = set(range(4 * len(outside), 52)) | set(range(52 + len(outside) - 2, 64))
    free = sorted(i - (i > remove) for i in old_free if i != remove)
    assert len(free) == 5 * k and len(new_seed) == 63
    return new_seed, free, dict(selected_lines=selected, line_order=order,
                                triple_concurrences=score, removed_gate=remove,
                                replacement_wire=replacement)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--seconds', type=int, default=600)
    ap.add_argument('--seed', type=int, default=76)
    ap.add_argument('--calibrate', action='store_true')
    ap.add_argument('--solver-calibrate', action='store_true')
    ap.add_argument('--initial-negatives',type=int,default=0)
    ap.add_argument('--query-seconds',type=int,default=30)
    args = ap.parse_args()
    root = Path(args.out); root.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    all_patterns = POSITIVE + NEGATIVE
    if args.calibrate:
        seed = star_circuit(list(range(N)))
        free = list(range(28, 52)) + list(range(58, 64))
        assert evaluate(seed, all_patterns) == (1 << len(POSITIVE)) - 1
        e = Encoding(seed, free, all_patterns)
        e.verify_known()
        report = dict(gates=64, positive=len(POSITIVE), negative=len(NEGATIVE),
                      closure_cases=1 << N, variables=e.count, clauses=len(e.clauses),
                      free_gates=free, circuit=seed)
        (root / 'calibration.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report), flush=True)
        return
    if args.solver_calibrate:
        seed = star_circuit(list(range(N)))
        free = list(range(36,52)) + list(range(60,64))
        negatives = list(dict.fromkeys([NEGATIVE[0],NEGATIVE[-1]] + [1<<v for v in range(NINPUT)] + rng.sample(NEGATIVE,40)))
        e = Encoding(seed,free,POSITIVE+negatives)
        e.least_or_strict()
        e.least_singleton()
        cnf = root/'control.cnf'; e.write(cnf)
        phases = root/'control.phases'; e.write_phases(phases)
        begin=time.monotonic()
        with (root/'control.log').open('w') as output:
            completed = subprocess.run([args.solver,str(cnf),str(phases),'60','1000000'],
                                       stdout=output,stderr=subprocess.STDOUT)
        report=dict(status=completed.returncode,seconds=time.monotonic()-begin,
                    gates=64,free_gates=free,variables=e.count,clauses=len(e.clauses))
        if completed.returncode==10:
            circuit=e.decode((root/'control.log').read_text())
            actual=evaluate(circuit,all_patterns)
            report['all_boundary_errors']=(actual^((1<<len(POSITIVE))-1)).bit_count()
            report['circuit']=circuit
        (root/'control.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report),flush=True)
        return
    start = time.monotonic()
    trial = 0
    while time.monotonic() - start < args.seconds:
        seed, free, details = neighborhood(rng, trial)
        negatives = list(dict.fromkeys([NEGATIVE[0], NEGATIVE[-1]] + [1<<v for v in range(NINPUT)] + rng.sample(NEGATIVE, args.initial_negatives)))
        for round_index in range(128):
            if time.monotonic() - start >= args.seconds:
                break
            patterns = POSITIVE + negatives
            e = Encoding(seed, free, patterns)
            e.least_or_strict()
            e.least_singleton()
            phases = root/'current.phases'; e.write_phases(phases)
            cnf = root / 'current.cnf'; e.write(cnf)
            record = dict(trial=trial, round=round_index, free_gates=free, seed_circuit=seed,
                          negative_patterns=negatives, variables=e.count, clauses=len(e.clauses), **details)
            prefix = root / f'trial-{trial:04d}-round-{round_index}'
            prefix.with_suffix('.json').write_text(json.dumps(record) + '\n')
            limit = max(1, min(args.query_seconds, int(args.seconds - (time.monotonic() - start))))
            with prefix.with_suffix('.log').open('w') as output:
                completed = subprocess.run([args.solver, str(cnf), str(phases), str(limit), '500000'],
                                           stdout=output, stderr=subprocess.STDOUT)
            record = {k:v for k,v in record.items() if k not in ('seed_circuit','negative_patterns')}
            record.update(status=completed.returncode, seconds=time.monotonic()-start, solver_limit=limit)
            if completed.returncode != 10:
                print(json.dumps(record), flush=True)
                break
            circuit = e.decode(prefix.with_suffix('.log').read_text())
            actual = evaluate(circuit, all_patterns)
            positive_mask = (1 << len(POSITIVE)) - 1
            assert actual & positive_mask == positive_mask
            bad = [mask for i,mask in enumerate(NEGATIVE) if actual >> (len(POSITIVE)+i) & 1]
            record['false_positive_boundaries'] = len(bad)
            print(json.dumps(record), flush=True)
            if not bad:
                witness = dict(circuit=circuit, edges=EDGES, n=NINPUT, output=NINPUT+len(circuit)-1,
                               all_boundary_patterns=len(all_patterns), seed=args.seed)
                (root / 'witness.json').write_text(json.dumps(witness,indent=2)+'\n')
                print('FOUND COUNTEREXAMPLE CANDIDATE', flush=True)
                return
            bad_mask=rng.choice(bad)
            order=list(range(NINPUT));rng.shuffle(order)
            for vertex in order:
                if bad_mask>>vertex&1:
                    smaller=bad_mask & ~(1<<vertex)
                    if evaluate(circuit,[smaller])&1:
                        bad_mask=smaller
            assert not any(bad_mask>>a&1 and bad_mask>>b&1 for a,b in EDGES)
            assert bad_mask not in negatives
            print(json.dumps(dict(event='minimal_false_cut',trial=trial,round=round_index,
                                  vertices=bad_mask.bit_count(),mask=bad_mask)),flush=True)
            negatives.append(bad_mask)
            seed=circuit
        trial += 1
    print(json.dumps(dict(event='finished', trials=trial, seconds=time.monotonic()-start)), flush=True)


if __name__ == '__main__':
    main()
