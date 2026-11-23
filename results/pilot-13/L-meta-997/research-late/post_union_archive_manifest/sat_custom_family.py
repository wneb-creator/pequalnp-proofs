import argparse
import functools
import itertools
import json
import operator
import subprocess
import time
from pathlib import Path


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def vars(self, count):
        out = list(range(self.n + 1, self.n + count + 1))
        self.n += count
        return out

    def one(self, xs):
        self.clauses.append(xs)
        if len(xs) < 2:
            return
        ps = self.vars(len(xs)-1)
        self.clauses.append([-xs[0], ps[0]])
        for i in range(1, len(xs)-1):
            self.clauses.extend([[-xs[i], ps[i]], [-ps[i-1], ps[i]],
                                 [-xs[i], -ps[i-1]]])
        self.clauses.append([-xs[-1], -ps[-1]])

    def imply_equal(self, selector, x, y):
        if isinstance(y, bool):
            self.clauses.append([-selector, x if y else -x])
        else:
            self.clauses.extend([[-selector, -x, y], [-selector, x, -y]])

    def gate(self, x, y, out, is_or):
        # is_or=0: out=x AND y; is_or=1: out=x OR y.
        self.clauses.extend([[is_or, -out, x], [is_or, -out, y],
                             [is_or, out, -x, -y],
                             [-is_or, out, -x], [-is_or, out, -y],
                             [-is_or, -out, x, y]])

    def save(self, path):
        with path.open('w') as f:
            f.write('p cnf %d %d\n' % (self.n, len(self.clauses)))
            for c in self.clauses:
                f.write(' '.join(map(str, c)) + ' 0\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--width', type=int, default=4)
    ap.add_argument('--prefix', choices=['factors', 'all'], default='factors')
    ap.add_argument('--pair-order', choices=['yp', 'pq', 'yq'], default='yp')
    ap.add_argument('--tail', type=int)
    ap.add_argument('--seconds', type=int, default=240)
    ap.add_argument('--rounds', type=int, default=5)
    ap.add_argument('--control', action='store_true')
    ap.add_argument('--all-low-weight', action='store_true')
    ap.add_argument('--family-json', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--solver', type=Path, default=Path('/tmp/oec/pequalnp-pilot-13/lean_setup/lean-4.36.0-linux/bin/cadical'))
    args = ap.parse_args()
    w = args.width
    n = 2*w + 4
    ys = {0, 1, 2}
    ps, qs = list(range(3, w+3)), list(range(w+3, 2*w+3))
    common = n-1
    family = [{i, ps[j], qs[(j+i) % w]} for i in range(3) for j in range(w)]
    family += [set(ps + [common]), set(qs + [common])]
    assert all(len(a & b) <= 1 for i, a in enumerate(family) for b in family[i+1:])
    choice = next(js for js in itertools.product(range(w), repeat=3)
                  if len(set(js)) == 3 and len({(js[i]+i) % w for i in range(3)}) == 3)
    factors = [i*w + choice[i] for i in range(3)]
    meeting_count = 3*w
    custom = None
    if args.family_json:
        custom = json.loads(args.family_json.read_text())
        n = custom['n']
        ys = set(custom['y'])
        family = [set(s) for s in custom['family']]
        factors = custom['factors']
        meeting_count = custom['meeting_count']
        assert len(ys)==3 and len(factors)==3
        assert all(len(a & b)<=1 for i,a in enumerate(family) for b in family[i+1:])
        assert all(not family[a] & family[b] for i,a in enumerate(factors) for b in factors[i+1:])
    prefix = []
    output_fixed = {}

    def add(op, a, b=None):
        prefix.append((op, a, b))
        return n+len(prefix)-1

    prefix_indices = factors if args.prefix == 'factors' else list(range(meeting_count))
    for j in prefix_indices:
        y = j // w
        p, q = ps[j % w], qs[(j % w+y) % w]
        if custom:
            anchors = family[j] & ys
            outside = sorted(family[j] - ys)
            assert len(anchors)==1 and len(outside)==2
            y = next(iter(anchors))
            p, q = outside
        if args.pair_order == 'yp':
            out = add('or', add('or', y, p), q)
        elif args.pair_order == 'yq':
            out = add('or', add('or', y, q), p)
        else:
            out = add('or', add('or', p, q), y)
        output_fixed[j] = out
    h = add('and', output_fixed[factors[0]], output_fixed[factors[1]])
    h = add('and', h, output_fixed[factors[2]])
    z = add('not', h)
    ni = n+len(prefix)
    need = [j for j in range(len(family)) if j not in output_fixed]
    lhs = sum(len(s) if not s & ys else min(3, len(s)) for s in family)
    min_refunds = sum(1 for s in family if not s & ys and len(s)>=2)
    max_gates = lhs - len(family) - min_refunds - 1
    if args.tail is not None:
        tail_size = args.tail
    elif args.control:
        tail_size = sum(len(family[j])-1 for j in need)
    else:
        tail_size = max_gates-len(prefix)
    assert tail_size > 0
    full_universe = (1 << (1 << n))-1
    initial = []
    for p in range(n):
        block = 1 << p
        initial.append((full_universe // ((1 << (2*block))-1))*(((1 << block)-1) << block))
    for op, a, b in prefix:
        initial.append(full_universe ^ initial[a] if op == 'not' else
                       initial[a] | initial[b] if op == 'or' else initial[a] & initial[b])
    target = [functools.reduce(operator.or_, (initial[p] for p in s), 0) for s in family]
    ym = sum(1 << p for p in ys)
    assert not (initial[z] >> ym) & 1
    assert all((initial[z] >> sum(1 << p for p in s)) & 1
               for r in range(3) for s in itertools.combinations(range(n), r))
    samples = {0, ym, (1 << n)-1} | {1 << p for p in range(n)} | {ym | (1 << p) for p in range(n)}
    samples |= {(1 << n)-1-sum(1 << p for p in family[j]) for j in need}
    samples |= {sum(1 << p for p in c) for c in itertools.product(*(sorted(family[j]) for j in factors))}
    if args.all_low_weight:
        samples |= {sum(1 << p for p in c) for r in range(3) for c in itertools.combinations(range(n),r)}
    result = {'n':n, 'width':w, 'prefix_kind':args.prefix, 'pair_order':args.pair_order,
              'prefix':prefix, 'tail_size':tail_size, 'total_gates':len(prefix)+tail_size,
              'family':[sorted(s) for s in family], 'y':sorted(ys), 'factors':factors,
              'lhs':lhs, 'max_violation_gates_with_mandatory_refunds':max_gates,
              'mandatory_refunds':min_refunds,
              'control':args.control, 'rounds':[]}
    result['all_low_weight']=args.all_low_weight
    print(json.dumps(result), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    for iteration in range(args.rounds):
        cnf = CNF()
        sample_list = sorted(samples)
        rows = len(sample_list)
        left, right, op, av, bv, value = [], [], [], [], [], []
        for g in range(tail_size):
            left.append(cnf.vars(ni+g))
            right.append(cnf.vars(ni+g))
            op.append(cnf.vars(1)[0])
            av.append(cnf.vars(rows))
            bv.append(cnf.vars(rows))
            value.append(cnf.vars(rows))
        output = [cnf.vars(tail_size) for _ in need]
        for g in range(tail_size):
            cnf.one(left[g])
            cnf.one(right[g])
            # Commutativity; no gate repetition/copy is ruled out.
            for a in range(ni+g):
                for b in range(a):
                    cnf.clauses.append([-left[g][a], -right[g][b]])
            for row, sample in enumerate(sample_list):
                for sels, picked in [(left[g], av[g][row]), (right[g], bv[g][row])]:
                    for wire, sel in enumerate(sels):
                        src = bool((initial[wire] >> sample) & 1) if wire < ni else value[wire-ni][row]
                        cnf.imply_equal(sel, picked, src)
                cnf.gate(av[g][row], bv[g][row], value[g][row], op[g])
        for j, sels in zip(need, output):
            cnf.one(sels)
            for g, sel in enumerate(sels):
                for row, sample in enumerate(sample_list):
                    cnf.imply_equal(sel, value[g][row], bool((target[j] >> sample) & 1))
        # Every tail gate is used by a later gate or an output. Any circuit with
        # at most the budget can be padded with output copies to satisfy this.
        for g in range(tail_size):
            uses = [sels[g] for sels in output]
            uses += [left[k][ni+g] for k in range(g+1,tail_size)]
            uses += [right[k][ni+g] for k in range(g+1,tail_size)]
            cnf.clauses.append(uses)
        stem = args.output.with_suffix('')
        cnf_path = Path(str(stem)+'.round%d.cnf' % iteration)
        log_path = Path(str(stem)+'.round%d.solver.log' % iteration)
        witness_path = Path(str(stem)+'.round%d.witness' % iteration)
        cnf.save(cnf_path)
        rd = {'iteration':iteration, 'samples':rows, 'variables':cnf.n,
              'clauses':len(cnf.clauses), 'cnf_bytes':cnf_path.stat().st_size}
        print(json.dumps(rd), flush=True)
        solve_start = time.monotonic()
        with log_path.open('w') as log:
            cp = subprocess.run([str(args.solver), '-t', str(args.seconds), '-w', str(witness_path),
                                 str(cnf_path)], stdout=log, stderr=subprocess.STDOUT)
        rd.update({'solver_exit':cp.returncode, 'seconds':time.monotonic()-solve_start})
        result['rounds'].append(rd)
        print(json.dumps(rd), flush=True)
        if cp.returncode == 20:
            result['status'] = 'UNSAT_for_fixed_prefix_and_gate_budget_on_samples'
            break
        if cp.returncode != 10:
            result['status'] = 'UNKNOWN_timeout_or_solver_error'
            break
        model = set()
        for line in witness_path.read_text().splitlines():
            if line.startswith('v '):
                model.update(int(t) for t in line.split()[1:] if int(t)>0)
        assert all(any((x>0 and x in model) or (x<0 and -x not in model) for x in c) for c in cnf.clauses)
        tail = []
        vals = list(initial)
        for g in range(tail_size):
            a = next(i for i, v in enumerate(left[g]) if v in model)
            b = next(i for i, v in enumerate(right[g]) if v in model)
            operation = 'or' if op[g] in model else 'and'
            tail.append((operation,a,b))
            vals.append(vals[a] | vals[b] if operation=='or' else vals[a] & vals[b])
        outs = dict(output_fixed)
        for j, sels in zip(need, output):
            outs[j] = ni+next(g for g,sel in enumerate(sels) if sel in model)
        failures = []
        new_samples = set()
        for j, wire in outs.items():
            diff = vals[wire] ^ target[j]
            if diff:
                failures.append(j)
                # Diverse counterexamples from least and greatest assignments.
                for _ in range(2):
                    if not diff:
                        break
                    lo = (diff & -diff).bit_length()-1
                    hi = diff.bit_length()-1
                    new_samples.update([lo,hi])
                    diff &= ~(1 << lo)
                    diff &= ~(1 << hi)
        rd.update({'failed_outputs':failures, 'new_samples':sorted(new_samples)})
        result.update({'last_tail':tail, 'last_outputs':outs})
        if not failures:
            refunds = []
            disjoint = [s for s in family if not s & ys]
            for g,bits in enumerate(vals[n:]):
                light = {p for p in range(n) if (bits >> (1 << p)) & 1}
                heavy = {p for p in range(n) if p not in ys and (bits >> (ym | (1 << p))) & 1}
                if light in family and heavy in disjoint:
                    refunds.append(g)
            rhs = len(prefix)+len(tail)+len(family)+len(refunds)
            result.update({'status':'EXACT_COUNTEREXAMPLE' if lhs>rhs else 'EXACT_CIRCUIT_NO_VIOLATION',
                           'refunds':refunds, 'rhs':rhs, 'truth_table_assignments':1<<n})
            break
        assert new_samples-samples
        samples |= new_samples
        result['status'] = 'SAT_samples_but_full_truth_failures'
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    result['elapsed'] = time.monotonic()-started
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'], 'elapsed':result['elapsed']}),flush=True)


if __name__ == '__main__':
    main()
