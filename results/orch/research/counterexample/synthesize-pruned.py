import argparse
import json
import time
from pathlib import Path
import z3

parser = argparse.ArgumentParser()
parser.add_argument('--gates', type=int, required=True)
parser.add_argument('--timeout-ms', type=int, default=900000)
parser.add_argument('--seed', type=int, default=1372583)
parser.add_argument('--fixed-seed', action='store_true')
parser.add_argument('--require-bad-edge', action='store_true')
parser.add_argument('--useful-gates', action='store_true')
parser.add_argument('--balanced-mux', action='store_true')
parser.add_argument('--top-form', action='store_true')
parser.add_argument('--memory-mb', type=int, default=3000)
parser.add_argument('--first-op', choices=['AND', 'OR'])
parser.add_argument('--first-pair', choices=['same', 'incident', 'nonincident'])
parser.add_argument('--prefix', required=True)
args = parser.parse_args()
assert not (args.require_bad_edge and args.first_op is not None)
root = Path(__file__).resolve().parent
problem = (root / 'problem.txt').read_text().splitlines()
width, target = map(int, problem[0].split())
columns = list(map(int, problem[1].split()))
canonical = [tuple(map(int, line.split())) for line in problem[2:]]
assert width == 58 and len(columns) == 14 and len(canonical) == 27
solver = z3.SolverFor('QF_BV')
solver.set(timeout=args.timeout_ms, random_seed=args.seed, max_memory=args.memory_mb, threads=1)
selector_bits = (14 + args.gates).bit_length()
left = [z3.BitVec(f'a_{j}', selector_bits) for j in range(args.gates)]
right = [z3.BitVec(f'b_{j}', selector_bits) for j in range(args.gates)]
ops = [z3.Bool(f'and_{j}') for j in range(args.gates)]
values = [z3.BitVecVal(c, width) for c in columns]
monomials = [z3.BitVecVal(1 if i == 0 else 2 if i == 7 else 0, 3) for i in range(14)]


def mux(selector, available):
    if args.balanced_mux:
        pool = available + [available[0]] * ((1 << selector_bits) - len(available))
        for bit in range(selector_bits):
            pool = [z3.If(z3.Extract(bit, bit, selector) == 0, pool[i], pool[i+1])
                    for i in range(0, len(pool), 2)]
        return pool[0]
    value = available[0]
    for i, wire in enumerate(available[1:], 1):
        value = z3.If(selector == i, wire, value)
    return value


for j in range(args.gates):
    solver.add(z3.ULT(left[j], 14 + j), z3.ULT(right[j], 14 + j))
    solver.add(z3.ULE(left[j], right[j]))
    a, b = mux(left[j], values), mux(right[j], values)
    value = z3.BitVec(f'value_{j}', width)
    solver.add(value == z3.If(ops[j], a & b, a | b))
    if args.top_form:
        negative = ((1 << width) - 1) ^ target
        below_a, below_b = a & negative == 0, b & negative == 0
        solver.add(z3.If(ops[j], z3.And(z3.Not(below_a), z3.Not(below_b)),
                         below_a == below_b))
    if args.useful_gates:
        solver.add(value & target != 0)
        negative = ((1 << width) - 1) ^ target
        solver.add(value & negative != negative)
    if args.require_bad_edge:
        ma, mb = mux(left[j], monomials), mux(right[j], monomials)
        xy = z3.Or(z3.And(ma & 1 != 0, mb & 2 != 0),
                   z3.And(ma & 2 != 0, mb & 1 != 0))
        monomial = z3.BitVec(f'monomials_{j}', 3)
        solver.add(monomial == z3.If(ops[j], z3.If(xy, z3.BitVecVal(4, 3),
                                                  z3.BitVecVal(0, 3)), ma | mb))
        monomials.append(monomial)
    values.append(value)
solver.add(values[-1] == z3.BitVecVal(target, width))
if args.require_bad_edge:
    solver.add(monomials[-1] & 4 == 0)
for j in range(args.gates - 1):
    solver.add(z3.Or(*[z3.Or(left[k] == 14 + j, right[k] == 14 + j)
                       for k in range(j + 1, args.gates)]))
if args.fixed_seed:
    assert args.gates == 27
    for j, (op, a, b) in enumerate(canonical):
        solver.add(ops[j] == bool(op), left[j] == min(a, b), right[j] == max(a, b))
if args.first_op is not None:
    assert args.first_pair is not None
    a, b = {'same': (0, 1), 'incident': (0, 7), 'nonincident': (0, 9)}[args.first_pair]
    solver.add(ops[0] == (args.first_op == 'AND'), left[0] == a, right[0] == b)

print(json.dumps({'z3': z3.get_version_string(), 'gates': args.gates,
                  'patterns': width, 'timeout_ms': args.timeout_ms,
                  'fixed_seed': args.fixed_seed, 'assertions': len(solver.assertions()),
                  'require_bad_edge': args.require_bad_edge, 'useful_gates': args.useful_gates,
                  'balanced_mux': args.balanced_mux,
                  'top_form': args.top_form,
                  'first_op': args.first_op, 'first_pair': args.first_pair,
                  'start_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}), flush=True)
(root / (args.prefix + '.smt2')).write_text(solver.to_smt2())
start = time.monotonic()
verdict = solver.check()
elapsed = time.monotonic() - start
print('VERDICT', verdict, 'seconds', elapsed, flush=True)
print('STATISTICS', solver.statistics(), flush=True)
if verdict == z3.unknown:
    print('REASON', solver.reason_unknown(), flush=True)
elif verdict == z3.sat:
    model = solver.model()
    gates = [(int(z3.is_true(model.eval(ops[j], model_completion=True))),
              model.eval(left[j]).as_long(), model.eval(right[j]).as_long())
             for j in range(args.gates)]
    output = 14 + args.gates - 1
    text = f'output {output}\n' + '\n'.join(
        f'{14+j} {"AND" if op else "OR"} {a} {b}'
        for j, (op, a, b) in enumerate(gates)) + '\n'
    (root / (args.prefix + '.model.txt')).write_text(text)
    print(text, flush=True)
    wrong = []
    for mask in range(1 << 14):
        wires = [bool(mask & (1 << i)) for i in range(14)]
        wanted = any(wires[p] and wires[7+l]
                     for l in range(7) for p in (l, (l+1) % 7, (l+3) % 7))
        for op, a, b in gates:
            wires.append((wires[a] and wires[b]) if op else (wires[a] or wires[b]))
        if wires[output] != wanted:
            wrong.append(mask)
    print('FULL_VALIDATION', 'PASS' if not wrong else 'FAIL', 'wrong', len(wrong), flush=True)
    assert not wrong
