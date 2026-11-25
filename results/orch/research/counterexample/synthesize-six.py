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
parser.add_argument('--first-op', choices=['AND', 'OR'])
parser.add_argument('--first-pair', choices=['same', 'incident', 'nonincident'])
parser.add_argument('--prefix', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent
problem = (root / 'problem.txt').read_text().splitlines()
width, target = map(int, problem[0].split())
columns = list(map(int, problem[1].split()))
canonical = [tuple(map(int, line.split())) for line in problem[2:]]
assert width == 58 and len(columns) == 14 and len(canonical) == 27
solver = z3.SolverFor('QF_BV')
solver.set(timeout=args.timeout_ms, random_seed=args.seed, max_memory=3000, threads=1)
selector_bits = (14 + args.gates).bit_length()
left = [z3.BitVec(f'a_{j}', selector_bits) for j in range(args.gates)]
right = [z3.BitVec(f'b_{j}', selector_bits) for j in range(args.gates)]
ops = [z3.Bool(f'and_{j}') for j in range(args.gates)]
values = [z3.BitVecVal(c, width) for c in columns]


def mux(selector, available):
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
    values.append(value)
solver.add(values[-1] == z3.BitVecVal(target, width))
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
