import argparse
import itertools
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time


class CNF:
    def __init__(self, path):
        self.path = path
        self.body = path.with_suffix('.clauses')
        self.out = self.body.open('w')
        self.variables = 0
        self.clauses = 0

    def var(self):
        self.variables += 1
        return self.variables

    def add(self, xs):
        literals = set()
        for x in xs:
            if x is True:
                return
            if x is False:
                continue
            if -x in literals:
                return
            literals.add(x)
        self.out.write(' '.join(map(str, sorted(literals, key=lambda x: (abs(x), x)))) + ' 0\n')
        self.clauses += 1

    @staticmethod
    def neg(x):
        return not x if type(x) is bool else -x

    def conj(self, xs):
        literals = set()
        for x in xs:
            if x is False:
                return False
            if x is True:
                continue
            if -x in literals:
                return False
            literals.add(x)
        if not literals:
            return True
        if len(literals) == 1:
            return next(iter(literals))
        y = self.var()
        for x in literals:
            self.add([-y, x])
        self.add([y] + [-x for x in literals])
        return y

    def disj(self, xs):
        return self.neg(self.conj([self.neg(x) for x in xs]))

    def equal(self, x, y):
        self.add([self.neg(x), y])
        self.add([x, self.neg(y)])

    def at_least(self, xs, k):
        state = [True] + [False] * k
        for x in xs:
            state = [True] + [self.disj([state[j], self.conj([x, state[j-1]])]) for j in range(1, k+1)]
        self.add([state[k]])

    def finish(self):
        self.out.close()
        with self.path.open('wb') as out, self.body.open('rb') as source:
            out.write(f'p cnf {self.variables} {self.clauses}\n'.encode())
            shutil.copyfileobj(source, out)
        self.body.unlink()


ap = argparse.ArgumentParser()
ap.add_argument('or_count', type=int)
ap.add_argument('--points', default=','.join(map(str, range(13))))
ap.add_argument('--seconds', type=int, default=900)
ap.add_argument('--tag', default='direct-multi-output')
ap.add_argument('--fixed-baseline', action='store_true')
ap.add_argument('--cnf-only', action='store_true')
ap.add_argument('--cover-suffix', type=int, default=3)
ap.add_argument('--exact-pencil', action='store_true')
args = ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS, (3*1024**3, 3*1024**3))
base = Path('/tmp/oec/pequalnp-pilot-62')
stem = base / args.tag
data = json.loads((base / 'multi-output-line-neighborhoods.json').read_text())
points = sorted(map(int, args.points.split(',')))
targets = [data['targets'][p] for p in points]
vertices = sorted({i for t in targets for i in range(13) if t['positive_mask'] >> i & 1})
index = {v:i for i,v in enumerate(vertices)}
def project(q):
    return sum((q >> j & 1) << i for i,j in enumerate(vertices))
nv = len(vertices)
positive = [1 << i for i in range(nv)]
target_masks = [project(t['positive_mask']) for t in targets]
original_negative = sorted({project(q) for q in data['negative_samples']})
negative_set = set()
for t in target_masks:
    rows = [q for q in original_negative if not q & t]
    negative_set.update(q for q in rows if not any(q != r and q & ~r == 0 for r in rows))
negative = sorted(negative_set)
samples = positive + negative
baseline_masks = []
baseline_signatures = positive.copy()
for target in target_masks:
    ids = [i for i in range(nv) if target >> i & 1]
    children = []
    for a,b in [(ids[0],ids[1]),(ids[2],ids[3])]:
        baseline_masks.append(sorted([baseline_signatures[a],baseline_signatures[b]]))
        children.append(len(baseline_signatures))
        baseline_signatures.append(baseline_signatures[a] | baseline_signatures[b])
    a,b = children
    baseline_masks.append(sorted([baseline_signatures[a],baseline_signatures[b]]))
    baseline_signatures.append(baseline_signatures[a] | baseline_signatures[b])
if args.fixed_baseline:
    assert args.or_count == len(baseline_masks)
start = time.monotonic()
cnf = CNF(stem.with_suffix('.cnf'))
wires = [[bool(q >> i & 1) for q in samples] for i in range(nv)]
signature_variables = []
for gate in range(args.or_count):
    terms = []
    branch_signatures = []
    for branch in range(2):
        sig = [cnf.var() for _ in range(nv)]
        signature_variables.append(sig)
        branch_signatures.append(sig)
        cnf.add(sig)
        include = [cnf.conj(cnf.disj([-sig[b], wire[b]]) for b in range(nv)) for wire in wires]
        # The following is implied by exact positive closure and incomparability,
        # but makes the no-empty-meet interpretation explicit.
        cnf.add(include)
        term = [cnf.conj(cnf.disj([cnf.neg(inc), wire[row]]) for inc,wire in zip(include,wires))
                for row in range(len(samples))]
        for b in range(nv):
            cnf.equal(sig[b], term[b])
        if args.fixed_baseline:
            mask = baseline_masks[gate][branch]
            for b,x in enumerate(sig):
                cnf.add([x if mask >> b & 1 else -x])
        terms.append(term)
    left,right = branch_signatures
    cnf.add([cnf.conj([a,-b]) for a,b in zip(left,right)])
    cnf.add([cnf.conj([b,-a]) for a,b in zip(left,right)])
    # Unsigned left < right, to remove branch exchange symmetry.
    eq = True
    less = []
    for a,b in reversed(list(zip(left,right))):
        less.append(cnf.conj([eq,-a,b]))
        eq = cnf.conj([eq, cnf.disj([-a,b]), cnf.disj([a,-b])])
    cnf.add(less)
    wires.append([cnf.disj([a,b]) for a,b in zip(*terms)])
for target in target_masks:
    contain = [cnf.conj(wire[b] for b in range(nv) if target >> b & 1) for wire in wires]
    for row,q in enumerate(negative, nv):
        if not target & q:
            cnf.add([cnf.conj([inc,cnf.neg(wire[row])]) for inc,wire in zip(contain,wires)])
false_bounds = []
for row,q in enumerate(negative, nv):
    required = [t for t in target_masks if not t & q]
    union = 0
    for t in required:
        union |= t
    bound = max(0, union.bit_count()-len(required))
    false_bounds.append(bound)
    if bound:
        cnf.at_least([cnf.neg(wire[row]) for wire in wires[nv:]], bound)
# A new false OR can reduce a false-wire cover number by at most one.
# At the end, the outputs false at this row give a cover with at most
# len(required) wires. Replace each future selected false OR by its two
# earlier false operands, whose free conjunctions each lie inside one
# available false wire. The resulting prefix cover has the bound below.
prefix = max(0,args.or_count-args.cover_suffix)
for row,q in enumerate(negative,nv):
    required = [t for t in target_masks if not t & q]
    target = 0
    for t in required:
        target |= t
    if not target:
        continue
    current = wires[:nv+prefix]
    selected = [cnf.var() for _ in current]
    for choose,wire in zip(selected,current):
        cnf.add([-choose,cnf.neg(wire[row])])
    for bit in range(nv):
        if target >> bit & 1:
            cnf.add([cnf.conj([choose,wire[bit]]) for choose,wire in zip(selected,current)])
    counted = selected + [wire[row] for wire in wires[nv+prefix:]]
    bound = len(required) + args.or_count-prefix
    # Sum(selected) + number of future true ORs <= outputs + future ORs.
    state = [True] + [False]*(bound+1)
    for x in counted:
        state = [True] + [cnf.disj([state[j],cnf.conj([x,state[j-1]])])
                          for j in range(1,bound+2)]
    cnf.add([cnf.neg(state[bound+1])])
if args.exact_pencil:
    assert points == list(range(13)) and vertices == list(range(13))
    assert args.or_count <= 38 or args.fixed_baseline
    # The no-exact-target guard-charging bound forces some exact pencil
    # support in every <=38-OR separator. A Singer rotation sends it to P0.
    # This concerns only singleton-positive supports, not whole functions.
    pencil = target_masks[0]
    exact_choices = [cnf.conj([wire[b] if pencil>>b&1 else cnf.neg(wire[b])
                              for b in range(nv)]) for wire in wires[nv:]]
    cnf.add(exact_choices)
actions = []
for multiplier in (1,3,9):
    for shift in range(13):
        # Preserve the already normalized P0 signal.
        if args.exact_pencil and shift != 0: continue
        if {(multiplier*p+shift)%13 for p in points} != set(points):
            continue
        mapped = [(multiplier*l+shift)%13 for l in vertices]
        assert set(mapped) == set(vertices)
        action = [index[l] for l in mapped]
        assert {sum((t>>i&1)<<action[i] for i in range(nv)) for t in target_masks} == set(target_masks)
        assert {sum((q>>i&1)<<action[i] for i in range(nv)) for q in negative} == set(negative)
        actions.append(action)
representatives = sorted({min(tuple(sorted((a[i],a[j]))) for a in actions)
                          for i,j in itertools.combinations(range(nv),2)})
if not args.fixed_baseline:
    choices = []
    for i,j in representatives:
        choices.append(cnf.conj([x if b == i else -x for b,x in enumerate(signature_variables[0])] +
                                [x if b == j else -x for b,x in enumerate(signature_variables[1])]))
    cnf.add(choices)
cnf.finish()
mapping = {'signature_variables':signature_variables, 'line_inputs':vertices, 'points':points,
           'positive_samples':positive, 'negative_samples':negative, 'target_masks':target_masks,
           'variables':cnf.variables, 'clauses':cnf.clauses, 'first_OR_representatives':representatives,
           'false_OR_bounds':false_bounds, 'fixed_baseline':args.fixed_baseline}
mapping['cover_prefix'] = prefix
mapping['exact_pencil_required'] = 0 if args.exact_pencil else None
mapping['symmetry_fixes_point_zero'] = args.exact_pencil
stem.with_suffix('.mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps({'points':points, 'inputs':nv, 'negative_rows':len(negative),
                  'or_count':args.or_count, 'variables':cnf.variables, 'clauses':cnf.clauses,
                  'encoding_seconds':time.monotonic()-start,
                  'max_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
if args.cnf_only:
    raise SystemExit(0)
command = ['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical',
           '-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
with stem.with_suffix('.solver.log').open('w') as log:
    done = subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
result = {10:'sat',20:'unsat'}.get(done.returncode,'unknown')
print('result',result,'solver_exit',done.returncode,'elapsed',time.monotonic()-start,flush=True)
if done.returncode != 10:
    raise SystemExit(0)
assignment = {}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit = int(word)
            if lit:
                assignment[abs(lit)] = lit > 0
assert all(v in assignment for group in signature_variables for v in group)
masks = [sum(int(assignment[v]) << b for b,v in enumerate(group)) for group in signature_variables]
truths = [sum(bool(q >> i & 1) << j for j,q in enumerate(samples)) for i in range(nv)]
if args.exact_pencil:
    assert any((masks[2*g] | masks[2*g+1]) == target_masks[0] for g in range(args.or_count))
positive_mask = (1 << nv)-1
full = (1 << len(samples))-1
decoded = []
for g in range(args.or_count):
    operands = []
    for s in masks[2*g:2*g+2]:
        selected = [i for i,w in enumerate(truths) if w & s == s]
        assert selected
        value = full
        for i in selected:
            value &= truths[i]
        assert value & positive_mask == s
        operands.append(value)
    truths.append(operands[0] | operands[1])
    decoded.append(masks[2*g:2*g+2])
for target in target_masks:
    output = full
    for w in truths:
        if w & target == target:
            output &= w
    assert output == sum(bool(q & target) << j for j,q in enumerate(samples))
# Independently evaluate every original generic row and every cap, using
# canonical operand lists reconstructed solely from the positive signatures.
pos_wires = positive.copy()
operands = []
for left,right in decoded:
    operands.append([[i for i,w in enumerate(pos_wires) if w & sig == sig] for sig in (left,right)])
    pos_wires.append(left | right)
out_wires = [[i for i,w in enumerate(pos_wires) if w & t == t] for t in target_masks]
allowed = [project(t) for t in data['allowed_concurrent_triples'] if t & ~sum(1 << v for v in vertices) == 0]
all_checks = set(original_negative) | {q for q in range(1 << nv) if not any(q & t == t for t in allowed)}
for q in all_checks:
    values = [bool(q >> i & 1) for i in range(nv)]
    for a,b in operands:
        values.append(all(values[i] for i in a) or all(values[i] for i in b))
    for target,chosen in zip(target_masks,out_wires):
        assert all(values[i] for i in chosen) == bool(q & target)
stem.with_suffix('.witness.json').write_text(json.dumps({'points':points,'line_inputs':vertices,
    'or_count':args.or_count,'operand_signatures':decoded,'operand_wire_lists':operands,
    'output_wire_lists':out_wires,'checked_assignments':len(all_checks)},indent=2)+'\n')
print('WITNESS_VERIFIED',args.or_count,'ORs',len(points),'outputs',len(all_checks),'assignments',flush=True)
