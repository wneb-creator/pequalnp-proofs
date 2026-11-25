import argparse
import ast
import itertools
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time

base = Path('/tmp/oec/pequalnp-pilot-62')
tree = ast.parse((base / 'multi_output_direct_cnf.py').read_text())
definition = next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name == 'CNF')
exec(compile(ast.Module(body=[definition],type_ignores=[]),'audited_CNF_class','exec'))
ap = argparse.ArgumentParser()
ap.add_argument('or_count',type=int)
ap.add_argument('--scenario',choices=['global','cycle4','cycle5','theta4'],default='global')
ap.add_argument('--seconds',type=int,default=900)
ap.add_argument('--tag',default='global-or')
ap.add_argument('--fixed-baseline',action='store_true')
ap.add_argument('--cnf-only',action='store_true')
ap.add_argument('--cover-suffix',type=int,default=0)
ap.add_argument('--dirty-singletons',action='store_true')
ap.add_argument('--cover-cyclic-reps',action='store_true')
ap.add_argument('--seeded',action='store_true')
ap.add_argument('--seed-witness')
ap.add_argument('--different-seed',action='store_true')
ap.add_argument('--delete-baseline-gate',type=int)
ap.add_argument('--free-gates',default='')
args = ap.parse_args()
assert args.cover_suffix >= 0
free_gates={int(g) for g in args.free_gates.split(',') if g}
if args.different_seed:
    assert args.seeded and args.or_count==51 and args.delete_baseline_gate is None and free_gates
if args.seeded:
    assert args.scenario=='global' and not args.fixed_baseline
    assert all(0<=g<args.or_count for g in free_gates)
else:
    assert args.delete_baseline_gate is None and not free_gates and not args.seed_witness
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
stem = base / args.tag
if args.scenario in ('global','theta4'):
    name = 'global-first-or-symmetry.json' if args.scenario == 'global' else 'theta4-first-or-symmetry.json'
    data = json.loads((base / name).read_text())
    positive,negative = data['positive_samples'],data['negative_samples']
    nv = 26 if args.scenario == 'global' else 10
    representatives = [o['representative_masks'] for o in data['first_OR_orbits']]
else:
    nv = int(args.scenario[5:])
    positive = [(1<<i)|(1<<((i+1)%nv)) for i in range(nv)]
    false = [q for q in range(1<<nv) if not any(q&p == p for p in positive)]
    negative = [q for q in false if not any(q != r and q&r == q for r in false)]
    input_masks = [sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(nv)]
    initial = set(input_masks)
    for a in range(1,1<<nv):
        mask = (1<<len(positive))-1
        for i in range(nv):
            if a>>i&1: mask &= input_masks[i]
        if mask: initial.add(mask)
    representatives = [sorted([a,b]) for a,b in itertools.combinations(sorted(initial),2)
                       if a&~b and b&~a]
original_negative_count = len(negative)
if args.dirty_singletons:
    assert args.scenario == 'global'
    assert args.or_count <= 50 or args.fixed_baseline or (args.seeded and args.or_count==51)
    negative = negative + [1<<i for i in range(nv)]
np = len(positive)
samples = positive+negative
input_masks = [sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(nv)]
baseline = []
seed_digest = None
if args.fixed_baseline or args.seeded:
    if args.scenario == 'global':
        known = json.loads((base / 'multi-output-baseline39.json').read_text())
        masks = input_masks.copy()
        for a,b in known['ors']:
            pair = sorted([masks[a+13],masks[b+13]])
            baseline.append(pair)
            masks.append(pair[0]|pair[1])
        accumulated = input_masks[0]
        for p in range(1,13):
            baseline.append(sorted([accumulated,input_masks[p]]))
            accumulated |= input_masks[p]
        assert len(baseline) == 51
    elif args.scenario == 'cycle4':
        baseline = [sorted([input_masks[0],input_masks[2]]),
                    sorted([input_masks[1],input_masks[3]])]
    else:
        accumulated = 1
        for p in range(1,np):
            baseline.append(sorted([accumulated,1<<p]))
            accumulated |= 1<<p
    if args.seed_witness:
        assert args.seeded and args.scenario=='global'
        seed_bytes=Path(args.seed_witness).read_bytes()
        seed_digest=hashlib.sha256(seed_bytes).hexdigest()
        seed=json.loads(seed_bytes)
        assert seed['input_count']==nv and seed['or_count']==51
        assert len(seed['operand_wire_lists'])==51
        full=(1<<len(samples))-1
        positive_mask=(1<<np)-1
        evaluations=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(nv)]
        baseline=[]
        for pair in seed['operand_wire_lists']:
            assert len(pair)==2
            terms=[]
            for refs in pair:
                assert refs and all(type(i) is int and 0<=i<len(evaluations) for i in refs)
                value=full
                for i in refs:value &= evaluations[i]
                terms.append(value)
            baseline.append(sorted([value&positive_mask for value in terms]))
            evaluations.append(terms[0]|terms[1])
        result=full
        assert seed['output_wire_list']
        for i in seed['output_wire_list']:
            assert type(i) is int and 0<=i<len(evaluations)
            result &= evaluations[i]
        assert result==positive_mask
    if args.seeded and args.delete_baseline_gate is not None:
        assert 0<=args.delete_baseline_gate<51 and args.or_count==50
        baseline.pop(args.delete_baseline_gate)
    assert len(baseline) == args.or_count
start = time.monotonic()
cnf = CNF(stem.with_suffix('.cnf'))
wires = [[bool(q>>i&1) for q in samples] for i in range(nv)]
signature_variables = []
seed_difference = []
for gate in range(args.or_count):
    terms = []
    branches = []
    for side in range(2):
        if args.seeded and gate not in free_gates:
            sig = [bool(baseline[gate][side]>>b&1) for b in range(np)]
        else:
            sig = [cnf.var() for _ in range(np)]
        branches.append(sig)
        signature_variables.append(sig)
        if args.different_seed and gate in free_gates:
            seed_difference.extend(cnf.neg(x) if baseline[gate][side]>>b&1 else x for b,x in enumerate(sig))
        cnf.add(sig)
        include = [cnf.conj(cnf.disj([cnf.neg(sig[b]),wire[b]]) for b in range(np)) for wire in wires]
        cnf.add(include)
        term = [cnf.conj(cnf.disj([cnf.neg(inc),wire[row]]) for inc,wire in zip(include,wires))
                for row in range(len(samples))]
        for b in range(np): cnf.equal(sig[b],term[b])
        if args.fixed_baseline:
            for b,x in enumerate(sig): cnf.add([x if baseline[gate][side]>>b&1 else -x])
        terms.append(term)
    left,right = branches
    cnf.add([cnf.conj([a,cnf.neg(b)]) for a,b in zip(left,right)])
    cnf.add([cnf.conj([b,cnf.neg(a)]) for a,b in zip(left,right)])
    equal = True
    less = []
    for a,b in reversed(list(zip(left,right))):
        less.append(cnf.conj([equal,cnf.neg(a),b]))
        equal = cnf.conj([equal,cnf.disj([cnf.neg(a),b]),cnf.disj([a,cnf.neg(b)])])
    cnf.add(less)
    wires.append([cnf.disj([a,b]) for a,b in zip(left,right)] +
                 [cnf.disj([a,b]) for a,b in zip(terms[0][np:],terms[1][np:])])
if args.different_seed:cnf.add(seed_difference)
full_positive = (1<<np)-1
if args.dirty_singletons:
    # Parent's independently checked CleanOr bound shows that a separator
    # using at most50 ORs must have an OR true on a singleton. The condition
    # also holds for the ordinary51-OR control. No empty input can be true
    # in this normalized model because every conjunction is nonempty.
    cnf.add([wire[row] for wire in wires[nv:]
             for row in range(np+original_negative_count,len(samples))])
contain = [cnf.conj(wire[:np]) for wire in wires]
for row in range(np,len(samples)):
    cnf.add([cnf.conj([inc,cnf.neg(wire[row])]) for inc,wire in zip(contain,wires)])
false_bounds = []
for row,q in enumerate(negative,np):
    sensitive = [i for i in range(nv) if not(q>>i&1) and
                 any(p & ~(q|(1<<i)) == 0 for p in positive)]
    bound = max(0,len(sensitive)-1)
    false_bounds.append(bound)
    if bound: cnf.at_least([cnf.neg(wire[row]) for wire in wires[nv:]],bound)
prefix = args.or_count
cover_rows = list(range(np,len(samples)))
if args.cover_cyclic_reps:
    assert args.scenario == 'global' and args.cover_suffix > 0
    original_rows = negative[:original_negative_count]
    original_set = set(original_rows)
    assert len(original_set) == 468
    def rotate_row(q,shift):
        a,b = q & 8191,q >> 13
        a = ((a << shift) | (a >> (13-shift))) & 8191
        b = ((b << shift) | (b >> (13-shift))) & 8191
        return a | (b << 13)
    chosen = set()
    for q in original_rows:
        orbit = {rotate_row(q,shift) for shift in range(13)}
        assert len(orbit) == 13 and orbit <= original_set
        chosen.add(min(orbit))
    assert len(chosen) == 36
    cover_rows = [np+i for i,q in enumerate(original_rows) if q in chosen]
if args.cover_suffix:
    prefix = max(0,args.or_count-args.cover_suffix)
    for row in cover_rows:
        current = wires[:nv+prefix]
        selected = [cnf.var() for _ in current]
        for choose,wire in zip(selected,current): cnf.add([-choose,cnf.neg(wire[row])])
        for bit in range(np):
            cnf.add([cnf.conj([choose,wire[bit]]) for choose,wire in zip(selected,current)])
        counted = selected+[wire[row] for wire in wires[nv+prefix:]]
        bound = 1+args.or_count-prefix
        state = [True]+[False]*(bound+1)
        for x in counted:
            state = [True]+[cnf.disj([state[j],cnf.conj([x,state[j-1]])]) for j in range(1,bound+2)]
        cnf.add([cnf.neg(state[bound+1])])
if not args.fixed_baseline and not args.seeded:
    choices = []
    for a,b in representatives:
        choices.append(cnf.conj([x if a>>j&1 else -x for j,x in enumerate(signature_variables[0])] +
                                [x if b>>j&1 else -x for j,x in enumerate(signature_variables[1])]))
    cnf.add(choices)
cnf.finish()
mapping = {'scenario':args.scenario,'input_count':nv,'positive_samples':positive,
           'negative_samples':negative,'signature_variables':signature_variables,
           'first_OR_representatives':representatives,'false_OR_bounds':false_bounds,
           'cover_prefix':prefix,'variables':cnf.variables,'clauses':cnf.clauses,
           'fixed_baseline':args.fixed_baseline}
mapping['dirty_singletons'] = args.dirty_singletons
mapping['cover_rows'] = cover_rows if args.cover_suffix else []
mapping['cover_cyclic_reps'] = args.cover_cyclic_reps
mapping['search_scope'] = 'fixed_signature_seed_neighborhood' if args.seeded else 'unrestricted'
mapping['seeded'] = args.seeded
mapping['deleted_baseline_gate'] = args.delete_baseline_gate
mapping['free_gates'] = sorted(free_gates)
mapping['signature_variables_may_contain_boolean_constants'] = True
stem.with_suffix('.mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps({'scenario':args.scenario,'input_count':nv,'positive_count':np,
    'negative_count':len(negative),'or_count':args.or_count,'first_OR_orbits':len(representatives),
    'false_OR_bounds':sorted(set(false_bounds)),'cover_prefix':prefix,
    'cover_row_count':len(cover_rows) if args.cover_suffix else 0,
    'search_scope':mapping['search_scope'],'free_gates':sorted(free_gates),
    'deleted_baseline_gate':args.delete_baseline_gate,'seed_witness':args.seed_witness,'seed_witness_sha256':seed_digest,'different_seed':args.different_seed,
    'variables':cnf.variables,'clauses':cnf.clauses,'encoding_seconds':time.monotonic()-start,
    'max_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
if args.cnf_only: raise SystemExit(0)
command = ['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical',
           '-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
with stem.with_suffix('.solver.log').open('w') as log:
    done = subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
result = {10:'sat',20:'unsat'}.get(done.returncode,'unknown')
print('result',result,'solver_exit',done.returncode,'elapsed',time.monotonic()-start,flush=True)
if done.returncode != 10: raise SystemExit(0)
assignment = {}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit = int(word)
            if lit: assignment[abs(lit)] = lit > 0
assert all(type(var) is bool or var in assignment for group in signature_variables for var in group)
sig_masks = [sum(int(var if type(var) is bool else assignment[var])<<b for b,var in enumerate(group)) for group in signature_variables]
positive_wires = input_masks.copy()
operands = []
for g in range(args.or_count):
    branch_masks = sig_masks[2*g:2*g+2]
    selected = [[i for i,mask in enumerate(positive_wires) if mask & sig == sig] for sig in branch_masks]
    assert all(selected)
    for sig,chosen in zip(branch_masks,selected):
        actual = full_positive
        for i in chosen: actual &= positive_wires[i]
        assert actual == sig
    operands.append(selected)
    positive_wires.append(branch_masks[0]|branch_masks[1])
output_wires = [i for i,mask in enumerate(positive_wires) if mask == full_positive]
assert output_wires
for q,wanted in [(q,True) for q in positive]+[(q,False) for q in negative]:
    values = [bool(q>>i&1) for i in range(nv)]
    for a,b in operands: values.append(all(values[i] for i in a) or all(values[i] for i in b))
    assert all(values[i] for i in output_wires) == wanted
stem.with_suffix('.witness.json').write_text(json.dumps({'scenario':args.scenario,'input_count':nv,
    'or_count':args.or_count,'operand_signatures':[sig_masks[2*g:2*g+2] for g in range(args.or_count)],
    'operand_wire_lists':operands,'output_wire_list':output_wires,
    'checked_positive_samples':np,'checked_negative_samples':len(negative)},indent=2)+'\n')
print('WITNESS_VERIFIED',args.or_count,'ORs',len(samples),'samples',flush=True)
