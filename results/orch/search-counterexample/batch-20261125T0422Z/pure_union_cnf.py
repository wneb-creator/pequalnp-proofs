import argparse
import ast
import itertools
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time

# Reuse only the independently audited CNF primitive class, without executing
# the other encoder's command line or model construction.
base = Path('/tmp/oec/pequalnp-pilot-62')
source = ast.parse((base / 'multi_output_direct_cnf.py').read_text())
definition = next(node for node in source.body if isinstance(node, ast.ClassDef) and node.name == 'CNF')
exec(compile(ast.Module(body=[definition], type_ignores=[]), 'audited_CNF_class', 'exec'))

ap = argparse.ArgumentParser()
ap.add_argument('or_count', type=int)
ap.add_argument('--seconds', type=int, default=900)
ap.add_argument('--tag', default='pure-union')
ap.add_argument('--fixed-baseline', action='store_true')
ap.add_argument('--cnf-only', action='store_true')
args = ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS, (3*1024**3, 3*1024**3))
stem = base / args.tag
data = json.loads((base / 'multi-output-line-neighborhoods.json').read_text())
baseline = json.loads((base / 'multi-output-baseline39.json').read_text())
targets = [t['positive_mask'] for t in data['targets']]
requirements = []
for t in data['targets']:
    rows = sorted({data['negative_samples'][i] for i in t['negative_rows']})
    requirements.extend((t['positive_mask'], q) for q in rows
                        if not any(q != r and q & r == q for r in rows))
if args.fixed_baseline:
    assert args.or_count == 39
start = time.monotonic()
cnf = CNF(stem.with_suffix('.cnf'))
wires = [[i == j for j in range(13)] for i in range(13)]
selectors = []
for g in range(args.or_count):
    branches = []
    choices = []
    for side in range(2):
        chosen = [cnf.var() for _ in wires]
        choices.append(chosen)
        cnf.add(chosen)
        for a,b in itertools.combinations(chosen,2):
            cnf.add([-a,-b])
        bits = [cnf.var() for _ in range(13)]
        for c,wire in zip(chosen,wires):
            for bit,value in zip(bits,wire):
                cnf.add([-c,-bit,value])
                cnf.add([-c,bit,cnf.neg(value)])
        if args.fixed_baseline:
            cnf.add([chosen[baseline['ors'][g][side]]])
        branches.append(bits)
    # Exchange the two inputs so their previous-wire indices increase.
    for j,a in enumerate(choices[0]):
        for k,b in enumerate(choices[1]):
            if j >= k:
                cnf.add([-a,-b])
    a,b = branches
    cnf.add([cnf.conj([x,-y]) for x,y in zip(a,b)])
    cnf.add([cnf.conj([y,-x]) for x,y in zip(a,b)])
    wires.append([cnf.disj([x,y]) for x,y in zip(a,b)])
    selectors.append(choices)
for target,cap in requirements:
    coverage = []
    for wire in wires[13:]:
        coverage.append(cnf.conj([wire[j] for j in range(13) if target >> j & 1] +
                                 [cnf.neg(wire[j]) for j in range(13) if cap >> j & 1]))
    cnf.add(coverage)
actions = [[(multiplier*j+shift)%13 for j in range(13)]
           for multiplier in (1,3,9) for shift in range(13)]
req_set = set(requirements)
for action in actions:
    def move(mask): return sum((mask >> j & 1) << action[j] for j in range(13))
    assert {(move(t),move(q)) for t,q in requirements} == req_set
representatives = sorted({min(tuple(sorted((action[a],action[b]))) for action in actions)
                          for a,b in itertools.combinations(range(13),2)})
if not args.fixed_baseline:
    cnf.add([cnf.conj([selectors[0][0][a],selectors[0][1][b]]) for a,b in representatives])
cnf.finish()
stem.with_suffix('.mapping.json').write_text(json.dumps({'selectors':selectors,
    'requirements':requirements,'first_OR_representatives':representatives,
    'variables':cnf.variables,'clauses':cnf.clauses,'fixed_baseline':args.fixed_baseline},indent=2)+'\n')
print(json.dumps({'or_count':args.or_count,'variables':cnf.variables,'clauses':cnf.clauses,
    'encoding_seconds':time.monotonic()-start,'max_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
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
            if lit: assignment[abs(lit)] = lit > 0
gate_masks = [1 << i for i in range(13)]
parents = []
for choices in selectors:
    picked = []
    for side in choices:
        chosen = [j for j,var in enumerate(side) if assignment[var]]
        assert len(chosen) == 1
        picked.append(chosen[0])
    a,b = picked
    gate_masks.append(gate_masks[a] | gate_masks[b])
    parents.append(picked)
assert all(any(mask & target == target and not mask & cap for mask in gate_masks) for target,cap in requirements)
outputs = [[mask for mask in gate_masks if mask & target == target] for target in targets]
checks = 0
for cap in range(8192):
    if any(cap & triple == triple for triple in data['allowed_concurrent_triples']): continue
    for target,output in zip(targets,outputs):
        assert all(mask & cap for mask in output) == bool(target & cap)
        checks += 1
stem.with_suffix('.witness.json').write_text(json.dumps({'input_count':13,'or_count':args.or_count,
    'ors':parents,'gate_masks':gate_masks[13:],'cover_deficit':0,'uncovered_requirements':0,
    'is_counterexample':args.or_count < 39,'verified_output_cap_checks':checks},indent=2)+'\n')
print('WITNESS_VERIFIED',args.or_count,'ORs',checks,'output/cap checks',flush=True)
