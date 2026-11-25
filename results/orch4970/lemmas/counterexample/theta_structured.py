"""Exact finite theta synthesis with all L4970 hypotheses encoded.

Monotonicity makes graph boundary rows exact for the final output.  A gate
computes OR(S) iff it accepts singleton i for every i in S and rejects the
complement of S.  Syntactic OR reach is propagated separately from semantics.
An output selector permits unused semantic-star gates after the output.
"""
from pathlib import Path
from itertools import combinations
import importlib.util
import json
import subprocess
import sys
import time

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('theta_local', HERE / 'theta_local.py')
LOCAL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LOCAL)
VSPEC = importlib.util.spec_from_file_location('theta_validate', HERE / 'theta_validate.py')
VALIDATOR = importlib.util.module_from_spec(VSPEC)
VSPEC.loader.exec_module(VALIDATOR)
DIR = Path('/tmp/oec/pequalnp-pilot-110/counterexample4970/theta-structured')
DIR.mkdir(exist_ok=True)

CONTROL = [('or',5,6),('or',8,7),('and',0,9),('or',4,5),('and',1,11),
           ('or',4,6),('and',2,13),('or',4,7),('and',3,15),('or',10,12),
           ('or',17,14),('or',18,16)]

def build(gate_count, control=False):
    cnf = LOCAL.CNF()
    selectors = []
    for j in range(gate_count):
        ops = [cnf.var(), cnf.var()]
        ass = [cnf.var() for _ in range(8+j)]
        bss = [cnf.var() for _ in range(8+j)]
        cnf.exactly_one(ops)
        cnf.exactly_one(ass)
        cnf.exactly_one(bss)
        for a in range(8+j):
            for b in range(a):
                cnf.add(-ass[a],-bss[b])
        selectors.append((ops,ass,bss))
    output = [cnf.var() for _ in range(gate_count)]
    cnf.exactly_one(output)
    stars = []
    for center in range(8):
        neighbors = [v if u == center else u for u,v in LOCAL.EDGES if center in (u,v)]
        for k in range(2,len(neighbors)+1):
            for leaves in combinations(neighbors,k):
                stars.append((center, leaves))
    rows = set(LOCAL.initial_rows()) | {1 << i for i in range(8)}
    rows.update(255 ^ sum(1 << i for i in leaves) for _,leaves in stars)
    values = {}
    for row in sorted(rows):
        wires = [bool(row >> i & 1) for i in range(8)]
        for j,(ops,ass,bss) in enumerate(selectors):
            va,vb,z = cnf.var(),cnf.var(),cnf.var()
            for source_selectors,val in ((ass,va),(bss,vb)):
                for source,s in enumerate(source_selectors):
                    cnf.add(-s,-val,wires[source])
                    cnf.add(-s,val,LOCAL.neg(wires[source]))
            cnf.gate(z,'and',va,vb,-ops[0])
            cnf.gate(z,'or',va,vb,-ops[1])
            wires.append(z)
            cnf.add(-output[j], z if LOCAL.target(row) else -z)
        values[row] = wires
    reach = [[i == k for k in range(8)] for i in range(8)]
    for j,(ops,ass,bss) in enumerate(selectors):
        current = []
        for k in range(8):
            va,vb,z = cnf.var(),cnf.var(),cnf.var()
            for source_selectors,val in ((ass,va),(bss,vb)):
                for source,s in enumerate(source_selectors):
                    cnf.add(-s,-val,reach[source][k])
                    cnf.add(-s,val,LOCAL.neg(reach[source][k]))
            cnf.add(-ops[0],-z)
            cnf.gate(z,'or',va,vb,-ops[1])
            current.append(z)
        for a in range(4):
            for b in range(4,8):
                cnf.add(-current[a],-current[b])
        reach.append(current)
    witnesses = []
    for center,leaves in stars:
        complement = 255 ^ sum(1 << i for i in leaves)
        gate_witnesses = []
        for j,(ops,_,_) in enumerate(selectors):
            witness = cnf.var()
            cnf.add(-witness,ops[1])
            cnf.add(-witness,-values[complement][8+j])
            for leaf in leaves:
                cnf.add(-witness,values[1 << leaf][8+j])
            gate_witnesses.append(witness)
        witnesses.append(gate_witnesses)
    for a,b in LOCAL.EDGES:
        cnf.add(*(w for (center,leaves),ws in zip(stars,witnesses)
                  if (center == a and b in leaves) or (center == b and a in leaves)
                  for w in ws))
    if control:
        assert gate_count == len(CONTROL)
        for (op,a,b),(ops,ass,bss) in zip(CONTROL,selectors):
            a,b = sorted((a,b))
            cnf.add(ops[op == 'or'])
            cnf.add(ass[a])
            cnf.add(bss[b])
        cnf.add(output[-1])
    return cnf,selectors,output,rows,stars

def solve(gate_count, seconds, control=False):
    cnf,selectors,outputs,rows,stars = build(gate_count,control)
    name = ('control-' if control else 'search-') + str(gate_count)
    path = DIR / name
    cnf.write(path.with_suffix('.cnf'))
    start = time.monotonic()
    with path.with_suffix('.log').open('w') as log:
        proc = subprocess.run([LOCAL.SOLVER,'-t',str(seconds),str(path.with_suffix('.cnf'))],
                              stdout=log,stderr=subprocess.STDOUT)
    result = {'gates':gate_count,'rows':len(rows),'stars':len(stars),
              'variables':cnf.count,'clauses':len(cnf.clauses),
              'seconds':time.monotonic()-start,'exit_code':proc.returncode,
              'status':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(proc.returncode,'ERROR')}
    if proc.returncode == 10:
        text = path.with_suffix('.log').read_text()
        model = {int(x) for line in text.splitlines() if line.startswith('v ')
                 for x in line.split()[1:] if int(x) > 0}
        circuit = []
        for ops,ass,bss in selectors:
            op = next(op for op,s in zip(['and','or'],ops) if s in model)
            a = next(i for i,s in enumerate(ass) if s in model)
            b = next(i for i,s in enumerate(bss) if s in model)
            circuit.append((op,a,b))
        output = 8 + next(j for j,s in enumerate(outputs) if s in model)
        result['circuit'] = circuit
        result['validation'] = VALIDATOR.validate(circuit,output)
        if not result['validation']['satisfies_4970_hypotheses']:
            raise RuntimeError('SAT reconstruction failed independent exhaustive validation')
    path.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
    return result

if __name__ == '__main__':
    if sys.argv[1:] == ['control']:
        solve(12,30,control=True)
    else:
        solve(11,int(sys.argv[1]) if len(sys.argv)>1 else 60)
