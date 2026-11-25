import argparse
import json
from pathlib import Path
import resource
import subprocess
import time

ap=argparse.ArgumentParser()
ap.add_argument('stem')
ap.add_argument('--seconds',type=int,default=900)
args=ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
stem=Path(args.stem)
mapping=json.loads(stem.with_suffix('.mapping.json').read_text())
variables=mapping['signature_variables']
assert len(variables)%2==0
k=len(variables)//2
n=mapping['input_count']
positive=mapping['positive_samples']
negative=mapping['negative_samples']
samples=positive+negative
command=['/tmp/oec/pequalnp-pilot-62/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical',
         '-t',str(args.seconds),'-w',str(stem.with_suffix('.sol')),str(stem.with_suffix('.cnf'))]
stem.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
start=time.monotonic()
print(json.dumps({'or_count':k,'inputs':n,'positive_samples':len(positive),
                  'negative_samples':len(negative),'solver_seconds':args.seconds}),flush=True)
with stem.with_suffix('.solver.log').open('w') as log:
    done=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
result={10:'sat',20:'unsat'}.get(done.returncode,'unknown')
status={'result':result,'solver_exit':done.returncode,'solver_wall_seconds':time.monotonic()-start}
stem.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True)
if done.returncode!=10:raise SystemExit(0)
assignment={}
for line in stem.with_suffix('.sol').read_text().splitlines():
    if line.startswith('v '):
        for word in line.split()[1:]:
            lit=int(word)
            if lit:assignment[abs(lit)]=lit>0
assert all(v in assignment for group in variables for v in group)
signatures=[sum(int(assignment[v])<<b for b,v in enumerate(group)) for group in variables]
np=len(positive)
pm=(1<<np)-1
full=(1<<len(samples))-1
values=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(n)]
operands=[]
for g in range(k):
    branch_signatures=signatures[2*g:2*g+2]
    a,b=branch_signatures
    assert a&~b and b&~a and a<b
    chosen=[[i for i,w in enumerate(values) if w&sig==sig] for sig in branch_signatures]
    assert all(chosen)
    branch_values=[]
    for sig,refs in zip(branch_signatures,chosen):
        value=full
        for ref in refs:value &= values[ref]
        assert value&pm==sig
        branch_values.append(value)
    operands.append(chosen)
    values.append(branch_values[0]|branch_values[1])
output_refs=[i for i,w in enumerate(values) if w&pm==pm]
assert output_refs
output=full
for ref in output_refs:output &= values[ref]
assert output==pm
for row,bound in enumerate(mapping['false_OR_bounds'],np):
    assert sum(not(w>>row&1) for w in values[n:])>=bound
if mapping.get('dirty_singletons'):
    assert negative[-n:]==[1<<i for i in range(n)]
    singleton_part=((1<<n)-1)<<(len(samples)-n)
    assert any(w&singleton_part for w in values[n:])
witness={'scenario':mapping['scenario'],'input_count':n,'or_count':k,
         'operand_signatures':[signatures[2*g:2*g+2] for g in range(k)],
         'operand_wire_lists':operands,'output_wire_list':output_refs,
         'checked_positive_samples':len(positive),'checked_negative_samples':len(negative)}
stem.with_suffix('.witness.json').write_text(json.dumps(witness,indent=2)+'\n')
print('WITNESS_VERIFIED',k,'ORs',len(samples),'samples',flush=True)
