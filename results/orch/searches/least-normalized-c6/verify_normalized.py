import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('--expect-read1',action='store_true');args=ap.parse_args()
folder=Path('/tmp/oec/pequalnp-pilot-86/read1-construction')
stem=folder/args.stem
text=stem.with_suffix('.solver.stdout').read_text()
assert 's SATISFIABLE' in text
literals=[int(x) for line in text.splitlines() if line.startswith('v ') for x in line.split()[1:] if x!='0']
model={abs(x):x>0 for x in literals}
cnf=stem.with_suffix('.cnf').read_text().splitlines()
for line in cnf[1:]:
 if not line or line.startswith('c'):continue
 clause=list(map(int,line.split()[:-1]));assert any(model[abs(x)]==(x>0) for x in clause)
data=json.loads((folder/'c6-optimal-normalized-not-read1.json').read_text())
n=data['n'];gates=[]
for a,b,o in zip(data['A'],data['B'],data['O']):
 aa=[i for i,s in enumerate(a) if model[s]];bb=[i for i,s in enumerate(b) if model[s]]
 assert len(aa)==len(bb)==1
 gates.append([int(model[o]),aa[0],bb[0]])
wires=[sum(((x>>i)&1)<<x for x in range(1<<n)) for i in range(n)]
for op,a,b in gates:wires.append(wires[a]|wires[b] if op else wires[a]&wires[b])
target=sum(any((x>>a&1) and (x>>b&1) for a,b in data['edges'])<<x for x in range(1<<n))
assert wires[-1]==target
below=[w&~target==0 for w in wires]
for i,(op,a,b) in enumerate(gates):
 assert below[a]==below[b] if op else not below[a] and not below[b]
p,q=data['probe_edge'];vec=[{(1,0)} if i==p else {(0,1)} if i==q else set() for i in range(n)]
for op,a,b in gates:
 vec.append(vec[a]|vec[b] if op else {(min(2,u[0]+v[0]),min(2,u[1]+v[1])) for u in vec[a] for v in vec[b]})
read1=any(a<=1 and b<=1 for a,b in vec[-1])
assert read1==args.expect_read1
result=dict(gates=gates,truth_table_equal=True,all64inputs_checked=True,or_uniform=True,no_and_below_operand=True,probe_edge=[p,q],probe_read1=read1,below=below)
stem.with_suffix('.verified.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
