from pathlib import Path
import json
p=Path('/tmp/oec/pequalnp-pilot-92')
lines=(p/'local1886-care-mixed-best.txt').read_text().splitlines()
gates=[tuple(map(int,s.split())) for s in lines[2:]]
output=int(lines[1].split()[1]);allbits=(1<<1024)-1
raw=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
values=raw[:]
for op,a,b in gates:values.append(values[a]&values[b] if op==0 else values[a]|values[b] if op==1 else allbits^values[a] if op==2 else 0 if op==3 else allbits)
truth=values[output];target=0
for a,b in edges:target|=raw[a]&raw[b]
missing=[(a,b) for a,b in edges if not(truth>>((1<<a)|(1<<b))&1)]
subgraph=0
for a,b in edges:
 if (a,b) not in missing:subgraph|=raw[a]&raw[b]
assert truth==subgraph
checks=[]
for a,b in edges:
 error=(truth|(raw[a]&raw[b]))^target
 checks.append({'supplied_AND_edge':[a,b],'full_errors':error.bit_count(),'counterexample':not error})
print(json.dumps({'missing_edges':missing,'raw_gates':len(gates),'rows_checked':1024,'all_supplied_edges':checks},indent=2))
