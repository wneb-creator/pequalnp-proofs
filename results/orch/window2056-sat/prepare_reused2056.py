import json
from pathlib import Path
root=Path('/workspace/pequalnp-proofs/results/orch/patch2056')
out=Path('/tmp/oec/pequalnp-pilot-121/window2056-sat')
d=json.loads((root/'collinear6-data.json').read_text())
s=json.loads((root/'collinear6-reused-dirty-seeds.json').read_text())[0]
n=d['inputs'];rows=d['rows'];edges=d['edges'];g=s['gates'];target=sum(int(any((r>>a)&(r>>b)&1 for a,b in edges))<<k for k,r in enumerate(rows));neg=((1<<len(rows))-1)^target
iv=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def evaluate(net,initial=iv):
 v=initial.copy()
 for op,a,b in net:v.append(v[a]&v[b] if op==0 else v[a]|v[b])
 return v
v=evaluate(g);assert v[-1]==target
removed=set()
def flatten(w):
 if w>=n and not v[w]&neg and g[w-n][0]==1:
  removed.add(w);_,a,b=g[w-n];return flatten(a)+flatten(b)
 return [w]
terms=flatten(s['output'])
for w in removed:assert sum(w in (a,b) for _,a,b in g)<=1
prefix_terms=[]
for point in [2,4]:
 candidates=[w for w in terms if {tuple(e) for e in edges if (v[w]>>rows.index((1<<e[0])|(1<<e[1])))&1}=={tuple(e) for e in edges if point in e}]
 assert len(candidates)==1
 prefix_terms.extend(candidates)
net=[];mapping={i:i for i in range(n)}
def emit(w):
 if w in mapping:return mapping[w]
 assert w not in removed
 op,a,b=g[w-n];a,b=sorted((emit(a),emit(b)));nw=n+len(net);net.append([op,a,b]);mapping[w]=nw;return nw
dirty=emit(s['dirty_and_wire']);assert len(net)==3
acc=emit(prefix_terms[0]);term=emit(prefix_terms[1]);net.append([1,min(acc,term),max(acc,term)]);acc=n+len(net)-1
prefix_count=len(net);assert prefix_count==12
for w in terms:
 if w in prefix_terms:continue
 term=emit(w);net.append([1,min(acc,term),max(acc,term)]);acc=n+len(net)-1
assert len(net)==32 and acc==n+31 and evaluate(net)[-1]==target
assert net[:3]==[[1,0,1],[1,6,7],[0,19,20]]
# Independently compare exact full truth tables after the topological change.
N=1<<n;ones=(1<<N)-1
full_inputs=[]
for i in range(n):
 step=1<<i;pattern=((1<<step)-1)<<step;full_inputs.append(pattern*((1<<N)-1)//((1<<(2*step))-1))
a=evaluate(g,full_inputs)[-1];b=evaluate(net,full_inputs)[-1]
assert a==b
expected=0
for u,w in edges:expected|=full_inputs[u]&full_inputs[w]
assert b==expected
normalized={'n':n,'points':d['points'],'lines':d['lines'],'edges':edges,'rows':rows,'prefix_size':12,'original_gates':g,'ordered_gates':net,'retained_dirty_wire':dirty,'unaffected_points':[2,4],'full_assignments_checked':N,'full_mismatches':0}
(out/'reused32-prefix12-2056.data.json').write_text(json.dumps(normalized,indent=2))
(out/'reused32-prefix12-2056-rows.json').write_text(json.dumps(rows))
(out/'reused32-prefix12-2056-gates.json').write_text(json.dumps(net))
# The placeholder suffix is ignored by the prefix encoder, but remains well formed.
placeholder=net[:12]+[[1,n+j-1,n+j-1] for j in range(12,28)]
(out/'reused28-prefix12-2056-placeholder.json').write_text(json.dumps(placeholder))
print(json.dumps({'n':n,'rows':len(rows),'fixed_prefix':12,'control_size':32,'target_size':28,'free_target_gates':16,'retained_dirty_wire':dirty,'full_assignments_checked':N,'full_mismatches':0}))
