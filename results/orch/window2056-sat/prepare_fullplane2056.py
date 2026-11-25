import json
from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-121')
out=root/'window2056-sat'
d=json.loads((root/'plane2056-sat/plane2056-data.json').read_text())
s=json.loads((out/'plane63-near-seed-2056.json').read_text())[0]
n=26;rows=d['rows'];edges=d['edges'];g=s['gates'];target=sum(int(any((r>>a)&(r>>b)&1 for a,b in edges))<<k for k,r in enumerate(rows));negative=((1<<len(rows))-1)^target
inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def evaluate(net):
 values=inputs.copy()
 for op,a,b in net:values.append(values[a]&values[b] if op==0 else values[a]|values[b])
 return values
values=evaluate(g);removed=set()
def flatten(w):
 if w>=n and not values[w]&negative and g[w-n][0]==1:
  removed.add(w);_,a,b=g[w-n];return flatten(a)+flatten(b)
 return [w]
terms=flatten(s['output'])
for w in removed:assert sum(w in (a,b) for _,a,b in g)<=1
unaffected=[3,4,5,6,7,9,11];selected=[]
for point in unaffected:
 matches=[w for w in terms if {tuple(e) for e in edges if values[w]>>rows.index((1<<e[0])|(1<<e[1]))&1}=={tuple(e) for e in edges if point in e}]
 assert len(matches)==1;selected+=matches
net=[];mapping={i:i for i in range(n)}
def emit(w):
 if w in mapping:return mapping[w]
 assert w not in removed
 op,a,b=g[w-n];a,b=sorted((emit(a),emit(b)));nw=n+len(net);net.append([op,a,b]);mapping[w]=nw;return nw
acc=emit(selected[0])
for w in selected[1:]:
 term=emit(w);net.append([1,min(acc,term),max(acc,term)]);acc=n+len(net)-1
assert len(net)==34
prefix=[x.copy() for x in net];prefix_output=acc
for w in terms:
 if w in selected:continue
 term=emit(w);net.append([1,min(acc,term),max(acc,term)]);acc=n+len(net)-1
assert len(net)==63 and evaluate(net)[-1]==values[-1]
control=[x.copy() for x in prefix];acc=prefix_output
for point in range(13):
 if point in unaffected:continue
 neighbors=[b for a,b in edges if a==point];assert len(neighbors)==4
 term=neighbors[0]
 for line in neighbors[1:]:control.append([1,min(term,line),max(term,line)]);term=n+len(control)-1
 control.append([0,point,term]);term=n+len(control)-1
 control.append([1,min(acc,term),max(acc,term)]);acc=n+len(control)-1
assert len(control)==64 and control[:34]==net[:34] and evaluate(control)[-1]==target
record={'n':n,'points':list(range(13)),'lines':list(range(13)),'rows':rows,'edges':edges,'prefix_size':34,'unaffected_points':unaffected,'original_gates':g,'ordered_gates':net,'positive_gates64':control,'seed_boundary_mismatches':(values[-1]^target).bit_count()}
(out/'plane63-prefix34-2056.data.json').write_text(json.dumps(record,indent=2))
(out/'plane63-prefix34-2056-rows.json').write_text(json.dumps(rows))
(out/'plane63-prefix34-2056-gates.json').write_text(json.dumps(net))
(out/'plane64-prefix34-control-2056-gates.json').write_text(json.dumps(control))
print(json.dumps({'prefix':34,'free_target':29,'target_size':63,'control_size':64,'boundary':len(rows),'near_mismatches':record['seed_boundary_mismatches']}))
