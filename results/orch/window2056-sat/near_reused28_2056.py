import itertools,json,time
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-121/window2056-sat');d=json.loads((p/'reused32-prefix12-2056.data.json').read_text());g=d['ordered_gates'];n=d['n'];rows=d['rows'];edges=d['edges']
target=sum(int(any((r>>a)&(r>>b)&1 for a,b in edges))<<k for k,r in enumerate(rows));inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
choices=[j for j in range(12,len(g)-1) if g[j][0]==1]
best=None;tried=0;started=time.monotonic()
for deleted in itertools.combinations(choices,4):
 for side in itertools.product([0,1],repeat=4):
  replace=dict(zip(deleted,side));mapping={i:i for i in range(n)};net=[];values=inputs.copy()
  for j,(op,a,b) in enumerate(g):
   if j in replace:mapping[n+j]=mapping[[a,b][replace[j]]];continue
   a,b=sorted((mapping[a],mapping[b]));mapping[n+j]=n+len(net);net.append([op,a,b]);values.append(values[a]&values[b] if op==0 else values[a]|values[b])
  assert len(net)==28 and net[:12]==g[:12] and mapping[n+31]==n+27
  assert values[-1]&~target==0
  errors=(values[-1]^target).bit_count();tried+=1
  live=set();todo=[n+27]
  while todo:
   w=todo.pop()
   if w<n or w in live:continue
   live.add(w);todo.extend(net[w-n][1:])
  if best is None or (errors,-len(live))<(best['boundary_errors'],-best['live_gate_count']):
   best={'n':n,'size':28,'gates':net,'boundary_errors':errors,'live_gate_count':len(live),'false_positive_rows':0,'deleted_original_gate_indices':deleted,'replacement_sides':side,'missing_edges':[e for e in edges if not(values[-1]>>rows.index((1<<e[0])|(1<<e[1])))&1]}
bad=[]
for left,right in edges:
 profile=[1 if i==left else 2 if i==right else 0 for i in range(n)]
 vals=[i in(left,right) for i in range(n)]
 for op,a,b in best['gates']:
  vals.append(vals[a] or vals[b] if op else vals[a] and vals[b])
  profile.append(profile[a]|profile[b] if op else (4 if ((profile[a]&1 and profile[b]&2)or(profile[a]&2 and profile[b]&1))else 0))
 if vals[-1] and not profile[-1]&4:bad.append([left,right])
best['accepted_without_read1']=bad
best.update({'scope':'best over four OR deletions in free suffix of this exact32 seed only','candidate_valid':best['boundary_errors']==0,'variants_evaluated':tried,'elapsed_seconds':time.monotonic()-started})
(p/'reused28-prefix12-near-hint-2056.json').write_text(json.dumps(best,indent=2))
print(json.dumps({k:v for k,v in best.items() if k!='gates'}))
