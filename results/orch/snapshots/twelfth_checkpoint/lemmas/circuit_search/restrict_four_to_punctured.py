"""Finite arc relabeling/restriction of archived sufficient four-owner phases."""
import itertools,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
old=json.loads((HERE/'joint-four-owner-packet.json').read_text())[0]
new=json.loads((HERE.parent/'status_review'/'punctured-four-arc.json').read_text())
compact=runpy.run_path(str(HERE.parent/'algebra_strategy'/'assemble_five_owner.py'))['compact_core']
old_raw=old['raw_inputs'];n=new['available_inputs'];raw=new['raw_inputs']
new_lines={}
for line in range(13,26):
 support=frozenset(i for i,p in enumerate(new['owners']) if (p+line-13)%13 in [0,1,3,9])
 if support:new_lines[support]=line
old_line_support={i:frozenset(j for j,p in enumerate(old['group']) if (p+line-13)%13 in [0,1,3,9]) for i,line in enumerate(old['input_original']) if i>=4}
supports=[1<<i for i in range(raw)]+[sum(1<<j for j in s) for s in new['features']]
free={s:i for i,s in enumerate(supports)}
columns=[int(('1'*(1<<i)+'0'*(1<<i))*(1<<(raw-i-1)),2) for i in range(raw)]
for s in new['features']:
 v=0
 for i in s:v|=columns[i]
 columns.append(v)
target=0
for a,b in new['edges']:target|=columns[a]&columns[b]
allmask=(1<<(1<<raw))-1
sources=[]
for name in ['joint-four-multiguard-seeds.json','joint-four-five-seeds.json','joint-four-priority-pool.json','joint-four-priority-final.json']:
 path=HERE/name
 if not path.exists():continue
 data=json.loads(path.read_text())
 if data and isinstance(data[0],list) and isinstance(data[0][0],int):data=[data]
 for i,x in enumerate(data):sources.append((name,i,x['gates'] if isinstance(x,dict) else x))
print('sources',len(sources),flush=True)
seen=set();accepted=[];trials=0
for name,idx,gs in sources:
 for perm in itertools.permutations(range(4)):
  trials+=1;rawmap=list(perm)
  for i in range(4,old_raw):
   line=new_lines[frozenset(perm[j] for j in old_line_support[i])]
   rawmap.append(-1 if line==new['punctured_line'] else new['raw_map'].index(line))
  g=[];memo={};wire_support=supports.copy();mapping=rawmap.copy()
  def add(op,a,b):
   if a<0 or b<0:return max(a,b) if op else -1
   if a==b:return a
   s=wire_support[a]|wire_support[b] if op and wire_support[a] and wire_support[b] else 0
   if s in free:return free[s]
   a,b=sorted((a,b));key=(op,a,b)
   if key not in memo:memo[key]=n+len(g);g.append([op,a,b]);wire_support.append(s)
   return memo[key]
  for f in old['features']:
   root=-1
   for i in f['raw_indices']:root=add(1,root,rawmap[i])
   mapping.append(root)
  for op,a,b in gs:mapping.append(add(op,mapping[a],mapping[b]))
  if mapping[-1]<0:continue
  g,output,_=compact(n,g,mapping[-1]);assert output==n+len(g)-1
  used={output}
  for j in range(len(g)-1,-1,-1):
   if n+j in used:used.update(g[j][1:])
  extra=sum(max(0,sum(i in used for i in group)-1) for group in new['optional_groups'])
  ands=sum(op==0 for op,_,_ in g)
  if len(g)+extra>15 or ands<5:continue
  key=json.dumps(g)
  if key in seen:continue
  seen.add(key);v=columns.copy()
  for op,a,b in g:v.append(v[a]|v[b] if op else v[a]&v[b])
  assert target&~v[-1]==0 and all(not(v[-1]>>m&1) for m in [15,((1<<raw)-1)^15]+[1<<i for i in range(raw)])
  errors=sum(v[-1]>>m&1 for m in new['maximal_negatives'])
  accepted.append(dict(gates=g,output=output,source=name,source_index=idx,owner_permutation=perm,gate_count=len(g),prefix_extra=extra,effective_cost=len(g)+extra,and_count=ands,boundary_errors=errors,false_positives=(v[-1]&~target&allmask).bit_count(),false_negatives=0,raw_assignments=1<<raw))
accepted.sort(key=lambda x:(x['boundary_errors'],x['effective_cost']))
(HERE/'punctured-four-restricted-seeds.json').write_text(json.dumps(accepted))
report=dict(trials=trials,accepted=len(accepted),best_errors=accepted[0]['boundary_errors'] if accepted else None)
(HERE/'punctured-four-restricted-seeds-report.json').write_text(json.dumps(report,indent=2));print(report,flush=True)
