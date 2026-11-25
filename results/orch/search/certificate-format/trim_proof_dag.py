"""Root-reachable DAG of completed computational exclusions, before Lean checking."""
import hashlib,json
from collections import Counter,defaultdict
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-87/library_route')
files={'part1':BASE/'signed17-oredge-trace.jsonl','part2':BASE/'signed17-oredge-part2.jsonl'}
children={};done={};resume={};hashes={};sizes={}
for part,path in files.items():
 ch=defaultdict(list);ds={};rs={};h=hashlib.sha256();current_source=None
 with path.open('rb')as f:
  for raw in f:
   h.update(raw);x=json.loads(raw);event=x['event']
   if event=='node'and x['parent']:ch[x['parent']].append(x['id'])
   elif event=='done':ds[x['id']]=(x['kind'],x['a'])
   elif event=='resume_header':current_source=x['sha256']
   elif event=='resume':rs[x['id']]=(current_source,x['source_node'])
 children[part]=ch;done[part]=ds;resume[part]=rs;hashes[part]=h.hexdigest();sizes[part]=len(ds)
byhash={v:k for k,v in hashes.items()};todo=[('part2',1)];seen=set();counts=Counter();links=0
while todo:
 part,index=todo.pop()
 if(part,index)in seen:continue
 seen.add((part,index));kind,arg=done[part][index];counts[kind]+=1
 assert kind not in('open','found'),(part,index,kind)
 if kind=='expand':todo.extend((part,j)for j in children[part][index]);links+=len(children[part][index])
 elif kind=='memo':
  if arg<0:source,j=resume[part][arg];todo.append((byhash[source],j))
  else:todo.append((part,arg))
  links+=1
selected={p:sorted(i for q,i in seen if q==p)for p in files};summary=dict(root=['part2',1],trace_sha256=hashes,total_visited=sizes,reachable={p:len(v)for p,v in selected.items()},kinds=dict(counts),dependency_edges=links,pending_formula_leaves=counts['formula0']+counts['formula1'],note='Computational dependency DAG; formula leaves and final Lean embedding remain pending')
(BASE/'signed17-oredge-dag.json').write_text(json.dumps(dict(summary=summary,node_ids=selected),separators=(',',':'))+'\n')
(BASE/'signed17-oredge-dag-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
