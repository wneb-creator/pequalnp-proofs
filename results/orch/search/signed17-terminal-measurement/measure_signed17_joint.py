from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json

base=Path(__file__).resolve().parent
out=base/'signed17-joint-measurement';out.mkdir(exist_ok=True)
paths={'part1':base/'signed17-oredge-trace.jsonl','edge':base/'signed17-oredge-part2.jsonl','nonedge':base/'signed17-ornonedge-trace.jsonl'}
done={};children={};resume={};hashes={}
for part,path in paths.items():
 ds={};ch=defaultdict(list);rs={};source=None;digest=hashlib.sha256()
 for raw in path.open('rb'):
  digest.update(raw);e=json.loads(raw)
  if e['event']=='node' and e['parent']:ch[e['parent']].append(e['id'])
  elif e['event']=='done':ds[e['id']]=(e['kind'],e['a'])
  elif e['event']=='resume_header':source=e['sha256']
  elif e['event']=='resume':rs[e['id']]=(source,e['source_node'])
 done[part]=ds;children[part]=ch;resume[part]=rs;hashes[part]=digest.hexdigest()
byhash={h:p for p,h in hashes.items()}
def dependency(part,node):
 kind,arg=done[part][node]
 if kind=='expand':return [(part,c) for c in children[part][node]]
 if kind=='memo':
  if arg>0:return [(part,arg)]
  h,c=resume[part][arg];return [(byhash[h],c)]
 return []
def reach(root):
 todo=[root];seen=set()
 while todo:
  p,n=todo.pop()
  if (p,n) in seen:continue
  seen.add((p,n));assert done[p][n][0] not in ('open','found')
  todo.extend(dependency(p,n))
 return seen
reached={part:reach((part,1)) for part in ['edge','nonedge']}
joint=set.union(*reached.values())
needed={p:{n for q,n in joint if p==q and done[q][n][0] in ('expand','formula0','formula1')} for p in paths}
states={};signals={};headers={}
for part,path in paths.items():
 stack=[];ss={}
 for line in path.open():
  e=json.loads(line);kind=e['event']
  if kind=='header':headers[part]=e
  elif kind=='node':
   stack.append(e)
   if e['id'] in needed[part]:
    states[part,e['id']]=dict(part=part,node=e['id'],kind=done[part][e['id']][0],remaining=e['remaining'],state=e['state'],history=[x['step'][:4] for x in stack],roots=[p for p,s in reached.items() if (part,e['id']) in s])
  elif kind=='done':
   assert stack[-1]['id']==e['id'];stack.pop()
  elif kind=='signal':ss[e['id']]=e['hex']
 signals[part]=ss
 assert not stack
signature_ids={};words=[]
def wordid(word):
 if word not in signature_ids:signature_ids[word]=len(words);words.append(word)
 return signature_ids[word]
records=[];leaf_keys={}
for key,rec in sorted(states.items()):
 part=rec['part'];rec['state']=[wordid(signals[part][x]) for x in rec['state']]
 rec['history']=[[d,wordid(signals[part][a]),wordid(signals[part][b]),wordid(signals[part][z])] for d,a,b,z in rec['history']]
 rec['state'].sort()
 if rec['kind'].startswith('formula'):
  leaf_key=(rec['remaining'],tuple(rec['state']))
  rec['exact_duplicate_of']=leaf_keys.get(leaf_key)
  leaf_keys.setdefault(leaf_key,[rec['part'],rec['node']])
 records.append(rec)
summary=dict(trace_sha256=hashes,total_visited={p:len(ds) for p,ds in done.items()},
 roots={p:dict(reachable=len(s),kinds=dict(Counter(done[q][n][0] for q,n in s))) for p,s in reached.items()},
 joint=dict(reachable=len(joint),kinds=dict(Counter(done[p][n][0] for p,n in joint))),
 proof_states=len(records),truth_functions=len(words),exact_distinct_formula_states=len(leaf_keys),
 scope='Structural root-reachable computational DAG and exact truth-bank census, not a Lean replay. Formula certificates remain obligations.')
(out/'leaf-banks.json').write_text(json.dumps(dict(summary=summary,signals=words,banks=[r for r in records if r['kind'].startswith('formula')]),separators=(',',':'))+'\n')
(out/'proof-states.json').write_text(json.dumps(dict(summary=summary,signals=words,states=records),separators=(',',':'))+'\n')
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
