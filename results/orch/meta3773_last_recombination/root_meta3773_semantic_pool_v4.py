from pathlib import Path
import itertools,json,time,hashlib,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};rows=[]
for p in range(13):
 for l in range(13):
  if (p+l)%13 in D:rows.append(((1<<p)|(1<<(13+l)),True))
for k in range(4):
 for sub in itertools.combinations(range(13),k):
  off=[l for l in range(13) if all((p+l)%13 not in D for p in sub)]
  a=sum(1<<p for p in sub);b=sum(1<<l for l in off)
  rows.extend([(a|(b<<13),False),(b|(a<<13),False)])
assert len(rows)==808
values=[sum(((m>>i)&1)<<t for t,(m,e) in enumerate(rows)) for i in range(26)]
cones=[0]*26;nodes=[None]*26;best={v:i for i,v in enumerate(values)};target=sum(int(e)<<t for t,(m,e) in enumerate(rows));events=[]
def add(op,a,b):
 value=(values[a]|values[b]) if op else (values[a]&values[b]);cone=cones[a]|cones[b];cost=cone.bit_count()+1
 old=best.get(value)
 if old is not None and cones[old].bit_count()<=cost:return old
 i=len(nodes);nodes.append((op,a,b));values.append(value);cones.append(cone|(1<<i));best[value]=i
 if value==target:events.append({'target_cost':cost,'node':i,'seconds':time.monotonic()-start});print(json.dumps(events[-1]),flush=True)
 return i
start=time.monotonic();inputs=[];skipped=[]
for name in (j/'root-meta3773-pool-v4-input-files.txt').read_text().splitlines():
 p=Path(name)
 try:
  raw=p.read_bytes();snap=j/'root-meta3773-pool-v4-inputs';snap.mkdir(exist_ok=True);(snap/(hashlib.sha256(raw).hexdigest()+'.json')).write_bytes(raw);d=json.loads(raw)
  if d.get('input_count',d.get('inputs',26))!=26:continue
  gs=d['gates'];out=d.get('output',d.get('outputs',[None])[0]);assert isinstance(out,int)
  inverse=d.get('operation_convention')=='0=OR,1=AND'
  wires=list(range(26))
  for op,a,b in gs:
   assert op in [0,1] and 0<=a<len(wires) and 0<=b<len(wires)
   wires.append(add(1-op if inverse else op,wires[a],wires[b]))
  actual=values[wires[out]];inputs.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'original_gates':len(gs),'recombined_cost':cones[wires[out]].bit_count(),'errors':(actual^target).bit_count()})
 except (ValueError,KeyError,AssertionError,IndexError) as e:skipped.append({'path':str(p),'reason':type(e).__name__})
print(json.dumps({'pool_nodes':len(nodes),'functions':len(best),'files':len(inputs),'skipped':len(skipped),'best_target':cones[best[target]].bit_count()}),flush=True)
pairs=0;rounds=0
while time.monotonic()-start<55 and rounds<5:
 rounds+=1;oldtarget=cones[best[target]].bit_count();oldn=len(nodes)
 reps=list(dict.fromkeys(best.values()))
 for i in reps:
  if i>=26:
   op,a,b=nodes[i];add(op,best[values[a]],best[values[b]])
 reps=list(dict.fromkeys(best.values()))
 stop=False
 for ii,a in enumerate(reps):
  for b in reps[:ii]:
   pairs+=1
   if pairs%4096==0 and (time.monotonic()-start>55 or len(nodes)>6000):stop=True;break
   ca=cones[a]|cones[b];cost=ca.bit_count()+1
   if cost>70:continue
   for op,value in [(0,values[a]&values[b]),(1,values[a]|values[b])]:
    old=best.get(value)
    if old is not None and cost<cones[old].bit_count():add(op,a,b)
  if stop:break
 print(json.dumps({'round':rounds,'pool_nodes':len(nodes),'pairs':pairs,'target':cones[best[target]].bit_count(),'seconds':time.monotonic()-start}),flush=True)
 if stop or len(nodes)==oldn:break
out=best[target];needed=cones[out];mapping={i:i for i in range(26)};gs=[]
for i in range(26,len(nodes)):
 if needed>>i&1:
  op,a,b=nodes[i];gs.append([op,mapping[a],mapping[b]]);mapping[i]=25+len(gs)
vals=values[:26]
for op,a,b in gs:vals.append((vals[a]|vals[b]) if op else (vals[a]&vals[b]))
assert vals[mapping[out]]==target
result={'scope':'semantic pool heuristic; finite808-row verification only','input_files':inputs,'skipped':skipped,'events':events,'seconds':time.monotonic()-start,'pairs':pairs,'rounds':rounds,'gates':gs,'output':mapping[out],'input_count':26,'size':len(gs),'errors':0,'first_gate':gs[0]}
(j/'root-meta3773-pool-v4-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['seconds','pairs','rounds','size','errors','first_gate']}),flush=True)

# Inspect the cheapest exact target obtained as a genuine final AND of two other functions.
reps=list(best.values());candidate=None
for ii,a in enumerate(reps):
 if values[a]==target:continue
 for b in reps[:ii]:
  if values[b]==target or values[a]&values[b]!=target:continue
  cost=(cones[a]|cones[b]).bit_count()+1
  if candidate is None or cost<candidate[0]:candidate=(cost,a,b)
if candidate is not None:
 cost,a,b=candidate;out=len(nodes);nodes.append((0,a,b));values.append(target);cones.append(cones[a]|cones[b]|(1<<out))
 needed=cones[out];mapping={i:i for i in range(26)};gs=[]
 for i in range(26,len(nodes)):
  if needed>>i&1:
   op,a,b=nodes[i];gs.append([op,mapping[a],mapping[b]]);mapping[i]=25+len(gs)
 vals=values[:26]
 for op,a,b in gs:vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
 assert vals[mapping[out]]==target and len(gs)==cost
 alt={'scope':'Finite808-row exact final-AND alternative, heuristic cost only; not a posted witness unless size/head/Lean checks pass.','input_count':26,'gates':gs,'output':mapping[out],'size':cost,'errors':0,'first_gate':gs[0]}
 (j/'root-meta3773-pool-v4-and-control.json').write_text(json.dumps(alt,indent=2)+'\n');print(json.dumps({'best_genuine_final_AND':cost,'first_gate':gs[0]}),flush=True)

# Bounded two-new-OR/final-AND resynthesis, with exact shared-cone accounting.
start4=time.monotonic();bag={};reps=list(best.values())
for ii,a in enumerate(reps):
 for b in reps[:ii]:
  v=values[a]|values[b]
  if v in [values[a],values[b],target] or v&target!=target:continue
  cone=cones[a]|cones[b]
  if cone.bit_count()>60:continue
  old=bag.get(v)
  if old is None or cone.bit_count()<old[0].bit_count():bag[v]=(cone,a,b)
items=list(bag.items());tries=0;smallest=None;found=None;limited=False
for ii,(va,(ca,a,b)) in enumerate(items):
 for vb,(cb,c,d) in items[:ii]:
  tries+=1
  if tries%4096==0 and (time.monotonic()-start4>15 or tries>2000000):limited=True;break
  if va&vb!=target:continue
  cost=(ca|cb).bit_count()+3
  if smallest is None or cost<smallest:smallest=cost
  if cost<=63:found=(ca|cb,a,b,c,d);break
 if limited or found is not None:break
report={'scope':'Bounded two-new-OR/final-AND heuristic; no minimum-size claim.','new_OR_functions':len(items),'pair_tests':tries,'limited':limited,'smallest_recombination_size':smallest,'seconds':time.monotonic()-start4,'found':found is not None}
if found is not None:
 needed,a,b,c,d=found;mapping={i:i for i in range(26)};gs=[]
 for i in range(26,len(nodes)):
  if needed>>i&1:
   op,u,v=nodes[i];gs.append([op,mapping[u],mapping[v]]);mapping[i]=25+len(gs)
 left=26+len(gs);gs.append([1,mapping[a],mapping[b]]);right=26+len(gs);gs.append([1,mapping[c],mapping[d]]);out=26+len(gs);gs.append([0,left,right])
 vals=values[:26]
 for op,u,v in gs:vals.append(vals[u]|vals[v] if op else vals[u]&vals[v])
 assert vals[out]==target and len(gs)<=63
 report.update(gates=gs,output=out,input_count=26,size=len(gs),errors=0,first_gate=gs[0])
(j/'root-meta3773-two-new-ors-result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='gates'}),flush=True)
