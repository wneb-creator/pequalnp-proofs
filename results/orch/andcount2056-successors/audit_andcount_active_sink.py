from pathlib import Path
import hashlib,json
base=Path('/tmp/oec/pequalnp-pilot-121/andcount2056')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
edges=[(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in {0,1,3,9}]
positives=[(1<<p)|(1<<l) for p,l in edges];negative=set()
for points in range(1<<13):
 lines=sum(1<<l for l in range(13) if all(not(points>>p&1) or (p+l)%13 not in {0,1,3,9} for p in range(13)))
 closed=sum(1<<p for p in range(13) if all(not(lines>>l&1) or (p+l)%13 not in {0,1,3,9} for l in range(13)))
 if closed==points:negative.add(points|(lines<<13))
rows=positives+sorted(negative);assert len(rows)==756 and len(set(rows))==756
P=(1<<52)-1;reports=[]
for name in ['active-sink-native13-free1','active-sink-control13-forced-swap','active-sink-control16-padded']:
 prefix=base/name;saved_prefix=base/('active-anchor-native16-padded' if '16-padded' in name else name);m=json.loads(prefix.with_suffix('.mapping.json').read_text());assert m['rows']==rows
 with prefix.with_suffix('.cnf').open('rb') as f:header=f.readline().split();variables,clauses=map(int,header[2:])
 assignment={};sat=False
 for line in saved_prefix.with_suffix('.sol').read_text().splitlines():
  if line.startswith('s '):sat=line=='s SATISFIABLE'
  if line.startswith('v '):
   for x in map(int,line.split()[1:]):
    if x:assert abs(x) not in assignment or assignment[abs(x)]==(x>0);assignment[abs(x)]=x>0
 assert sat and set(assignment)==set(range(1,variables+1))
 true_tokens={str(v if b else -v).encode() for v,b in assignment.items()};checked=0
 with prefix.with_suffix('.cnf').open('rb') as f:
  f.readline()
  for line in f:
   xs=line.split();assert xs[-1]==b'0' and any(x in true_tokens for x in xs[:-1]);checked+=1
 assert checked==clauses
 flipped=set(m['flipped_variables']);truth=lambda x:assignment[x]^(x in flipped)
 values=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)];records=[];active=[]
 for j,(ls,rs) in enumerate(zip(m['left'],m['right'])):
  left=[i for i,x in enumerate(ls) if truth(x)];right=[i for i,x in enumerate(rs) if truth(x)];assert not set(left)&set(right)
  a=b=0
  for i in left:a|=values[i]
  for i in right:b|=values[i]
  value=a&b;values.append(value);live=bool(value&P);active.append(live);assert truth(m['active'][j])==live
  if not live:assert left==right==[]
  assert all(i<26 or active[i-26] for i in left+right)
  for k,var in enumerate(m['values'][j]):assert truth(var)==bool(value>>k&1)
  records.append({'left':left,'right':right})
 assert active==sorted(active,reverse=True) and sum(active)>=10
 assert 0 in records[0]['left'] and 13 in records[0]['right']
 outputs=[i for i,x in enumerate(m['output']) if truth(x)];assert all(active[i] for i in outputs);out=0
 for j in outputs:
  for k in range(j+1,len(records)):assert 26+j not in records[k]['left']+records[k]['right']
 for i in outputs:out|=values[26+i]
 assert out==P
 saved=json.loads(saved_prefix.with_suffix('.and-model.json').read_text());assert saved=={'ands':records,'output':outputs}
 net=json.loads(saved_prefix.with_suffix('.ordinary.json').read_text());vals=values[:26]
 for j,(op,a,b) in enumerate(net['gates']):assert op in(0,1) and 0<=a<26+j and 0<=b<26+j;vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
 assert vals[net['output']]==P
 if 'forced-swap' in name:
  assert 12 not in records[12]['left'];fixed=json.loads((base/'active-sink-native13-free1.and-model.json').read_text());assert records[:12]==fixed['ands'][:12] and records[12]!=fixed['ands'][12]
 reports.append({'prefix':name,'variables':variables,'clauses_checked':checked,'active_records':sum(active),'ordinary_gates':len(net['gates']),'ordinary_ANDs':sum(op==0 for op,a,b in net['gates']),'boundary_errors':0,'model_sha256':digest(saved_prefix.with_suffix('.sol'))})

old=base/'active-anchor-target12-v2';new=base/'active-sink-target12'
om=json.loads(old.with_suffix('.mapping.json').read_text());nm=json.loads(new.with_suffix('.mapping.json').read_text());assert om==nm
with old.with_suffix('.cnf').open('rb') as f:oh=f.readline().split();oldlines=f.read().splitlines()
with new.with_suffix('.cnf').open('rb') as f:nh=f.readline().split();newlines=f.read().splitlines()
assert oh[2]==nh[2] and int(nh[3])-int(oh[3])==132
assert newlines[:len(oldlines)-2]==oldlines[:-2] and newlines[-2:]==oldlines[-2:]
flipped=set(nm['flipped_variables'])
def rename(v):return -v if abs(v) in flipped else v
expected=[]
for j in range(12):
 for k in range(j+1,12):
  for side in ('left','right'):
   expected.append(' '.join(map(str,[rename(-nm['output'][j]),rename(-nm[side][k][26+j]),0])).encode())
assert newlines[len(oldlines)-2:-2]==expected
violations=[i+1 for i,line in enumerate(newlines) if not any(int(x)<0 for x in line.split()[:-1])]
assert len(violations)==4 and max(violations)<len(oldlines)-2
report={'scope':'Independent sink source/control artifact audit. K12 target is known impossible by existing L1898; infrastructure only, not a launch recommendation or target witness.','source_sha256':digest(base/'andcount_active_sink2056.py'),'controls':reports,'padded16_model_origin':'Replay of existing actual anchor native16 model against new sink clauses; no native rerun','target_added_clauses':132,'target_old_clauses_preserved':len(oldlines),'target_phase_violations':violations,'target_sha256':digest(new.with_suffix('.cnf'))}
p=Path('/tmp/oec/pequalnp-pilot-121/andcount-active-sink-independent-review.json');p.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
