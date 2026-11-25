from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/andcount2056')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
edges=[(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in {0,1,3,9}];positives=[(1<<p)|(1<<l) for p,l in edges];negative=set()
for points in range(8192):
 lines=sum(1<<l for l in range(13) if all(not(points>>p&1) or (p+l)%13 not in {0,1,3,9} for p in range(13)))
 closed=sum(1<<p for p in range(13) if all(not(lines>>l&1) or (p+l)%13 not in {0,1,3,9} for l in range(13)))
 if closed==points:negative.add(points|(lines<<13))
rows=positives+sorted(negative);target=(1<<52)-1;reports=[]
for stem,mode in [('final-native16-control67','native'),('final-native16-star64-negative','negative_phase'),('final-target16-nested','target_phase')]:
 pre=base/stem;m=json.loads(pre.with_suffix('.mapping.json').read_text());meta=json.loads(pre.with_suffix('.json').read_text());assert m['rows']==rows
 with pre.with_suffix('.cnf').open('rb') as f:h=f.readline().split();nv,nc=map(int,h[2:])
 assign={i:False for i in range(1,nv+1)}
 if mode=='native':
  assign={};sat=False
  for line in pre.with_suffix('.sol').read_text().splitlines():
   if line.startswith('s '):sat=line=='s SATISFIABLE'
   if line.startswith('v '):
    for x in map(int,line.split()[1:]):
     if x:assert abs(x) not in assign or assign[abs(x)]==(x>0);assign[abs(x)]=x>0
  assert sat and set(assign)==set(range(1,nv+1))
 true_tokens={str(v if b else -v).encode() for v,b in assign.items()};all_false=not any(assign.values());fails=[]
 with pre.with_suffix('.cnf').open('rb') as f:
  f.readline()
  for count,line in enumerate(f,1):
   xs=line.split();assert xs[-1]==b'0'
   if not (b'-' in line if all_false else any(x in true_tokens for x in xs[:-1])):fails.append((count,list(map(int,xs[:-1]))))
 assert count==nc
 flip=set(m['flipped_variables']);truth=lambda v:assign[v]^(v in flip)
 vals=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)];records=[]
 for j,(ls,rs) in enumerate(zip(m['left'],m['right'])):
  L=[i for i,v in enumerate(ls) if truth(v)];R=[i for i,v in enumerate(rs) if truth(v)];a=b=0
  for i in L:a|=vals[i]
  for i in R:b|=vals[i]
  y=a&b;vals.append(y);records.append({'left':L,'right':R})
  for k,v in enumerate(m['values'][j]):assert truth(v)==bool(y>>k&1)
 outputs=[j for j,v in enumerate(m['output']) if truth(v)];out=0
 for j in outputs:out|=vals[26+j]
 model={'ands':records,'output':outputs};saved=json.loads(pre.with_suffix('.and-model.json' if mode=='native' else '.warm.json').read_text());assert model==saved
 A=sum(bool(r['left']) for r in records);M=sum(len(r['left'])+len(r['right']) for r in records)+len(outputs);assert all(bool(r['left'])==bool(r['right']) for r in records);assert M-A-1<=meta['ordinary_limit']
 missing=[k for k,(p,l) in enumerate(edges) if not any((p in records[j]['left'] and l in records[j]['right']) or (l in records[j]['left'] and p in records[j]['right']) for j in outputs)]
 selected=[k for k,v in enumerate(m['nonread_witness']) if truth(v)]
 assert all(k in missing for k in selected)
 bad=[(j,a,b) for j,rec in enumerate(records) for a in rec['left'] if a<26 for b in rec['right'] if b<26 and tuple(sorted((a,b))) not in {tuple(sorted(e)) for e in edges}]
 encoded_bad=[(j,a,b) for j,a,b,var in m['bad_primary_crossings'] if truth(var)];assert bad==encoded_bad and A>=13
 extra={'bad_primary_crossings':bad}
 if mode=='native':
  assert not fails and out==target and selected and bad
  for suffix in ['.ordinary.json','.literal.json']:
   net=json.loads(pre.with_suffix(suffix).read_text());v=vals[:26]
   for j,(op,a,b) in enumerate(net['gates']):assert op in(0,1) and 0<=a<26+j and 0<=b<26+j;v.append(v[a]|v[b] if op else v[a]&v[b])
   assert v[net['output']]==target and len(net['gates'])<=M-A-1
   misses=[]
   for k,(p,l) in enumerate(edges):
    counts=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(26)]
    for op,a,b in net['gates']:
     counts.append(counts[a]|counts[b] if op else {(min(2,x+u),min(2,y+w)) for x,y in counts[a] for u,w in counts[b]})
    if (1,1) not in counts[net['output']]:misses.append(k)
   if suffix=='.literal.json':assert misses==missing
   extra[suffix]={'gates':len(net['gates']),'ANDs':sum(op==0 for op,a,b in net['gates']),'missing_read1':misses}
 elif mode=='negative_phase':
  assert out==target and missing==selected==bad==[] and len(fails)==2
  expected=[[-v if v in flip else v for v in m['nonread_witness']],[-v if v in flip else v for j,a,b,v in m['bad_primary_crossings']]];assert [c for i,c in fails]==expected
  assert 's UNSATISFIABLE' in pre.with_suffix('.sol').read_text()
 else:
  assert (out^target).bit_count()==6 and (out>>52)==0 and len(fails)==6 and selected and bad
 reports.append({'prefix':stem,'mode':mode,'variables':nv,'clauses_checked':count,'unsatisfied_phase_clauses':[{'index':i,'width':len(c),'clause_sha256':hashlib.sha256(json.dumps(c).encode()).hexdigest()} for i,c in fails],'active_AND_records':A,'memberships':M,'literal_cost_bound':M-A-1,'missing_positive_indices':[k for k in range(52) if not(out>>k&1)],'false_positives':(out>>52).bit_count(),'selected_nonread_witnesses':selected,'literal_split_missing_read1':missing,'circuits':extra,'cnf_sha256':digest(pre.with_suffix('.cnf'))})
r={'status':'APPROVED final source7bc8492e actual native positive, fixed negative and K16 target phase; no target witness','source_sha256':digest(base/'andcount_budget_final2056.py'),'reports':reports}
p=Path('/tmp/oec/pequalnp-pilot-121/budget-final-native-independent-review.json');p.write_text(json.dumps(r,indent=2)+'\n');print(p.read_text())
