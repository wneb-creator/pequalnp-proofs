from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-87/status_review');src=Path('/tmp/oec/pequalnp-pilot-87/library_route/mono18-weak-dag/complete-fixture-20369.json');x=json.loads(src.read_text())
values={int(k):int(v,16) for k,v in x['signals'].items()};mask=(1<<1024)-1
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(r):return any(r>>a&1 and r>>b&1 for a,b in edges)
pairs=[((1<<a)|(1<<b),n)for a,b in edges for n in range(1024)if not target(n)and all(n>>i&1 or target(n|1<<i)for i in range(10))]
def sep(v,p,n):return bool(v>>p&1)and not bool(v>>n&1)
def vec(xs):return '!['+', '.join(map(str,xs))+']'
lines=['import CountTableChecker','import CountDagCheck','import Memo20376','','namespace PEqualNP.Outside.L_meta_2373.Weak20369','open Live1024 CountVector','']
for sid,v in sorted(values.items()):lines.append(f'def s{sid} : Sig := {hex(v)}')
reports=[]
for nid in [9611,20369]:
 n=x['nodes'][str(nid)];es=n['entries'];ids=n['basis']['roots'];total=n['basis']['total'];state=n['node']['state'];cuts=[]
 for c in n['cuts']:
  a,b=es[c['left']],es[c['right']];cs=tuple(i+j for i,j in zip(a['counts'],b['counts']));z=values[a['signal']]&values[b['signal']]if c['op']==0 else values[a['signal']]|values[b['signal']]
  assert z==values[c['signal']];assert c['remaining']==n['node']['remaining']-sum(cs)+1;cuts.append((cs,c['signal']))
 kept={(tuple(e['counts']),values[e['signal']])for e in es};blocked={(cs,values[v])for cs,v in cuts};obs=[];keptcases=cutcases=0
 for a in es:
  for b in es:
   cs=tuple(i+j for i,j in zip(a['counts'],b['counts']));av,bv=values[a['signal']],values[b['signal']]
   if av==bv or any(c>t for c,t in zip(cs,total)):continue
   for op in [0,1]:
    z=av&bv if op==0 else av|bv
    if z in [0,mask,av,bv]:continue
    if(cs,z)in kept:keptcases+=1;continue
    if(cs,z)in blocked:cutcases+=1;continue
    opts={j for j,(p,q)in enumerate(pairs)if not sep(z,p,q)and all(cs[k]>=total[k]or not sep(values[s],p,q)for k,s in enumerate(ids))};assert opts,(nid,a['index'],b['index'],op);obs.append(opts)
 remaining=set(range(len(obs)));chosen=[]
 while remaining:
  best=max(range(len(pairs)),key=lambda j:sum(j in obs[k]for k in remaining));cover={k for k in remaining if best in obs[k]};assert cover;chosen.append(best);remaining-=cover
 rows=[pairs[j]for j in chosen]
 sources=[]
 for e in es:
  if e['left']<0:
   j=ids.index(e['signal']);assert e['counts']==[int(k==j)for k in range(11)];sources.append('Sum.inl '+str(j))
  else:sources.append(f'Sum.inr ({e["left"]}, {e["right"]}, {e["op"]})')
 lines += ['',f'def signal{nid} : Fin 11 → Sig := {vec(["s"+str(s)for s in ids])}',f'def total{nid} : Fin 11 → Nat := {vec(total)}',f'def tag{nid} : Fin {len(state)} → Fin 11 := {vec([ids.index(s)for s in state])}',f'def entries{nid} : List (CountEntry 11) := [',',\n'.join('  ('+vec(e['counts'])+', s'+str(e['signal'])+')'for e in es)+']',f'def cuts{nid} : List (CountEntry 11) := ['+', '.join('('+vec(c)+', s'+str(v)+')'for c,v in cuts)+']',f'def sources{nid} : List (Sum (Fin 11) (Nat × Nat × Nat)) := ['+', '.join(sources)+']',f'def rows{nid} : List (Row × Row) := ['+', '.join(f'(⟨{p}, by decide⟩, ⟨{q}, by decide⟩)'for p,q in rows)+']','',f'lemma checked_provenance{nid} : dagCheck false signal{nid} entries{nid} sources{nid} = true := by decide +kernel','set_option maxRecDepth 16384 in','set_option maxHeartbeats 0 in',f'lemma checked_gates{nid} : countGateCheck false graph total{nid} signal{nid} entries{nid} cuts{nid} rows{nid} = true := by decide +kernel',f'lemma checked_leaves{nid} : countLeafCheck total{nid} signal{nid} entries{nid} = true := by decide +kernel',f'lemma missing{nid} : (total{nid}, graph) ∉ entries{nid} := by decide +kernel',f'lemma counts{nid} : count tag{nid} (Finset.univ : Finset (Fin {len(state)})) = total{nid} := by','  funext j; fin_cases j <;> decide +kernel']
 reports.append({'node':nid,'entries':len(es),'cut_records':len(cuts),'kept_cases':keptcases,'cut_cases':cutcases,'row_rejected':len(obs),'rows':rows,'depth':n['node']['remaining']-len(state)+1})
lines += ['','lemma signal9611_memo : signal9611 = Memo20376.priorSignal := by','  funext j; fin_cases j <;> decide +kernel','lemma total9611_memo : total9611 = Memo20376.priorTotal := by decide +kernel','lemma signal20369_memo : signal20369 = Memo20376.sourceSignal := by','  funext j; fin_cases j <;> decide +kernel','','end PEqualNP.Outside.L_meta_2373.Weak20369','']
s='\n'.join(lines);(base/'Weak20369Data.lean').write_text(s);report={'fixture_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(s.encode()).hexdigest(),'nodes':reports,'scope':'Two concrete finite closure/provenance tables and memo signal/count identity; Run cuts and node completion remain separate.'};(base/'weak20369-generation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
