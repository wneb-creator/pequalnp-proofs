from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-87/status_review')
source=Path('/tmp/oec/pequalnp-pilot-87/library_route/mono18-weak-dag/complete-fixture-80905.json')
x=json.loads(source.read_text());vals={int(k):int(v,16) for k,v in x['signals'].items()};mask=(1<<1024)-1
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(r):return any(r>>a&1 and r>>b&1 for a,b in edges)
positive=[(1<<a)|(1<<b) for a,b in edges]
negative=[r for r in range(1024) if not target(r) and all(r>>j&1 or target(r|1<<j) for j in range(10))]
pairs=[(p,n) for p in positive for n in negative]
def sep(v,p,n):return bool(v>>p&1) and not bool(v>>n&1)
def vec(xs):return '!['+', '.join(map(str,xs))+']'
lines=['import CountTableChecker','import CountDagCheck','','namespace PEqualNP.Outside.L_meta_2373.Weak80905','open Live1024 CountVector','']
for sid,v in sorted(vals.items()):lines.append(f'def s{sid} : Sig := {hex(v)}')
ids=x['nodes']['76616']['basis']['roots'];assert ids==x['nodes']['80905']['basis']['roots']
lines += ['',f'def signal : Fin 11 → Sig := {vec(["s"+str(s) for s in ids])}',
'def unit (i : Fin 11) : Fin 11 → Nat := fun j => if i = j then 1 else 0',
'def entries : List (CountEntry 11) := List.ofFn (fun i : Fin 11 => (unit i, signal i))',
'def sources : List (Sum (Fin 11) (Nat × Nat × Nat)) := List.ofFn (fun i : Fin 11 => Sum.inl i)',
'lemma checked_provenance : dagCheck false signal entries sources = true := by decide +kernel','']
reports=[]
for nodeid in [76616,80905]:
 node=x['nodes'][str(nodeid)];es=node['entries'];total=node['basis']['total'];state=node['node']['state'];assert all(e['signal']==ids[e['index']] and e['counts']==[int(j==e['index']) for j in range(11)] for e in es)
 cuts=[]
 for c in node['cuts']:
  a,b=es[c['left']],es[c['right']];counts=tuple(i+j for i,j in zip(a['counts'],b['counts']))
  z=vals[a['signal']]&vals[b['signal']] if c['op']==0 else vals[a['signal']]|vals[b['signal']]
  assert z==vals[c['signal']]
  cuts.append((counts,c['signal']))
 kept={(tuple(e['counts']),vals[e['signal']]) for e in es};cutset={(c,vals[s]) for c,s in cuts};obligations=[];cutcases=0
 for a in es:
  for b in es:
   cs=tuple(i+j for i,j in zip(a['counts'],b['counts']));av,bv=vals[a['signal']],vals[b['signal']]
   if any(c>t for c,t in zip(cs,total)) or av==bv:continue
   for op in [0,1]:
    z=av&bv if op==0 else av|bv
    if z in [0,mask,av,bv] or (cs,z) in kept:continue
    if (cs,z) in cutset:cutcases+=1;continue
    opts={i for i,(p,n) in enumerate(pairs) if not sep(z,p,n) and all(cs[j]>=total[j] or not sep(vals[s],p,n) for j,s in enumerate(ids))}
    assert opts,(nodeid,a['index'],b['index'],op)
    obligations.append(opts)
 remaining=set(range(len(obligations)));selected=[]
 while remaining:
  k=max(range(len(pairs)),key=lambda k:sum(k in obligations[j] for j in remaining));covers={j for j in remaining if k in obligations[j]};assert covers;selected.append(k);remaining-=covers
 rows=[pairs[k] for k in selected]
 lines += [f'def total{nodeid} : Fin 11 → Nat := {vec(total)}',f'def cuts{nodeid} : List (CountEntry 11) := ['+', '.join('('+vec(c)+', s'+str(s)+')' for c,s in cuts)+']',f'def rows{nodeid} : List (Row × Row) := ['+', '.join(f'(⟨{p}, by decide⟩, ⟨{n}, by decide⟩)' for p,n in rows)+']',f'def tag{nodeid} : Fin {len(state)} → Fin 11 := {vec([ids.index(s) for s in state])}','',
'set_option maxRecDepth 16384 in','set_option maxHeartbeats 0 in',f'lemma checked_gates{nodeid} : countGateCheck false graph total{nodeid} signal entries cuts{nodeid} rows{nodeid} = true := by decide +kernel',
f'lemma checked_leaves{nodeid} : countLeafCheck total{nodeid} signal entries = true := by decide +kernel',f'lemma missing{nodeid} : (total{nodeid}, graph) ∉ entries := by decide +kernel',f'lemma counts{nodeid} : count tag{nodeid} (Finset.univ : Finset (Fin {len(state)})) = total{nodeid} := by','  funext j; fin_cases j <;> decide +kernel','']
 reports.append({'node':nodeid,'row_count':len(rows),'row_rejected':len(obligations),'ordered_cut_cases':cutcases,'rows':rows,'root_occurrences':len(state),'depth':node['node']['remaining']-len(state)+1})
lines+=['end PEqualNP.Outside.L_meta_2373.Weak80905','']
lean='\n'.join(lines);(base/'Weak80905Data.lean').write_text(lean)
report={'fixture_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(lean.encode()).hexdigest(),'reports':reports,'scope':'Exact two finite node tables; cofactor cuts, recursive child and completion-order assembly are separate.'}
(base/'weak80905-generation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
