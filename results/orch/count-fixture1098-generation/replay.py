from pathlib import Path
import hashlib,json,sys
src=Path(__file__).with_name('proof-smoke-node1098.json')
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
x=json.loads(src.read_text());entries=x['entries'];basis=x['basis'];total=basis['total'];m=len(total)
values={int(k):int(v,16)for k,v in x['signals'].items()};allbits=(1<<1024)-1
assert len(x['node']['state'])==sum(total)==16 and m==12
assert [x['node']['state'].count(k)for k in basis['roots']]==total
lookup={(tuple(e['counts']),values[e['signal']])for e in entries}
cutentries=[]
for cut in x['subtree_cuts']:
 a,b=entries[cut['left']],entries[cut['right']]
 counts=tuple(c+d for c,d in zip(a['counts'],b['counts']))
 v=values[a['signal']]&values[b['signal']]if cut['op']==0 else values[a['signal']]|values[b['signal']]
 assert v==values[cut['signal']]
 assert cut['remaining']==x['node']['remaining']-sum(counts)+1
 cutentries.append((counts,cut['signal']))
cutlookup={(c,values[s])for c,s in cutentries}
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target=lambda r:any((r>>a&1)and(r>>b&1)for a,b in E)
positive=[(1<<a)|(1<<b)for a,b in E]
negative=[r for r in range(1024)if not target(r)and all((r>>i&1)or target(r|1<<i)for i in range(10))]
pairs=[(p,n)for p in positive for n in negative]
separates=lambda v,p,n:bool(v>>p&1)and not(v>>n&1)
obligations=[];kept=cuts=0
for a in entries:
 for b in entries:
  c=tuple(x+y for x,y in zip(a['counts'],b['counts']))
  av,bv=values[a['signal']],values[b['signal']]
  if any(x>y for x,y in zip(c,total))or av==bv:continue
  for op in [0,1]:
   z=av&bv if op==0 else av|bv
   if z in [0,allbits,av,bv]:continue
   if (c,z)in lookup:kept+=1;continue
   if (c,z)in cutlookup:cuts+=1;continue
   candidates={i for i,(p,n)in enumerate(pairs)if not separates(z,p,n)and all(c[j]>=total[j]or not separates(values[s],p,n)for j,s in enumerate(basis['roots']))}
   assert candidates,(a['index'],b['index'],op)
   obligations.append(candidates)
left=set(range(len(obligations)));selected=[]
while left:
 ix=max(range(len(pairs)),key=lambda i:sum(i in obligations[j]for j in left))
 cover={j for j in left if ix in obligations[j]};assert cover
 selected.append(ix);left-=cover
rows=[pairs[i]for i in selected]
vec=lambda xs:'!['+', '.join(map(str,xs))+']'
lines=['import CountTableChecker','','namespace PEqualNP.Outside.L_meta_2373.CountFixture1098','open Live1024 CountVector','']
for sid in sorted(values):lines.append(f'def s{sid} : Sig := {hex(values[sid])}')
lines+=['',f'def total : Fin {m} → Nat := {vec(total)}',f'def signal : Fin {m} → Sig := {vec(["s"+str(s)for s in basis["roots"]])}']
lines.append(f'def entries : List (CountEntry {m}) := [')
lines.append(',\n'.join('  ('+vec(e['counts'])+', s'+str(e['signal'])+')'for e in entries)+']')
lines.append(f'def cuts : List (CountEntry {m}) := [')
lines.append(',\n'.join('  ('+vec(c)+', s'+str(s)+')'for c,s in cutentries)+']')
lines.append('def rows : List (Row × Row) := [')
lines.append(',\n'.join(f'  (⟨{p}, by decide⟩, ⟨{n}, by decide⟩)'for p,n in rows)+']')
tags=[basis['roots'].index(s)for s in x['node']['state']]
lines += [f'def basisTag : Fin 16 → Fin {m} := {vec(tags)}','',
 'set_option maxRecDepth 16384 in','set_option maxHeartbeats 0 in',
 'lemma checked_gates : countGateCheck false graph total signal entries cuts rows = true := by decide +kernel','',
 'set_option maxRecDepth 16384 in','set_option maxHeartbeats 0 in',
 'lemma checked_leaves : countLeafCheck total signal entries = true := by decide +kernel','',
 'set_option maxRecDepth 16384 in','set_option maxHeartbeats 0 in',
 'lemma missing : (total, graph) ∉ entries := by decide +kernel','',
 'lemma basis_counts : count basisTag (Finset.univ : Finset (Fin 16)) = total := by',
 '  funext j','  fin_cases j <;> decide +kernel','',
 'lemma closed : CountClosed total signal (pairColumn false) (pairColumn false graph)',
 '    (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts) false :=',
 '  countGateCheck_sound checked_gates','',
 'end PEqualNP.Outside.L_meta_2373.CountFixture1098']
lean='\n'.join(lines)+'\n';(out/'CountFixture1098.lean').write_text(lean)
report={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(lean.encode()).hexdigest(),'classes':m,'root_occurrences':16,'remaining':16,'entries':len(entries),'cuts':len(cutentries),'ordered_kept_gates':kept,'ordered_cut_gates':cuts,'row_rejected_gates':len(obligations),'rows':rows,'scope':'Exact finite count-table leaf/closure/missing obligations; cofactor cutSound and depth1 child recurrence remain external.'}
(out/'count-fixture1098-generation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
