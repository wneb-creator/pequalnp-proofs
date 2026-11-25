from pathlib import Path
import json
BASE=Path('/tmp/oec/pequalnp-pilot-87')
p=BASE/'copy_checker'
d=json.loads((BASE/'library_route/pruned-copy-state-0.json').read_text())
cm=json.loads((p/'pruned-copy-fixture0-cut-map.json').read_text())
vals={s['id']:int(s['hex'],16)for s in d['signals']}
FULL=(1<<1024)-1
pairs=[(a,b)for a in d['positive_rows']for b in d['negative_rows']]
parentcopy={c['child']:c for c in d['nodes'][0]['copies']}
def lab(i,node):
 return str(i) if node==0 else f'(Sum.inl {i})' if i<12 else '(Sum.inr false)' if i==12 else '(Sum.inr true)'
def mask(m,node):
 return '{'+', '.join(lab(i,node)for i in range(14)if m>>i&1)+'}' if m else '∅'
def ls(xs):return '['+', '.join(xs)+']'
def wsreject(pool,pr):
 a,b=pr;return all(not(v>>a&1)or(v>>b&1)for v in pool)
cutby={i:[]for i in range(len(d['nodes']))}
for c in cm:
 src=c['source']
 if src[0]=='omitted':node=d['nodes'][src[1]];e=node['omitted'][src[2]]
 else:
  pn=d['nodes'][src[1]];cp=pn['copies'][src[2]];node=d['nodes'][cp['child']];e=pn['entries'][cp['bridges'][src[3]]['entry']]
 cutby[node['id']].append((c['index'],e['mask'],e['sig']))
out=['import EntryTableAdapters\nimport PrunedCopyFixture0Cuts\n\nnamespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0\n\nabbrev ChildLabel := Sum (Fin 12) Bool\n']
rowdata={}
for n in d['nodes']:
 i=n['id'];typ='Fin 12'if i==0 else'ChildLabel'
 labels=[lab(j,i)for j in range(len(n['raw']))if n['basis']>>j&1]
 out.append(f'\ndef rootLabels{i} : List ({typ}) := {ls(labels)}\ndef roots{i} : Finset ({typ}) := rootLabels{i}.toFinset\n')
 if i==0:out.append('def nodeRaw0 (i : Fin 12) : Sig := '+ls([f's{x}'for x in n['raw']])+'.getD i.val zero\n')
 else:
  e=d['nodes'][0]['entries'][parentcopy[i]['entry']]
  out.append(f'def nodeRaw{i} : ChildLabel → Sig := duplicateRaw nodeRaw0 s{e["sig"]}\n')
 out.append(f'def entries{i} : List (Entry ({typ})) := '+ls([f'({mask(e["mask"],i)}, s{e["sig"]})'for e in n['entries']])+'\n')
 out.append(f'def cuts{i} : List (Entry ({typ})) := '+ls([f'({mask(a,i)}, s{v})'for _,a,v in cutby[i]])+'\n')
 kept={(e['mask'],vals[e['sig']])for e in n['entries']};known={(a,vals[v])for _,a,v in cutby[i]};blocked=[]
 for ei,e in enumerate(n['entries']):
  for f in n['entries'][:ei]:
   A=e['mask']|f['mask'];a=vals[e['sig']];b=vals[f['sig']]
   if e['mask']&f['mask'] or a==b:continue
   for op in range(2):
    z=a&b if op==0 else a|b
    if z in(0,FULL,a,b)or(A,z)in kept or(A,z)in known:continue
    pool=[vals[s]for j,s in enumerate(n['raw'])if n['basis']>>j&1 and not A>>j&1]+[z]
    choices={k for k,pr in enumerate(pairs)if wsreject(pool,pr)}
    assert choices,(i,A,op)
    blocked.append(choices)
 covered=set();chosen=[]
 while len(covered)<len(blocked):
  best=max(range(len(pairs)),key=lambda k:sum(k in opts and j not in covered for j,opts in enumerate(blocked)))
  chosen.append(pairs[best]);covered|={j for j,opts in enumerate(blocked)if best in opts}
 rowdata[i]=dict(rejected=len(blocked),rows=chosen)
 out.append(f'def rows{i} : List (Row × Row) := '+ls([f'({a}, {b})'for a,b in chosen])+'\n')
 for ci,A,v in cutby[i]:
  labels2=[f'(Sum.inl {lab(j,i)})'for j in range(len(n['raw']))if n['basis']>>j&1 and not A>>j&1]+['(Sum.inr false)']
  cap=cm[ci]['cut']['budget'];depth=n['depth']
  out.append(f'\ntheorem budgetCut{ci} : BudgetRunCut (compressRoots roots{i} {mask(A,i)})\n    (duplicateRaw nodeRaw{i} s{v}) false graph {depth} := by\n')
  out.append(f'  apply budgetRunCut_of_list _ _ {ls(labels2)} cutWs{ci} (by decide) (by decide) (by rfl)\n    false graph {depth} {cap} (by decide)\n  exact fun k bound => cutRun{ci} bound\n')
 out.append(f'\ntheorem cutsSound{i} : ∀ A v, (A, v) ∈ cuts{i} →\n    BudgetRunCut (compressRoots roots{i} A) (duplicateRaw nodeRaw{i} v) false graph {n["depth"]} := by\n  intro A v h\n')
 if not cutby[i]:out.append(f'  simp [cuts{i}] at h\n')
 else:
  out.append(f'  simp only [cuts{i}, List.mem_cons, List.not_mem_nil, or_false] at h\n')
  out.append('  rcases h with '+' | '.join('h'+str(k)for k in range(len(cutby[i])))+'\n')
  for k,(ci,_,_)in enumerate(cutby[i]):out.append(f'  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h{k}\n    exact budgetCut{ci}\n')
 for name,prop in [('Leaves',f'entryLeafCheck rootLabels{i} nodeRaw{i} entries{i} = true'),('Gates',f'entryGateCheck false graph rootLabels{i} nodeRaw{i} entries{i} cuts{i} rows{i} = true'),('Missing',f'(roots{i}, graph) ∉ entries{i}')]:
  out.append(f'\nset_option maxRecDepth 10000 in\nset_option maxHeartbeats 0 in\ntheorem checked{name}{i} : {prop} := by\n  decide +kernel\n')
 out.append(f'\ntheorem closed{i} : PrunedGateClosed roots{i} nodeRaw{i} (pairColumn false)\n    (pairColumn false graph) (entryCert entries{i}) false graph {n["depth"]} :=\n  entryGateCheck_sound cutsSound{i} checkedGates{i}\n')
 if i:
  out.append(f'\ntheorem childNode{i} : PrunedNode (pairColumn false) (pairColumn false graph)\n    false graph 0 ChildLabel roots{i} nodeRaw{i} (entryCert entries{i}) :=\n  prunedNode_zero_of_checks rootLabels{i} nodeRaw{i} false graph entries{i} cuts{i} rows{i}\n    cutsSound{i} checkedLeaves{i} checkedGates{i} checkedMissing{i}\n')
out.append('\nend PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0\n')
s=''.join(out);(p/'PrunedCopyFixture0Tables.lean').write_text(s);(p/'fixture0-row-selection.json').write_text(json.dumps(rowdata,indent=2)+'\n')
print('table_bytes',len(s.encode()),'nodes',len(rowdata),'row_counts',[len(rowdata[i]['rows'])for i in rowdata])
