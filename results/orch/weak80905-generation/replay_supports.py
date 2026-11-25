from pathlib import Path
import sys
import json
base=Path(sys.argv[1]);base.mkdir(parents=True,exist_ok=True)
x=json.loads(Path(__file__).with_name('complete-fixture-80905.json').read_text())
lines=['import Weak80905Data','','namespace PEqualNP.Outside.L_meta_2373.Weak80905','open Live1024 CountVector','']
for nodeid,dim,depth in [(76616,13,1),(80905,12,2)]:
 n=x['nodes'][str(nodeid)];state=n['node']['state'];roots=n['basis']['roots'];supports=[state.index(s) for s in roots]
 childlists=[];valuelists=[]
 for edge in n['children']:
  i=edge['entry'];kid=x['nodes'][str(edge['child'])];avail={}
  for r,s in enumerate(state):
   if r!=supports[i]:avail.setdefault(s,[]).append(f'Sum.inl {r}')
  avail.setdefault(roots[i],[]).extend(['Sum.inr false','Sum.inr true'])
  ls=[avail[s].pop(0) for s in kid['node']['state']];assert all(not a for a in avail.values())
  childlists.append(ls);valuelists.append(['s'+str(s) for s in kid['node']['state']])
 lines += [f'def support{nodeid} : Fin 11 → Finset (Fin {dim}) := !['+', '.join('{'+str(s)+'}' for s in supports)+']',f'lemma support_counts{nodeid} : ∀ i : Fin 11, count tag{nodeid} (support{nodeid} i) = unit i := by','  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel','',f'def childLabels{nodeid} : Fin 11 → List (Sum (Fin {dim}) Bool) := ![',',\n'.join('  ['+', '.join(ls)+']' for ls in childlists),']',f'def childWs{nodeid} : Fin 11 → List Sig := ![',',\n'.join('  ['+', '.join(ls)+']' for ls in valuelists),']','',f'lemma childLabels_nodup{nodeid} : ∀ i : Fin 11, (childLabels{nodeid} i).Nodup := by decide +kernel',f'lemma childLabels_basis{nodeid} : ∀ i : Fin 11, (childLabels{nodeid} i).toFinset =',f'    duplicateRoots Finset.univ (support{nodeid} i) := by decide +kernel',f'lemma childLabels_values{nodeid} : ∀ i : Fin 11,',f'    (childLabels{nodeid} i).map (duplicateRaw (fun r => signal (tag{nodeid} r)) (signal i)) = childWs{nodeid} i := by','  decide +kernel',f'lemma childLabels_size{nodeid} : ∀ i : Fin 11,',f'    (duplicateRoots Finset.univ (support{nodeid} i)).card + {depth} ≤ 15 := by decide +kernel','']
state=x['nodes']['76616']['node']['state'];sup=[state.index(8),state.index(13864)]
labels=[f'Sum.inl {r}' for r in range(len(state)) if r not in sup]+['Sum.inr false']
lines += ['def gateSupport : Finset (Fin 13) := {'+', '.join(map(str,sup))+'}', 'def gateVector : Fin 11 → Nat := fun j => unit 7 j + unit 10 j','def gateValue : Fin 2 → Sig := ![s29951, s15934]', 'def gateLabels : List (Sum (Fin 13) Bool) := ['+', '.join(labels)+']','', 'lemma gateSupport_counts : count tag76616 gateSupport = gateVector := by','  funext j; fin_cases j <;> decide +kernel','lemma gate_table : cuts76616 = List.ofFn (fun i : Fin 2 => (gateVector, gateValue i)) := by decide +kernel','lemma gateLabels_nodup : gateLabels.Nodup := by decide +kernel','lemma gateLabels_basis : gateLabels.toFinset = compressRoots Finset.univ gateSupport := by decide +kernel','lemma gateLabels_size : (compressRoots Finset.univ gateSupport).card + 2 ≤ 14 := by decide +kernel','','end PEqualNP.Outside.L_meta_2373.Weak80905','']
(base/'Weak80905Supports.lean').write_text('\n'.join(lines));print(len('\n'.join(lines).encode()))
