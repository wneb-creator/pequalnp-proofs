from pathlib import Path
import sys
import json
base=Path(sys.argv[1]);base.mkdir(parents=True,exist_ok=True)
x=json.loads(Path(__file__).with_name('complete-fixture-20369.json').read_text())
lines=['import Weak20369Data','','namespace PEqualNP.Outside.L_meta_2373.Weak20369','open Live1024 CountVector','']
for nid in [9611,20369]:
 n=x['nodes'][str(nid)];state=n['node']['state'];ids=n['basis']['roots'];es=n['entries'];dim=len(state);num=len(es);depth=n['node']['remaining']-dim
 def support(cs):
  return sorted(r for j,c in enumerate(cs)for r in [r for r,s in enumerate(state)if s==ids[j]][:c])
 supports=[support(e['counts'])for e in es];childlabels=[];childvalues=[];caps=[]
 for edge in n['children']:
  i=edge['entry'];e=es[i];kid=x['nodes'][str(edge['child'])];avail={}
  for r,s in enumerate(state):
   if r not in supports[i]:avail.setdefault(s,[]).append(f'Sum.inl {r}')
  avail.setdefault(e['signal'],[]).extend(['Sum.inr false','Sum.inr true'])
  childlabels.append([avail[s].pop(0)for s in kid['node']['state']]);assert all(not ls for ls in avail.values());childvalues.append(['s'+str(s)for s in kid['node']['state']]);caps.append(kid['node']['remaining'])
 lines += [f'def entryVector{nid} (i : Fin {num}) : Fin 11 → Nat := (entries{nid}.getD i.val ((fun _ => 0), zero)).1',f'def entryValue{nid} (i : Fin {num}) : Sig := (entries{nid}.getD i.val ((fun _ => 0), zero)).2',f'def support{nid} : Fin {num} → Finset (Fin {dim}) := !['+', '.join('{'+', '.join(map(str,s))+'}'for s in supports)+']',f'lemma entry_table{nid} : entries{nid} = List.ofFn (fun i : Fin {num} => (entryVector{nid} i, entryValue{nid} i)) := by decide +kernel',f'lemma support_counts{nid} : ∀ i : Fin {num}, count tag{nid} (support{nid} i) = entryVector{nid} i := by','  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel','',f'def childLabels{nid} : Fin {num} → List (Sum (Fin {dim}) Bool) := ![',',\n'.join('  ['+', '.join(ls)+']'for ls in childlabels),']',f'def childWs{nid} : Fin {num} → List Sig := ![',',\n'.join('  ['+', '.join(ls)+']'for ls in childvalues),']',f'def childCap{nid} : Fin {num} → Nat := !['+', '.join(map(str,caps))+']','',f'lemma childLabels_nodup{nid} : ∀ i : Fin {num}, (childLabels{nid} i).Nodup := by decide +kernel',f'lemma childLabels_basis{nid} : ∀ i : Fin {num}, (childLabels{nid} i).toFinset =',f'    duplicateRoots Finset.univ (support{nid} i) := by decide +kernel',f'lemma childLabels_values{nid} : ∀ i : Fin {num},',f'    (childLabels{nid} i).map (duplicateRaw (fun r => signal{nid} (tag{nid} r)) (entryValue{nid} i)) = childWs{nid} i := by','  decide +kernel',f'lemma childLabels_size{nid} : ∀ i : Fin {num},',f'    (duplicateRoots Finset.univ (support{nid} i)).card + {depth} ≤ childCap{nid} i + 1 := by decide +kernel','']
 if n['cuts']:
  cvecs=[tuple(a+b for a,b in zip(es[c['left']]['counts'],es[c['right']]['counts']))for c in n['cuts']];csupports=[support(cs)for cs in cvecs];glabels=[]
  for s in csupports:glabels.append([f'Sum.inl {r}'for r in range(dim)if r not in s]+['Sum.inr false'])
  lines += [f'def gateVector (i : Fin {len(cvecs)}) : Fin 11 → Nat := (cuts{nid}.getD i.val ((fun _ => 0), zero)).1',f'def gateValue (i : Fin {len(cvecs)}) : Sig := (cuts{nid}.getD i.val ((fun _ => 0), zero)).2',f'def gateSupport : Fin {len(cvecs)} → Finset (Fin {dim}) := !['+', '.join('{'+', '.join(map(str,s))+'}'for s in csupports)+']',f'def gateCap : Fin {len(cvecs)} → Nat := !['+', '.join(str(c['remaining'])for c in n['cuts'])+']',f'def gateLabels : Fin {len(cvecs)} → List (Sum (Fin {dim}) Bool) := ![',',\n'.join('  ['+', '.join(ls)+']'for ls in glabels),']',f'lemma gate_table : cuts{nid} = List.ofFn (fun i : Fin {len(cvecs)} => (gateVector i, gateValue i)) := by decide +kernel',f'lemma gateSupport_counts : ∀ i : Fin {len(cvecs)}, count tag{nid} (gateSupport i) = gateVector i := by','  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel',f'lemma gateLabels_nodup : ∀ i : Fin {len(cvecs)}, (gateLabels i).Nodup := by decide +kernel',f'lemma gateLabels_basis : ∀ i : Fin {len(cvecs)}, (gateLabels i).toFinset = compressRoots Finset.univ (gateSupport i) := by decide +kernel',f'lemma gateLabels_size : ∀ i : Fin {len(cvecs)}, (compressRoots Finset.univ (gateSupport i)).card + {depth+1} ≤ gateCap i + 1 := by decide +kernel','']
lines += ['end PEqualNP.Outside.L_meta_2373.Weak20369','']
(base/'Weak20369Supports.lean').write_text('\n'.join(lines));print(len('\n'.join(lines).encode()))
