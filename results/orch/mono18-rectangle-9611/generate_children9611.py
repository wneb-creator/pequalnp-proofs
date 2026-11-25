from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;c=p.parent/'mono18-oredge-weak-census';source=p.parent.parent/'library_route/mono18-weak-dag/complete-fixture-20369.json';fixture=json.loads(source.read_text());nodes=[fixture['rectangles'][str(i)] for i in range(9612,9624)]
assert all(n['matrix']==0 for n in nodes)
mat=json.loads((c/'matrices.json').read_text())[0];profiles=json.loads((c/'profiles.json').read_text());locator=json.loads((p/'profile-locator.json').read_text());profile_ids={(v['weight'],v['positive_mask'],v['negative_false_mask'],v['cost']):i for i,v in enumerate(profiles)}
ids=sorted(set().union(*(set(n['state']) for n in nodes)));assert len(ids)==12;index={x:i for i,x in enumerate(ids)};rows=[]
for sid in ids:
 x=int(fixture['signals'][str(sid)],16);pm=sum(((x>>r)&1)<<i for i,r in enumerate(mat['positive_rows']));nm=sum((1-((x>>r)&1))<<i for i,r in enumerate(mat['negative_rows']));costs={n['root_costs'][j] for n in nodes for j,s in enumerate(n['state']) if s==sid};assert len(costs)==1;cost=costs.pop();pid=profile_ids[0,pm,nm,cost];rows.append(dict(signal=sid,hex=hex(x),profile=pid,cost=cost,**locator[str(pid)]))
assert all(sum(rows[index[s]]['cost'] for s in n['state'])==n['cost_sum']<79 for n in nodes)
s='''import Mono18RectangleLookup
import Mono18RectangleBank
import Mono18RectangleLabels
import Mono18RectangleTotals

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle9611

open Live1024 Mono18Rectangle

def signal : Fin 12 → Sig := ![
'''+',\n'.join('  '+r['hex'] for r in rows)+''']

def record : Fin 12 → Nat := !['''+','.join(r['record'] for r in rows)+''']
def labels9611 : Fin 12 → List (Fin 12) := ![
'''+',\n'.join('  ['+','.join(str(index[x]) for x in n['state'])+']' for n in nodes)+''']

def childSignals9611 (i : Fin 12) : List Sig := (labels9611 i).map signal
def childPairs9611 (i : Fin 12) : List (Sig × Nat) :=
  (labels9611 i).map (fun j => (signal j, record j))

lemma record_valid : ∀ i : Fin 12, checkRecord 0 (record i) = true := by
  intro i; fin_cases i
'''+''.join('  · exact certifiedAt_valid '+str(r['block'])+' '+str(r['offset'])+'\n' for r in rows)+'''
lemma support_valid : ∀ i : Fin 12, supportCheck 0 (record i) (signal i) = true := by
  intro i; fin_cases i <;> decide +kernel

lemma cost_gap : ∀ i : Fin 12,
    ((childPairs9611 i).map (fun a => recordCap (matrixWeight 0) a.2)).sum <
      weightTotals.getD (matrixWeight 0) 0 := by
  decide +kernel

lemma gap (i : Fin 12) :
    ((childPairs9611 i).map (fun a => recordCap (matrixWeight 0) a.2)).sum < targetCost 0 := by
  have total := targetCost_eq (0 : Fin 39)
  change targetCost 0 = weightTotals.getD (matrixWeight 0) 0 at total
  rw [total]
  exact cost_gap i

lemma child_cut9611 (i : Fin 12) {k : Nat}
    (cap : k + 1 ≤ (childSignals9611 i).length) :
    ¬ Run false (observe graph) k ((childSignals9611 i).map observe) := by
  intro trace
  have valid : ∀ a ∈ childPairs9611 i, checkRecord (matrixWeight 0) a.2 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact record_valid j
  have covered : ∀ a ∈ childPairs9611 i, supportCheck 0 a.2 a.1 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact support_valid j
  have cap' : k + 1 ≤ (childPairs9611 i).length := by
    simpa only [childPairs9611, childSignals9611, List.length_map] using cap
  have trace' : Run false (observe graph) k
      ((childPairs9611 i).map (fun a => observe a.1)) := by
    simpa only [childPairs9611, childSignals9611, List.map_map, Function.comp_def] using trace
  exact run_exclusion_of_records 0 (childPairs9611 i) valid covered
    (sample_positive 0) (sample_negative 0) (gap i) cap' trace'

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle9611
'''
(p/'Mono18Rectangle9611.lean').write_text(s)
(p/'children9611.json').write_text(json.dumps(dict(fixture=str(source),fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),nodes=nodes,signal_order=ids,profiles=rows),indent=2));print(json.dumps(dict(source_bytes=len(s.encode()),signals=ids,children=[n['node'] for n in nodes],costs=[n['cost_sum'] for n in nodes],lengths=[len(n['state']) for n in nodes]),indent=2))
