from pathlib import Path
import json
p=Path(__file__).resolve().parent;c=p.parent/'mono18-oredge-weak-census';trace=p.parent.parent/'root-mono18-oredge-weak-proof/rectangles.jsonl'
node=None;signals={}
for line in trace.open():
 d=json.loads(line)
 if d['event']=='rectangle' and d['node']==38:node=d
 elif d['event']=='signal':signals[d['id']]=int(d['hex'],16)
assert node and node['matrix']==0
mat=json.loads((c/'matrices.json').read_text())[0];profiles=json.loads((c/'profiles.json').read_text());locator=json.loads((p/'profile-locator.json').read_text())
profile_ids={(v['weight'],v['positive_mask'],v['negative_false_mask'],v['cost']):i for i,v in enumerate(profiles)}
ids=list(dict.fromkeys(node['state']));index={v:i for i,v in enumerate(ids)};rows=[]
for sid in ids:
 x=signals[sid];pm=sum(((x>>r)&1)<<i for i,r in enumerate(mat['positive_rows']));nm=sum((1-((x>>r)&1))<<i for i,r in enumerate(mat['negative_rows']));cost=node['root_costs'][node['state'].index(sid)];pid=profile_ids[0,pm,nm,cost];rows.append(dict(signal=sid,hex=hex(x),profile=pid,**locator[str(pid)]))
s='''import Mono18RectangleLookup
import Mono18RectangleBank
import Mono18RectangleLabels

namespace PEqualNP.Outside.L_meta_2373.Mono18RectangleNode38

open Live1024 Mono18Rectangle

def raw : Fin 12 → Sig := ![
'''+',\n'.join('  '+r['hex'] for r in rows)+''']

def record : Fin 12 → Nat := !['''+','.join(r['record'] for r in rows)+''']
def labels : List (Fin 12) := ['''+','.join(str(index[i]) for i in node['state'])+''']
def rootPairs : List (Sig × Nat) := labels.map (fun i => (raw i, record i))

lemma record_valid : ∀ i : Fin 12, checkRecord 0 (record i) = true := by
  intro i; fin_cases i
'''+''.join('  · exact certifiedAt_valid '+str(r['block'])+' '+str(r['offset'])+'\n' for r in rows)+'''
lemma support_valid : ∀ i : Fin 12, supportCheck 0 (record i) (raw i) = true := by
  intro i; fin_cases i <;> decide +kernel

lemma gap : (rootPairs.map (fun a => recordCap (matrixWeight 0) a.2)).sum < targetCost 0 := by
  decide +kernel

lemma run_exclusion {k : Nat} (cap : k ≤ 16)
    (trace : Run false (observe graph) k (rootPairs.map (fun a => observe a.1))) : False := by
  apply run_exclusion_of_records 0 rootPairs _ _ (sample_positive 0) (sample_negative 0) gap _ trace
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact record_valid i
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact support_valid i
  · change k + 1 ≤ 17
    omega

end PEqualNP.Outside.L_meta_2373.Mono18RectangleNode38
'''
(p/'Mono18RectangleNode38.lean').write_text(s)
(p/'node38.json').write_text(json.dumps(dict(node=node,signal_order=ids,profiles=rows,trace=str(trace)),indent=2));print('source bytes',len(s.encode()))
