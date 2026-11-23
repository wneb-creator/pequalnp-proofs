from pathlib import Path
import json
root=Path('/tmp/oec/pequalnp-pilot-7')
cases=json.loads((root/'term-context-982-cases.json').read_text())
parts=[]
for idx in [e['case'] for e in json.loads((root/'root982-pair-manifest.json').read_text())]:
 data_name=f'term-context-982-seed{idx}-reduced-data' if idx in [0,8] else f'root982-core{idx}-data'
 d=json.loads((root/(data_name+'.json')).read_text())
 c=cases[idx]; n=c['n']; k=d['K']; tag=f'seed{idx}'
 rows=d['paired_rows']
 witnesses=[]
 for v in range(n):
  u=next(b if a==v else a for a,b in c['edges'] if v in (a,b))
  witnesses.append((rows.index(1<<u),rows.index((1<<u)|(1<<v))))
 function=' || '.join(f'(x {a} && x {b})' for a,b in c['edges'])
 witnesslean='['+', '.join(f'({a}, {b})' for a,b in witnesses)+']'
 parts.append(f'''
namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def {tag}Fn : BFn {n} := fun x => {function}
def {tag}Pack (x : Fin {n} → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem {tag}Pack_spec (x : Fin {n} → Bool) :
    {tag}Pack x < {1<<n} ∧ pt {n} ({tag}Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem {tag}Rows_cover : ∀ x : Fin {n} → Bool, ∃ v ∈ {tag}Rows, pt {n} v = x := by
  have hmem : ∀ v : Fin {1<<n}, v.val ∈ {tag}Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := {tag}Pack_spec x
  exact ⟨{tag}Pack x,hmem ⟨_,hb⟩,he⟩

def {tag}Witnesses : List (Nat × Nat) := {witnesslean}

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem {tag}Essential : ∀ a ∈ {tag}Inputs, ∃ i j : Nat,
    {tag}Mask.testBit i = {tag}Mask.testBit j ∧
    {tag}Goal.testBit i ≠ {tag}Goal.testBit j ∧
    ∀ b ∈ {tag}Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ {tag}Inputs, ∃ p : Fin {n},
      {tag}Mask.testBit ({tag}Witnesses.getD p.val (0,0)).1 =
        {tag}Mask.testBit ({tag}Witnesses.getD p.val (0,0)).2 ∧
      {tag}Goal.testBit ({tag}Witnesses.getD p.val (0,0)).1 ≠
        {tag}Goal.testBit ({tag}Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ {tag}Inputs, b ≠ a →
        b.testBit ({tag}Witnesses.getD p.val (0,0)).1 =
          b.testBit ({tag}Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨({tag}Witnesses.getD p.val (0,0)).1,({tag}Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem {tag}Lower_of_noRun
    (hno : ∀ t < {c['lower_bound']}, ¬ RNatRun {tag}Forbidden {tag}Mask {tag}Goal t {tag}Inputs) :
    ∀ s, HasCircuitSize {n} {tag}Fn s → {c['lower_bound']} ≤ s := by
  apply lower_from_rows {tag}Fn {tag}Rows {tag}Inputs {tag}Forbidden {tag}Mask {tag}Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact {tag}Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact {tag}Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite
''')
append=''.join(parts)
(root/'AllCoreBridge982Append.lean.txt').write_text(append)
base=(root/'Bridge982.lean').read_text()
data=''
for e in json.loads((root/'root982-pair-manifest.json').read_text()):
 i=e['case']
 name=f'term-context-982-seed{i}-reduced-data.lean' if i in [0,8] else f'root982-core{i}-data.lean'
 text=(root/name).read_text().split(f'def seed{i}Pool')[0]
 text='\n'.join(line for line in text.splitlines() if not line.startswith((f'def seed{i}NegativeRows',f'def seed{i}PositiveRows')))
 data+=text+'\nend PEqualNP.Outside.L_meta_982_aux.Finite\n'
(root/'AllCoreBridge982Data.lean.txt').write_text(data)
(root/'AllCoreBridge982.lean').write_text(base+data+append)
print('Wrote concrete bridges for all14 finite cores')
