from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-64/ReductionsNormalizeFast.lean')
s=['import ReductionsSemantics','', 'namespace PEqualNP.Outside.Pilot64Bridge','', 'set_option maxRecDepth 100000','set_option maxHeartbeats 0','', 'def distinctFast (c : Candidate) : Prop :=', '  '+' ∧ '.join(f'c.a{i} ≠ c.b{i}' for i in range(5)), '', 'def orderedLeft {n : Nat} (a b : Fin n) : Fin n := if a.val < b.val then a else b','def orderedRight {n : Nat} (a b : Fin n) : Fin n := if a.val < b.val then b else a','', 'def normalizeFast (c : Candidate) : Candidate :=','  {']
for i in range(5):
    s += [f'    op{i} := c.op{i}',f'    a{i} := orderedLeft c.a{i} c.b{i}',f'    b{i} := orderedRight c.a{i} c.b{i}']
s += ['  }','', '''theorem ordered_val {n : Nat} (a b : Fin n) (op : Bool) (w : List Bool) :
    (if op then w.getD (orderedLeft a b).val false && w.getD (orderedRight a b).val false
      else w.getD (orderedLeft a b).val false || w.getD (orderedRight a b).val false) =
    (if op then w.getD a.val false && w.getD b.val false
      else w.getD a.val false || w.getD b.val false) := by
  by_cases h : a.val < b.val
  · simp [orderedLeft, orderedRight, h]
  · simp [orderedLeft, orderedRight, h, Bool.and_comm, Bool.or_comm]

theorem ordered_deriv {n : Nat} (a b : Fin n) (op : Bool) (v d : List Bool) :
    (if op then
       (v.getD (orderedLeft a b).val false && d.getD (orderedRight a b).val false) ||
       (d.getD (orderedLeft a b).val false && v.getD (orderedRight a b).val false)
     else d.getD (orderedLeft a b).val false || d.getD (orderedRight a b).val false) =
    (if op then (v.getD a.val false && d.getD b.val false) ||
       (d.getD a.val false && v.getD b.val false)
     else d.getD a.val false || d.getD b.val false) := by
  by_cases h : a.val < b.val
  · simp [orderedLeft, orderedRight, h]
  · simp [orderedLeft, orderedRight, h, Bool.and_comm, Bool.or_comm]
''', 'theorem normalizeFast_valid (c : Candidate) (hd : distinctFast c) : valid (normalizeFast c) := by','  rcases hd with ⟨h0, h1, h2, h3, h4⟩']
for i in range(5):
    s += [f'  have hn{i} : (normalizeFast c).a{i}.val < (normalizeFast c).b{i}.val := by',f'    by_cases h : c.a{i}.val < c.b{i}.val','    · simp [normalizeFast, orderedLeft, orderedRight, h]','    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]',f'      have hn : c.a{i}.val ≠ c.b{i}.val := by',f'        intro he',f'        exact h{i} (Fin.ext he)','      omega']
s+=['  exact ⟨hn0, hn1, hn2, hn3, hn4⟩','', '''theorem evalCircuit_normalizeFast (c : Candidate) (mask : Nat) :
    evalCircuit (normalizeFast c) mask = evalCircuit c mask := by
  dsimp only [evalCircuit, normalizeFast]
  simp only [ordered_val]

theorem derivativeCircuit_normalizeFast (c : Candidate) (base seed : Nat) :
    derivativeCircuit (normalizeFast c) base seed = derivativeCircuit c base seed := by
  dsimp only [derivativeCircuit, normalizeFast]
  simp only [ordered_val, ordered_deriv]
''','end PEqualNP.Outside.Pilot64Bridge','']
p.write_text('\n'.join(s));print(p,p.stat().st_size)
