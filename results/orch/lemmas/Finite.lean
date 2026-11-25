import Mathlib

namespace PEqualNP.Outside.L_meta_2592_aux

def finiteEdge (r : ℕ) : Bool :=
  (r.testBit 0 && r.testBit 1) ||
  (r.testBit 1 && r.testBit 2) ||
  (r.testBit 2 && r.testBit 3) ||
  (r.testBit 3 && r.testBit 4) ||
  (r.testBit 4 && r.testBit 0) ||
  (r.testBit 0 && r.testBit 5) ||
  (r.testBit 1 && r.testBit 6) ||
  (r.testBit 2 && r.testBit 7) ||
  (r.testBit 3 && r.testBit 8) ||
  (r.testBit 4 && r.testBit 9) ||
  (r.testBit 5 && r.testBit 7) ||
  (r.testBit 7 && r.testBit 9) ||
  (r.testBit 9 && r.testBit 6) ||
  (r.testBit 6 && r.testBit 8) ||
  (r.testBit 8 && r.testBit 5)

def finiteRows : List ℕ :=
  [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201,
    208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_independent_count : ((List.range 1024).filter fun r => !finiteEdge r).length = 76 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_rows_distinct : finiteRows.Nodup := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma finite_rows_bounded : ∀ r ∈ finiteRows, r < 1024 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma finite_true_covered : ∀ r : Fin 1024, finiteEdge r.val = true →
    finiteRows.any (fun t => finiteEdge t && decide (t &&& r.val = t)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma finite_false_covered : ∀ r : Fin 1024, finiteEdge r.val = false →
    finiteRows.any (fun t => !finiteEdge t && decide (r.val &&& t = r.val)) = true := by
  decide +kernel

lemma finite_rows_complete (g : ℕ → Bool)
    (hmono : ∀ a b, a &&& b = a → g a = true → g b = true)
    (hrows : ∀ r ∈ finiteRows, g r = finiteEdge r) :
    ∀ r < 1024, g r = finiteEdge r := by
  intro r hr
  cases h : finiteEdge r with
  | false =>
    obtain ⟨t, ht, hval⟩ := List.any_eq_true.mp (finite_false_covered ⟨r, hr⟩ h)
    have hh : finiteEdge t = false ∧ r &&& t = r := by simpa using hval
    cases hg : g r with
    | false => rfl
    | true =>
      have hm := hmono r t hh.2 hg
      rw [hrows t ht, hh.1] at hm
      contradiction
  | true =>
    obtain ⟨t, ht, hval⟩ := List.any_eq_true.mp (finite_true_covered ⟨r, hr⟩ h)
    have hh : finiteEdge t = true ∧ t &&& r = t := by simpa using hval
    exact hmono t r hh.2 ((hrows t ht).trans hh.1)

end PEqualNP.Outside.L_meta_2592_aux
