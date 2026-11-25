import ReadTwiceCollapse

namespace PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers

lemma nonNotCount_sum (gs : List Gate) :
    nonNotCount gs = (gs.map (fun g => if isNotGate g.op then 0 else 1)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    unfold nonNotCount at *
    cases flag : isNotGate g.op <;> simp [List.countP_cons, flag, ih, Nat.add_comm]

lemma binaryIndices_count (gs : List Gate) : (binaryIndices gs).card = nonNotCount gs := by
  rw [nonNotCount_sum]
  have listEq : List.ofFn (fun j : Fin gs.length => if isNotGate (gs.get j).op then 0 else 1) =
      gs.map (fun g => if isNotGate g.op then 0 else 1) := by
    change List.ofFn ((fun g : Gate => if isNotGate g.op then 0 else 1) ∘ gs.get) = _
    rw [← List.map_ofFn]
    congr 1
    exact List.ofFn_getElem
  rw [← listEq, List.sum_ofFn]
  simp only [binaryIndices, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases isNotGate (gs.get j).op <;> simp

lemma sum_fiber_counts {α : Type*} [DecidableEq α] (n : ℕ) (S : Finset α) (label : α → ℕ) :
    (∑ v : Fin n, (S.filter (fun s => label s = v.val)).card) =
      (S.filter (fun s => label s < n)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases small : label s < n
  · let v : Fin n := ⟨label s, small⟩
    have test : ∀ i : Fin n, label s = i.val ↔ i = v := by
      intro i
      constructor
      · intro equal
        apply Fin.ext
        exact equal.symm
      · rintro rfl
        rfl
    simp [test, small]
  · have none : ∀ i : Fin n, label s ≠ i.val := by
      intro i equal
      have := i.isLt
      omega
    simp [none, small]

def primaryReads (n : ℕ) (gs : List Gate) (v : Fin n) : ℕ :=
  ((slots gs).filter (fun s => slotOrigin n gs s = v.val)).card

lemma primaryReads_sum (n : ℕ) (gs : List Gate) (out : ℕ) (clean : CleanL n gs)
    (live : ∀ j, j < gs.length → out ≠ n + j → ∃ q, j < q ∧ Reads gs q (n + j)) :
    (∑ v : Fin n, primaryReads n gs v) ≤ nonNotCount gs + 1 := by
  rw [← binaryIndices_count]
  unfold primaryReads
  rw [sum_fiber_counts]
  exact collapsed_primary_budget n gs out clean live

lemma singleton_bound {n : ℕ} (reads : Fin n → ℕ) (essential : ∀ i, 1 ≤ reads i) :
    2 * n ≤ (∑ i, reads i) + (Finset.univ.filter (fun i => reads i = 1)).card := by
  have pointwise : ∀ i, 2 ≤ reads i + if reads i = 1 then 1 else 0 := by
    intro i
    have hi := essential i
    split_ifs <;> omega
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pointwise i)
  simpa [Finset.sum_add_distrib, Nat.mul_comm] using summed

lemma three_single_inputs (gs : List Gate) (out : ℕ) (clean : CleanL 10 gs)
    (live : ∀ j, j < gs.length → out ≠ 10 + j → ∃ q, j < q ∧ Reads gs q (10 + j))
    (essential : ∀ i, 1 ≤ primaryReads 10 gs i) (small : nonNotCount gs ≤ 16) :
    3 ≤ (Finset.univ.filter (fun i => primaryReads 10 gs i = 1)).card := by
  have budget := primaryReads_sum 10 gs out clean live
  have lower := singleton_bound (primaryReads 10 gs) essential
  omega

lemma least_primaryReads_sum {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) :
    (∑ v : Fin n, primaryReads n gs v) ≤ nonNotCount gs + 1 :=
  primaryReads_sum n gs out least.hcl (least.live nonconstant)

end PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse
