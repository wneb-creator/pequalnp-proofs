import Mathlib

namespace PEqualNP.Outside.NestedCheckpoints

def ValidPath {State : Type*} (step : State → State) (D C : ℕ)
    (path : Fin (C + 1) → State) : Prop :=
  ∀ j : Fin C, step^[D] (path j.castSucc) = path j.succ

lemma valid_path_value {State : Type*} (step : State → State) (D C : ℕ)
    (path : Fin (C + 1) → State) (hpath : ValidPath step D C path) :
    ∀ j : Fin (C + 1), path j = step^[D * j.val] (path 0) := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [← hpath j, ih]
    change step^[D] (step^[D * j.val] (path 0)) =
      step^[D * (j.val + 1)] (path 0)
    rw [Nat.mul_succ, Nat.add_comm (D * j.val) D, Function.iterate_add_apply]

lemma canonical_path_valid {State : Type*} (step : State → State) (D C : ℕ)
    (start : State) :
    ValidPath step D C (fun j => step^[D * j.val] start) := by
  intro j
  change step^[D] (step^[D * j.val] start) = step^[D * (j.val + 1)] start
  rw [Nat.mul_succ, Nat.add_comm (D * j.val) D, Function.iterate_add_apply]

lemma path_exists_iff {State : Type*} (step : State → State) (D C : ℕ)
    (start finish : State) :
    (∃ path : Fin (C + 1) → State,
      path 0 = start ∧ path (Fin.last C) = finish ∧ ValidPath step D C path) ↔
      step^[D * C] start = finish := by
  constructor
  · rintro ⟨path, hstart, hfinish, hpath⟩
    have h := valid_path_value step D C path hpath (Fin.last C)
    simpa [hstart, hfinish] using h.symm
  · intro h
    exact ⟨fun j => step^[D * j.val] start, by simp, by simpa using h,
      canonical_path_valid step D C start⟩

lemma path_dual_iff {State : Type*} (step : State → State) (D C : ℕ)
    (start finish : State) :
    (∀ path : Fin (C + 1) → State,
      path 0 = start → path (Fin.last C) ≠ finish →
        ∃ j : Fin C, step^[D] (path j.castSucc) ≠ path j.succ) ↔
      step^[D * C] start = finish := by
  classical
  constructor
  · intro h
    by_contra hbad
    obtain ⟨j, hj⟩ := h (fun j => step^[D * j.val] start) (by simp) (by simpa using hbad)
    exact hj (canonical_path_valid step D C start j)
  · intro h path hstart hfinish
    by_contra! hnone
    have hv := valid_path_value step D C path hnone (Fin.last C)
    apply hfinish
    calc
      path (Fin.last C) = step^[D * C] start := by simpa [hstart] using hv
      _ = finish := h

lemma three_block_checkpoints_iff {State : Type*} (step : State → State) (D C B : ℕ)
    (start finish : State) :
    (∃ outer : Fin (B + 1) → State,
      outer 0 = start ∧ outer (Fin.last B) = finish ∧
      ∀ i : Fin B, ∀ trial : Fin (C + 1) → State,
        trial 0 = outer i.castSucc → trial (Fin.last C) ≠ outer i.succ →
          ∃ j : Fin C, step^[D] (trial j.castSucc) ≠ trial j.succ) ↔
      step^[(D * C) * B] start = finish := by
  have hgame (outer : Fin (B + 1) → State) :
      (∀ i : Fin B, ∀ trial : Fin (C + 1) → State,
        trial 0 = outer i.castSucc → trial (Fin.last C) ≠ outer i.succ →
          ∃ j : Fin C, step^[D] (trial j.castSucc) ≠ trial j.succ) ↔
      ValidPath step (D * C) B outer := by
    simp only [path_dual_iff, ValidPath]
  simp only [hgame]
  exact path_exists_iff step (D * C) B start finish

end PEqualNP.Outside.NestedCheckpoints
