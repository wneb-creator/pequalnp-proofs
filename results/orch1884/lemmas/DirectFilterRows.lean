import SharedFilter
import StrongRelaxRows

namespace PEqualNP.Outside.L_meta_1884.DirectFilterRows

open SoleOrPartner SharedFilter StrongRelaxRows

def row10 (m : Nat) : Fin 10 → Bool :=
  fun i => if i = 0 then false else m.testBit (i.val - 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma geometry : negatives.all (fun m => decide (
    SoleOrPartner.target (row10 m) = false ∧
      (SoleOrPartner.target (Function.update (row10 m) 1 true) = true ∨
       SoleOrPartner.target (Function.update (row10 m) 5 true) = true ∨
       ∃ j : Fin 10, Function.update (Function.update (row10 m) 1 false) 5 false =
         SoleOrPartner.singleton j))) = true := by decide

theorem negative_rows (H : (Fin 10 → Bool) → Bool)
    (hm : fiberMono H) (hi1 : independent 1 H) (hi5 : independent 5 H)
    (hf1 : factor 1 H) (hf5 : factor 5 H) :
    ∀ m ∈ negatives, H (row10 m) = false := by
  intro m hmem
  have hg := of_decide_eq_true (List.all_eq_true.mp geometry m hmem)
  obtain ⟨hnegative, hcases⟩ := hg
  cases hh : H (row10 m)
  · rfl
  · rcases hcases with hp | hp | ⟨j, hj⟩
    · have hbad := hf1 (row10 m) (Function.update (row10 m) 1 true)
        (by intro i hi; simp [Function.update_of_ne hi]) (by simp [hh])
      rw [hnegative, hp] at hbad
      cases hbad
    · have hbad := hf5 (row10 m) (Function.update (row10 m) 5 true)
        (by intro i hi; simp [Function.update_of_ne hi]) (by simp [hh])
      rw [hnegative, hp] at hbad
      cases hbad
    · have h1 : H (Function.update (row10 m) 1 false) = H (row10 m) := by
        apply hi1
        intro i hi
        simp [Function.update_of_ne hi]
      have h5 : H (Function.update (Function.update (row10 m) 1 false) 5 false) =
          H (Function.update (row10 m) 1 false) := by
        apply hi5
        intro i hi
        simp [Function.update_of_ne hi]
      have hbad := h5.trans h1
      rw [hj, rejects_singleton 1 (by decide) H hm hi1 hf1 j, hh] at hbad
      cases hbad

lemma target_rows (m : Nat) : SoleOrPartner.target (row10 m) =
    StrongRelaxRows.target (StrongRelaxRows.row m) := by
  simp [SoleOrPartner.target, StrongRelaxRows.target, row10, StrongRelaxRows.row]

lemma positives_true : positives.all (fun m =>
    SoleOrPartner.target (row10 m)) = true := by decide

end PEqualNP.Outside.L_meta_1884.DirectFilterRows
