import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotSurvive

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def support (x : Fin 10 → Bool) : Finset (Fin 10) :=
  Finset.univ.filter fun i => x i = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma independent_card_le_four :
    ∀ x : Fin 10 → Bool, petersen x = false → (support x).card ≤ 4 := by
  decide +kernel

def zeroAt (i j : Fin 10) : Bool := decide (j ≠ i)

def deadCoords (g : (Fin 10 → Bool) → Bool) : Finset (Fin 10) :=
  Finset.univ.filter fun i => g (zeroAt i) = false

lemma dead_subset_support (g : (Fin 10 → Bool) → Bool) (mono : Monotone g)
    (x : Fin 10 → Bool) (hx : g x = true) : deadCoords g ⊆ support x := by
  intro i hi
  have hd : g (zeroAt i) = false := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  cases hxi : x i with
  | true => rfl
  | false =>
      have below : x ≤ zeroAt i := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [zeroAt, hxi]
        · simp [zeroAt, hji]
      have impossible : (true : Bool) ≤ false := by
        simpa only [hx, hd] using mono below
      exact False.elim ((by decide : ¬ (true : Bool) ≤ false) impossible)

lemma dead_card_le_four (g : (Fin 10 → Bool) → Bool) (mono : Monotone g)
    (outside : ∃ x, g x = true ∧ petersen x = false) : (deadCoords g).card ≤ 4 := by
  obtain ⟨x, hx, hf⟩ := outside
  exact (Finset.card_le_card (dead_subset_support g mono x hx)).trans
    (independent_card_le_four x hf)

lemma zero_value_false (g : (Fin 10 → Bool) → Bool) (mono : Monotone g)
    (misses : ∃ x, petersen x = true ∧ g x = false) : g (fun _ => false) = false := by
  obtain ⟨x, _, hx⟩ := misses
  apply le_antisymm
  · calc
      g (fun _ => false) ≤ g x := mono (by intro i; exact bot_le)
      _ = false := hx
  · exact bot_le

lemma six_surviving_zero_restrictions (g : (Fin 10 → Bool) → Bool) (mono : Monotone g)
    (outside : ∃ x, g x = true ∧ petersen x = false)
    (misses : ∃ x, petersen x = true ∧ g x = false) :
    ∃ S : Finset (Fin 10), 6 ≤ S.card ∧
      ∀ i ∈ S, ∃ x y : Fin 10 → Bool,
        x i = false ∧ y i = false ∧ g x = false ∧ g y = true := by
  let S : Finset (Fin 10) := Finset.univ \ deadCoords g
  have bound := dead_card_le_four g mono outside
  have total := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (deadCoords g))
  have large : 6 ≤ S.card := by
    change (Finset.univ \ deadCoords g).card + (deadCoords g).card = 10 at total
    change 6 ≤ (Finset.univ \ deadCoords g).card
    omega
  refine ⟨S, large, ?_⟩
  intro i hi
  have notDead : i ∉ deadCoords g := (Finset.mem_sdiff.mp hi).2
  have hg : g (zeroAt i) = true := by
    cases h : g (zeroAt i) with
    | false => exact False.elim (notDead (by simp [deadCoords, h]))
    | true => rfl
  refine ⟨(fun _ => false), zeroAt i, rfl, ?_, zero_value_false g mono misses, hg⟩
  simp [zeroAt]

end PEqualNP.Outside.L_meta_2592_aux.OneNotSurvive
