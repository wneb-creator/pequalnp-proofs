import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.FourRows

def pairInput (p l : Fin 13) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)

end PEqualNP.Outside.L_meta_1896_aux.FourRows

namespace PEqualNP.Outside.L_meta_1896_aux.Flags

open PEqualNP.Outside.L_meta_1896_aux.FourRows

def flag (a : Fin 52) : Fin 13 × Fin 13 :=
  ([(0, 0), (1, 0), (3, 0), (9, 0), (1, 1), (2, 1), (4, 1), (10, 1), (2, 2), (3, 2), (5, 2), (11, 2), (3, 3), (4, 3), (6, 3), (12, 3), (4, 4), (5, 4), (7, 4), (0, 4), (5, 5), (6, 5), (8, 5), (1, 5), (6, 6), (7, 6), (9, 6), (2, 6), (7, 7), (8, 7), (10, 7), (3, 7), (8, 8), (9, 8), (11, 8), (4, 8), (9, 9), (10, 9), (12, 9), (5, 9), (10, 10), (11, 10), (0, 10), (6, 10), (11, 11), (12, 11), (1, 11), (7, 11), (12, 12), (0, 12), (2, 12), (8, 12)] : List (Fin 13 × Fin 13)).getD a.val (0, 0)

def input (a : Fin 52) : Fin 26 → Bool := pairInput (flag a).1 (flag a).2

end PEqualNP.Outside.L_meta_1896_aux.Flags

namespace PEqualNP.Outside.L_meta_1896_aux.Flags

def flagsAt (v : Fin 26) : Finset (Fin 52) :=
  Finset.univ.filter fun a => input a v = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma degree_four : ∀ v : Fin 26, (flagsAt v).card = 4 := by decide +kernel

def surviving (S : Finset (Fin 26)) : Finset (Fin 52) :=
  Finset.univ \ S.biUnion flagsAt

lemma surviving_lower_bound (S : Finset (Fin 26)) :
    52 - 4 * S.card ≤ (surviving S).card := by
  have hbad : (S.biUnion flagsAt).card ≤ 4 * S.card := by
    calc
      (S.biUnion flagsAt).card ≤ ∑ v ∈ S, (flagsAt v).card := Finset.card_biUnion_le
      _ = 4 * S.card := by simp [degree_four, Nat.mul_comm]
  have hcard : (surviving S).card = 52 - (S.biUnion flagsAt).card := by
    unfold surviving
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  omega

lemma surviving_card (S : Finset (Fin 26)) (hS : S.card ≤ 4) :
    36 ≤ (surviving S).card := by
  have h := surviving_lower_bound S
  omega

lemma surviving_avoids (S : Finset (Fin 26)) (a : Fin 52)
    (ha : a ∈ surviving S) (v : Fin 26) (hv : v ∈ S) : input a v = false := by
  have hn : a ∉ S.biUnion flagsAt := (Finset.mem_sdiff.mp ha).2
  cases h : input a v with
  | false => rfl
  | true =>
    exfalso
    apply hn
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

lemma surviving_flags (S : Finset (Fin 26)) (hS : S.card ≤ 4) :
    ∃ M : Finset (Fin 52), 36 ≤ M.card ∧
      ∀ a ∈ M, ∀ v ∈ S, input a v = false := by
  exact ⟨surviving S, surviving_card S hS, fun a ha v hv => surviving_avoids S a ha v hv⟩

end PEqualNP.Outside.L_meta_1896_aux.Flags
