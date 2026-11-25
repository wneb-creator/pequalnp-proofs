import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma incidence_prime_iff (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧ S = {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  have separated (p : Fin P) (l : Fin L) :
      Fin.castAdd L p ≠ Fin.natAdd P l := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = P + l.val at hv
    omega
  have accepts (T : Finset (Fin (P + L))) :
      circuitFun (P + L) C (setInput T) = true ↔
        ∃ p : Fin P, ∃ l : Fin L, I p l ∧
          Fin.castAdd L p ∈ T ∧ Fin.natAdd P l ∈ T := by
    rw [hC]
    simp [setInput]
  constructor
  · rintro ⟨htrue, hproper⟩
    obtain ⟨p, l, hI, hp, hl⟩ := (accepts S).mp htrue
    let T : Finset (Fin (P + L)) := {Fin.castAdd L p, Fin.natAdd P l}
    have hsub : T ⊆ S := by
      simp only [T, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp, hl⟩
    have heq : T = S := by
      by_contra hne
      have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      have ht : circuitFun (P + L) C (setInput T) = true :=
        (accepts T).mpr ⟨p, l, hI, by simp [T], by simp [T]⟩
      have hf := hproper T (Finset.mem_ssubsets.mpr hstrict)
      exact Bool.noConfusion (ht.symm.trans hf)
    exact ⟨p, l, hI, heq.symm⟩
  · rintro ⟨p, l, hI, rfl⟩
    refine ⟨(accepts _).mpr ⟨p, l, hI, by simp, by simp⟩, ?_⟩
    intro T hT
    by_contra hnot
    have htrue : circuitFun (P + L) C (setInput T) = true := by simpa using hnot
    obtain ⟨p', l', _, hp', hl'⟩ := (accepts T).mp htrue
    have hsub : {Fin.castAdd L p', Fin.natAdd P l'} ⊆ T := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp', hl'⟩
    have htwo : 2 ≤ T.card := by
      simpa [separated] using Finset.card_le_card hsub
    have hlt := Finset.card_lt_card (Finset.mem_ssubsets.mp hT)
    have hcard : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))).card = 2 := by
      simp [separated]
    omega

end PEqualNP.Outside.L_meta_2583
