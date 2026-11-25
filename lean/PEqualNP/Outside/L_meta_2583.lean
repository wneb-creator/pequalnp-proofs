import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def incidenceTarget (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧
    x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)

lemma point_ne_line {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma incidence_eval_set {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {C : Circuit} (correct : ∀ x, circuitFun (N + N) C x = incidenceTarget N I x)
    (S : Finset (Fin (N + N))) :
    circuitFun (N + N) C (setInput S) = true ↔
      ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
  rw [correct]
  simp [incidenceTarget, setInput]

lemma incidence_prime_iff {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {C : Circuit} (correct : ∀ x, circuitFun (N + N) C x = incidenceTarget N I x)
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  constructor
  · intro hS
    obtain ⟨p, l, hi, hp, hl⟩ := (incidence_eval_set correct S).mp hS.1
    refine ⟨p, l, hi, ?_⟩
    have hsub : {Fin.castAdd N p, Fin.natAdd N l} ⊆ S := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hp
      · have heq := Finset.mem_singleton.mp hv
        rw [heq]
        exact hl
    by_contra hne
    have hss : {Fin.castAdd N p, Fin.natAdd N l} ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hS.2 _ (Finset.mem_ssubsets.mpr hss)
    have htrue := (incidence_eval_set correct {Fin.castAdd N p, Fin.natAdd N l}).mpr
      ⟨p, l, hi, by simp, by simp⟩
    exact Bool.false_ne_true (hfalse.symm.trans htrue)
  · rintro ⟨p, l, hi, rfl⟩
    constructor
    · exact (incidence_eval_set correct _).mpr ⟨p, l, hi, by simp, by simp⟩
    · intro T hT
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨p', l', _, hp', hl'⟩ := (incidence_eval_set correct T).mp htrue
      obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp (Finset.mem_ssubsets.mp hT)
      have hp : Fin.castAdd N p' = Fin.castAdd N p := by
        rcases Finset.mem_insert.mp (hsub hp') with h | h
        · exact h
        · exact (point_ne_line p' l (Finset.mem_singleton.mp h)).elim
      have hl : Fin.natAdd N l' = Fin.natAdd N l := by
        rcases Finset.mem_insert.mp (hsub hl') with h | h
        · exact (point_ne_line p l' h.symm).elim
        · exact Finset.mem_singleton.mp h
      have hback : {Fin.castAdd N p, Fin.natAdd N l} ⊆ T := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simpa only [hp] using hp'
        · have heq := Finset.mem_singleton.mp hv
          subst v
          simpa only [hl] using hl'
      exact hne (Finset.Subset.antisymm hsub hback)

lemma incidence_read_one_iff {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {C : Circuit} (correct : ∀ x, circuitFun (N + N) C x = incidenceTarget N I x) :
    IsReadK (N + N) C 1 ↔
      ∀ p l : Fin N, I p l →
        readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 1 = true := by
  constructor
  · intro h p l hi
    exact h _ ((incidence_prime_iff correct _).mpr ⟨p, l, hi, rfl⟩)
  · intro h S hS
    obtain ⟨p, l, hi, rfl⟩ := (incidence_prime_iff correct S).mp hS
    exact h p l hi

end PEqualNP.Outside.L_meta_2583_aux
