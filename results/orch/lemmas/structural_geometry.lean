import PEqualNP.Defs
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_2583_aux

open scoped BigOperators

lemma incidence_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hf (l : Fin N) : (E.filter (fun e => e.2 = l)).card =
      (Finset.univ.filter (fun p => I p l)).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      have he' : I e.1 e.2 ∧ e.2 = l := by simpa [E] using he
      simpa [he'.2] using he'.1
    · intro e he e' he' heq
      have h : e.2 = l := (Finset.mem_filter.mp he).2
      have h' : e'.2 = l := (Finset.mem_filter.mp he').2
      exact Prod.ext heq (h.trans h'.symm)
    · intro p hp
      refine ⟨(p, l), ?_, rfl⟩
      simpa [E] using hp
  have hs := Finset.sum_card_fiberwise_eq_card_filter E (Finset.univ : Finset (Fin N)) Prod.snd
  have heq : E.card = ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
    simpa only [hf, Finset.mem_univ, Finset.filter_true] using hs.symm
  change E.card = N * (q + 1)
  rw [heq]
  simp [hline]

lemma point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let F (l : Fin N) : Finset (Fin N) := (Finset.univ.filter (fun r => I r l)).erase p
  have hc : ∀ l ∈ L, (F l).card = q := by
    intro l hl
    have hp : p ∈ Finset.univ.filter (fun r => I r l) := by
      simpa [L] using hl
    simp only [F, Finset.card_erase_of_mem hp, hline]
    omega
  have hd : (L : Set (Fin N)).PairwiseDisjoint F := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrl : r ≠ p ∧ I r l := by simpa [F] using hr
    have hrl' : r ≠ p ∧ I r l' := by simpa [F] using hr'
    have hpl : I p l := by simpa [L] using hl
    have hpl' : I p l' := by simpa [L] using hl'
    obtain ⟨a, ha, hu⟩ := hpair p r (Ne.symm hrl.1)
    exact hne ((hu l ⟨hpl, hrl.2⟩).trans (hu l' ⟨hpl', hrl'.2⟩).symm)
  have hu : L.biUnion F = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion, L, F, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨l, hpl, hrp, hrl⟩
      exact ⟨hrp, trivial⟩
    · rintro ⟨hrp, _⟩
      obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := hpair p r (Ne.symm hrp)
      exact ⟨l, hpl, hrp, hrl⟩
  have hsum : (L.biUnion F).card = L.card * q := by
    rw [Finset.card_biUnion hd]
    exact Finset.sum_const_nat hc
  have hcount : (Finset.univ.erase p).card + 1 = N := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ p)
  rw [← hu, hsum] at hcount
  change L.card = q + 1
  have hmul : q * L.card = q * (q + 1) := by nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

end PEqualNP.Outside.L_meta_2583_aux
