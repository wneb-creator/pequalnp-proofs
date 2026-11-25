import PEqualNP.Defs
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_2583_aux.CoverRigidity

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

lemma restricted_incidence_card_left (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (P : Finset (Fin N))
    (hdegree : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = d) :
    ((Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).filter
      (fun e => e.1 ∈ P)).card = P.card * d := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hf (p : Fin N) : (E.filter (fun e => e.1 = p)).card =
      (Finset.univ.filter (fun l => I p l)).card := by
    apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      have he' : I e.1 e.2 ∧ e.1 = p := by simpa [E] using he
      simpa [he'.2] using he'.1
    · intro e he e' he' heq
      have h : e.1 = p := (Finset.mem_filter.mp he).2
      have h' : e'.1 = p := (Finset.mem_filter.mp he').2
      exact Prod.ext (h.trans h'.symm) heq
    · intro l hl
      refine ⟨(p, l), ?_, rfl⟩
      simpa [E] using hl
  have hs := Finset.sum_card_fiberwise_eq_card_filter E P Prod.fst
  change (E.filter (fun e => e.1 ∈ P)).card = P.card * d
  rw [← hs]
  exact Finset.sum_const_nat (fun p _ => (hf p).trans (hdegree p))

lemma restricted_incidence_card_right (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (L : Finset (Fin N))
    (hdegree : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d) :
    ((Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).filter
      (fun e => e.2 ∈ L)).card = L.card * d := by
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
  have hs := Finset.sum_card_fiberwise_eq_card_filter E L Prod.snd
  change (E.filter (fun e => e.2 ∈ L)).card = L.card * d
  rw [← hs]
  exact Finset.sum_const_nat (fun l _ => (hf l).trans (hdegree l))

lemma incidence_cover_size (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hsub : E ⊆ E.filter (fun e => e.1 ∈ P) ∪ E.filter (fun e => e.2 ∈ L) := by
    intro e he
    have hi : I e.1 e.2 := by simpa [E] using he
    rcases hcover e.1 e.2 hi with hp | hl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hp⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hl⟩))
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have he := incidence_card q N I hline
  have hp := restricted_incidence_card_left N (q + 1) I P (point_degree q N I hq hN hline hpair)
  have hl := restricted_incidence_card_right N (q + 1) I L hline
  change E.card = N * (q + 1) at he
  change (E.filter (fun e => e.1 ∈ P)).card = P.card * (q + 1) at hp
  change (E.filter (fun e => e.2 ∈ L)).card = L.card * (q + 1) at hl
  rw [he, hp, hl] at hcount
  have hm : N * (q + 1) ≤ (P.card + L.card) * (q + 1) := by nlinarith
  exact Nat.le_of_mul_le_mul_right hm (by omega)

lemma strict_incidence_expansion (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (P : Finset (Fin N)) (hP : P.Nonempty) (hproper : P ≠ Finset.univ) :
    P.card < (Finset.univ.filter (fun l => ∃ p ∈ P, I p l)).card := by
  classical
  let L := Finset.univ.filter (fun l => ∃ p ∈ P, I p l)
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let A := E.filter (fun e => e.1 ∈ P)
  let B := E.filter (fun e => e.2 ∈ L)
  have hsub : A ⊆ B := by
    intro e he
    have he' : e ∈ E ∧ e.1 ∈ P := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨he'.1, ?_⟩
    have hi : I e.1 e.2 := by simpa [E] using he'.1
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e.1, he'.2, hi⟩
  obtain ⟨p, hp⟩ := hP
  have hex : ∃ r : Fin N, r ∉ P := by
    by_contra hn
    apply hproper
    ext r
    simp only [Finset.mem_univ, iff_true]
    by_contra hr
    exact hn ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hex
  have hpr : p ≠ r := by
    intro heq
    exact hr (heq ▸ hp)
  obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := hpair p r hpr
  have hrlB : (r, l) ∈ B := by
    simp only [B, E, L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hrl, p, hp, hpl⟩
  have hrlA : (r, l) ∉ A := by simp [A, hr]
  have hstrict : A ⊂ B := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    exact hrlA (heq ▸ hrlB)
  have hcount := Finset.card_lt_card hstrict
  have hleft : A.card = P.card * (q + 1) :=
    restricted_incidence_card_left N (q + 1) I P (point_degree q N I hq hN hline hpair)
  have hright : B.card = L.card * (q + 1) :=
    restricted_incidence_card_right N (q + 1) I L hline
  rw [hleft, hright] at hcount
  exact Nat.lt_of_mul_lt_mul_right hcount

lemma mixed_incidence_cover_size (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ P ∨ l ∈ L)
    (hP : P.Nonempty) (hproper : P ≠ Finset.univ) :
    N < P.card + L.card := by
  classical
  let Q := Finset.univ \ P
  have hQ : Q.Nonempty := by
    by_contra hn
    apply hproper
    ext p
    simp only [Finset.mem_univ, iff_true]
    by_contra hp
    exact hn ⟨p, by simp [Q, hp]⟩
  have hQproper : Q ≠ Finset.univ := by
    intro heq
    obtain ⟨p, hp⟩ := hP
    have hpQ : p ∈ Q := by rw [heq]; exact Finset.mem_univ p
    exact (Finset.mem_sdiff.mp hpQ).2 hp
  have hstrict := strict_incidence_expansion q N I hq hN hline hpair Q hQ hQproper
  have hsub : (Finset.univ.filter (fun l => ∃ p ∈ Q, I p l)) ⊆ L := by
    intro l hl
    obtain ⟨p, hp, hi⟩ := (Finset.mem_filter.mp hl).2
    rcases hcover p l hi with hpp | hll
    · exact False.elim ((Finset.mem_sdiff.mp hp).2 hpp)
    · exact hll
  have hcard : Q.card + P.card = N := by
    simpa [Q] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  have hle := Finset.card_le_card hsub
  omega

lemma minimum_incidence_cover_rigid (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ P ∨ l ∈ L)
    (hcard : P.card + L.card = N) :
    (P = Finset.univ ∧ L = ∅) ∨ (P = ∅ ∧ L = Finset.univ) := by
  classical
  by_cases hP : P = ∅
  · right
    refine ⟨hP, ?_⟩
    have hLc : L.card = N := by simpa [hP] using hcard
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ L)
    simp [hLc]
  · have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
    by_cases hfull : P = Finset.univ
    · left
      refine ⟨hfull, ?_⟩
      apply Finset.card_eq_zero.mp
      have hPc : P.card = N := by simp [hfull]
      omega
    · have hs := mixed_incidence_cover_size q N I hq hN hline hpair P L hcover hPne hfull
      omega

end PEqualNP.Outside.L_meta_2583_aux.CoverRigidity
