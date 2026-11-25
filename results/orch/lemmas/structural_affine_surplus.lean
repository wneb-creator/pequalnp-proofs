import PEqualNP.Defs
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_2583_aux.AffineSurplus

open scoped BigOperators

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

lemma dual_pair (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l l' : Fin N) (hne : l ≠ l') : ∃! p : Fin N, I p l ∧ I p l' := by
  classical
  let P := Finset.univ.filter (fun p => I p l)
  let F (p : Fin N) := (Finset.univ.filter (fun t => I p t)).erase l
  have hc : ∀ p ∈ P, (F p).card = q := by
    intro p hp
    have hlp : l ∈ Finset.univ.filter (fun t => I p t) := by simpa [P] using hp
    simp only [F, Finset.card_erase_of_mem hlp, point_degree q N I hq hN hline hpair]
    omega
  have hd : (P : Set (Fin N)).PairwiseDisjoint F := by
    intro p hp p' hp' hpp'
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    have htl : t ≠ l ∧ I p t := by simpa [F] using ht
    have htl' : t ≠ l ∧ I p' t := by simpa [F] using ht'
    have hpl : I p l := by simpa [P] using hp
    have hpl' : I p' l := by simpa [P] using hp'
    obtain ⟨a, ha, hu⟩ := hpair p p' hpp'
    exact htl.1 ((hu t ⟨htl.2, htl'.2⟩).trans (hu l ⟨hpl, hpl'⟩).symm)
  have hsub : P.biUnion F ⊆ Finset.univ.erase l := by
    intro t ht
    obtain ⟨p, hp, ht⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1, Finset.mem_univ t⟩
  have hcard : (P.biUnion F).card = (q + 1) * q := by
    rw [Finset.card_biUnion hd, Finset.sum_const_nat hc]
    simp [P, hline]
  have hfull : P.biUnion F = Finset.univ.erase l := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hrem : (Finset.univ.erase l).card + 1 = N := by
      simpa using Finset.card_erase_add_one (Finset.mem_univ l)
    nlinarith
  have hmem : l' ∈ P.biUnion F := by
    rw [hfull]
    simp [Ne.symm hne]
  obtain ⟨p, hp, hpl'⟩ := Finset.mem_biUnion.mp hmem
  have hpl : I p l := by simpa [P] using hp
  have hpl' : I p l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hpl').2).2
  refine ⟨p, ⟨hpl, hpl'⟩, ?_⟩
  intro p' hp'
  by_contra hpp'
  obtain ⟨a, ha, hu⟩ := hpair p' p hpp'
  exact hne ((hu l ⟨hp'.1, hpl⟩).trans (hu l' ⟨hp'.2, hpl'⟩).symm)

lemma restricted_incidence_card_left_on (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (P : Finset (Fin N))
    (hdegree : ∀ p ∈ P, (Finset.univ.filter (fun l => I p l)).card = d) :
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
  exact Finset.sum_const_nat (fun p hp => (hf p).trans (hdegree p hp))

lemma degree_away_from_point (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (r p : Fin N) (hne : r ≠ p) :
    (Finset.univ.filter (fun l => I r l ∧ ¬ I p l)).card = q := by
  classical
  obtain ⟨c, hc, hu⟩ := hpair r p hne
  have heq : (Finset.univ.filter (fun l => I r l ∧ ¬ I p l)) =
      (Finset.univ.filter (fun l => I r l)).erase c := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hr, hp⟩
      refine ⟨?_, hr⟩
      intro heq
      exact hp (heq ▸ hc.2)
    · rintro ⟨hne, hr⟩
      exact ⟨hr, fun hp => hne (hu l ⟨hr, hp⟩)⟩
  rw [heq, Finset.card_erase_of_mem (by simp [hc.1])]
  rw [point_degree q N I hq hN hline hpair r]
  omega

lemma line_bound_of_avoided_line (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (Q : Finset (Fin N)) (ell : Fin N) (havoid : ∀ p ∈ Q, ¬ I p ell)
    (l : Fin N) : (Q.filter (fun r => I r l)).card ≤ q := by
  classical
  have hex : ∃ t : Fin N, I t l ∧ I t ell := by
    by_cases heq : l = ell
    · have hp : (Finset.univ.filter (fun t => I t l)).Nonempty := by
        apply Finset.card_pos.mp
        rw [hline]
        omega
      obtain ⟨t, ht⟩ := hp
      have hi : I t l := (Finset.mem_filter.mp ht).2
      exact ⟨t, hi, heq ▸ hi⟩
    · obtain ⟨t, ht, _⟩ := dual_pair q N I hq hN hline hpair l ell heq
      exact ⟨t, ht⟩
  obtain ⟨t, htl, htell⟩ := hex
  have hsub : Q.filter (fun r => I r l) ⊆ (Finset.univ.filter (fun r => I r l)).erase t := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    apply Finset.mem_erase.mpr
    refine ⟨?_, by simp [hr'.2]⟩
    intro heq
    exact havoid r hr'.1 (heq ▸ htell)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp [htl]), hline] at hc
  simpa using hc

lemma affine_neighborhood_surplus (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (Q : Finset (Fin N)) (hQ : Q.Nonempty) (ell : Fin N)
    (havoid : ∀ r ∈ Q, ¬ I r ell) :
    Q.card + q ≤ (Finset.univ.filter (fun l => ∃ r ∈ Q, I r l)).card := by
  classical
  obtain ⟨p, hp⟩ := hQ
  let R := Q.erase p
  let A := Finset.univ.filter (fun l => I p l)
  let U := Finset.univ.filter (fun l => ∃ r ∈ Q, I r l)
  let K := U \ A
  let E := (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ ¬ I p e.2)).filter
    (fun e => e.1 ∈ R)
  have hecard : E.card = R.card * q := by
    apply restricted_incidence_card_left_on N q (fun r l => I r l ∧ ¬ I p l) R
    intro r hr
    exact degree_away_from_point q N I hq hN hline hpair r p (Finset.mem_erase.mp hr).1
  have hK : ∀ e ∈ E, e.2 ∈ K := by
    intro e he
    have he' : (I e.1 e.2 ∧ ¬ I p e.2) ∧ e.1 ∈ R := by simpa [E] using he
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e.1, (Finset.mem_erase.mp he'.2).2, he'.1.1⟩
    · simpa [A] using he'.1.2
  have hcol (l : Fin N) : (E.filter (fun e => e.2 = l)).card ≤ q := by
    have hinj : (E.filter (fun e => e.2 = l)).card ≤ (Q.filter (fun r => I r l)).card := by
      apply Finset.card_le_card_of_injOn (fun e : Fin N × Fin N => e.1)
      · intro e he
        have heE : e ∈ E := (Finset.mem_filter.mp he).1
        have hel : e.2 = l := (Finset.mem_filter.mp he).2
        have he' : (I e.1 e.2 ∧ ¬ I p e.2) ∧ e.1 ∈ R := by simpa [E] using heE
        apply Finset.mem_filter.mpr
        refine ⟨(Finset.mem_erase.mp he'.2).2, ?_⟩
        simpa [hel] using he'.1.1
      · intro e he e' he' hfirst
        have hel : e.2 = l := (Finset.mem_filter.mp he).2
        have hel' : e'.2 = l := (Finset.mem_filter.mp he').2
        exact Prod.ext hfirst (hel.trans hel'.symm)
    exact hinj.trans (line_bound_of_avoided_line q N I hq hN hline hpair Q ell havoid l)
  have hs := Finset.sum_card_fiberwise_eq_card_filter E K Prod.snd
  have hfilter : E.filter (fun e => e.2 ∈ K) = E := Finset.filter_eq_self.mpr hK
  rw [hfilter] at hs
  have hcount : E.card ≤ K.card * q := by
    calc
      E.card = ∑ l ∈ K, (E.filter (fun e => e.2 = l)).card := hs.symm
      _ ≤ ∑ l ∈ K, q := Finset.sum_le_sum (fun l _ => hcol l)
      _ = K.card * q := by simp
  rw [hecard] at hcount
  have hRK : R.card ≤ K.card := Nat.le_of_mul_le_mul_right hcount (by omega)
  have hAU : A ⊆ U := by
    intro l hl
    have hi : I p l := by simpa [A] using hl
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, hp, hi⟩
  have hparts : K.card + A.card = U.card := Finset.card_sdiff_add_card_eq_card hAU
  have hAc : A.card = q + 1 := point_degree q N I hq hN hline hpair p
  have hRc : R.card + 1 = Q.card := Finset.card_erase_add_one hp
  change Q.card + q ≤ U.card
  omega

lemma mixed_cover_surplus (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ P ∨ l ∈ L)
    (hP : P ≠ Finset.univ) (hL : L ≠ Finset.univ) :
    N + q ≤ P.card + L.card := by
  classical
  let Q := Finset.univ \ P
  have hQ : Q.Nonempty := by
    by_contra hn
    apply hP
    ext p
    simp only [Finset.mem_univ, iff_true]
    by_contra hp
    exact hn ⟨p, by simp [Q, hp]⟩
  have hell : ∃ ell : Fin N, ell ∉ L := by
    by_contra hn
    apply hL
    ext ell
    simp only [Finset.mem_univ, iff_true]
    by_contra he
    exact hn ⟨ell, he⟩
  obtain ⟨ell, hell⟩ := hell
  have havoid : ∀ r ∈ Q, ¬ I r ell := by
    intro r hr hi
    rcases hcover r ell hi with hp | hl
    · exact (Finset.mem_sdiff.mp hr).2 hp
    · exact hell hl
  have hsur := affine_neighborhood_surplus q N I hq hN hline hpair Q hQ ell havoid
  have hsub : (Finset.univ.filter (fun l => ∃ r ∈ Q, I r l)) ⊆ L := by
    intro l hl
    obtain ⟨r, hr, hi⟩ := (Finset.mem_filter.mp hl).2
    rcases hcover r l hi with hp | hl
    · exact False.elim ((Finset.mem_sdiff.mp hr).2 hp)
    · exact hl
  have hc := Finset.card_le_card hsub
  have hparts : Q.card + P.card = N := by
    simpa [Q] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  omega

end PEqualNP.Outside.L_meta_2583_aux.AffineSurplus
