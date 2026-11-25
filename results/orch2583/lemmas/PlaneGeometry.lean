import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Geometry

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

def Inc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    Finset (Fin N × Fin N) := (A ×ˢ B).filter (fun pl => I pl.1 pl.2)

theorem Inc_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ l ∈ B, (A.filter (fun p => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem Inc_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ p ∈ A, (B.filter (fun l => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

def edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) := Finset.univ.filter fun pl => I pl.1 pl.2

lemma inc_univ_eq_edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Inc I Finset.univ Finset.univ = edges I := by
  ext pl
  simp [Inc, edges]

lemma edge_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (edges I).card = N * (q + 1) := by
  rw [← inc_univ_eq_edges, Inc_right]
  simp_rw [hline]
  simp

lemma no_rectangle {N : ℕ} (I : Fin N → Fin N → Prop)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p p' l l' : Fin N) (hp : p ≠ p') (hl : l ≠ l') :
    ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  rintro ⟨a, b, c, d⟩
  exact hl ((huniq p p' hp).unique ⟨a, c⟩ ⟨b, d⟩)

lemma cover_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (P L : Finset (Fin N))
    (hcover : ∀ p l : Fin N, I p l → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [inc_univ_eq_edges]
    exact edge_count I hline
  have h1 : (Inc I P Finset.univ).card = P.card * (q + 1) := by
    rw [Inc_left]
    simp_rw [hpoint]
    simp
  have h2 : (Inc I Finset.univ L).card = L.card * (q + 1) := by
    rw [Inc_right]
    simp_rw [hline]
    simp
  have hsub : Inc I Finset.univ Finset.univ ⊆
      Inc I P Finset.univ ∪ Inc I Finset.univ L := by
    intro pl hpl
    have hi : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    rcases hcover pl.1 pl.2 hi with hp | hl
    · exact Finset.mem_union_left _ (by simp [Inc, hp, hi])
    · exact Finset.mem_union_right _ (by simp [Inc, hl, hi])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [h0, h1, h2, ← Nat.add_mul] at hc
  exact Nat.le_of_mul_le_mul_right hc (Nat.succ_pos q)

lemma hall_condition {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpoint : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (P : Finset (Fin N)) :
    P.card ≤ (Finset.univ.filter fun l => ∃ p ∈ P, I p l).card := by
  let L := Finset.univ.filter fun l => ∃ p ∈ P, I p l
  have h1 : (Inc I P Finset.univ).card = P.card * (q + 1) := by
    rw [Inc_left]
    simp_rw [hpoint]
    simp
  have h2 : (Inc I Finset.univ L).card = L.card * (q + 1) := by
    rw [Inc_right]
    simp_rw [hline]
    simp
  have hsub : Inc I P Finset.univ ⊆ Inc I Finset.univ L := by
    intro pl hpl
    have hp : pl.1 ∈ P := (Finset.mem_product.mp (Finset.mem_filter.mp hpl).1).1
    have hi : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    have hl : pl.2 ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, pl.1, hp, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hl⟩, hi⟩
  have hc := Finset.card_le_card hsub
  rw [h1, h2] at hc
  exact Nat.le_of_mul_le_mul_right hc (Nat.succ_pos q)

lemma plane_data {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) ∧
    (edges I).card = N * (q + 1) ∧
    (∀ P L : Finset (Fin N), (∀ p l : Fin N, I p l → p ∈ P ∨ l ∈ L) →
      N ≤ P.card + L.card) := by
  have hp := lines_through q I (by omega) hN hline huniq
  exact ⟨hp, edge_count I hline, fun P L hc => cover_lower I hline hp P L hc⟩

end PEqualNP.Outside.L_meta_2583_aux.Geometry
