import PEqualNP.Outside.L_meta_3760

namespace PEqualNP.Outside.L_meta_2448_aux.earliestJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3760 PEqualNP.Outside.L_meta_3760.Close
open PEqualNP.Outside.L_meta_3760.M1528.P1.S98 (W AO AO_of_IsAO2 W_and)
open PEqualNP.Outside.L_meta_3760.M1528.P2 (OrR mem_orIn orR_mono opnd_eq graphFun_pair orR_le orR_cone)

lemma cone_earlier {n : ℕ} (C : Circuit) (i k : ℕ)
    (hk : k < C.gates.length) (hic : InCone n C i k) : i < k := by
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    rw [M1528.P2.inCone_iff n C i k hk] at hic
    obtain ⟨w, hwin, hnw, hwlt, hcase⟩ := hic
    rcases hcase with rfl | hc'
    · omega
    · have hlt' := ihk (w - n) (by omega) (by omega) hc'
      omega

lemma earliest_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hT : TopForm G C) (g : ℕ) (hg : g ∈ junk G C)
    (hmin : ∀ k ∈ junk G C, g ≤ k) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ ¬ BelowF G C g ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False) := by
  have hmem_iff : ∀ k, k ∈ junk G C ↔
      k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
    intro k
    have h1 := M1528.P1.junk_iff G C k
    simpa [BelowF] using h1
  obtain ⟨hg_lt, hg_op, hg_notB⟩ := (hmem_iff g).mp hg
  refine ⟨hg_lt, hg_op, hg_notB, ?_⟩
  intro h hh hop hc
  by_cases hB : BelowF G C h
  · exact hT h hh g hg_lt hop hB hg_op hc
  · have hlow := hmin h ((hmem_iff h).mpr ⟨hh, hop, hB⟩)
    have hearly := cone_earlier C h g hg_lt hc
    omega

lemma earliest_no_and_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g : ℕ) (hg : g ∈ junk G C)
    (hmin : ∀ k ∈ junk G C, g ≤ k)
    (b : Fin 2) :
    opnd C g b < n + g ∧
    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (opnd C g b) (n + h) := by
  have hA : AO n C := AO_of_IsAO2 n C hAO
  obtain ⟨hg_lt, hg_op, _, hno_in_g⟩ := earliest_no_and_ancestor G C hT g hg hmin
  have hlt := opnd_lt' hA g hg_lt b
  refine ⟨hlt, fun h hh hop hr => ?_⟩
  have hmem : opnd C g b ∈ (gateAt C g).inputs := by
    have := M1528.P2.opnd_eq n C hA g hg_lt
    fin_cases b <;> rw [this] <;> simp
  have hic : InCone n C h g := by
    by_cases hw : opnd C g b < n
    · have := orR_le n C hA _ _ hr; omega
    · obtain ⟨k, hk_eq⟩ : ∃ k, opnd C g b = n + k := ⟨opnd C g b - n, by omega⟩
      rcases orR_cone n C hA h (opnd C g b) hr k hk_eq (by omega) with rfl | hc
      · exact M1528.P2.inCone_c1 n C hA h g hg_lt (hk_eq ▸ hmem)
      · exact M1528.P2.inCone_c2 n C hA h k g hg_lt hc (hk_eq ▸ hmem)
  exact hno_in_g h hh hop hic
lemma earliest_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g : ℕ) (hg : g ∈ junk G C)
    (hmin : ∀ k ∈ junk G C, g ≤ k) :
    let P := side (n := n) C g 0
    let Q := side (n := n) C g 1
    let Wg := wmax G C g
    P.Nonempty ∧ Q.Nonempty ∧
    (∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true)) ∧
    (∀ w : Fin n, w ∈ Wg ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) ∧
    (∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q) := by
  have hA : AO n C := AO_of_IsAO2 n C hAO
  obtain ⟨hg_lt, hg_op, hg_notB, _⟩ := earliest_no_and_ancestor G C hT g hg hmin
  obtain ⟨h0_lt, h0_no⟩ := earliest_no_and_operand G C hAO hT g hg hmin 0
  obtain ⟨h1_lt, h1_no⟩ := earliest_no_and_operand G C hAO hT g hg hmin 1
  obtain ⟨hPne, hPeval⟩ := pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no
  obtain ⟨hQne, hQeval⟩ := pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no
  have hgeval : ∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ side (n := n) C g 0, x p = true) ∧ (∃ q ∈ side (n := n) C g 1, x q = true) := by
    intro x
    rw [W_and n C x g hg_lt hg_op (opnd C g 0) (opnd C g 1) (opnd_eq n C hA g hg_lt) h0_lt h1_lt,
      Bool.and_eq_true, hPeval x, hQeval x]
    rfl
  refine ⟨hPne, hQne, hgeval, ?_, ?_⟩
  · intro w
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw p hp q hq
      let x : Fin n → Bool := fun i => decide (i = p ∨ i = q ∨ i = w)
      have hgx : gateVal n C g x = true := by
        rw [← W_eq_gateVal, hgeval x]
        exact ⟨⟨p, hp, by simp [x]⟩, ⟨q, hq, by simp [x]⟩⟩
      have hxw : x w = true := by simp [x]
      have hF := hw x hgx hxw
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hF
      obtain ⟨a, b, hab, hxa, hxb⟩ := hF
      simp only [x, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl | rfl <;> rcases hxb with rfl | rfl | rfl
      · exact (G.irrefl hab).elim
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
      · exact Or.inl hab.symm
      · exact (G.irrefl hab).elim
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hab.symm)
      · exact Or.inr (Or.inr hab.symm)
      · exact (G.irrefl hab).elim
    · intro hcond x hgx hxw
      rw [← W_eq_gateVal, hgeval x] at hgx
      obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      rcases hcond p hp q hq with h | h | h
      · exact ⟨p, q, h, hxp, hxq⟩
      · exact ⟨p, w, h, hxp, hxw⟩
      · exact ⟨q, w, h, hxq, hxw⟩
  · simp only [BelowF, not_forall] at hg_notB
    obtain ⟨x, hx⟩ := hg_notB
    push Not at hx
    obtain ⟨hgx, hFx⟩ := hx
    rw [← W_eq_gateVal, hgeval x] at hgx
    obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
    refine ⟨p, hp, q, hq, fun hadj => hFx ?_⟩
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, q, hadj, hxp, hxq⟩

end PEqualNP.Outside.L_meta_2448_aux.earliestJunk
