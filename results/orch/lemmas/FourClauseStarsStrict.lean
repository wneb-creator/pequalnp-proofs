import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma rectangle_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (L R : Finset (Fin n))
    (hcross : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ T : Finset (Fin n), T.card ≤ 1 ∧
      ∀ u ∈ L, ∀ v ∈ R, u ∈ T ∨ v ∈ T := by
  classical
  by_cases hL : L.card ≤ 1
  · exact ⟨L, hL, fun _ hu _ _ => Or.inl hu⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
  have hsub : R ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha v hv, hcross b hb v hv⟩
  exact ⟨R, (Finset.card_le_card hsub).trans (hG a b hab), fun _ _ _ hv => Or.inr hv⟩

lemma independent_clause {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (clauses : Fin m → Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, ∃ v ∈ clauses i, x v = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ i, Disjoint (clauses i) S := by
  classical
  by_contra hnone
  have hall : ∀ i, ∃ v ∈ clauses i, v ∈ S := by
    intro i
    by_contra hnot
    apply hnone
    refine ⟨i, Finset.disjoint_left.mpr ?_⟩
    intro v hv hs
    exact hnot ⟨v, hv, hs⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hclean (fun w => decide (w ∈ S)) (by
    intro i
    obtain ⟨w, hw, hs⟩ := hall i
    exact ⟨w, hw, by simpa⟩)
  exact hS u (of_decide_eq_true hu) v (of_decide_eq_true hv) huv

lemma bipartite_pure_clauses {n m : ℕ} (G : SimpleGraph (Fin n))
    (L : Finset (Fin n)) (clauses : Fin m → Finset (Fin n))
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    (hR : ∀ u ∉ L, ∀ v ∉ L, ¬ G.Adj u v)
    (hne : ∀ i, (clauses i).Nonempty)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, ∃ v ∈ clauses i, x v = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ i j, i ≠ j ∧ clauses i ⊆ L ∧ Disjoint (clauses j) L := by
  classical
  obtain ⟨j, hj⟩ := independent_clause G L clauses hL hclean
  obtain ⟨i, hi⟩ := independent_clause G (Finset.univ \ L) clauses (by
    intro u hu v hv
    exact hR u (Finset.mem_sdiff.mp hu).2 v (Finset.mem_sdiff.mp hv).2) hclean
  have hisub : clauses i ⊆ L := by
    intro v hv
    by_contra hn
    exact Finset.disjoint_left.mp hi hv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
  refine ⟨i, j, ?_, hisub, hj⟩
  intro hij
  obtain ⟨v, hv⟩ := hne i
  exact Finset.disjoint_left.mp hj (hij ▸ hv) (hisub hv)

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma two_filter_cover_no_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hnone : ¬ ∃ p ∈ P, p ∈ U ∧ p ∈ V) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) (Q.filter (· ∈ V)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inl (Finset.mem_filter.mp hp).2) (Or.inr (Finset.mem_filter.mp hq).2))
  obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  obtain ⟨T₃, h₃, hc₃⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
    intro p hp q hq
    exact hcross p hp q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2.1) (Or.inr (Finset.mem_filter.mp hq).2.2))
  refine ⟨T₁ ∪ T₂ ∪ T₃, ?_, ?_⟩
  · have hx := Finset.card_union_le T₁ T₂
    have hy := Finset.card_union_le (T₁ ∪ T₂) T₃
    omega
  · intro p hp q hq hU hV
    have ht₁ : T₁ ⊆ T₁ ∪ T₂ ∪ T₃ := by intro w hw; simp only [Finset.mem_union]; exact Or.inl (Or.inl hw)
    have ht₂ : T₂ ⊆ T₁ ∪ T₂ ∪ T₃ := by intro w hw; simp only [Finset.mem_union]; exact Or.inl (Or.inr hw)
    have ht₃ : T₃ ⊆ T₁ ∪ T₂ ∪ T₃ := Finset.subset_union_right
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun h => hnone ⟨p, hp, hpU, h⟩
      exact (hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q
        (Finset.mem_filter.mpr ⟨hq, hV.resolve_left hpV⟩)).imp (ht₁ ·) (ht₁ ·)
    · by_cases hpV : p ∈ V
      · exact (hc₂ p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q
          (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU⟩)).imp (ht₂ ·) (ht₂ ·)
      · exact (hc₃ p hp q (Finset.mem_filter.mpr
          ⟨hq, hU.resolve_left hpU, hV.resolve_left hpV⟩)).imp (ht₃ ·) (ht₃ ·)

lemma two_filter_cover_anchor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hQ : 2 ≤ Q.card) (a b : Fin n)
    (haP : a ∈ P) (haU : a ∈ U) (haV : a ∈ V)
    (hbP : b ∈ P) (hbU : b ∈ U) (hbV : b ∉ V) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  have hab : a ≠ b := by intro h; exact hbV (h ▸ haV)
  have hadj (q : Fin n) (hq : q ∈ Q) : G.Adj a q :=
    hcross a haP q hq (Or.inl haU) (Or.inl haV)
  have hsmall : (Q.filter (· ∈ V)).card ≤ 1 := by
    have hsub : Q.filter (· ∈ V) ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
      intro q hq
      obtain ⟨hq, hqV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj q hq,
        hcross b hbP q hq (Or.inl hbU) (Or.inr hqV)⟩
    exact (Finset.card_le_card hsub).trans (hG a b hab)
  have huniq (p : Fin n) (hp : p ∈ P) (hpU : p ∈ U) (hpV : p ∈ V) : p = a := by
    by_contra hne
    have hsub : Q ⊆ Finset.univ.filter (fun q => G.Adj p q ∧ G.Adj a q) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hcross p hp q hq (Or.inl hpU) (Or.inl hpV), hadj q hq⟩
    have hx := (Finset.card_le_card hsub).trans (hG p a hne)
    omega
  obtain ⟨S, hS, hcS⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  refine ⟨{a} ∪ Q.filter (· ∈ V) ∪ S, ?_, ?_⟩
  · have hx := Finset.card_union_le ({a} : Finset (Fin n)) (Q.filter (· ∈ V))
    have hy := Finset.card_union_le ({a} ∪ Q.filter (· ∈ V)) S
    have hz : ({a} : Finset (Fin n)).card = 1 := Finset.card_singleton a
    omega
  · intro p hp q hq hU hV
    have htA : a ∈ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := by simp
    have htQ : Q.filter (· ∈ V) ⊆ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := by
      intro w hw
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    have htS : S ⊆ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := Finset.subset_union_right
    by_cases hpV : p ∈ V
    · by_cases hpU : p ∈ U
      · exact Or.inl (huniq p hp hpU hpV ▸ htA)
      · exact (hcS p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q
          (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU⟩)).imp (htS ·) (htS ·)
    · exact Or.inr (htQ (Finset.mem_filter.mpr ⟨hq, hV.resolve_left hpV⟩))

lemma two_filter_cover_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  by_cases hQ : Q.card ≤ 1
  · exact ⟨Q, by omega, fun _ _ _ hq _ _ => Or.inr hq⟩
  by_cases hboth : ∃ a ∈ P, a ∈ U ∧ a ∈ V
  · obtain ⟨a, haP, haU, haV⟩ := hboth
    by_cases hleft : ∃ b ∈ P, b ∈ U ∧ b ∉ V
    · obtain ⟨b, hbP, hbU, hbV⟩ := hleft
      exact two_filter_cover_anchor G hG P Q U V hcross (by omega) a b haP haU haV hbP hbU hbV
    by_cases hright : ∃ b ∈ P, b ∈ V ∧ b ∉ U
    · obtain ⟨b, hbP, hbV, hbU⟩ := hright
      obtain ⟨T, hT, hcT⟩ := two_filter_cover_anchor G hG P Q V U
        (fun p hp q hq hV hU => hcross p hp q hq hU hV) (by omega)
        a b haP haV haU hbP hbV hbU
      exact ⟨T, hT, fun p hp q hq hU hV => hcT p hp q hq hV hU⟩
    have hequiv (p : Fin n) (hp : p ∈ P) : p ∈ U ↔ p ∈ V := by
      constructor
      · intro h
        by_contra hn
        exact hleft ⟨p, hp, h, hn⟩
      · intro h
        by_contra hn
        exact hright ⟨p, hp, h, hn⟩
    obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) Q (by
      intro p hp q hq
      obtain ⟨hp, hpU⟩ := Finset.mem_filter.mp hp
      exact hcross p hp q hq (Or.inl hpU) (Or.inl ((hequiv p hp).mp hpU)))
    obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
      intro p hp q hq
      obtain ⟨hq, hqU, hqV⟩ := Finset.mem_filter.mp hq
      exact hcross p hp q hq (Or.inr hqU) (Or.inr hqV))
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · have hx := Finset.card_union_le T₁ T₂
      omega
    · intro p hp q hq hU hV
      by_cases hpU : p ∈ U
      · exact (hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q hq).imp
          (Finset.mem_union_left T₂) (Finset.mem_union_left T₂)
      · have hpV : p ∉ V := fun hv => hpU ((hequiv p hp).mpr hv)
        exact (hc₂ p hp q (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU, hV.resolve_left hpV⟩)).imp
          (Finset.mem_union_right T₁) (Finset.mem_union_right T₁)
  · exact two_filter_cover_no_both G hG P Q U V hcross hboth

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma nested_neighbor_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q) (a b : Fin n)
    (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) (hsub : N a ⊆ N b) :
    (N a).card ≤ 1 := by
  have hinc : N a ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj a ha q hq, hAdj b hb q (hsub hq)⟩
  exact (Finset.card_le_card hinc).trans (hG a b hne)

lemma two_filter_heavy_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    (P.filter (fun p => 2 ≤ (Q.filter (fun q =>
      (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card)).card ≤ 2 := by
  classical
  let N : Fin n → Finset (Fin n) := fun p => Q.filter (fun q =>
    (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))
  let H := P.filter (fun p => 2 ≤ (N p).card)
  change H.card ≤ 2
  have hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q := by
    intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  by_cases hboth : ∃ a ∈ H, a ∈ U ∧ a ∈ V
  · obtain ⟨a, ha, haU, haV⟩ := hboth
    have hcard : H.card ≤ 1 := Finset.card_le_one.mpr (by
      intro b hb c hc
      have heq (b : Fin n) (hb : b ∈ H) : b = a := by
        by_contra hne
        obtain ⟨hbP, hbN⟩ := Finset.mem_filter.mp hb
        have hsub : N b ⊆ N a := by
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, Or.inl haU, Or.inl haV⟩
        have hx := nested_neighbor_small G hG P N hAdj b a hbP (Finset.mem_filter.mp ha).1 hne hsub
        omega
      exact (heq b hb).trans (heq c hc).symm)
    omega
  by_cases hneither : ∃ a ∈ H, a ∉ U ∧ a ∉ V
  · obtain ⟨a, ha, haU, haV⟩ := hneither
    have hcard : H.card ≤ 1 := Finset.card_le_one.mpr (by
      intro b hb c hc
      have heq (b : Fin n) (hb : b ∈ H) : b = a := by
        by_contra hne
        have hsub : N a ⊆ N b := by
          intro q hq
          obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_filter.mpr ⟨hq, Or.inr (hU.resolve_left haU), Or.inr (hV.resolve_left haV)⟩
        have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
          (Finset.mem_filter.mp hb).1 (Ne.symm hne) hsub
        have haN := (Finset.mem_filter.mp ha).2
        omega
      exact (heq b hb).trans (heq c hc).symm)
    omega
  have hsmallU : (H.filter (· ∈ U)).card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    obtain ⟨ha, haU⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbU⟩ := Finset.mem_filter.mp hb
    have haV : a ∉ V := fun h => hboth ⟨a, ha, haU, h⟩
    have hbV : b ∉ V := fun h => hboth ⟨b, hb, hbU, h⟩
    by_contra hne
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, _, hV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, Or.inl hbU, Or.inr (hV.resolve_left haV)⟩
    have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 hne hsub
    have haN := (Finset.mem_filter.mp ha).2
    omega)
  have hsmallV : (H.filter (· ∈ V)).card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    obtain ⟨ha, haV⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbV⟩ := Finset.mem_filter.mp hb
    have haU : a ∉ U := fun h => hboth ⟨a, ha, h, haV⟩
    by_contra hne
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, hU, _⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, Or.inr (hU.resolve_left haU), Or.inl hbV⟩
    have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 hne hsub
    have haN := (Finset.mem_filter.mp ha).2
    omega)
  have hsub : H ⊆ H.filter (· ∈ U) ∪ H.filter (· ∈ V) := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hpU⟩)
    · have hpV : p ∈ V := by
        by_contra hn
        exact hneither ⟨p, hp, hpU, hn⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpV⟩)
  have hx := Finset.card_le_card hsub
  have hy := Finset.card_union_le (H.filter (· ∈ U)) (H.filter (· ∈ V))
  omega

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma degree_sum_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hQ : Q.Nonempty) (hsub : ∀ p ∈ P, N p ⊆ Q)
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q)
    (hheavy : (P.filter (fun p => 2 ≤ (N p).card)).card ≤ 2) :
    (∑ p ∈ P, (N p).card) + 1 ≤ P.card + Q.card := by
  classical
  let H := P.filter (fun p => 2 ≤ (N p).card)
  have hHP : H ⊆ P := Finset.filter_subset _ _
  have hsum : (∑ p ∈ P \ H, (N p).card) + (∑ p ∈ H, (N p).card) = ∑ p ∈ P, (N p).card :=
    Finset.sum_sdiff hHP
  have hcard := Finset.card_sdiff_add_card_eq_card hHP
  have hlight : (∑ p ∈ P \ H, (N p).card) ≤ (P \ H).card := by
    calc
      _ ≤ ∑ _p ∈ P \ H, 1 := Finset.sum_le_sum (by
        intro p hp
        obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
        have hn2 : ¬ 2 ≤ (N p).card := fun h => hn (Finset.mem_filter.mpr ⟨hp, h⟩)
        omega)
      _ = _ := by simp
  have hQpos := Finset.card_pos.mpr hQ
  by_cases h0 : H.card = 0
  · have he : H = ∅ := Finset.card_eq_zero.mp h0
    have hsum0 : (∑ p ∈ H, (N p).card) = 0 := by rw [he]; simp
    omega
  have hlarge : (∑ p ∈ H, (N p).card) + 1 ≤ Q.card + H.card := by
    by_cases h1 : H.card = 1
    · obtain ⟨a, he⟩ := Finset.card_eq_one.mp h1
      have haH : a ∈ H := by rw [he]; simp
      have ha := Finset.card_le_card (hsub a (hHP haH))
      have hs : (∑ p ∈ H, (N p).card) = (N a).card := by rw [he]; simp
      omega
    · have h2 : H.card = 2 := by change H.card ≤ 2 at hheavy; omega
      obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
      have haH : a ∈ H := by rw [he]; simp
      have hbH : b ∈ H := by rw [he]; simp
      have haP := hHP haH
      have hbP := hHP hbH
      have huni : (N a ∪ N b).card ≤ Q.card := Finset.card_le_card
        (Finset.union_subset (hsub a haP) (hsub b hbP))
      have hinter : (N a ∩ N b).card ≤ 1 := by
        have hinc : N a ∩ N b ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
          intro q hq
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hAdj a haP q (Finset.mem_inter.mp hq).1,
            hAdj b hbP q (Finset.mem_inter.mp hq).2⟩
        exact (Finset.card_le_card hinc).trans (hG a b hab)
      have hx := Finset.card_union_add_card_inter (N a) (N b)
      have hs : (∑ p ∈ H, (N p).card) = (N a).card + (N b).card := by rw [he]; simp [hab]
      omega
  omega

lemma two_filter_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hQ : Q.Nonempty)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    (∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card) + 1 ≤
      P.card + Q.card := by
  apply degree_sum_bound G hG P Q _ hQ
  · intro p _
    exact Finset.filter_subset _ _
  · intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  · exact two_filter_heavy_card G hG P Q U V hcross

lemma two_filter_gate_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ((∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card) +
        T.card - 1 ≤ P.card + Q.card + 1) ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨T, hT, hcT⟩ := two_filter_cover_three G hG P Q U V hcross
    have he := two_filter_edge_bound G hG P Q U V hQ hcross
    exact ⟨T, hT, by omega, hcT⟩
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    refine ⟨∅, by simp, ?_, ?_⟩
    · simp [he]
    · intro p hp q hq
      rw [he] at hq
      simp at hq

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.StarDecomposition

lemma directed_stars {n : ℕ} (R : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : R.Nonempty) (hT : ∀ e ∈ R, e.1 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum = R.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R) ∧
      (∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2) := by
  classical
  let S := R.image Prod.fst
  let N : Fin n → Finset (Fin n) := fun c => (R.filter (fun e => e.1 = c)).image Prod.snd
  let ss : List (Fin n × List (Fin n)) := S.toList.map (fun c => (c, (N c).toList))
  have hNm (c v : Fin n) : v ∈ N c ↔ (c, v) ∈ R := by
    constructor
    · intro hv
      obtain ⟨⟨a, b⟩, he, hv⟩ := Finset.mem_image.mp hv
      obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
      dsimp at ha hv
      subst a
      subst b
      exact he
    · intro hv
      exact Finset.mem_image.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨hv, rfl⟩, rfl⟩
  have hNcard (c : Fin n) : (N c).card = (R.filter (fun e => e.1 = c)).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  have hlen : ss.length = S.card := by simp [ss]
  have hScard : S.card ≤ T.card := Finset.card_le_card (by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact hT e he)
  have hssne : ss ≠ [] := by
    intro he
    obtain ⟨e, heR⟩ := hne
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e.1, Finset.mem_image.mpr ⟨e, heR, rfl⟩⟩
    simp only [he, List.length_nil] at hlen
    omega
  have hentry : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R := by
    intro s hs v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact (hNm c v).mp (by simpa using hv)
  have hall : ∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2 := by
    intro e he
    refine ⟨(e.1, (N e.1).toList), ?_, rfl, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨e.1, Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
    · exact Finset.mem_toList.mpr ((hNm e.1 e.2).mpr he)
  have hnonempty : ∀ s ∈ ss, s.2 ≠ [] := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hcS : c ∈ S := by simpa using hc
    obtain ⟨e, he, hc⟩ := Finset.mem_image.mp hcS
    have hmem : e.2 ∈ (N c).toList := Finset.mem_toList.mpr ((hNm c e.2).mpr (by rw [← hc]; exact he))
    intro hn
    change (N c).toList = [] at hn
    rw [hn] at hmem
    simp at hmem
  have hcost : (ss.map fun s => s.2.length).sum = R.card := by
    simp only [ss, List.map_map, Function.comp_def, Finset.length_toList]
    rw [Finset.sum_map_toList]
    simp_rw [hNcard]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  exact ⟨ss, hssne, hnonempty, hlen.trans_le hScard, hcost, hentry, hall⟩

lemma oriented_stars {n : ℕ} (E : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : E.Nonempty) (hT : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum ≤ E.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)) := by
  classical
  let orient : (Fin n × Fin n) → (Fin n × Fin n) := fun e =>
    if e.1 ∈ T then e else (e.2, e.1)
  let R := E.image orient
  have hRne : R.Nonempty := Finset.Nonempty.image hne orient
  have hRT : ∀ e ∈ R, e.1 ∈ T := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    by_cases hh : f.1 ∈ T
    · simpa [orient, hh] using hh
    · simpa [orient, hh] using (hT f hf).resolve_left hh
  obtain ⟨ss, hss, hneigh, hlen, hcost, hentry, hall⟩ := directed_stars R T hRne hRT
  have hedges : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E := by
    intro s hs v hv
    obtain ⟨e, he, hor⟩ := Finset.mem_image.mp (hentry s hs v hv)
    by_cases hh : e.1 ∈ T
    · have heq : e = (s.1, v) := by simpa [orient, hh] using hor
      exact Or.inl (heq ▸ he)
    · have heq : (e.2, e.1) = (s.1, v) := by simpa [orient, hh] using hor
      have heq' : e = (v, s.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      exact Or.inr (heq' ▸ he)
  refine ⟨ss, hss, hneigh, hlen, hcost.trans_le (Finset.card_image_le), hedges, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hxs, v, hv, hxv⟩
    rcases hedges s hs v hv with he | he
    · exact ⟨(s.1, v), he, hxs, hxv⟩
    · exact ⟨(v, s.1), he, hxv, hxs⟩
  · rintro ⟨e, he, hx1, hx2⟩
    have heR : orient e ∈ R := Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨s, hs, hs1, hv⟩ := hall (orient e) heR
    refine ⟨s, hs, ?_, (orient e).2, hv, ?_⟩
    · rw [hs1]
      by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx1
      · simpa [orient, hh] using hx2
    · by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx2
      · simpa [orient, hh] using hx1

end PEqualNP.Outside.L_meta_1477.StarDecomposition


namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

def filteredEdges {n : ℕ} (P Q U V : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (P ×ˢ Q).filter (fun e => (e.1 ∈ U ∨ e.2 ∈ U) ∧ (e.1 ∈ V ∨ e.2 ∈ V))

lemma filteredEdges_card {n : ℕ} (P Q U V : Finset (Fin n)) :
    (filteredEdges P Q U V).card =
      ∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card := by
  classical
  let E := filteredEdges P Q U V
  have hfiber (p : Fin n) (hp : p ∈ P) :
      E.filter (fun e => e.1 = p) =
        (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).image (fun q => (p, q)) := by
    ext e
    constructor
    · intro he
      obtain ⟨he, hep⟩ := Finset.mem_filter.mp he
      obtain ⟨hepQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨_, heQ⟩ := Finset.mem_product.mp hepQ
      refine Finset.mem_image.mpr ⟨e.2, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨heQ, hep ▸ hU, hep ▸ hV⟩
      · exact Prod.ext hep.symm rfl
    · intro he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hU, hV⟩, rfl⟩
  have hcard (p : Fin n) (hp : p ∈ P) :
      (E.filter (fun e => e.1 = p)).card =
        (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card := by
    rw [hfiber p hp]
    apply Finset.card_image_of_injective
    intro q r h
    exact congrArg Prod.snd h
  have hs := Finset.sum_card_fiberwise_eq_card_filter E P Prod.fst
  have hfilter : E.filter (fun e => e.1 ∈ P) = E := Finset.filter_eq_self.mpr (by
    intro e he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
  rw [hfilter] at hs
  rw [← hs]
  exact Finset.sum_congr rfl hcard

lemma filtered_stars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hne : (filteredEdges P Q U V).Nonempty) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ 3 ∧
      (ss.map fun s => s.2.length).sum + ss.length ≤ P.card + Q.card + 2 ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, G.Adj s.1 v) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ filteredEdges P Q U V, x e.1 = true ∧ x e.2 = true)) := by
  classical
  obtain ⟨T, hT, hbudget, hcover⟩ := two_filter_gate_budget G hG P Q U V hcross
  have hcov : ∀ e ∈ filteredEdges P Q U V, e.1 ∈ T ∨ e.2 ∈ T := by
    intro e he
    obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
    exact hcover e.1 hp e.2 hq hU hV
  obtain ⟨ss, hss, hsne, hlen, hcost, hentry, hfun⟩ :=
    StarDecomposition.oriented_stars (filteredEdges P Q U V) T hne hcov
  have hcard := filteredEdges_card P Q U V
  have hpos := Finset.card_pos.mpr hne
  refine ⟨ss, hss, hsne, hlen.trans hT, ?_, ?_, hfun⟩
  · omega
  · intro s hs v hv
    rcases hentry s hs v hv with he | he
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact hcross s.1 hp v hq hU hV
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact (hcross v hp s.1 hq hU hV).symm

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses


namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm PEqualNP.EdgeOwnership

def clauseValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def fourValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  (clauseValue P x && clauseValue Q x) && (clauseValue U x && clauseValue V x)

def edgeValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ filteredEdges P Q U V, x e.1 = true ∧ x e.2 = true)

lemma edgeValue_le_fourValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) :
    edgeValue P Q U V x ≤ fourValue P Q U V x := by
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hx1, hx2⟩ := of_decide_eq_true hx
  obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
  simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨e.1, hp, hx1⟩, ⟨e.2, hq, hx2⟩⟩, ?_, ?_⟩
  · rcases hU with h | h
    · exact ⟨e.1, h, hx1⟩
    · exact ⟨e.2, h, hx2⟩
  · rcases hV with h | h
    · exact ⟨e.1, h, hx1⟩
    · exact ⟨e.2, h, hx2⟩

lemma edgeValue_pair_eq_fourValue {n : ℕ} (P Q U V : Finset (Fin n))
    (hdis : Disjoint P Q) (u v : Fin n) :
    edgeValue P Q U V (pairInput u v) = fourValue P Q U V (pairInput u v) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact Bool.le_iff_imp.mp (edgeValue_le_fourValue P Q U V (pairInput u v))
  · intro hf
    simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨p, hp, hpx⟩, ⟨q, hq, hqx⟩⟩, ⟨r, hr, hrx⟩, ⟨s, hs, hsx⟩⟩ := hf
    simp only [pairInput, decide_eq_true_eq] at hpx hqx hrx hsx
    have hUV : u ∈ U ∨ v ∈ U := by rcases hrx with rfl | rfl <;> simp_all
    have hVV : u ∈ V ∨ v ∈ V := by rcases hsx with rfl | rfl <;> simp_all
    have hpq : p ≠ q := fun he => Finset.disjoint_left.mp hdis hp (he ▸ hq)
    simp only [edgeValue, decide_eq_true_eq]
    change ∃ e ∈ filteredEdges P Q U V, pairInput u v e.1 = true ∧ pairInput u v e.2 = true
    rcases hpx with rfl | rfl <;> rcases hqx with rfl | rfl
    · exact (hpq rfl).elim
    · refine ⟨(p, q), ?_, by simp [pairInput], by simp [pairInput]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hUV, hVV⟩
    · refine ⟨(p, q), ?_, by simp [pairInput], by simp [pairInput]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hUV.symm, hVV.symm⟩
    · exact (hpq rfl).elim

lemma filtered_stars_semantic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hdis : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hne : (filteredEdges P Q U V).Nonempty) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ 3 ∧
      (ss.map fun s => s.2.length).sum + ss.length ≤ P.card + Q.card + 2 ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, G.Adj s.1 v) ∧
      (∀ x : Fin n → Bool, (ss.any fun s => x s.1 && s.2.any x) ≤ fourValue P Q U V x) ∧
      (∀ u v : Fin n, (ss.any fun s => pairInput u v s.1 && s.2.any (pairInput u v)) =
        fourValue P Q U V (pairInput u v)) := by
  obtain ⟨ss, hss, hsne, hlen, hcost, hclean, hfun⟩ := filtered_stars G hG P Q U V hcross hne
  refine ⟨ss, hss, hsne, hlen, hcost, hclean, ?_, ?_⟩
  · intro x
    rw [hfun x]
    exact edgeValue_le_fourValue P Q U V x
  · intro u v
    rw [hfun (pairInput u v)]
    exact edgeValue_pair_eq_fourValue P Q U V hdis u v

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.MixedShared
open PEqualNP.TopForm

lemma common_filter_forces_centers {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
      a = p ∨ b = q := by
  classical
  intro a ha b hb hU hV
  by_cases hap : a = p
  · exact Or.inl hap
  apply Or.inr
  have hs := Finset.card_le_one.mp (hG a p hap)
  apply hs
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha b hb hU hV,
      hcross p hp b hb (Or.inl hpU) (Or.inl hpV)⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a ha q hq (Or.inr hqU) (Or.inr hqV),
      hcross p hp q hq (Or.inl hpU) (Or.inl hpV)⟩

lemma common_filter_cover_two {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ G.Adj p q ∧
      ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
        a ∈ T ∨ b ∈ T := by
  classical
  refine ⟨{p, q}, by simpa using (Finset.card_insert_le p ({q} : Finset (Fin n))),
    hcross p hp q hq (Or.inl hpU) (Or.inl hpV), ?_⟩
  intro a ha b hb hU hV
  rcases common_filter_forces_centers G hG P Q U V hcross p q hp hq hpU hpV hqU hqV
    a ha b hb hU hV with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

lemma two_common_left_force_right_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hP : 2 ≤ (P.filter fun p => p ∈ U ∧ p ∈ V).card) : Q.card ≤ 1 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (P.filter fun p => p ∈ U ∧ p ∈ V).card)
  obtain ⟨haP, haU, haV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbU, hbV⟩ := Finset.mem_filter.mp hb
  have hsub : Q ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a haP q hq (Or.inl haU) (Or.inl haV),
      hcross b hbP q hq (Or.inl hbU) (Or.inl hbV)⟩
  exact (Finset.card_le_card hsub).trans (hG a b hab)

lemma two_common_right_force_left_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hQ : 2 ≤ (Q.filter fun q => q ∈ U ∧ q ∈ V).card) : P.card ≤ 1 :=
  two_common_left_force_right_small G hG Q P U V
    (fun a ha b hb hU hV => (hcross b hb a ha hU.symm hV.symm).symm) hQ

end PEqualNP.Outside.L_meta_1477.MixedShared


namespace PEqualNP.Outside.L_meta_1477.FourClauseCover

open PEqualNP.TopForm TwoJunkClauses

def Obstruction {n : ℕ} (P Q U V : Finset (Fin n)) : Prop :=
  (P.filter (fun p => p ∈ U ∧ p ∉ V)).Nonempty ∧
  (P.filter (fun p => p ∈ V ∧ p ∉ U)).Nonempty ∧
  (P.filter (fun p => p ∉ U ∧ p ∉ V)).Nonempty ∧
  (Q.filter (fun q => q ∈ U ∧ q ∉ V)).Nonempty ∧
  (Q.filter (fun q => q ∈ V ∧ q ∉ U)).Nonempty ∧
  (Q.filter (fun q => q ∈ U ∧ q ∈ V)).Nonempty

lemma clean_no_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) : ¬ Obstruction P Q U V := by
  classical
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨z, hz⟩⟩
  obtain ⟨haP, haU, haV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbV, hbU⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcP, hcU, hcV⟩ := Finset.mem_filter.mp hc
  obtain ⟨hyQ, hyU, hyV⟩ := Finset.mem_filter.mp hy
  obtain ⟨hxQ, hxV, hxU⟩ := Finset.mem_filter.mp hx
  obtain ⟨hzQ, hzU, hzV⟩ := Finset.mem_filter.mp hz
  have hcz := hcross c hcP z hzQ (Or.inr hzU) (Or.inr hzV)
  have hax := hcross a haP x hxQ (Or.inl haU) (Or.inr hxV)
  have haz := hcross a haP z hzQ (Or.inl haU) (Or.inr hzV)
  have hby := hcross b hbP y hyQ (Or.inr hyU) (Or.inl hbV)
  have hbz := hcross b hbP z hzQ (Or.inr hzU) (Or.inl hbV)
  have hca : c ≠ a := by intro he; exact hcU (he ▸ haU)
  have hcb : c ≠ b := by intro he; exact hcV (he ▸ hbV)
  have hcx : ¬ G.Adj c x := by
    intro hh
    have he : x = z := Finset.card_le_one.mp (hG c a hca) x
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hax⟩) z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz, haz⟩)
    exact hxU (he ▸ hzU)
  have hcy : ¬ G.Adj c y := by
    intro hh
    have he : y = z := Finset.card_le_one.mp (hG c b hcb) y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hby⟩) z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz, hbz⟩)
    exact hyV (he ▸ hzV)
  let input : Fin n → Bool := fun w => decide (w = c ∨ w = x ∨ w = y)
  have hf : fourValue P Q U V input = true := by
    simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨c, hcP, by simp [input]⟩, ⟨x, hxQ, by simp [input]⟩⟩,
      ⟨y, hyU, by simp [input]⟩, ⟨x, hxV, by simp [input]⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hclean input hf
  simp only [input, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact G.loopless.irrefl _ huv
  · exact hcx huv
  · exact hcy huv
  · exact hcx huv.symm
  · exact G.loopless.irrefl _ huv
  · exact hQ _ hxQ _ hyQ huv
  · exact hcy huv.symm
  · exact hQ _ hyQ _ hxQ huv
  · exact G.loopless.irrefl _ huv

end PEqualNP.Outside.L_meta_1477.FourClauseCover

namespace PEqualNP.Outside.L_meta_1477.FourClauseCover

open PEqualNP.TopForm TwoJunkClauses

lemma no_both_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hnone : ¬ ∃ p ∈ P, p ∈ U ∧ p ∈ V) (hbad : ¬ Obstruction P Q U V) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) (Q.filter (· ∈ V)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inl (Finset.mem_filter.mp hp).2) (Or.inr (Finset.mem_filter.mp hq).2))
  obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  obtain ⟨T₃, h₃, hc₃⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
    intro p hp q hq
    exact hcross p hp q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2.1) (Or.inr (Finset.mem_filter.mp hq).2.2))
  have hfirst (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hpU : p ∈ U) (hqV : q ∈ V) :
      p ∈ T₁ ∨ q ∈ T₁ := hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q (Finset.mem_filter.mpr ⟨hq, hqV⟩)
  have hsecond (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hpV : p ∈ V) (hqU : q ∈ U) :
      p ∈ T₂ ∨ q ∈ T₂ := hc₂ p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q (Finset.mem_filter.mpr ⟨hq, hqU⟩)
  have hthird (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hqU : q ∈ U) (hqV : q ∈ V) :
      p ∈ T₃ ∨ q ∈ T₃ := hc₃ p hp q (Finset.mem_filter.mpr ⟨hq, hqU, hqV⟩)
  have h12 : (T₁ ∪ T₂).card ≤ 2 := by have h := Finset.card_union_le T₁ T₂; omega
  have h13 : (T₁ ∪ T₃).card ≤ 2 := by have h := Finset.card_union_le T₁ T₃; omega
  have h23 : (T₂ ∪ T₃).card ≤ 2 := by have h := Finset.card_union_le T₂ T₃; omega
  by_cases hB : (P.filter (fun p => p ∈ U ∧ p ∉ V)).Nonempty
  swap
  · refine ⟨T₂ ∪ T₃, h23, ?_⟩
    intro p hp q hq hU hV
    have hpU : p ∉ U := by
      intro hu
      have hv : p ∉ V := fun hv => hnone ⟨p, hp, hu, hv⟩
      exact hB ⟨p, Finset.mem_filter.mpr ⟨hp, hu, hv⟩⟩
    have hqU := hU.resolve_left hpU
    by_cases hpV : p ∈ V
    · exact (hsecond p hp q hq hpV hqU).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (hthird p hp q hq hqU (hV.resolve_left hpV)).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hC : (P.filter (fun p => p ∈ V ∧ p ∉ U)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₃, h13, ?_⟩
    intro p hp q hq hU hV
    have hpV : p ∉ V := by
      intro hv
      have hu : p ∉ U := fun hu => hnone ⟨p, hp, hu, hv⟩
      exact hC ⟨p, Finset.mem_filter.mpr ⟨hp, hv, hu⟩⟩
    have hqV := hV.resolve_left hpV
    by_cases hpU : p ∈ U
    · exact (hfirst p hp q hq hpU hqV).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (hthird p hp q hq (hU.resolve_left hpU) hqV).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hD : (P.filter (fun p => p ∉ U ∧ p ∉ V)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₂, h12, ?_⟩
    intro p hp q hq hU hV
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
    · have hpV : p ∈ V := by
        by_contra hn
        exact hD ⟨p, Finset.mem_filter.mpr ⟨hp, hpU, hn⟩⟩
      exact (hsecond p hp q hq hpV (hU.resolve_left hpU)).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hRU : (Q.filter (fun q => q ∈ U ∧ q ∉ V)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₃, h13, ?_⟩
    intro p hp q hq hU hV
    by_cases hqU : q ∈ U
    · have hqV : q ∈ V := by
        by_contra hn
        exact hRU ⟨q, Finset.mem_filter.mpr ⟨hq, hqU, hn⟩⟩
      exact (hthird p hp q hq hqU hqV).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
    · have hpU := hU.resolve_right hqU
      have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  by_cases hRV : (Q.filter (fun q => q ∈ V ∧ q ∉ U)).Nonempty
  swap
  · refine ⟨T₂ ∪ T₃, h23, ?_⟩
    intro p hp q hq hU hV
    by_cases hqV : q ∈ V
    · have hqU : q ∈ U := by
        by_contra hn
        exact hRV ⟨q, Finset.mem_filter.mpr ⟨hq, hqV, hn⟩⟩
      exact (hthird p hp q hq hqU hqV).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
    · have hpV := hV.resolve_right hqV
      have hpU : p ∉ U := fun hu => hnone ⟨p, hp, hu, hpV⟩
      exact (hsecond p hp q hq hpV (hU.resolve_left hpU)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  by_cases hRB : (Q.filter (fun q => q ∈ U ∧ q ∈ V)).Nonempty
  · exact (hbad ⟨hB, hC, hD, hRU, hRV, hRB⟩).elim
  · refine ⟨T₁ ∪ T₂, h12, ?_⟩
    intro p hp q hq hU hV
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
    · have hqU := hU.resolve_left hpU
      have hpV : p ∈ V := by
        by_contra hn
        exact hRB ⟨q, Finset.mem_filter.mpr ⟨hq, hqU, hV.resolve_left hn⟩⟩
      exact (hsecond p hp q hq hpV hqU).imp (Finset.mem_union_right _) (Finset.mem_union_right _)

lemma clean_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hP : ∀ p ∈ P, ∀ r ∈ P, ¬ G.Adj p r)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  have hbad := clean_no_obstruction G hG P Q U V hcross hQ hclean
  by_cases hPB : ∃ p ∈ P, p ∈ U ∧ p ∈ V
  · obtain ⟨p, hp, hpU, hpV⟩ := hPB
    by_cases hQB : ∃ q ∈ Q, q ∈ U ∧ q ∈ V
    · obtain ⟨q, hq, hqU, hqV⟩ := hQB
      obtain ⟨T, hT, _, hc⟩ := MixedShared.common_filter_cover_two G hG P Q U V hcross
        p q hp hq hpU hpV hqU hqV
      exact ⟨T, hT, hc⟩
    · have hcross' : ∀ q ∈ Q, ∀ p ∈ P, (q ∈ U ∨ p ∈ U) → (q ∈ V ∨ p ∈ V) → G.Adj q p :=
        fun q hq p hp hU hV => (hcross p hp q hq hU.symm hV.symm).symm
      have hclean' : ∀ x : Fin n → Bool, fourValue Q P U V x = true →
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        intro x hx
        apply hclean x
        simpa only [fourValue, Bool.and_comm] using hx
      have hbad' := clean_no_obstruction G hG Q P U V hcross' hP hclean'
      obtain ⟨T, hT, hc⟩ := no_both_cover_two G hG Q P U V hcross' hQB hbad'
      exact ⟨T, hT, fun p hp q hq hU hV => (hc q hq p hp hU.symm hV.symm).symm⟩
  · exact no_both_cover_two G hG P Q U V hcross hPB hbad

end PEqualNP.Outside.L_meta_1477.FourClauseCover


namespace PEqualNP.Outside.L_meta_1477.FourClauseCover

open PEqualNP.TopForm PEqualNP.EdgeOwnership TwoJunkClauses

lemma filtered_stars_strict {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hdis : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hP : ∀ p ∈ P, ∀ r ∈ P, ¬ G.Adj p r)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    (hne : (filteredEdges P Q U V).Nonempty) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ 2 ∧
      (ss.map fun s => s.2.length).sum + ss.length ≤ P.card + Q.card + 1 ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, G.Adj s.1 v) ∧
      (∀ x : Fin n → Bool, (ss.any fun s => x s.1 && s.2.any x) ≤ fourValue P Q U V x) ∧
      (∀ u v : Fin n, (ss.any fun s => pairInput u v s.1 && s.2.any (pairInput u v)) =
        fourValue P Q U V (pairInput u v)) := by
  classical
  obtain ⟨T, hT, hcover⟩ := clean_cover_two G hG P Q U V hcross hP hQ hclean
  have hcov : ∀ e ∈ filteredEdges P Q U V, e.1 ∈ T ∨ e.2 ∈ T := by
    intro e he
    obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
    exact hcover e.1 hp e.2 hq hU hV
  obtain ⟨ss, hss, hsne, hlen, hcost, hentry, hfun⟩ :=
    StarDecomposition.oriented_stars (filteredEdges P Q U V) T hne hcov
  have hcard := filteredEdges_card P Q U V
  have hQne : Q.Nonempty := by
    obtain ⟨e, he⟩ := hne
    exact ⟨e.2, (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2⟩
  have hbound := two_filter_edge_bound G hG P Q U V hQne hcross
  refine ⟨ss, hss, hsne, hlen.trans hT, by omega, ?_, ?_, ?_⟩
  · intro s hs v hv
    rcases hentry s hs v hv with he | he
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact hcross s.1 hp v hq hU hV
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact (hcross v hp s.1 hq hU hV).symm
  · intro x
    rw [hfun x]
    exact edgeValue_le_fourValue P Q U V x
  · intro u v
    rw [hfun (pairInput u v)]
    exact edgeValue_pair_eq_fourValue P Q U V hdis u v

end PEqualNP.Outside.L_meta_1477.FourClauseCover
