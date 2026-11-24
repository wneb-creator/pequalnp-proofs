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


namespace PEqualNP.Outside.L_meta_1477.TwoCenterSignatures

open PEqualNP.TopForm TwoJunkClauses

lemma heavy_centers_incomparable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b)
    (hadegree : 2 ≤ (Q.filter (fun q => (a ∈ U ∨ q ∈ U) ∧ (a ∈ V ∨ q ∈ V))).card)
    (hbdegree : 2 ≤ (Q.filter (fun q => (b ∈ U ∨ q ∈ U) ∧ (b ∈ V ∨ q ∈ V))).card) :
    (a ∈ U ∧ a ∉ V ∧ b ∈ V ∧ b ∉ U) ∨
      (b ∈ U ∧ b ∉ V ∧ a ∈ V ∧ a ∉ U) := by
  classical
  let N : Fin n → Finset (Fin n) := fun p => Q.filter (fun q =>
    (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))
  have hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q := by
    intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  have hAB : ¬ ((a ∈ U → b ∈ U) ∧ (a ∈ V → b ∈ V)) := by
    rintro ⟨hU, hV⟩
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, hqa, hqv⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, hqa.imp hU id, hqv.imp hV id⟩
    have hsmall := nested_neighbor_small G hG P N hAdj a b ha hb hne hsub
    change 2 ≤ (N a).card at hadegree
    omega
  have hBA : ¬ ((b ∈ U → a ∈ U) ∧ (b ∈ V → a ∈ V)) := by
    rintro ⟨hU, hV⟩
    have hsub : N b ⊆ N a := by
      intro q hq
      obtain ⟨hq, hqb, hqv⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, hqb.imp hU id, hqv.imp hV id⟩
    have hsmall := nested_neighbor_small G hG P N hAdj b a hb ha hne.symm hsub
    change 2 ≤ (N b).card at hbdegree
    omega
  tauto

lemma common_filter_support_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    (Q.filter (fun q => q ∈ U ∧ q ∈ V)).card ≤ 1 := by
  have hsub : Q.filter (fun q => q ∈ U ∧ q ∈ V) ⊆
      Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a ha q hq (Or.inr hU) (Or.inr hV),
      hcross b hb q hq (Or.inr hU) (Or.inr hV)⟩
  exact (Finset.card_le_card hsub).trans (hG a b hne)

end PEqualNP.Outside.L_meta_1477.TwoCenterSignatures
