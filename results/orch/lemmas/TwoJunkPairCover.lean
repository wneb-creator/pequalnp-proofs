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

open PEqualNP.TopForm PEqualNP.EdgeOwnership

def FourClauses {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true) ∧
    (∃ u ∈ U, x u = true) ∧ (∃ v ∈ V, x v = true)

lemma pair_graph_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma four_clause_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hdis : Disjoint P Q)
    (hclean : ∀ x : Fin n → Bool, FourClauses P Q U V x →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ u v : Fin n, FourClauses P Q U V (pairInput u v) → u ∈ T ∨ v ∈ T := by
  classical
  have hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q := by
    intro p hp q hq hU hV
    apply (pair_graph_iff G p q).mp
    apply hclean (pairInput p q)
    refine ⟨⟨p, hp, by simp [pairInput]⟩, ⟨q, hq, by simp [pairInput]⟩, ?_, ?_⟩
    · rcases hU with h | h
      · exact ⟨p, h, by simp [pairInput]⟩
      · exact ⟨q, h, by simp [pairInput]⟩
    · rcases hV with h | h
      · exact ⟨p, h, by simp [pairInput]⟩
      · exact ⟨q, h, by simp [pairInput]⟩
  obtain ⟨T, hT, hcT⟩ := two_filter_cover_three G hG P Q U V hcross
  refine ⟨T, hT, ?_⟩
  intro u v hf
  obtain ⟨⟨p, hp, hpu⟩, ⟨q, hq, hqv⟩, ⟨r, hr, hru⟩, ⟨s, hs, hsu⟩⟩ := hf
  simp only [pairInput, decide_eq_true_eq] at hpu hqv hru hsu
  have hUV : u ∈ U ∨ v ∈ U := by rcases hru with rfl | rfl <;> simp_all
  have hVV : u ∈ V ∨ v ∈ V := by rcases hsu with rfl | rfl <;> simp_all
  have hpq : p ≠ q := fun he => Finset.disjoint_left.mp hdis hp (he ▸ hq)
  rcases hpu with rfl | rfl <;> rcases hqv with rfl | rfl
  · exact (hpq rfl).elim
  · exact hcT p hp q hq hUV hVV
  · exact (hcT p hp q hq hUV.symm hVV.symm).symm
  · exact (hpq rfl).elim

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses
