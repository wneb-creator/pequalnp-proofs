import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.rectangleCluster

open PEqualNP.TopForm

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (noFour : NoFourCycle G)
    {a b c d : Fin n} (ab : a ≠ b)
    (ac : G.Adj a c) (bc : G.Adj b c) (ad : G.Adj a d) (bd : G.Adj b d) :
    c = d := by
  classical
  apply Finset.card_le_one.mp (noFour a b ab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ac, bc⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ad, bd⟩

lemma cross_exclusions {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : NoFourCycle G) {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ab : G.Adj a b) (cd : G.Adj c d) :
    (G.Adj a c → ¬ G.Adj a d) ∧
    (G.Adj a c → ¬ G.Adj b c) ∧
    (G.Adj a c → ¬ G.Adj b d) ∧
    (G.Adj a d → ¬ G.Adj b c) ∧
    (G.Adj a d → ¬ G.Adj b d) ∧
    (G.Adj b c → ¬ G.Adj b d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ac ad
    exact tri c a d ac.symm ad cd.symm
  · intro ac bc
    exact tri a c b ac bc.symm ab.symm
  · intro ac bd
    exact hbc (common_neighbor_unique G noFour had ab bd.symm ac cd.symm)
  · intro ad bc
    exact hbd (common_neighbor_unique G noFour hac ab bc.symm ad cd)
  · intro ad bd
    exact tri a d b ad bd.symm ab.symm
  · intro bc bd
    exact tri c b d bc.symm bd cd.symm

lemma cross_classification {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : NoFourCycle G) {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ab : G.Adj a b) (cd : G.Adj c d) :
    (¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∨
    (G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a c ∧ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a c ∧ ¬ G.Adj a d ∧ G.Adj b c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ G.Adj b d) := by
  obtain ⟨ac_ad, ac_bc, ac_bd, ad_bc, ad_bd, bc_bd⟩ :=
    cross_exclusions G tri noFour hac had hbc hbd ab cd
  by_cases ac : G.Adj a c
  · exact Or.inr (Or.inl ⟨ac, ac_ad ac, ac_bc ac, ac_bd ac⟩)
  by_cases ad : G.Adj a d
  · exact Or.inr (Or.inr (Or.inl ⟨ac, ad, ad_bc ad, ad_bd ad⟩))
  by_cases bc : G.Adj b c
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ac, ad, bc, bc_bd bc⟩)))
  by_cases bd : G.Adj b d
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ac, ad, bc, bd⟩)))
  exact Or.inl ⟨ac, ad, bc, bd⟩

lemma intersection_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && ((a || d) && (b || c))) =
      ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma patch_ac_identity (a b c d : Bool) :
    ((a && (b || c)) || (c && d)) =
      (((a && b) || (c && d)) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma patch_ad_identity (a b c d : Bool) :
    ((a && (b || d)) || (c && d)) =
      (((a && b) || (c && d)) || (a && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma patch_bc_identity (a b c d : Bool) :
    ((b && (a || c)) || (c && d)) =
      (((a && b) || (c && d)) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma patch_bd_identity (a b c d : Bool) :
    ((b && (a || d)) || (c && d)) =
      (((a && b) || (c && d)) || (b && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

end PEqualNP.Outside.L_meta_1772_aux.rectangleCluster

namespace PEqualNP.Outside.L_meta_1772_aux.sharedSide

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_1772_aux.rectangleCluster

def tripleInput {n : ℕ} (a b c : Fin n) : Fin n → Bool :=
  fun w => decide (w = a ∨ w = b ∨ w = c)

lemma triple_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (h : graphFun G ∅ (tripleInput a b c) = true) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Finset.notMem_empty, false_and, exists_false, false_or] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [tripleInput, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (G.irrefl huv).elim
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact (G.irrefl huv).elim
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact (G.irrefl huv).elim

lemma shared_cross_matching {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : NoFourCycle G) {a b c d e : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hce : c ≠ e)
    (ac : G.Adj a c) (bc : G.Adj b c)
    (safe : ∀ x : Fin n → Bool,
      (((x a || x b) && (x c || x d)) &&
        ((x a || x b) && (x c || x e))) = true → graphFun G ∅ x = true) :
    (G.Adj a d → ¬ G.Adj b d) ∧
    (G.Adj a e → ¬ G.Adj b e) ∧
    (G.Adj a d → ¬ G.Adj a e) ∧
    (G.Adj b d → ¬ G.Adj b e) := by
  have column_d : G.Adj a d → ¬ G.Adj b d := by
    intro ad bd
    exact hcd (common_neighbor_unique G noFour hab ac bc ad bd)
  have column_e : G.Adj a e → ¬ G.Adj b e := by
    intro ae be
    exact hce (common_neighbor_unique G noFour hab ac bc ae be)
  refine ⟨column_d, column_e, ?_, ?_⟩
  · intro ad ae
    have hF := safe (tripleInput b d e) (by simp [tripleInput])
    rcases triple_graph G b d e hF with bd | be | de
    · exact column_d ad bd
    · exact column_e ae be
    · exact tri d a e ad.symm ae de.symm
  · intro bd be
    have hF := safe (tripleInput a d e) (by simp [tripleInput])
    rcases triple_graph G a d e hF with ad | ae | de
    · exact column_d ad bd
    · exact column_e ae be
    · exact tri d b e bd.symm be de.symm

end PEqualNP.Outside.L_meta_1772_aux.sharedSide
