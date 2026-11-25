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
