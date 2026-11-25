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

namespace PEqualNP.Outside.L_meta_1772_aux.rectanglePatch

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.Outside.L_meta_1772_aux.rectangleCluster

def quadEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) : Bool :=
  (((decide (G.Adj a b) && x a) && x b) ||
    ((decide (G.Adj c d) && x c) && x d)) ||
  (((decide (G.Adj a c) && x a) && x c) ||
    (((decide (G.Adj a d) && x a) && x d) ||
      (((decide (G.Adj b c) && x b) && x c) ||
        ((decide (G.Adj b d) && x b) && x d))))

lemma quad_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) :
    quadEdges G a b c d x = true → graphFun G ∅ x = true := by
  intro h
  simp only [quadEdges, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  suffices ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true by
    simpa [graphFun] using this
  rcases h with (⟨⟨h, ha⟩, hb⟩ | ⟨⟨h, hc⟩, hd⟩) |
    ⟨⟨h, ha⟩, hc⟩ | ⟨⟨h, ha⟩, hd⟩ | ⟨⟨h, hb⟩, hc⟩ | ⟨⟨h, hb⟩, hd⟩
  · exact ⟨a, b, h, ha, hb⟩
  · exact ⟨c, d, h, hc, hd⟩
  · exact ⟨a, c, h, ha, hc⟩
  · exact ⟨a, d, h, ha, hd⟩
  · exact ⟨b, c, h, hb, hc⟩
  · exact ⟨b, d, h, hb, hd⟩

lemma quad_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b c d u v : Fin n} (adjacent : G.Adj u v)
    (hu : u = a ∨ u = b ∨ u = c ∨ u = d)
    (hv : v = a ∨ v = b ∨ v = c ∨ v = d) :
    quadEdges G a b c d (pairInput u v) = true := by
  have reverse := adjacent.symm
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp_all [quadEdges, pairInput]

lemma rectangle_pair_support {n : ℕ} {a b c d u v : Fin n}
    (ab : a ≠ b) (ad : a ≠ d) (cb : c ≠ b) (cd : c ≠ d)
    (hit : ((pairInput u v a || pairInput u v c) &&
      (pairInput u v b || pairInput u v d)) = true) :
    (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, pairInput, decide_eq_true_eq] at hit
  rcases hit with ⟨(ha | ha), (hb | hb)⟩ <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> aesop

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨a, b, adjacent, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl adjacent).elim
    · exact adjacent
    · exact adjacent.symm
    · exact (G.irrefl adjacent).elim
  · intro adjacent
    exact ⟨u, v, adjacent, by simp [pairInput], by simp [pairInput]⟩

lemma safe_intersection_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (a b c d : Fin n)
    (safe : ∀ x : Fin n → Bool,
      (((x a || x c) && (x b || x d)) &&
        ((x a || x d) && (x b || x c))) = true → graphFun G ∅ x = true) :
    G.Adj a b ∧ G.Adj c d := by
  constructor
  · exact (graph_pair G a b).mp (safe (pairInput a b) (by simp [pairInput]))
  · exact (graph_pair G c d).mp (safe (pairInput c d) (by simp [pairInput]))

lemma quad_covers_rectangles {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {a b c d u v : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ab : G.Adj a b) (cd : G.Adj c d) (uv : G.Adj u v)
    (hit : (((pairInput u v a || pairInput u v c) &&
        (pairInput u v b || pairInput u v d)) ||
      ((pairInput u v a || pairInput u v d) &&
        (pairInput u v b || pairInput u v c))) = true) :
    quadEdges G a b c d (pairInput u v) = true := by
  simp only [Bool.or_eq_true] at hit
  rcases hit with left | right
  · obtain ⟨hu, hv⟩ := rectangle_pair_support ab.ne had hbc.symm cd.ne left
    exact quad_pair G uv hu hv
  · obtain ⟨hu, hv⟩ := rectangle_pair_support ab.ne hac hbd.symm cd.ne.symm right
    apply quad_pair G uv <;> aesop

lemma safe_cluster_patch {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : NoFourCycle G) {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (safe : ∀ x : Fin n → Bool,
      (((x a || x c) && (x b || x d)) &&
        ((x a || x d) && (x b || x c))) = true → graphFun G ∅ x = true) :
    ∃ p : (Fin n → Bool) → Bool,
      (p = (fun x => (x a && x b) || (x c && x d)) ∨
        p = (fun x => (x a && (x b || x c)) || (x c && x d)) ∨
        p = (fun x => (x a && (x b || x d)) || (x c && x d)) ∨
        p = (fun x => (x b && (x a || x c)) || (x c && x d)) ∨
        p = (fun x => (x b && (x a || x d)) || (x c && x d))) ∧
      (∀ x, p x = true → graphFun G ∅ x = true) ∧
      (∀ u v, G.Adj u v →
        (((pairInput u v a || pairInput u v c) &&
          (pairInput u v b || pairInput u v d)) ||
        ((pairInput u v a || pairInput u v d) &&
          (pairInput u v b || pairInput u v c))) = true →
        p (pairInput u v) = true) := by
  obtain ⟨ab, cd⟩ := safe_intersection_edges G a b c d safe
  refine ⟨quadEdges G a b c d, ?_, quad_below G a b c d, ?_⟩
  · rcases cross_classification G tri noFour hac had hbc hbd ab cd with
      ⟨ac, ad, bc, bd⟩ | ⟨ac, ad, bc, bd⟩ | ⟨ac, ad, bc, bd⟩ |
      ⟨ac, ad, bc, bd⟩ | ⟨ac, ad, bc, bd⟩
    · left
      funext x
      simp [quadEdges, ab, cd, ac, ad, bc, bd]
    · right; left
      funext x
      simpa [quadEdges, ab, cd, ac, ad, bc, bd] using
        (patch_ac_identity (x a) (x b) (x c) (x d)).symm
    · right; right; left
      funext x
      simpa [quadEdges, ab, cd, ac, ad, bc, bd] using
        (patch_ad_identity (x a) (x b) (x c) (x d)).symm
    · right; right; right; left
      funext x
      simpa [quadEdges, ab, cd, ac, ad, bc, bd] using
        (patch_bc_identity (x a) (x b) (x c) (x d)).symm
    · right; right; right; right
      funext x
      simpa [quadEdges, ab, cd, ac, ad, bc, bd] using
        (patch_bd_identity (x a) (x b) (x c) (x d)).symm
  · intro u v uv hit
    exact quad_covers_rectangles G hac had hbc hbd ab cd uv hit

end PEqualNP.Outside.L_meta_1772_aux.rectanglePatch
