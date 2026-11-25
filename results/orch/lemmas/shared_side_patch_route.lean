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

namespace PEqualNP.Outside.L_meta_1772_aux.rectanglePrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_1772_aux.rectangleCluster
  PEqualNP.Outside.L_meta_1772_aux.rectanglePatch

def matchingPrefix {n : ℕ} (a b c d : Fin n) : Circuit :=
  ⟨[⟨GateOp.and, [a.val, b.val]⟩, ⟨GateOp.and, [c.val, d.val]⟩,
    ⟨GateOp.or, [n, n + 1]⟩], n + 2⟩

def starPrefix {n : ℕ} (a b c d e : Fin n) : Circuit :=
  ⟨[⟨GateOp.or, [b.val, c.val]⟩, ⟨GateOp.and, [a.val, n]⟩,
    ⟨GateOp.and, [d.val, e.val]⟩,
    ⟨GateOp.or, [n + 1, n + 2]⟩], n + 3⟩

lemma matching_wires {n : ℕ} (a b c d : Fin n) (x : Fin n → Bool) :
    (matchingPrefix a b c d).wires (List.ofFn x) =
      List.ofFn x ++ [x a && x b, x c && x d, (x a && x b) || (x c && x d)] := by
  simp [matchingPrefix, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, a.isLt, b.isLt, c.isLt, d.isLt, List.append_assoc]

lemma star_wires {n : ℕ} (a b c d e : Fin n) (x : Fin n → Bool) :
    (starPrefix a b c d e).wires (List.ofFn x) =
      List.ofFn x ++ [x b || x c, x a && (x b || x c), x d && x e,
        (x a && (x b || x c)) || (x d && x e)] := by
  simp [starPrefix, Circuit.wires, GateOp.eval, List.getElem?_append,
    List.getD_eq_getElem?_getD, a.isLt, b.isLt, c.isLt, d.isLt, e.isLt,
    List.append_assoc]

lemma matching_mono {n : ℕ} (a b c d : Fin n) : Monotone2 (matchingPrefix a b c d) := by
  simp [Monotone2, matchingPrefix]

lemma star_mono {n : ℕ} (a b c d e : Fin n) : Monotone2 (starPrefix a b c d e) := by
  simp [Monotone2, starPrefix]

lemma matching_eval {n : ℕ} (a b c d : Fin n) (x : Fin n → Bool) :
    circuitFun n (matchingPrefix a b c d) x =
      ((x a && x b) || (x c && x d)) := by
  change ((matchingPrefix a b c d).wires (List.ofFn x)).getD (n + 2) false = _
  rw [matching_wires]
  simp [List.getD_append]

lemma star_eval {n : ℕ} (a b c d e : Fin n) (x : Fin n → Bool) :
    circuitFun n (starPrefix a b c d e) x =
      ((x a && (x b || x c)) || (x d && x e)) := by
  change ((starPrefix a b c d e).wires (List.ofFn x)).getD (n + 3) false = _
  rw [star_wires]
  simp [List.getD_append]

lemma edge_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (uv : G.Adj u v) (x : Fin n → Bool)
    (hu : x u = true) (hv : x v = true) : graphFun G ∅ x = true := by
  have h : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := ⟨u, v, uv, hu, hv⟩
  simpa [graphFun] using h

lemma matching_ands_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b c d : Fin n} (ab : G.Adj a b) (cd : G.Adj c d)
    (j : ℕ) (hj : j < (matchingPrefix a b c d).gates.length)
    (hand : (gateAt (matchingPrefix a b c d) j).op = GateOp.and) :
    BelowF G (matchingPrefix a b c d) j := by
  change j < 3 at hj
  interval_cases j
  · intro x hx
    have hx' : x a = true ∧ x b = true := by
      simpa [gateVal, matching_wires, List.getD_append] using hx
    exact edge_true G ab x hx'.1 hx'.2
  · intro x hx
    have hx' : x c = true ∧ x d = true := by
      simpa [gateVal, matching_wires, List.getD_append] using hx
    exact edge_true G cd x hx'.1 hx'.2
  · simp [gateAt, matchingPrefix, List.getD_eq_getElem?_getD] at hand

lemma star_ands_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b c d e : Fin n} (ab : G.Adj a b) (ac : G.Adj a c) (de : G.Adj d e)
    (j : ℕ) (hj : j < (starPrefix a b c d e).gates.length)
    (hand : (gateAt (starPrefix a b c d e) j).op = GateOp.and) :
    BelowF G (starPrefix a b c d e) j := by
  change j < 4 at hj
  interval_cases j
  · simp [gateAt, starPrefix, List.getD_eq_getElem?_getD] at hand
  · intro x hx
    have hx' : x a = true ∧ (x b = true ∨ x c = true) := by
      simpa [gateVal, star_wires, List.getD_append] using hx
    rcases hx'.2 with hb | hc
    · exact edge_true G ab x hx'.1 hb
    · exact edge_true G ac x hx'.1 hc
  · intro x hx
    have hx' : x d = true ∧ x e = true := by
      simpa [gateVal, star_wires, List.getD_append] using hx
    exact edge_true G de x hx'.1 hx'.2
  · simp [gateAt, starPrefix, List.getD_eq_getElem?_getD] at hand

lemma both_rectangles_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : NoFourCycle G) {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ab : G.Adj a b) (cd : G.Adj c d) :
    (∃ u v, graphFun G ∅ (pairInput u v) = false ∧
      ((pairInput u v a || pairInput u v c) &&
        (pairInput u v b || pairInput u v d)) = true) ∧
    (∃ u v, graphFun G ∅ (pairInput u v) = false ∧
      ((pairInput u v a || pairInput u v d) &&
        (pairInput u v b || pairInput u v c)) = true) := by
  obtain ⟨_, _, ac_bd, ad_bc, _, _⟩ :=
    cross_exclusions G tri noFour hac had hbc hbd ab cd
  have false_pair : ∀ u v, ¬ G.Adj u v → graphFun G ∅ (pairInput u v) = false := by
    intro u v h
    exact Bool.eq_false_iff.mpr (fun ht => h ((graph_pair G u v).mp ht))
  constructor
  · by_cases ad : G.Adj a d
    · exact ⟨b, c, false_pair b c (ad_bc ad), by simp [pairInput]⟩
    · exact ⟨a, d, false_pair a d ad, by simp [pairInput]⟩
  · by_cases ac : G.Adj a c
    · exact ⟨b, d, false_pair b d (ac_bd ac), by simp [pairInput]⟩
    · exact ⟨a, c, false_pair a c ac, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_1772_aux.rectanglePrefix

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

namespace PEqualNP.Outside.L_meta_1772_aux.sharedPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_1772_aux.rectanglePatch
  PEqualNP.Outside.L_meta_1772_aux.rectanglePrefix
  PEqualNP.Outside.L_meta_1772_aux.sharedSide

def sixEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d e : Fin n) (x : Fin n → Bool) : Bool :=
  (((decide (G.Adj a c) && x a) && x c) ||
    ((decide (G.Adj b c) && x b) && x c)) ||
  (((decide (G.Adj a d) && x a) && x d) ||
    (((decide (G.Adj a e) && x a) && x e) ||
      (((decide (G.Adj b d) && x b) && x d) ||
        ((decide (G.Adj b e) && x b) && x e))))

lemma six_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d e : Fin n) (x : Fin n → Bool) :
    sixEdges G a b c d e x = true → graphFun G ∅ x = true := by
  intro h
  simp only [sixEdges, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨⟨h, ha⟩, hc⟩ | ⟨⟨h, hb⟩, hc⟩) |
    ⟨⟨h, ha⟩, hd⟩ | ⟨⟨h, ha⟩, he⟩ | ⟨⟨h, hb⟩, hd⟩ | ⟨⟨h, hb⟩, he⟩
  · exact edge_true G h x ha hc
  · exact edge_true G h x hb hc
  · exact edge_true G h x ha hd
  · exact edge_true G h x ha he
  · exact edge_true G h x hb hd
  · exact edge_true G h x hb he

lemma six_covers_rectangles {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {a b c d e u v : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (uv : G.Adj u v)
    (hit : (((pairInput u v a || pairInput u v b) &&
        (pairInput u v c || pairInput u v d)) ||
      ((pairInput u v a || pairInput u v b) &&
        (pairInput u v c || pairInput u v e))) = true) :
    sixEdges G a b c d e (pairInput u v) = true := by
  have vu := uv.symm
  simp only [Bool.or_eq_true, Bool.and_eq_true, pairInput, decide_eq_true_eq] at hit
  rcases hit with h | h
  all_goals
    rcases h with ⟨((h₁ | h₁) | (h₁ | h₁)), ((h₂ | h₂) | (h₂ | h₂))⟩ <;>
      subst_vars <;> simp_all [sixEdges, pairInput]

lemma shared_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d e : Fin n)
    (safe : ∀ x : Fin n → Bool,
      (((x a || x b) && (x c || x d)) &&
        ((x a || x b) && (x c || x e))) = true → graphFun G ∅ x = true) :
    G.Adj a c ∧ G.Adj b c := by
  constructor
  · exact (graph_pair G a c).mp (safe (pairInput a c) (by simp [pairInput]))
  · exact (graph_pair G b c).mp (safe (pairInput b c) (by simp [pairInput]))

lemma matching_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b d e : Fin n}
    (hd : G.Adj a d → ¬ G.Adj b d) (he : G.Adj a e → ¬ G.Adj b e)
    (ha : G.Adj a d → ¬ G.Adj a e) (hb : G.Adj b d → ¬ G.Adj b e) :
    (¬ G.Adj a d ∧ ¬ G.Adj a e ∧ ¬ G.Adj b d ∧ ¬ G.Adj b e) ∨
    (G.Adj a d ∧ ¬ G.Adj a e ∧ ¬ G.Adj b d ∧ ¬ G.Adj b e) ∨
    (¬ G.Adj a d ∧ G.Adj a e ∧ ¬ G.Adj b d ∧ ¬ G.Adj b e) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj a e ∧ G.Adj b d ∧ ¬ G.Adj b e) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj a e ∧ ¬ G.Adj b d ∧ G.Adj b e) ∨
    (G.Adj a d ∧ ¬ G.Adj a e ∧ ¬ G.Adj b d ∧ G.Adj b e) ∨
    (¬ G.Adj a d ∧ G.Adj a e ∧ G.Adj b d ∧ ¬ G.Adj b e) := by
  by_cases ad : G.Adj a d
  · by_cases be : G.Adj b e
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ad, ha ad, hd ad, be⟩)))))
    · exact Or.inr (Or.inl ⟨ad, ha ad, hd ad, be⟩)
  by_cases ae : G.Adj a e
  · by_cases bd : G.Adj b d
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ad, ae, bd, he ae⟩)))))
    · exact Or.inr (Or.inr (Or.inl ⟨ad, ae, bd, he ae⟩))
  by_cases bd : G.Adj b d
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ad, ae, bd, hb bd⟩)))
  by_cases be : G.Adj b e
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ad, ae, bd, be⟩))))
  exact Or.inl ⟨ad, ae, bd, be⟩

def doubleStarPrefix {n : ℕ} (a b c d e : Fin n) : Circuit :=
  ⟨[⟨GateOp.or, [c.val, d.val]⟩, ⟨GateOp.or, [c.val, e.val]⟩,
    ⟨GateOp.and, [a.val, n]⟩, ⟨GateOp.and, [b.val, n + 1]⟩,
    ⟨GateOp.or, [n + 2, n + 3]⟩], n + 4⟩

lemma double_star_wires {n : ℕ} (a b c d e : Fin n) (x : Fin n → Bool) :
    (doubleStarPrefix a b c d e).wires (List.ofFn x) =
      List.ofFn x ++ [x c || x d, x c || x e, x a && (x c || x d),
        x b && (x c || x e), (x a && (x c || x d)) || (x b && (x c || x e))] := by
  simp [doubleStarPrefix, Circuit.wires, GateOp.eval, List.getElem?_append,
    List.getD_eq_getElem?_getD, a.isLt, b.isLt, c.isLt, d.isLt, e.isLt,
    List.append_assoc]

lemma double_star_mono {n : ℕ} (a b c d e : Fin n) :
    Monotone2 (doubleStarPrefix a b c d e) := by
  simp [Monotone2, doubleStarPrefix]

lemma double_star_eval {n : ℕ} (a b c d e : Fin n) (x : Fin n → Bool) :
    circuitFun n (doubleStarPrefix a b c d e) x =
      ((x a && (x c || x d)) || (x b && (x c || x e))) := by
  change ((doubleStarPrefix a b c d e).wires (List.ofFn x)).getD (n + 4) false = _
  rw [double_star_wires]
  simp

lemma double_star_ands_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b c d e : Fin n} (ac : G.Adj a c) (ad : G.Adj a d)
    (bc : G.Adj b c) (be : G.Adj b e)
    (j : ℕ) (hj : j < (doubleStarPrefix a b c d e).gates.length)
    (hand : (gateAt (doubleStarPrefix a b c d e) j).op = GateOp.and) :
    BelowF G (doubleStarPrefix a b c d e) j := by
  change j < 5 at hj
  interval_cases j
  · simp [gateAt, doubleStarPrefix, List.getD_eq_getElem?_getD] at hand
  · simp [gateAt, doubleStarPrefix, List.getD_eq_getElem?_getD] at hand
  · intro x hx
    have hx' : x a = true ∧ (x c = true ∨ x d = true) := by
      simpa [gateVal, double_star_wires, List.getD_append] using hx
    rcases hx'.2 with hc | hd
    · exact edge_true G ac x hx'.1 hc
    · exact edge_true G ad x hx'.1 hd
  · intro x hx
    have hx' : x b = true ∧ (x c = true ∨ x e = true) := by
      simpa [gateVal, double_star_wires, List.getD_append] using hx
    rcases hx'.2 with hc | he
    · exact edge_true G bc x hx'.1 hc
    · exact edge_true G be x hx'.1 he
  · simp [gateAt, doubleStarPrefix, List.getD_eq_getElem?_getD] at hand

lemma shared_rectangles_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {a b c d e : Fin n}
    (hd : G.Adj a d → ¬ G.Adj b d) (he : G.Adj a e → ¬ G.Adj b e) :
    (∃ u v, graphFun G ∅ (pairInput u v) = false ∧
      ((pairInput u v a || pairInput u v b) &&
        (pairInput u v c || pairInput u v d)) = true) ∧
    (∃ u v, graphFun G ∅ (pairInput u v) = false ∧
      ((pairInput u v a || pairInput u v b) &&
        (pairInput u v c || pairInput u v e)) = true) := by
  have false_pair : ∀ u v, ¬ G.Adj u v → graphFun G ∅ (pairInput u v) = false := by
    intro u v h
    exact Bool.eq_false_iff.mpr (fun ht => h ((graph_pair G u v).mp ht))
  constructor
  · by_cases ad : G.Adj a d
    · exact ⟨b, d, false_pair b d (hd ad), by simp [pairInput]⟩
    · exact ⟨a, d, false_pair a d ad, by simp [pairInput]⟩
  · by_cases ae : G.Adj a e
    · exact ⟨b, e, false_pair b e (he ae), by simp [pairInput]⟩
    · exact ⟨a, e, false_pair a e ae, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_1772_aux.sharedPatch
