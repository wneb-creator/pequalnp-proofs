import Mathlib
import PEqualNP.Outside.L_meta_599

namespace PEqualNP.Outside.L_meta_650_aux.GlobalOrCharge

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 PaidGraph599 CoreFacts599
open scoped Classical

variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

theorem accepts_without_min_two (h : detects G C)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  obtain ⟨u, hvu⟩ := G.mem_support.mp hv
  obtain ⟨a, b, hab, ha, hb⟩ := two_neighbors (degrees u hvu.mem_support_right)
  obtain ⟨w, hw, hwv⟩ : ∃ w, G.Adj u w ∧ w ≠ v := by
    by_cases he : a = v
    · exact ⟨b, hb, fun h => hab (he.trans h.symm)⟩
    · exact ⟨a, ha, he⟩
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  exact ⟨x, by simp [x], (h x).mpr ⟨u, w, hw,
    by simp [x, Function.update_of_ne hvu.ne.symm],
    by simp [x, Function.update_of_ne hwv]⟩⟩

theorem pay_from_bit_min_two (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) (hf : GraphInduction599.noFour G)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u) (p : ℕ)
    (X Y : Finset (Fin n)) (hx : ¬ X ⊆ Y) (hy : ¬ Y ⊆ X)
    (hp : ∀ v ∈ X ∪ Y, Leaf599.Charged C v p)
    (bit_eq : ∀ U : Finset (Fin n),
      (C.wires (List.ofFn (CycleCut599.mask U))).getD (n + p) false = true ↔
        CycleModule599.bit X Y U) :
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  let S := X ∪ Y
  have active : ∀ v ∈ S, v ∈ G.support :=
    fun v hv => charge_is_active hm h hc hmin (hp v hv)
  by_contra hn
  have only : ∀ v ∈ S, ∀ j, CycleCut599.releaseAt C.gates v j → j = p := by
    intro v hv j hj
    by_contra hne
    have pay := double_saving hm h hc v hne
      ((charged_iff_release v j).mpr hj) (hp v hv)
    exact hn ⟨v, active v hv, hmin ▸ pay⟩
  have free := fun v hv => accepts_without_min_two h degrees (active v hv)
  have spec (U : Finset (Fin n)) : C.eval (List.ofFn (CycleCut599.mask U)) = true ↔
      CycleModule599.edgeAt G U := by
    rw [h]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, hab⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, b, hab, decide_eq_true ha, decide_eq_true hb⟩
  have hXS : X ⊆ S := Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right
  obtain ⟨u, hu, huy⟩ := Finset.not_subset.mp hx
  obtain ⟨v, hv, hvx⟩ := Finset.not_subset.mp hy
  have neq : u ≠ v := fun e => hvx (e ▸ hu)
  have ff := CycleCut599.graph_factors G S X Y C p hm hXS hYS only free bit_eq spec
  exact CycleModule599.no_module_of_no_four hXS hYS ⟨u, hu⟩ ⟨v, hv⟩
    ⟨u, hXS hu, v, hYS hv, neq⟩
    (fun w hw => two_neighbors (degrees w (active w hw))) hf ff

theorem two_or_paid_deletion (hf : GraphInduction599.noFour G)
    (degrees : ∀ u ∈ G.support, 2 ≤ G.degree u)
    (hg : best G + 1 < G.edgeSet.ncard) :
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  obtain ⟨C, A, hm, h, hc, hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  obtain ⟨v, hv⟩ := support_nonempty (show 0 < G.edgeSet.ncard by omega)
  obtain ⟨pre, g, post, shape, ands, hor, hlen⟩ :=
    Leaf599.first_or C v hm (one_bit h hv) (accepts_without_min_two h degrees hv)
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre ++ [g]) ++ post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut599.prefix_decision (n := n) pre post g ands hor hlen with copy | choice
    · exact False.elim
        (forbids_copy hm h hc hmin hj hor (CycleCut599.global_copy pre post g copy))
    · obtain ⟨X, Y, hx, hy, charges, bits⟩ := choice
      exact pay_from_bit_min_two hm h hc hmin hf degrees pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits

end PEqualNP.Outside.L_meta_650_aux.GlobalOrCharge
