import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite

namespace PEqualNP.Outside.L_meta_1031_aux

def independent {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

lemma boundary_certificate (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (mono : ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (edges : ∀ u v : Fin n, G.Adj u v →
      f (fun i => decide (i = u ∨ i = v)) = true)
    (misses : ∀ S : Finset (Fin n), independent G S →
      (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) →
      f (fun i => decide (i ∈ S)) = false) :
    ∀ x : Fin n → Bool, f x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  classical
  intro x
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hu, hv⟩ := hx
    have hf : f x = true := mono _ x (by
      intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv) (edges u v huv)
    simp [hf, show ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true from ⟨u,v,huv,hu,hv⟩]
  · let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
    have hS : independent G S := by
      intro u hu v hv huv
      exact hx ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
    let family := Finset.univ.powerset.filter (independent G)
    have member (T : Finset (Fin n)) : T ∈ family ↔ independent G T := by
      simp [family]
    obtain ⟨T, hST, hmax⟩ := Finset.exists_le_maximal family ((member S).mpr hS)
    have hT : independent G T := (member T).mp hmax.1
    have hbound : ∀ U : Finset (Fin n), independent G U → T ⊆ U → U ⊆ T := by
      intro U hU hTU
      exact hmax.2 ((member U).mpr hU) hTU
    have hmiss := misses T hT hbound
    have hf : f x = false := by
      cases hfx : f x with
      | false => rfl
      | true =>
        have htrue : f (fun i => decide (i ∈ T)) = true := mono x _ (by
          intro i hi
          simp only [decide_eq_true_eq]
          exact hST (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)) hfx
        exact Bool.noConfusion (hmiss.symm.trans htrue)
    simp [hx, hf]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.CircuitBoundary

open PEqualNP.CircuitLowerBounds

lemma snoc_mono (a b : List Bool) (p q : Bool)
    (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hpq : p = true → q = true) :
    ∀ i, (a ++ [p]).getD i false = true → (b ++ [q]).getD i false = true := by
  intro i hi
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hab i hi
  · by_cases heq : i = a.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, hlen] using hpq (by
        simpa [List.getD_eq_getElem?_getD] using hi)
    · have hfalse : (a ++ [p]).getD i false = false := by
        apply List.getD_eq_default
        simp only [List.length_append, List.length_singleton]
        omega
      exact Bool.noConfusion (hfalse.symm.trans hi)

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with h | h <;> rw [h]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro ha i hi
    exact hab i (ha i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, hab i ha⟩

lemma fold_mono (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (Circuit.wires ⟨gs, 0⟩ a).getD i false = true →
      (Circuit.wires ⟨gs, 0⟩ b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    have hg := legal g (by simp)
    have hs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact legal h (by simp [hh])
    exact ih hs _ _ (by simp [hlen]) (snoc_mono a b _ _ hlen hab (gate_mono g hg a b hab))

lemma circuit_monotone (n : ℕ) (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply fold_mono C.gates legal (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases hlt : i < n
  · simpa [List.getD_eq_getElem, hlt] using hxy ⟨i, hlt⟩ (by
      simpa [List.getD_eq_getElem, hlt] using hi)
  · simp [Nat.le_of_not_gt hlt] at hi

end PEqualNP.Outside.L_meta_1031_aux.CircuitBoundary

namespace PEqualNP.Outside.L_meta_1031_aux

lemma maximal_independent_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : independent G S) :
    (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) ↔
      ∀ v, v ∉ S → ∃ u ∈ S, G.Adj u v := by
  classical
  constructor
  · intro maximal v hv
    by_contra hnone
    have hind : independent G (insert v S) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hav | haS
      · subst a
        rcases Finset.mem_insert.mp hb with hbv | hbS
        · exact G.ne_of_adj hab hbv.symm
        · exact hnone ⟨b, hbS, hab.symm⟩
      · rcases Finset.mem_insert.mp hb with hbv | hbS
        · subst b
          exact hnone ⟨a, haS, hab⟩
        · exact hS a haS b hbS hab
    exact hv (maximal _ hind (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  · intro boundary T hT hST v hv
    by_contra hvS
    obtain ⟨u, hu, huv⟩ := boundary v hvS
    exact hT u (hST hu) v hv huv

lemma circuit_boundary_certificate (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : ∀ g ∈ C.gates,
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (edges : ∀ u v : Fin n, G.Adj u v →
      C.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true)
    (misses : ∀ S : Finset (Fin n), independent G S →
      (∀ v, v ∉ S → ∃ u ∈ S, G.Adj u v) →
      C.eval (List.ofFn (fun i => decide (i ∈ S))) = false) :
    ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  apply boundary_certificate n G (fun x => C.eval (List.ofFn x))
    (CircuitBoundary.circuit_monotone n C legal) edges
  intro S hS hmax
  exact misses S hS ((maximal_independent_iff G S hS).mp hmax)

end PEqualNP.Outside.L_meta_1031_aux
