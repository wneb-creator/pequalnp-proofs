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
