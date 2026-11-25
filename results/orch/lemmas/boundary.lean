import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451_aux.Boundary

def Independent {ι : Type*} (E : ι → ι → Prop) (s : Finset ι) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ E u v

def MaximalIndependent {ι : Type*} (E : ι → ι → Prop) (s : Finset ι) : Prop :=
  Independent E s ∧ ∀ t : Finset ι, s ⊆ t → Independent E t → t = s

lemma exists_maximal_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (s : Finset ι) (hs : Independent E s) :
    ∃ t : Finset ι, s ⊆ t ∧ MaximalIndependent E t := by
  classical
  let family : Finset (Finset ι) := Finset.univ.filter fun t =>
    s ⊆ t ∧ Independent E t
  have hmem : s ∈ family := by simp [family, hs]
  obtain ⟨t, ht, hcard⟩ := family.exists_max_image Finset.card ⟨s, hmem⟩
  have hprops : s ⊆ t ∧ Independent E t := (Finset.mem_filter.mp ht).2
  refine ⟨t, hprops.1, hprops.2, ?_⟩
  intro u htu hu
  have huf : u ∈ family := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprops.1.trans htu, hu⟩
  exact (Finset.eq_of_subset_of_card_le htu (hcard u huf)).symm

lemma boundary_complete {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (g : (ι → Bool) → Bool)
    (hmono : ∀ x y : ι → Bool,
      (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hedge : ∀ u v, E u v → g (fun i => decide (i = u ∨ i = v)) = true)
    (hmax : ∀ s : Finset ι, MaximalIndependent E s →
      g (fun i => decide (i ∈ s)) = false) :
    ∀ x : ι → Bool, g x = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true := by
  classical
  intro x
  constructor
  · intro hx
    by_contra hno
    let s : Finset ι := Finset.univ.filter fun i => x i = true
    have hs : Independent E s := by
      intro u hu v hv huv
      exact hno ⟨u, v, huv, (Finset.mem_filter.mp hu).2,
        (Finset.mem_filter.mp hv).2⟩
    obtain ⟨t, hst, ht⟩ := exists_maximal_independent E s hs
    have hxt : ∀ i, x i = true → decide (i ∈ t) = true := by
      intro i hi
      exact decide_eq_true (hst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    have httrue := hmono x (fun i => decide (i ∈ t)) hxt hx
    rw [hmax t ht] at httrue
    contradiction
  · rintro ⟨u, v, huv, hu, hv⟩
    apply hmono (fun i => decide (i = u ∨ i = v)) x _ (hedge u v huv)
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact hu
    · exact hv

lemma maximal_iff_single_extensions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (s : Finset ι) :
    MaximalIndependent E s ↔ Independent E s ∧
      ∀ i, i ∉ s → ¬ Independent E (insert i s) := by
  constructor
  · rintro ⟨hs, hmax⟩
    refine ⟨hs, ?_⟩
    intro i hi hins
    have heq := hmax (insert i s) (Finset.subset_insert _ _) hins
    exact hi (heq ▸ Finset.mem_insert_self i s)
  · rintro ⟨hs, hsingle⟩
    refine ⟨hs, ?_⟩
    intro t hst ht
    apply Finset.Subset.antisymm _ hst
    intro i hi
    by_contra his
    apply hsingle i his
    intro u hu v hv
    apply ht u (Finset.insert_subset hi hst hu) v (Finset.insert_subset hi hst hv)

def edgeFunction {ι : Type*} [Fintype ι] (E : ι → ι → Prop) [DecidableRel E]
    (x : ι → Bool) : Bool :=
  decide (∃ u v, E u v ∧ x u = true ∧ x v = true)

lemma edgeFunction_false_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) [DecidableRel E] (s : Finset ι) :
    edgeFunction E (fun i => decide (i ∈ s)) = false ↔ Independent E s := by
  classical
  simp only [edgeFunction, decide_eq_false_iff_not, decide_eq_true_eq]
  unfold Independent
  aesop

lemma boundary_complete_tests {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) [DecidableRel E] (g : (ι → Bool) → Bool)
    (hmono : ∀ x y : ι → Bool,
      (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hedge : ∀ u v, E u v → g (fun i => decide (i = u ∨ i = v)) = true)
    (hmax : ∀ x : ι → Bool, edgeFunction E x = false →
      (∀ i, x i = false →
        edgeFunction E (fun j => if j = i then true else x j) = true) →
      g x = false) :
    ∀ x : ι → Bool, g x = edgeFunction E x := by
  classical
  have hneg : ∀ s : Finset ι, MaximalIndependent E s →
      g (fun i => decide (i ∈ s)) = false := by
    intro s hs
    apply hmax _ ((edgeFunction_false_iff E s).mpr hs.1)
    intro i hi
    have his : i ∉ s := of_decide_eq_false hi
    have hn := (maximal_iff_single_extensions E s).mp hs |>.2 i his
    have hfunc : (fun j => if j = i then true else decide (j ∈ s)) =
        (fun j => decide (j ∈ insert i s)) := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [hfunc]
    have hnot := (edgeFunction_false_iff E (insert i s)).not.mpr hn
    cases heq : edgeFunction E (fun j => decide (j ∈ insert i s)) <;> simp_all
  intro x
  have heq := boundary_complete E g hmono hedge hneg x
  have hgraph : edgeFunction E x = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by simp [edgeFunction]
  have hbool := heq.trans hgraph.symm
  cases hx : g x <;> cases hf : edgeFunction E x <;> simp_all

end PEqualNP.Outside.L_meta_3451_aux.Boundary
