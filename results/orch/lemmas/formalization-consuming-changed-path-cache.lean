import PNPAccepted6659
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace PEqualNP.Outside.L_meta_6659_aux

lemma consuming_changed_path {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k) (target : Nat)
    (changed : val D x target ≠ val D y target) (absent : i ∉ supp n D target) :
    ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
        (n+e.1) target := by
  have first : ∀ {a b : Nat},
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) a b →
      i ∈ supp n D a → i ∉ supp n D b →
      ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
          (n+e.1) b := by
    intro a b path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => intro present absent; exact False.elim (absent present)
    | @head a c step rest ih =>
      intro present absent
      by_cases next : i ∈ supp n D c
      · exact ih next absent
      · obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step.1
        refine ⟨(j,s),sem_mem_W.mpr ⟨hj,?_,next⟩,step.2,rest⟩
        rw [source]
        exact present
  apply first (sem_changed_path hS x y i inputs target changed) _ absent
  rw [supp_input D i]
  exact Finset.mem_singleton_self i

end PEqualNP.Outside.L_meta_6659_aux
