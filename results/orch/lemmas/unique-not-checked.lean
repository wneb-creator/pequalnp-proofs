import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1884.Reader
open PEqualNP.CircuitLowerBounds

lemma one_le_countP_of_get {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Fin l.length), p (l.get i)=true → 1≤l.countP p := by
  intro l
  induction l with
  | nil => intro i;exact Fin.elim0 i
  | cons a l ih =>
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      change p a=true at h
      simp [List.countP_cons,h]
    · intro h
      have hc := ih i h
      simp only [List.countP_cons]
      omega

lemma countP_le_one_indices_equal {α : Type} (p : α → Bool) :
    ∀ (l : List α),l.countP p≤1 → ∀ i j : Fin l.length,
      p (l.get i)=true → p (l.get j)=true → i=j := by
  intro l
  induction l with
  | nil => intro _ i;exact Fin.elim0 i
  | cons a l ih =>
    intro hc i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _ _;rfl
      · intro hi hj
        change p a=true at hi
        have ht := one_le_countP_of_get p l j hj
        simp only [List.countP_cons,hi,ite_true] at hc
        omega
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hi hj
        change p a=true at hj
        have ht := one_le_countP_of_get p l i hi
        simp only [List.countP_cons,hj,ite_true] at hc
        omega
      · intro hi hj
        apply congrArg Fin.succ
        apply ih _ i j hi hj
        simp only [List.countP_cons] at hc
        omega

lemma exists_unique_not_index (C : Circuit)
    (hcount : C.gates.countP (fun g => g.op.eval [false])≤1)
    (hex : ∃ j : Fin C.gates.length,(C.gates.get j).op=GateOp.not) :
    ∃ j : Fin C.gates.length,(C.gates.get j).op=GateOp.not ∧
      ∀ k : Fin C.gates.length,(C.gates.get k).op=GateOp.not → k=j := by
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,hj,?_⟩
  intro k hk
  exact countP_le_one_indices_equal (fun g : Gate => g.op.eval [false]) C.gates hcount k j
    (by change (C.gates.get k).op.eval [false]=true;rw [hk];rfl)
    (by change (C.gates.get j).op.eval [false]=true;rw [hj];rfl)

end PEqualNP.Outside.L_meta_1884.Reader
