import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitsBelow (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma bitsBelow_append {a b : List Bool} (len : a.length = b.length)
    (h : bitsBelow a b) {p q : Bool} (pq : p = true → q = true) :
    bitsBelow (a ++ [p]) (b ++ [q]) := by
  intro i hi
  by_cases earlier : i < a.length
  · rw [List.getD_append _ _ _ _ earlier] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases last : i = a.length
    · subst i
      have hp : p = true := by simpa using hi
      have hq := pq hp
      simpa [← len] using hq
    · have beyondA : (a ++ [p]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_default _ _ beyondA] at hi
      contradiction

lemma and_values_below (a b : List Bool) (h : bitsBelow a b) (ins : List Nat) :
    GateOp.and.eval (ins.map fun i => a.getD i false) = true →
      GateOp.and.eval (ins.map fun i => b.getD i false) = true := by
  induction ins with
  | nil => simp [GateOp.eval]
  | cons i ins ih =>
    simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at ih ⊢
    exact fun hi => ⟨h i hi.1, ih hi.2⟩

lemma or_values_below (a b : List Bool) (h : bitsBelow a b) (ins : List Nat) :
    GateOp.or.eval (ins.map fun i => a.getD i false) = true →
      GateOp.or.eval (ins.map fun i => b.getD i false) = true := by
  induction ins with
  | nil => simp [GateOp.eval]
  | cons i ins ih =>
    simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq, Bool.or_eq_true] at ih ⊢
    exact fun hi => hi.elim (fun hi => Or.inl (h i hi)) (fun hi => Or.inr (ih hi))

lemma mono_wires_below (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (len : a.length = b.length) (h : bitsBelow a b) :
    bitsBelow ((⟨gs, 0⟩ : Circuit).wires a) ((⟨gs, 0⟩ : Circuit).wires b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change bitsBelow ((⟨gs, 0⟩ : Circuit).wires (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]))
      ((⟨gs, 0⟩ : Circuit).wires (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]))
    apply ih (fun g hg => mono g (List.mem_cons_of_mem _ hg))
    · simpa using len
    · apply bitsBelow_append len h
      rcases mono g List.mem_cons_self with op | op
      · rw [op]
        exact and_values_below a b h g.inputs
      · rw [op]
        exact or_values_below a b h g.inputs

lemma mono_eval_below (C : Circuit) (mono : Monotone2 C)
    (a b : List Bool) (len : a.length = b.length) (h : bitsBelow a b) :
    C.eval a = true → C.eval b = true := by
  apply mono_wires_below C.gates (fun g hg => ?_) a b len h C.output
  have op := (mono g hg).1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op

lemma negated_mono_endpoints (C : Circuit) (mono : Monotone2 C) (n : Nat) :
    ¬ (!(C.eval (List.replicate n false)) = false ∧ !(C.eval (List.replicate n true)) = true) := by
  rintro ⟨lo, hi⟩
  have h : bitsBelow (List.replicate n false) (List.replicate n true) := by
    intro i hi
    have zero : (List.replicate n false).getD i false = false := by simp
    rw [zero] at hi
    contradiction
  have passed := mono_eval_below C mono (List.replicate n false) (List.replicate n true)
    (by simp) h (by simpa using lo)
  simp [passed] at hi

end PEqualNP.Outside.L_meta_2592_aux
