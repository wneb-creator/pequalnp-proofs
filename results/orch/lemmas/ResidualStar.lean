import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.ResidualStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def linear {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def mixed {n : ℕ} (A : Finset (Fin n)) (b d : Fin n) (x : Fin n → Bool) : Bool :=
  linear A x && (x b || x d)

def star {n : ℕ} (A : Finset (Fin n)) (b : Fin n) (x : Fin n → Bool) : Bool :=
  linear A x && x b

def primaryEval {n : ℕ} (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)

lemma eval_empty {n : ℕ} (x : Fin n → Bool) :
    primaryEval ⟨GateOp.or, []⟩ x = false := rfl

lemma eval_literal {n : ℕ} (d : Fin n) (x : Fin n → Bool) :
    primaryEval ⟨GateOp.or, [d.val]⟩ x = x d := by
  simp [primaryEval, GateOp.eval, List.getD_eq_getElem?_getD]

lemma eval_edge {n : ℕ} (a d : Fin n) (x : Fin n → Bool) :
    primaryEval ⟨GateOp.and, [a.val, d.val]⟩ x = (x a && x d) := by
  simp [primaryEval, GateOp.eval, List.getD_eq_getElem?_getD]

lemma outside_forces_d {n : ℕ} (A : Finset (Fin n)) (b d : Fin n) (x : Fin n → Bool)
    (off : star A b x = false) (on : mixed A b d x = true) : x d = true := by
  cases ha : linear A x <;> cases hb : x b <;> cases hd : x d <;>
    simp_all [star, mixed]

lemma pair_residual {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (b d u v : Fin n) (notD : d ∉ A) (edge : G.Adj u v)
    (off : star A b (pairInput u v) = false)
    (on : mixed A b d (pairInput u v) = true) :
    ∃ a ∈ A, G.Adj a d ∧ pairInput u v a = true ∧ pairInput u v d = true := by
  have hd := outside_forces_d A b d (pairInput u v) off on
  have hlin : linear A (pairInput u v) = true := by
    have both : linear A (pairInput u v) = true ∧
        (pairInput u v b || pairInput u v d) = true := by simpa [mixed] using on
    exact both.1
  obtain ⟨a, ha, active⟩ : ∃ a ∈ A, pairInput u v a = true := by simpa [linear] using hlin
  have ad : a ≠ d := by intro eq; exact notD (eq ▸ ha)
  have aPosition : a = u ∨ a = v := by simpa [pairInput] using active
  have dPosition : d = u ∨ d = v := by simpa [pairInput] using hd
  refine ⟨a, ha, ?_, active, hd⟩
  rcases aPosition with rfl | rfl <;> rcases dPosition with rfl | rfl
  · exact (ad rfl).elim
  · exact edge
  · exact edge.symm
  · exact (ad rfl).elim

lemma residual_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (A : Finset (Fin n)) (b d : Fin n)
    (hstar : ∀ a ∈ A, G.Adj b a) :
    ∃ g : Gate,
      (g = ⟨GateOp.or, []⟩ ∨ g = ⟨GateOp.or, [d.val]⟩ ∨
        ∃ a ∈ A, G.Adj a d ∧ g = ⟨GateOp.and, [a.val, d.val]⟩) ∧
      (∀ x, primaryEval g x = true → mixed A b d x = true) ∧
      ∀ u v, G.Adj u v → star A b (pairInput u v) = false →
        primaryEval g (pairInput u v) = mixed A b d (pairInput u v) := by
  classical
  by_cases same : b = d
  · subst d
    refine ⟨⟨GateOp.or, []⟩, Or.inl rfl, ?_, ?_⟩
    · intro x hx
      change false = true at hx
      contradiction
    · intro u v edge off
      simpa [eval_empty, mixed, star] using off.symm
  · by_cases inA : d ∈ A
    · refine ⟨⟨GateOp.or, [d.val]⟩, Or.inr (Or.inl rfl), ?_, ?_⟩
      · intro x hx
        rw [eval_literal] at hx
        have lin : linear A x = true := by simpa [linear] using (show ∃ a ∈ A, x a = true from ⟨d, inA, hx⟩)
        simp [mixed, lin, hx]
      · intro u v edge off
        rw [eval_literal]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro hd
          have lin : linear A (pairInput u v) = true := by
            simpa [linear] using (show ∃ a ∈ A, pairInput u v a = true from ⟨d, inA, hd⟩)
          simp [mixed, lin, hd]
        · exact outside_forces_d A b d (pairInput u v) off
    · by_cases residual : ∃ a ∈ A, G.Adj a d
      · obtain ⟨a₀, ha₀, edge₀⟩ := residual
        have unique (a : Fin n) (ha : a ∈ A) (ad : G.Adj a d) : a = a₀ := by
          apply Finset.card_le_one.mp (hfour b d same)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar a ha, ad.symm⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar a₀ ha₀, edge₀.symm⟩
        have down (x : Fin n → Bool) : primaryEval ⟨GateOp.and, [a₀.val, d.val]⟩ x = true →
            mixed A b d x = true := by
          rw [eval_edge]
          intro hx
          have both : x a₀ = true ∧ x d = true := by simpa using hx
          have lin : linear A x = true := by
            simpa [linear] using (show ∃ a ∈ A, x a = true from ⟨a₀, ha₀, both.1⟩)
          simp [mixed, lin, both.2]
        refine ⟨⟨GateOp.and, [a₀.val, d.val]⟩,
          Or.inr (Or.inr ⟨a₀, ha₀, edge₀, rfl⟩), down, ?_⟩
        intro u v edge off
        apply Bool.eq_iff_iff.mpr
        constructor
        · exact down _
        · intro on
          obtain ⟨a, ha, ad, active, hd⟩ := pair_residual G A b d u v inA edge off on
          have sameA := unique a ha ad
          rw [sameA] at active
          simp [eval_edge, active, hd]
      · refine ⟨⟨GateOp.or, []⟩, Or.inl rfl, ?_, ?_⟩
        · intro x hx
          change false = true at hx
          contradiction
        · intro u v edge off
          rw [eval_empty]
          symm
          apply Bool.eq_false_iff.mpr
          intro on
          obtain ⟨a, ha, ad, _, _⟩ := pair_residual G A b d u v inA edge off on
          exact residual ⟨a, ha, ad⟩

end PEqualNP.Outside.L_meta_1772_aux.ResidualStar
