import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds

def signedBit (b x : Bool) : Bool := if b then !x else x

lemma signedBit_flip (b x : Bool) : Bool.not (signedBit b x) = signedBit (!b) x := by
  cases b <;> cases x <;> rfl

lemma signedBit_constant (b x y : Bool) (h : x = y) : signedBit b x = signedBit b y :=
  congrArg (signedBit b) h

lemma not_prefix_signed (n : ℕ) (gs : List Gate)
    (clean : ∀ (p : ℕ) (g : Gate), gs[p]? = some g →
      ∃ j, j < n + p ∧ g.op = GateOp.not ∧ g.inputs = [j]) :
    ∀ i, i < n + gs.length → ∃ (j : Fin n) (b : Bool),
      ∀ x : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false = signedBit b (x j) := by
  have go (gates : List Gate) : ∀ (m : ℕ) (w : (Fin n → Bool) → List Bool),
      (∀ x, (w x).length = m) →
      (∀ i, i < m → ∃ (j : Fin n) (b : Bool), ∀ x, (w x).getD i false = signedBit b (x j)) →
      (∀ (p : ℕ) (g : Gate), gates[p]? = some g →
        ∃ j, j < m + p ∧ g.op = GateOp.not ∧ g.inputs = [j]) →
      ∀ i, i < m + gates.length → ∃ (j : Fin n) (b : Bool),
        ∀ x, (Circuit.wires ⟨gates, 0⟩ (w x)).getD i false = signedBit b (x j) := by
    induction gates with
    | nil =>
      intro m w hlen hsign _ i hi
      exact hsign i hi
    | cons g gates ih =>
      intro m w hlen hsign hclean i hi
      obtain ⟨read, hr, hop, hins⟩ := hclean 0 g (by simp)
      have hr' : read < m := by omega
      obtain ⟨v, b, hv⟩ := hsign read hr'
      let next : (Fin n → Bool) → List Bool := fun x => w x ++ [signedBit (!b) (x v)]
      have step (x : Fin n → Bool) :
          w x ++ [g.op.eval (g.inputs.map fun j => (w x).getD j false)] = next x := by
        simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
          hv, signedBit_flip, next]
      have result : ∃ (j : Fin n) (c : Bool), ∀ x,
          (Circuit.wires ⟨gates, 0⟩ (next x)).getD i false = signedBit c (x j) := by
        apply ih (m + 1) next (by intro x; simp [next, hlen]) ?_ ?_ i (by simp only [List.length_cons] at hi; omega)
        · intro j hj
          by_cases before : j < m
          · obtain ⟨u, c, hu⟩ := hsign j before
            refine ⟨u, c, fun x => ?_⟩
            change (w x ++ [_]).getD j false = _
            rw [List.getD_append _ _ _ _ (by rw [hlen]; exact before)]
            exact hu x
          · have e : j = m := by omega
            subst j
            refine ⟨v, !b, fun x => ?_⟩
            change (w x ++ [_]).getD m false = _
            rw [← hlen x]
            simp
        · intro p a ha
          obtain ⟨j, hj, hop, hins⟩ := hclean (p + 1) a (by simpa using ha)
          exact ⟨j, by omega, hop, hins⟩
      obtain ⟨u, c, hu⟩ := result
      refine ⟨u, c, fun x => ?_⟩
      change (Circuit.wires ⟨gates, 0⟩ (w x ++ [_])).getD i false = _
      rw [step]
      exact hu x
  apply go gs n (fun x => List.ofFn x) (by intro x; simp) ?_ clean
  intro i hi
  refine ⟨⟨i, hi⟩, false, ?_⟩
  intro x
  simp [List.getD_eq_getElem?_getD, hi, signedBit]

lemma signed_same_input_binary (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Bool) :
    (∃ c : Bool, ∀ x : Bool, op.eval [signedBit a x, signedBit b x] = c) ∨
    ∀ x : Bool, op.eval [signedBit a x, signedBit b x] = signedBit a x := by
  rcases hop with rfl | rfl <;> cases a <;> cases b
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inl ⟨false, by intro x; cases x <;> rfl⟩
  · exact Or.inl ⟨false, by intro x; cases x <;> rfl⟩
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inl ⟨true, by intro x; cases x <;> rfl⟩
  · exact Or.inl ⟨true, by intro x; cases x <;> rfl⟩
  · exact Or.inr (by intro x; cases x <;> rfl)

lemma signed_binary_control (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (b : Bool) : ∃ v c : Bool, ∀ a : Bool, op.eval [a, signedBit b v] = c := by
  rcases hop with rfl | rfl <;> cases b
  · exact ⟨false, false, by intro a; cases a <;> rfl⟩
  · exact ⟨true, false, by intro a; cases a <;> rfl⟩
  · exact ⟨true, true, by intro a; cases a <;> rfl⟩
  · exact ⟨false, true, by intro a; cases a <;> rfl⟩

end PEqualNP.Outside.L_meta_2592_aux
