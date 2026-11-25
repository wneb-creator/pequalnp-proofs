import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.IdentityPad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def SatGate (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)) ∧
  ∀ i ∈ g.inputs, i < n + j + 1

def SatGates (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | j, g :: gs => SatGate n j g ∧ SatGates n (j + 1) gs

def appendCopy (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, C.output]⟩], n + C.size + 1⟩

def padCopies (n : ℕ) (C : Circuit) : ℕ → Circuit
  | 0 => C
  | k + 1 => appendCopy n (padCopies n C k)

lemma wiresLength (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  obtain ⟨gs, out⟩ := C
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length =
      xs.length + (g :: gs).length
    rw [ih]
    simp [Circuit.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma appendCopySize (n : ℕ) (C : Circuit) :
    (appendCopy n C).size = C.size + 1 := by
  simp [appendCopy, Circuit.size]

lemma appendCopyEval (n : ℕ) (C : Circuit) (xs : List Bool)
    (length : xs.length = n + 1) :
    (appendCopy n C).eval xs = C.eval xs := by
  have wires : (C.wires xs).length = n + C.size + 1 := by
    rw [wiresLength, length]
    omega
  simp only [Circuit.eval, appendCopy, Circuit.wires, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  change ((C.wires xs) ++ [GateOp.or.eval
    ([C.output, C.output].map fun i => (C.wires xs).getD i false)]).getD
      (n + C.size + 1) false = C.eval xs
  rw [← wires, List.getD_append_right _ _ _ _ (by omega)]
  simp [Circuit.eval, GateOp.eval]

lemma appendCopyValid (n : ℕ) (C : Circuit) :
    (appendCopy n C).output < n + (appendCopy n C).size + 1 := by
  rw [appendCopySize]
  simp only [appendCopy]
  omega

lemma appendCopyLast (n : ℕ) (C : Circuit) :
    (appendCopy n C).output + 1 = n + 1 + (appendCopy n C).size := by
  rw [appendCopySize]
  simp only [appendCopy]
  omega

lemma satAppend (n j : ℕ) (gs qs : List Gate)
    (left : SatGates n j gs) (right : SatGates n (j + gs.length) qs) :
    SatGates n j (gs ++ qs) := by
  induction gs generalizing j with
  | nil => simpa using right
  | cons g gs ih =>
    refine ⟨left.1, ih (j + 1) left.2 ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using right

lemma appendCopySat (n : ℕ) (C : Circuit)
    (sat : SatGates n 0 C.gates) (valid : C.output < n + C.size + 1) :
    SatGates n 0 (appendCopy n C).gates := by
  apply satAppend n 0 C.gates _ sat
  refine ⟨?_, trivial⟩
  refine ⟨Or.inl ⟨Or.inr rfl, rfl⟩, ?_⟩
  intro i hi
  have eq : i = C.output := by simpa using hi
  subst i
  simpa only [Nat.zero_add, Circuit.size] using valid

lemma appendCopyHasNot (n : ℕ) (C : Circuit)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (appendCopy n C).gates, g.op = .not := by
  obtain ⟨g, mem, op⟩ := hasNot
  exact ⟨g, List.mem_append_left _ mem, op⟩

lemma padCopiesSize (n : ℕ) (C : Circuit) (k : ℕ) :
    (padCopies n C k).size = C.size + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padCopies, appendCopySize, ih]; omega

lemma padCopiesValid (n : ℕ) (C : Circuit) (k : ℕ)
    (valid : C.output < n + C.size + 1) :
    (padCopies n C k).output < n + (padCopies n C k).size + 1 := by
  cases k with
  | zero => exact valid
  | succ k => exact appendCopyValid n (padCopies n C k)

lemma padCopiesLast (n : ℕ) (C : Circuit) (k : ℕ)
    (last : C.output + 1 = n + 1 + C.size) :
    (padCopies n C k).output + 1 = n + 1 + (padCopies n C k).size := by
  cases k with
  | zero => exact last
  | succ k => exact appendCopyLast n (padCopies n C k)

lemma padCopiesEval (n : ℕ) (C : Circuit) (k : ℕ) (xs : List Bool)
    (length : xs.length = n + 1) :
    (padCopies n C k).eval xs = C.eval xs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padCopies, appendCopyEval n _ xs length, ih]

lemma padCopiesSat (n : ℕ) (C : Circuit) (k : ℕ)
    (sat : SatGates n 0 C.gates) (valid : C.output < n + C.size + 1) :
    SatGates n 0 (padCopies n C k).gates := by
  induction k with
  | zero => exact sat
  | succ k ih => exact appendCopySat n _ ih (padCopiesValid n C k valid)

lemma padCopiesHasNot (n : ℕ) (C : Circuit) (k : ℕ)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (padCopies n C k).gates, g.op = .not := by
  induction k with
  | zero => exact hasNot
  | succ k ih => exact appendCopyHasNot n _ ih

lemma padToBudget (n budget : ℕ) (C : Circuit)
    (small : C.size ≤ budget) (sat : SatGates n 0 C.gates)
    (last : C.output + 1 = n + 1 + C.size)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ D : Circuit, D.size = budget ∧ SatGates n 0 D.gates ∧
      D.output + 1 = n + 1 + D.size ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ xs : List Bool, xs.length = n + 1 → D.eval xs = C.eval xs := by
  refine ⟨padCopies n C (budget - C.size), ?_, ?_, ?_, ?_, ?_⟩
  · rw [padCopiesSize]
    omega
  · exact padCopiesSat n C _ sat (by omega)
  · exact padCopiesLast n C _ last
  · exact padCopiesHasNot n C _ hasNot
  · exact padCopiesEval n C _

end PEqualNP.Outside.L_meta_2592_aux.IdentityPad
