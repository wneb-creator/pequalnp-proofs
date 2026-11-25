import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OperandSort

open PEqualNP.CircuitLowerBounds

def SatGate (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)) ∧
  ∀ i ∈ g.inputs, i < n + j + 1

def SatGates (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | j, g :: gs => SatGate n j g ∧ SatGates n (j + 1) gs

def sortInputs : List ℕ → List ℕ
  | [a, b] => [min a b, max a b]
  | xs => xs

def sortGate (g : Gate) : Gate :=
  match g.op with
  | .not => g
  | _ => ⟨g.op, sortInputs g.inputs⟩

lemma sortInputsPerm (xs : List ℕ) : (sortInputs xs).Perm xs := by
  cases xs with
  | nil => exact List.Perm.refl _
  | cons a xs =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons b xs =>
      cases xs with
      | cons c xs => exact List.Perm.refl _
      | nil =>
        by_cases h : a ≤ b
        · simp only [sortInputs, min_eq_left h, max_eq_right h]
          exact List.Perm.refl _
        · have h' : b ≤ a := by omega
          simp only [sortInputs, min_eq_right h', max_eq_left h']
          exact List.Perm.swap _ _ _

lemma sortInputsOrdered (xs : List ℕ) (a b : ℕ)
    (eq : sortInputs xs = [a, b]) : a ≤ b := by
  cases xs with
  | nil => simp [sortInputs] at eq
  | cons i xs =>
    cases xs with
    | nil => simp [sortInputs] at eq
    | cons j xs =>
      cases xs with
      | cons k xs => simp [sortInputs] at eq
      | nil =>
        change [min i j, max i j] = [a, b] at eq
        obtain ⟨ha, tail⟩ := List.cons.inj eq
        obtain ⟨hb, _⟩ := List.cons.inj tail
        subst a
        subst b
        exact min_le_max

lemma sortGateOp (g : Gate) : (sortGate g).op = g.op := by
  cases h : g.op <;> simp [sortGate, h]

lemma sortGatePerm (g : Gate) : (sortGate g).inputs.Perm g.inputs := by
  cases h : g.op <;> simp only [sortGate, h]
  all_goals first | exact sortInputsPerm _ | exact List.Perm.refl _

lemma sortGateValue (g : Gate) (xs : List Bool)
    (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (sortGate g).op.eval ((sortGate g).inputs.map fun i => xs.getD i false) =
      g.op.eval (g.inputs.map fun i => xs.getD i false) := by
  have perm := (sortGatePerm g).map (fun i => xs.getD i false)
  rw [sortGateOp]
  rcases basis with h | h | h
  · rw [h]
    exact perm.all_eq
  · rw [h]
    exact perm.any_eq
  · simp [sortGate, h]

lemma sortGateSat (n j : ℕ) (g : Gate) (sat : SatGate n j g) :
    SatGate n j (sortGate g) := by
  refine ⟨?_, ?_⟩
  · simpa only [sortGateOp, (sortGatePerm g).length_eq] using sat.1
  · intro i hi
    exact sat.2 i ((sortGatePerm g).mem_iff.mp hi)

lemma sortGateOrdered (n j : ℕ) (g : Gate) (sat : SatGate n j g)
    (a b : ℕ) (eq : (sortGate g).inputs = [a, b]) : a ≤ b := by
  rcases sat.1 with ⟨basis, length⟩ | ⟨op, length⟩
  · have inputs : (sortGate g).inputs = sortInputs g.inputs := by
      rcases basis with h | h <;> simp [sortGate, h]
    rw [inputs] at eq
    exact sortInputsOrdered g.inputs a b eq
  · have inputs : (sortGate g).inputs = g.inputs := by simp [sortGate, op]
    rw [inputs] at eq
    have bad := congrArg List.length eq
    simp [length] at bad

lemma satMember (n j : ℕ) (gs : List Gate) (sat : SatGates n j gs)
    (g : Gate) (mem : g ∈ gs) : ∃ k, SatGate n k g := by
  induction gs generalizing j with
  | nil => simp at mem
  | cons h gs ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨j, sat.1⟩
    · exact ih (j + 1) sat.2 mem

lemma sortGatesSat (n j : ℕ) (gs : List Gate) (sat : SatGates n j gs) :
    SatGates n j (gs.map sortGate) := by
  induction gs generalizing j with
  | nil => trivial
  | cons g gs ih => exact ⟨sortGateSat n j g sat.1, ih (j + 1) sat.2⟩

lemma sortGatesWires (gs : List Gate) (xs : List Bool)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    Circuit.wires ⟨gs.map sortGate, 0⟩ xs = Circuit.wires ⟨gs, 0⟩ xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.wires, List.foldl_cons]
    rw [sortGateValue g xs (basis g List.mem_cons_self)]
    exact ih _ (fun h hm => basis h (List.mem_cons_of_mem _ hm))

lemma sortedCircuit (n : ℕ) (C : Circuit) (sat : SatGates n 0 C.gates) :
    ∃ D : Circuit, D.size = C.size ∧ D.output = C.output ∧
      SatGates n 0 D.gates ∧
      ((∃ g ∈ C.gates, g.op = .not) → ∃ g ∈ D.gates, g.op = .not) ∧
      (∀ g ∈ D.gates, ∀ a b, g.inputs = [a, b] → a ≤ b) ∧
      ∀ xs : List Bool, D.eval xs = C.eval xs := by
  let D : Circuit := ⟨C.gates.map sortGate, C.output⟩
  refine ⟨D, List.length_map sortGate, rfl, sortGatesSat n 0 C.gates sat, ?_, ?_, ?_⟩
  · rintro ⟨g, mem, op⟩
    exact ⟨sortGate g, List.mem_map.mpr ⟨g, mem, rfl⟩, (sortGateOp g).trans op⟩
  · intro g mem a b eq
    obtain ⟨h, hm, rfl⟩ := List.mem_map.mp mem
    obtain ⟨j, hs⟩ := satMember n 0 C.gates sat h hm
    exact sortGateOrdered n j h hs a b eq
  · intro xs
    have basis : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      intro g mem
      obtain ⟨j, hs⟩ := satMember n 0 C.gates sat g mem
      rcases hs.1 with ⟨h | h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact congrArg (fun ws : List Bool => ws.getD C.output false) (sortGatesWires C.gates xs basis)

end PEqualNP.Outside.L_meta_2592_aux.OperandSort
