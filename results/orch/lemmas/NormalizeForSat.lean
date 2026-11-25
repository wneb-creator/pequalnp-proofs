import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot96Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shift (n i : ℕ) : ℕ := if i < n then i else i + 1

def read (n j i : ℕ) : ℕ := if i < n + j then shift n i else n

def canonicalGate (n j : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .and, [] => ⟨.not, [n]⟩
  | .or, [] => ⟨.or, [n, n]⟩
  | .not, [] => ⟨.not, [n]⟩
  | .and, [i] => ⟨.and, [read n j i, read n j i]⟩
  | .or, [i] => ⟨.or, [read n j i, read n j i]⟩
  | .not, i :: _ => ⟨.not, [read n j i]⟩
  | .and, i :: k :: _ => ⟨.and, [read n j i, read n j k]⟩
  | .or, i :: k :: _ => ⟨.or, [read n j i, read n j k]⟩
  | _, _ => ⟨.or, [n, n]⟩

def canonicalGates (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => canonicalGate n j g :: canonicalGates n (j + 1) gs

def Related (n j : ℕ) (w z : List Bool) : Prop :=
  w.length = n + j ∧ z.length = n + j + 1 ∧ z.getD n false = false ∧
    ∀ i, z.getD (shift n i) false = w.getD i false

lemma relatedInitial (n : ℕ) (x : Fin n → Bool) :
    Related n 0 (List.ofFn x) (List.ofFn x ++ [false]) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · intro i
    by_cases hi : i < n
    · simp only [shift, ite_eq_left hi]
      exact List.getD_append _ _ _ _ (by simpa)
    · simp only [shift, ite_eq_right hi]
      rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_eq_default _ _ (by simp; omega)]

lemma readBound (n j i : ℕ) : read n j i < n + j + 1 := by
  unfold read shift
  split_ifs <;> omega

lemma readBoundLE (n j i : ℕ) : read n j i ≤ n + j := by
  have := readBound n j i
  omega

lemma readValue {n j : ℕ} {w z : List Bool} (h : Related n j w z) (i : ℕ) :
    z.getD (read n j i) false = w.getD i false := by
  unfold read
  split_ifs with hi
  · exact h.2.2.2 i
  · have hw := h.1
    rw [h.2.2.1, List.getD_eq_default _ _ (by omega)]

lemma relatedAppend {n j : ℕ} {w z : List Bool} (h : Related n j w z) (b : Bool) :
    Related n (j + 1) (w ++ [b]) (z ++ [b]) := by
  obtain ⟨hw, hz, zero, same⟩ := h
  refine ⟨by simp [hw]; omega, by simp [hz]; omega, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact zero
  · intro i
    by_cases hi : i < n + j
    · rw [List.getD_append _ _ _ _ (by unfold shift; split_ifs <;> omega)]
      rw [List.getD_append _ _ _ _ (by omega)]
      exact same i
    · by_cases he : i = n + j
      · subst i
        have hs : shift n (n + j) = n + j + 1 := by simp [shift]
        rw [hs, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        simp [hw, hz]
      · rw [List.getD_eq_default _ _ (by simp [hz]; unfold shift; split_ifs <;> omega)]
        rw [List.getD_eq_default _ _ (by simp [hw]; omega)]

lemma canonicalGateValue {n j : ℕ} {w z : List Bool} (h : Related n j w z)
    (g : Gate) (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (canonicalGate n j g).op.eval
      ((canonicalGate n j g).inputs.map fun i => z.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with rfl | rfl | rfl
  all_goals
    cases ins with
    | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, h.2.2.1, id_eq, Bool.false_or, Bool.not_false]
    | cons i rest =>
      cases rest with
      | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, readValue h, Bool.and_true, Bool.or_false, Bool.and_self, Bool.or_self]
      | cons k tail =>
        cases tail with
        | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, readValue h, Bool.and_true, Bool.or_false, Bool.and_self, Bool.or_self]
        | cons l tail => simp at hlen

lemma canonicalGateNot (n j : ℕ) (g : Gate) (h : g.op = .not) :
    (canonicalGate n j g).op = .not := by
  obtain ⟨op, ins⟩ := g
  cases h
  cases ins <;> rfl

lemma canonicalGatesLength (n j : ℕ) (gs : List Gate) :
    (canonicalGates n j gs).length = gs.length := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih => simp [canonicalGates, ih]

lemma canonicalGatesNot (n j : ℕ) (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = .not) :
    ∃ g ∈ canonicalGates n j gs, g.op = .not := by
  induction gs generalizing j with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, hop⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨canonicalGate n j _, List.mem_cons_self, canonicalGateNot n j _ hop⟩
    · obtain ⟨a, ha, hop⟩ := ih (j + 1) ⟨a, ha, hop⟩
      exact ⟨a, List.mem_cons_of_mem _ ha, hop⟩

lemma canonicalGatesRelated (n j : ℕ) (gs : List Gate) (w z : List Bool)
    (h : Related n j w z)
    (fan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2) :
    Related n (j + gs.length)
      (Circuit.wires ⟨gs, 0⟩ w) (Circuit.wires ⟨canonicalGates n j gs, 0⟩ z) := by
  induction gs generalizing j w z with
  | nil => simpa [Circuit.wires, canonicalGates] using h
  | cons g gs ih =>
    have hv := canonicalGateValue h g (fan g List.mem_cons_self)
    have hr := relatedAppend h (g.op.eval (g.inputs.map fun i => w.getD i false))
    have ht := ih (j + 1)
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (z ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) hr
      (fun a ha => fan a (List.mem_cons_of_mem _ ha))
    simp only [canonicalGates, Circuit.wires, List.foldl_cons, hv]
    simpa only [Circuit.wires, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht


def SatGate (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)) ∧
  ∀ i ∈ g.inputs, i < n + j + 1

def SatGates (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | j, g :: gs => SatGate n j g ∧ SatGates n (j + 1) gs

lemma canonicalGateSat (n j : ℕ) (g : Gate) : SatGate n j (canonicalGate n j g) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [canonicalGate, SatGate]
  | cons i rest =>
    cases rest with
    | nil => simp [canonicalGate, SatGate, readBoundLE]
    | cons k tail => simp [canonicalGate, SatGate, readBoundLE]

lemma canonicalGatesSat (n j : ℕ) (gs : List Gate) :
    SatGates n j (canonicalGates n j gs) := by
  induction gs generalizing j with
  | nil => trivial
  | cons g gs ih => exact ⟨canonicalGateSat n j g, ih (j + 1)⟩

lemma normalizedCircuit (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ D : Circuit, D.size = C.size ∧ SatGates n 0 D.gates ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x) := by
  let D : Circuit := ⟨canonicalGates n 0 C.gates, shift n C.output⟩
  refine ⟨D, canonicalGatesLength n 0 C.gates, canonicalGatesSat n 0 C.gates,
    canonicalGatesNot n 0 C.gates hasNot, ?_⟩
  intro x
  have hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fan g hg
  have h := canonicalGatesRelated n 0 C.gates (List.ofFn x)
    (List.ofFn x ++ [false]) (relatedInitial n x) hfan
  exact h.2.2.2 C.output

end PEqualNP.Outside.Pilot96Normalize
