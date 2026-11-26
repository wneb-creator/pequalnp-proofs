import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4310_1
    (hA : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) C.gates ≤ (1 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (15 : ℕ) ≤ C.size)
    (hB : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) C.gates ≤ (1 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 1) → (15 : ℕ) ≤ C.size)
    (hC : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) C.gates ≤ (1 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ a < 11 ∧ b < 11) → (15 : ℕ) ≤ C.size)
    (hD : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval [Bool.false]) C.gates → List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval [Bool.false]) C.gates ≤ (1 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ (11 ≤ a ∨ 11 ≤ b)) → (15 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) x1.gates ≤ (1 : ℕ) → (15 : ℕ) ≤ x1.size := by
  intro C hfan hfun h13 h1
  by_contra hsmall
  push_neg at hsmall
  have hsum : List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) C.gates + List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) C.gates = C.gates.length := by
    induction C.gates with
    | nil => simp
    | cons g gs ih =>
      cases hb : g.op.eval [Bool.false] with
      | true => simp [List.countP_cons, hb]; omega
      | false => simp [List.countP_cons, hb]; omega
  have hsize : C.size = C.gates.length := rfl
  have h1lt : 1 < C.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[1]? = some g := ⟨C.gates[1]'h1lt, List.getElem?_eq_getElem h1lt⟩
  have hgeq : g = C.gates[1]'h1lt := Option.some.inj (hg.symm.trans (List.getElem?_eq_getElem h1lt))
  have hgmem : g ∈ C.gates := by rw [hgeq]; exact List.getElem_mem h1lt
  rcases hfan g hgmem with ⟨hop, hin⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hopA | hopO | hopN
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · have hx := hB C hfan hfun h13 h1 ⟨g, hg, Or.inl hopA, by omega⟩; omega
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 11 with ha | ha
      · rcases Nat.lt_or_ge b 11 with hb | hb
        · have hx := hC C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inl hopA, hab, ha, hb⟩; omega
        · have hx := hD C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inl hopA, hab, Or.inr hb⟩; omega
      · have hx := hD C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inl hopA, hab, Or.inl ha⟩; omega
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · have hx := hB C hfan hfun h13 h1 ⟨g, hg, Or.inr hopO, by omega⟩; omega
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 11 with ha | ha
      · rcases Nat.lt_or_ge b 11 with hb | hb
        · have hx := hC C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inr hopO, hab, ha, hb⟩; omega
        · have hx := hD C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inr hopO, hab, Or.inr hb⟩; omega
      · have hx := hD C hfan hfun h13 h1 ⟨g, a, b, hg, Or.inr hopO, hab, Or.inl ha⟩; omega
  · have hx := hA C hfan hfun h13 h1 ⟨g, hg, hopN⟩; omega
