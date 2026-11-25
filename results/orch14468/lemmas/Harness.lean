import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14468.Harness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List Nat := [0, 4, 1, 5, 0, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7]

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) ||
  (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) ||
  (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)

def posted (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

lemma vectorEight (x : Fin 8 → Bool) :
    x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  funext i
  fin_cases i <;> rfl

lemma equalEight {f g : (Fin 8 → Bool) → Bool}
    (h : ∀ a b c d e f' g' h' : Bool,
      f ![a, b, c, d, e, f', g', h'] = g ![a, b, c, d, e, f', g', h']) : f = g := by
  funext x
  rw [vectorEight x]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma target_posted : target = posted := equalEight (by decide)

def baseline : Circuit := ⟨[
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [8, 9]⟩,
    ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [12, 5]⟩,
    ⟨GateOp.and, [7, 13]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [16, 14]⟩,
    ⟨GateOp.or, [17, 15]⟩], 18⟩

lemma baseline_monotone : Monotone2 baseline := by
  simp [Monotone2, baseline]

lemma baseline_size : baseline.size = 11 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma baseline_correct : ∀ x : Fin 8 → Bool,
    baseline.eval (List.ofFn x) = target x :=
  congrFun (equalEight (by decide))

lemma baseline_posted (x : Fin 8 → Bool) :
    baseline.eval (List.ofFn x) = posted x := by
  rw [baseline_correct, target_posted]

def isNot (g : Gate) : Bool := match g.op with
  | GateOp.not => true
  | _ => false

lemma isNot_true (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]

lemma replacement_of_binary_floor
    (lower : ∀ (gs : List Gate) (o : Nat),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = target x) →
      10 ≤ gs.countP (fun g => !isNot g))
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = posted x) :
    ∃ (gs' : List Gate) (o' : Nat),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧
      ∀ x : Fin 8 → Bool, (Circuit.mk gs' o').eval (List.ofFn x) = posted x := by
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · have lo := lower gs o legal (fun x => by rw [correct, target_posted])
    obtain ⟨g, hg, hop⟩ := hn
    have lt : gs.countP (fun t => !isNot t) < gs.length := by
      by_contra h
      have eq : gs.countP (fun t => !isNot t) = gs.length :=
        Nat.le_antisymm List.countP_le_length (by omega)
      have all := List.countP_eq_length.mp eq g hg
      have no := (isNot_true g).2 hop
      simp [no] at all
    refine ⟨baseline.gates, baseline.output, ?_, ?_, baseline_posted⟩
    · exact baseline_monotone
    · change 11 ≤ gs.length
      omega
  · refine ⟨gs, o, ?_, le_rfl, correct⟩
    intro g hg
    obtain ⟨hop, hi⟩ := legal g hg
    refine ⟨?_, hi⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn ⟨g, hg, h⟩)

end PEqualNP.Outside.L_meta_14468.Harness
