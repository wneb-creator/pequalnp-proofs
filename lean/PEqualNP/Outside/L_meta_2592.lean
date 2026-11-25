import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def trimNot (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma trimNot_op (g : Gate) : (trimNot g).op = g.op := by
  cases g with
  | mk op ins => cases op <;> rfl

lemma trimNot_eval (g : Gate) (w : ℕ → Bool) :
    (trimNot g).op.eval ((trimNot g).inputs.map w) = g.op.eval (g.inputs.map w) := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [trimNot]
    cases ins <;> simp [GateOp.eval]

lemma trimNot_fanin (g : Gate) (h : g.inputs.length ≤ 2) :
    (trimNot g).inputs.length ≤ 2 := by
  cases g with
  | mk op ins =>
    cases op <;> simp_all [trimNot]

lemma trimNot_unary (g : Gate) (h : (trimNot g).op = GateOp.not) :
    (trimNot g).inputs.length ≤ 1 := by
  cases g with
  | mk op ins => cases op <;> simp_all [trimNot]

def trimNotCircuit (C : Circuit) : Circuit := ⟨C.gates.map trimNot, C.output⟩

lemma trimNotCircuit_fanin (C : Circuit) (h : FanInTwo C) :
    FanInTwo (trimNotCircuit C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  exact ⟨by simpa only [trimNot_op] using (h a ha).1, trimNot_fanin a (h a ha).2⟩

lemma trimNotCircuit_size (C : Circuit) : (trimNotCircuit C).size = C.size :=
  List.length_map _

lemma trimNotCircuit_wires (C : Circuit) (w : List Bool) :
    (trimNotCircuit C).wires w = C.wires w := by
  cases C with
  | mk gs out =>
    change (gs.map trimNot).foldl _ w = gs.foldl _ w
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, trimNot_eval, ih]

lemma trimNotCircuit_eval (C : Circuit) (w : List Bool) :
    (trimNotCircuit C).eval w = C.eval w := by
  unfold Circuit.eval
  rw [trimNotCircuit_wires]
  rfl

lemma trimNotCircuit_hasNot (C : Circuit) :
    (∃ g ∈ (trimNotCircuit C).gates, g.op = GateOp.not) ↔
      ∃ g ∈ C.gates, g.op = GateOp.not := by
  constructor
  · rintro ⟨g, hg, hn⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ⟨a, ha, (trimNot_op a).symm.trans hn⟩
  · rintro ⟨g, hg, hn⟩
    exact ⟨trimNot g, List.mem_map.mpr ⟨g, hg, rfl⟩, (trimNot_op g).trans hn⟩

end PEqualNP.Outside.L_meta_2592_aux
