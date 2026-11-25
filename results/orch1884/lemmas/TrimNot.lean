import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.TrimNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

def circuit (C : Circuit) : Circuit := ⟨C.gates.map gate, C.output⟩

lemma op (g : Gate) : (gate g).op = g.op := by
  cases h : g.op <;> simp [gate, h]

lemma input_length (g : Gate) : (gate g).inputs.length ≤ g.inputs.length := by
  cases h : g.op <;> simp [gate, h]

lemma not_input_length (g : Gate) (h : (gate g).op = .not) :
    (gate g).inputs.length ≤ 1 := by
  rw [op] at h
  simp [gate, h]

lemma eval (g : Gate) (w : List Bool) :
    (gate g).op.eval ((gate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases h : g.op <;> simp only [gate, h]
  cases g.inputs <;> rfl

lemma wires (C : Circuit) (w : List Bool) : (circuit C).wires w = C.wires w := by
  cases C with
  | mk gs out =>
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (List.map gate gs).foldl _
        (w ++ [(gate g).op.eval ((gate g).inputs.map fun i => w.getD i false)]) = _
      rw [eval]
      exact ih _

lemma computes (C : Circuit) (w : List Bool) : (circuit C).eval w = C.eval w := by
  unfold Circuit.eval
  rw [wires]
  rfl

lemma size (C : Circuit) : (circuit C).size = C.size := by
  simp [circuit, Circuit.size]

lemma legal (C : Circuit) (h : FanInTwo C) : FanInTwo (circuit C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact ⟨by simpa only [op] using (h g' hg').1,
    (input_length g').trans (h g' hg').2⟩

lemma count (C : Circuit) :
    PEqualNP.NotBracket.notCount (circuit C) = PEqualNP.NotBracket.notCount C := by
  cases C with
  | mk gs out =>
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      change ((List.map gate (g :: gs)).filter (fun g =>
        @decide (g.op = .not) (lineDegreeGateOpDecEq g.op .not))).length =
        ((g :: gs).filter (fun g =>
          @decide (g.op = .not) (lineDegreeGateOpDecEq g.op .not))).length
      simp only [List.map_cons, List.filter_cons]
      rw [op]
      split_ifs
      · simp only [List.length_cons]
        exact congrArg Nat.succ ih
      · exact ih

lemma not_reads_head (g : Gate) (h : g.op = .not) (i : Nat) :
    i ∈ (gate g).inputs ↔ g.inputs.head? = some i := by
  cases hi : g.inputs with
  | nil => simp [gate, h, hi]
  | cons a as => simp [gate, h, hi, eq_comm]

lemma nonnot (g : Gate) (h : g.op ≠ .not) : gate g = g := by
  cases hg : g.op <;> simp_all [gate]

end PEqualNP.Outside.L_meta_1884.TrimNot
