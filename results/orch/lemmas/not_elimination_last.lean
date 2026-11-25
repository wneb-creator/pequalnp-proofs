import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds

def wireBelow (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma wireBelow_snoc {a b : List Bool} {x y : Bool}
    (h : wireBelow a b) (hxy : x = true → y = true) :
    wireBelow (a ++ [x]) (b ++ [y]) := by
  have hlen := h.1
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by omega)]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), h.1]
    cases i - b.length with
    | zero => simpa using hxy
    | succ k => simp

lemma gate_preserves_below (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with h | h
  · simp only [h, GateOp.eval, List.all_eq_true, id_eq]
    intro ha v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hab.2 i (ha _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp only [h, GateOp.eval, List.any_eq_true, id_eq]
    intro ha
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, hab.2 i he⟩

lemma gates_preserve_below (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) :
    wireBelow ((⟨gs, 0⟩ : Circuit).wires a) ((⟨gs, 0⟩ : Circuit).wires b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    change wireBelow ((⟨gs, 0⟩ : Circuit).wires
      (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]))
      ((⟨gs, 0⟩ : Circuit).wires
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]))
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
      (wireBelow_snoc hab (gate_preserves_below g (hgs g List.mem_cons_self) hab))

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  obtain ⟨gs, o⟩ := C
  induction gs generalizing x with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (((⟨gs, o⟩ : Circuit).wires
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]))).length = _
    rw [ih]
    simp [Circuit.size]
    omega

lemma append_not_eval (C : Circuit) (x : List Bool) (i : ℕ) :
    (⟨C.gates ++ [⟨.not, [i]⟩], x.length + C.size⟩ : Circuit).eval x =
      !(C.wires x).getD i false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  change ((C.wires x) ++ [!(C.wires x).getD i false]).getD
    (x.length + C.size) false = _
  rw [← wires_length C x, List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rfl

lemma final_not_cannot_rise (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) (i : ℕ)
    (ha : (⟨C.gates ++ [⟨.not, [i]⟩], a.length + C.size⟩ : Circuit).eval a = false) :
    (⟨C.gates ++ [⟨.not, [i]⟩], b.length + C.size⟩ : Circuit).eval b = false := by
  rw [append_not_eval] at ha ⊢
  have hm := (gates_preserve_below C.gates hC hab).2 i
  have ha' : (C.wires a).getD i false = true := by simpa using ha
  have hb' : (C.wires b).getD i false = true := hm ha'
  rw [hb']
  rfl

end PEqualNP.Outside.L_meta_2592_aux
