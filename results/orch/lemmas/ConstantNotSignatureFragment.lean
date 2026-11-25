namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

lemma pin_wire_bit (gs : List Gate) (out : Nat)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (r : Row) :
    bit r ((execute gs pins).getD out zero) =
      (Circuit.mk gs out).eval (List.ofFn (assign r)) := by
  rw [← b_read, execute_bits _ _ _ legal]
  change (Circuit.mk gs out).eval (pins.map (bit r)) = _
  rw [rowPins]

lemma not_gate_constant (gs : List Gate) (ins : List Nat) (b : Bool)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (constant : ∀ x : Fin 10 → Bool,
      Bool.not ((Circuit.mk gs (ins.headD (10 + gs.length))).eval (List.ofFn x)) = b) :
    gv (execute gs pins) ⟨GateOp.not, ins⟩ = if b then one else zero := by
  apply bit_ext
  intro r
  rw [run_bit r _ _ (by simp), execute_bits _ _ _ legal, rowPins]
  change GateOp.not.eval
    (ins.map fun i => (PEqualNP.Outside.L_meta_2592.TerminalNot.wf gs
      (List.ofFn (assign r))).getD i false) = _
  rw [PEqualNP.Outside.L_meta_2592.TerminalNot.not_inputs_eval, constant]
  cases b <;> simp [bit_one, bit_zero]

lemma final_and_not_constant (gs : List Gate) (ins : List Nat)
    (q : (Fin 10 → Bool) → Bool)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (computes : ∀ x : Fin 10 → Bool,
      (Bool.not ((Circuit.mk gs (ins.headD (10 + gs.length))).eval (List.ofFn x)) && q x)
        = f10 x) :
    gv (execute gs pins) ⟨GateOp.not, ins⟩ = one ∧ ∀ x, q x = f10 x := by
  have top : f10 (fun _ => true) = true := by decide +kernel
  obtain ⟨constant, sibling⟩ :=
    PEqualNP.Outside.L_meta_2592.TerminalNot.one_not_and_terminal_reduces
      10 (Circuit.mk gs (ins.headD (10 + gs.length))) f10 q mono top computes
  refine ⟨?_, sibling⟩
  exact not_gate_constant gs ins true
    (fun g hg => by rcases mono g hg with h | h <;> simp [h]) constant

lemma final_or_not_constant (gs : List Gate) (ins : List Nat)
    (q : (Fin 10 → Bool) → Bool)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (computes : ∀ x : Fin 10 → Bool,
      (Bool.not ((Circuit.mk gs (ins.headD (10 + gs.length))).eval (List.ofFn x)) || q x)
        = f10 x) :
    gv (execute gs pins) ⟨GateOp.not, ins⟩ = zero ∧ ∀ x, q x = f10 x := by
  have bottom : f10 (fun _ => false) = false := by decide +kernel
  obtain ⟨constant, sibling⟩ :=
    PEqualNP.Outside.L_meta_2592.TerminalNot.one_not_or_terminal_reduces
      10 (Circuit.mk gs (ins.headD (10 + gs.length))) f10 q mono bottom computes
  refine ⟨?_, sibling⟩
  exact not_gate_constant gs ins false
    (fun g hg => by rcases mono g hg with h | h <;> simp [h]) constant

end PEqualNP.Outside.L_meta_2592.Signed.Extended
