import PEqualNP.Outside.L_meta_2592
import ConstantNot
open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]


end PEqualNP.Outside.L_meta_2592.Signed.Extended
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
