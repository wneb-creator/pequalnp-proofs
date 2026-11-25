import ConstantNotSignature
open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
open PEqualNP.CircuitLowerBounds

def constantNegations : List Gate → List Sig → Prop
  | [], _ => True
  | g :: gs, w => (isNot g = true → gv w g = zero ∨ gv w g = one) ∧
      constantNegations gs (w ++ [gv w g])

lemma constantNegations_mono (gs : List Gate) (w : List Sig)
    (mono : ∀ g ∈ gs, isNot g = false) : constantNegations gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨?_, ih _ (fun a ha => mono a (by simp [ha]))⟩
    intro hn
    rw [mono g (by simp)] at hn
    contradiction

lemma constantNegations_append (gs hs : List Gate) (w : List Sig) :
    constantNegations (gs ++ hs) w ↔
      constantNegations gs w ∧ constantNegations hs (execute gs w) := by
  induction gs generalizing w with
  | nil => simp [constantNegations, execute]
  | cons g gs ih => simp only [List.cons_append, constantNegations, execute, List.foldl_cons, ih, and_assoc]

end PEqualNP.Outside.L_meta_2592.Signed.Extended
namespace PEqualNP.Outside.L_meta_2592.TerminalNot

lemma output_binary_eval (gs : List Gate) (op : GateOp) (i j n : Nat)
    (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨op, [i, j]⟩]) (n + gs.length)).eval (List.ofFn x) =
      op.eval [(Circuit.mk gs i).eval (List.ofFn x),
        (Circuit.mk gs j).eval (List.ofFn x)] := by
  have hlen : (wf gs (List.ofFn x)).length = n + gs.length := by simp [wf_len]
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change ((wf gs (List.ofFn x)) ++ [op.eval
    ([i, j].map fun k => (wf gs (List.ofFn x)).getD k false)]).getD
      (n + gs.length) false = _
  rw [← hlen, getD_snoc_eq]
  rfl

lemma read_internal_not (pre post : List Gate) (ins : List Nat) (n : Nat)
    (x : Fin n → Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.not, ins⟩ :: post) (n + pre.length)).eval (List.ofFn x) =
      Bool.not ((Circuit.mk pre (ins.headD (n + pre.length))).eval (List.ofFn x)) := by
  rw [show pre ++ ⟨GateOp.not, ins⟩ :: post =
    (pre ++ [⟨GateOp.not, ins⟩]) ++ post by simp]
  rw [appended_eval _ _ _ _ (by simp), output_not_eval_all]

lemma unique_not_context_mono (pre post : List Gate) (ins : List Nat) (out : Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (pre ++ ⟨GateOp.not, ins⟩ :: post) out))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk (pre ++ ⟨GateOp.not, ins⟩ :: post) out) = 1) :
    (∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have zero : ((pre ++ post).filter (fun g => decide (g.op = GateOp.not))).length = 0 := by
    simp only [List.filter_append, List.length_append]
    simpa [PEqualNP.NotBracket.notCount, List.filter_append, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using count
  have noNot : ∀ g ∈ pre ++ post, g.op ≠ GateOp.not := by
    intro g hg hop
    have member : g ∈ (pre ++ post).filter (fun a => decide (a.op = GateOp.not)) := by
      exact List.mem_filter.mpr ⟨hg, by simp [hop]⟩
    have positive := List.length_pos_of_mem member
    omega
  have mono : ∀ g ∈ pre ++ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have member : g ∈ pre ++ ⟨GateOp.not, ins⟩ :: post := by
      simp only [List.mem_append, List.mem_cons] at hg ⊢
      tauto
    have allowed := (legal g member).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
    rcases allowed with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (noNot g hg h)
  exact ⟨fun g hg => mono g (List.mem_append_left _ hg),
    fun g hg => mono g (List.mem_append_right _ hg)⟩

end PEqualNP.Outside.L_meta_2592.TerminalNot

namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

lemma direct_not_child_impossible
    (floor : ∀ gs : List Gate,
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) → constantNegations gs pins →
      target ∈ execute gs pins → 18 ≤ gs.countP (fun g => !isNot g))
    (pre post : List Gate) (ins : List Nat) (j : Nat) (isOr reverse : Bool)
    (preMono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (postMono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk ((pre ++ ⟨GateOp.not, ins⟩ :: post) ++
        [⟨if isOr then GateOp.or else GateOp.and,
          if reverse then [j, 10 + pre.length] else [10 + pre.length, j]⟩])
        (10 + (pre ++ ⟨GateOp.not, ins⟩ :: post).length)))
    (budget : (Circuit.mk ((pre ++ ⟨GateOp.not, ins⟩ :: post) ++
        [⟨if isOr then GateOp.or else GateOp.and,
          if reverse then [j, 10 + pre.length] else [10 + pre.length, j]⟩])
        (10 + (pre ++ ⟨GateOp.not, ins⟩ :: post).length)).size ≤ 19) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk ((pre ++ ⟨GateOp.not, ins⟩ :: post) ++
        [⟨if isOr then GateOp.or else GateOp.and,
          if reverse then [j, 10 + pre.length] else [10 + pre.length, j]⟩])
        (10 + (pre ++ ⟨GateOp.not, ins⟩ :: post).length)).eval (List.ofFn x) = f10 x := by
  intro computes
  let gs := pre ++ ⟨GateOp.not, ins⟩ :: post
  let q := fun x : Fin 10 → Bool => (Circuit.mk gs j).eval (List.ofFn x)
  have shape : ∀ x : Fin 10 → Bool,
      (if isOr then
        Bool.not ((Circuit.mk pre (ins.headD (10 + pre.length))).eval (List.ofFn x)) || q x
      else
        Bool.not ((Circuit.mk pre (ins.headD (10 + pre.length))).eval (List.ofFn x)) && q x)
        = f10 x := by
    intro x
    have h := computes x
    cases isOr <;> cases reverse <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true,
        PEqualNP.Outside.L_meta_2592.TerminalNot.output_binary_eval,
        PEqualNP.Outside.L_meta_2592.TerminalNot.read_internal_not,
        GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
        Bool.and_true, Bool.or_false, Bool.true_and, Bool.false_or, id_eq,
        Bool.and_comm, Bool.or_comm, gs, q] using h
  have constantAndCorrect :
      (gv (execute pre pins) ⟨GateOp.not, ins⟩ = zero ∨
        gv (execute pre pins) ⟨GateOp.not, ins⟩ = one) ∧
      ∀ x, q x = f10 x := by
    cases isOr with
    | false =>
      obtain ⟨constant, correct⟩ := final_and_not_constant pre ins q preMono shape
      exact ⟨Or.inr constant, correct⟩
    | true =>
      obtain ⟨constant, correct⟩ := final_or_not_constant pre ins q preMono shape
      exact ⟨Or.inl constant, correct⟩
  have preNot : ∀ g ∈ pre, isNot g = false := by
    intro g hg
    rcases preMono g hg with h | h <;> simp [isNot, h]
  have postNot : ∀ g ∈ post, isNot g = false := by
    intro g hg
    rcases postMono g hg with h | h <;> simp [isNot, h]
  have constants : constantNegations gs pins := by
    dsimp only [gs]
    rw [constantNegations_append]
    exact ⟨constantNegations_mono pre pins preNot,
      ⟨fun _ => constantAndCorrect.1, constantNegations_mono post _ postNot⟩⟩
  have gsLegal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact legal g (List.mem_append_left _ hg)
  have targetRead : (execute gs pins).getD j zero = target := by
    apply bit_ext
    intro r
    rw [pin_wire_bit gs j (fun g hg => (gsLegal g hg).1)]
    exact (constantAndCorrect.2 _).trans (rowTarget r).symm
  have targetMember : target ∈ execute gs pins := by
    simp only [List.getD_eq_getElem?_getD] at targetRead
    cases h : (execute gs pins)[j]? with
    | none =>
      rw [h] at targetRead
      exact False.elim ((by decide +kernel : target ≠ zero) targetRead.symm)
    | some a =>
      rw [h] at targetRead
      exact targetRead ▸ List.mem_of_getElem? h
  have lower := floor gs gsLegal constants targetMember
  have preCount : pre.countP (fun g => !isNot g) = pre.length := by
    apply List.countP_eq_length.mpr
    intro g hg
    simp [preNot g hg]
  have postCount : post.countP (fun g => !isNot g) = post.length := by
    apply List.countP_eq_length.mpr
    intro g hg
    simp [postNot g hg]
  simp only [gs, List.countP_append, List.countP_cons, preCount, postCount] at lower
  simp only [isNot, Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero] at lower
  simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at budget
  omega

end PEqualNP.Outside.L_meta_2592.Signed.Extended
