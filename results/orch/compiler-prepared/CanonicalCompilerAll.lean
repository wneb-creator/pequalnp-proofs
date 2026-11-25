import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Program (n : Nat) : Nat → Type
  | 0 => List (Fin n)
  | k + 1 => (List (Fin n) × List (Fin n)) × Program (n + 1) k

def evaluate {n : Nat} : (k : Nat) → Program n k → (Fin n → Bool) → Bool
  | 0, output, values => output.all values
  | k + 1, program, values =>
      evaluate k program.2 (Fin.snoc values (program.1.1.all values || program.1.2.all values))

def conjunction (offset : Nat) : List Nat → List Gate
  | [] => [⟨.and, []⟩]
  | wire :: tail => conjunction offset tail ++ [⟨.and, [wire, offset + tail.length]⟩]

def compile {n : Nat} : (k : Nat) → Program n k → Nat → (Fin n → Nat) → Circuit
  | 0, output, offset, refs =>
      ⟨conjunction offset (output.map refs), offset + output.length⟩
  | k + 1, program, offset, refs =>
      let left := program.1.1
      let right := program.1.2
      let leftGates := conjunction offset (left.map refs)
      let rightOffset := offset + left.length + 1
      let rightGates := conjunction rightOffset (right.map refs)
      let orWire := rightOffset + right.length + 1
      let later := compile k program.2 (orWire + 1) (Fin.snoc refs orWire)
      ⟨leftGates ++ rightGates ++
          [⟨.or, [offset + left.length, rightOffset + right.length]⟩] ++ later.gates,
        later.output⟩

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def emittedOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma conjunction_legal (offset : Nat) (wires : List Nat) :
    ∀ g ∈ conjunction offset wires,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction wires with
  | nil => simp [conjunction]
  | cons wire wires ih =>
    intro g hg
    simp only [conjunction, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · simp

lemma conjunction_or_count (offset : Nat) (wires : List Nat) :
    (conjunction offset wires).countP emittedOr = 0 := by
  induction wires with
  | nil => rfl
  | cons wire wires ih => simp [conjunction, List.countP_append, emittedOr, ih]

lemma compile_monotone2 {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) : Monotone2 (compile k program offset refs) := by
  induction k generalizing n offset with
  | zero => exact conjunction_legal offset (program.map refs)
  | succ k ih =>
    intro g hg
    simp only [compile, List.mem_append, List.mem_cons, List.not_mem_nil, false_or, or_assoc] at hg
    rcases hg with hl | hr | ho | ht
    · exact conjunction_legal _ _ g hl
    · exact conjunction_legal _ _ g hr
    · subst g
      simp
    · exact (ih (n := n + 1) program.2 _ _) g ht

lemma compile_or_count {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    (compile k program offset refs).gates.countP emittedOr = k := by
  induction k generalizing n offset with
  | zero => exact conjunction_or_count offset (program.map refs)
  | succ k ih =>
    simp [compile, List.countP_append, List.countP_cons, conjunction_or_count, emittedOr, ih, Nat.add_comm]

lemma emittedOr_count_filter (gs : List Gate) :
    (Finset.univ.filter (fun i : Fin gs.length => emittedOr (gs.get i) = true)).card =
      gs.countP emittedOr := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    show (Finset.univ.filter
      (fun i : Fin (gs.length + 1) => emittedOr ((g :: gs).get i) = true)).card = _
    rw [Fin.card_filter_univ_succ]
    simp only [List.countP_cons]
    split_ifs with h₁ h₂ h₂
    · simpa using ih
    · exact absurd h₁ h₂
    · exact absurd h₂ h₁
    · simpa using ih

lemma emittedOr_count_ncard (gs : List Gate) :
    {i : Fin gs.length | (gs.get i).op = GateOp.or}.ncard = gs.countP emittedOr := by
  have he : {i : Fin gs.length | (gs.get i).op = GateOp.or} =
      ↑(Finset.univ.filter (fun i : Fin gs.length => emittedOr (gs.get i) = true)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    unfold emittedOr
    cases (gs.get i).op <;> simp
  rw [he, Set.ncard_coe_finset, emittedOr_count_filter]

lemma compile_or_ncard {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    {i : Fin (compile k program offset refs).gates.length |
      ((compile k program offset refs).gates.get i).op = GateOp.or}.ncard = k := by
  rw [emittedOr_count_ncard, compile_or_count]

lemma compile_or_ncard_getElem {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    {i : Fin (compile k program offset refs).gates.length |
      ((compile k program offset refs).gates[i]).op = GateOp.or}.ncard = k := by
  simpa only [List.get_eq_getElem, Fin.getElem_fin] using compile_or_ncard k program offset refs

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gates : List Gate) (wires : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wires

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w =
      run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma run_keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma conjunction_length (offset : Nat) (args : List Nat) :
    (conjunction offset args).length = args.length + 1 := by
  induction args with
  | nil => rfl
  | cons i tail ih => simp [conjunction, ih, Nat.add_assoc]

lemma conjunction_output (offset : Nat) (args : List Nat) (w : List Bool)
    (hlen : w.length = offset) (hbound : ∀ i ∈ args, i < offset) :
    (run (conjunction offset args) w).getD (offset + args.length) false =
      args.all (fun i => w.getD i false) := by
  induction args with
  | nil =>
    simp only [conjunction, run, List.foldl_cons, List.foldl_nil,
      List.map_nil, GateOp.eval, List.all_nil, List.length_nil, Nat.add_zero]
    rw [← hlen, getD_snoc_eq]
  | cons i tail ih =>
    rw [conjunction, run_snoc]
    have hi : i < w.length := by rw [hlen]; exact hbound i (by simp)
    have he : offset + (i :: tail).length = (run (conjunction offset tail) w).length := by
      rw [run_length, conjunction_length, hlen]
      simp
    rw [he, getD_snoc_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]
    rw [run_keep _ _ _ hi, ih (fun j hj => hbound j (by simp [hj]))]
    rfl

lemma compile_eval {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) (w : List Bool)
    (hlen : w.length = offset) (hbound : ∀ i, refs i < offset) :
    (compile k program offset refs).eval w =
      evaluate k program (fun i => w.getD (refs i) false) := by
  induction k generalizing n offset w with
  | zero =>
    change List (Fin n) at program
    change (run (conjunction offset (program.map refs)) w).getD
        (offset + program.length) false = program.all (fun i => w.getD (refs i) false)
    have h := conjunction_output offset (program.map refs) w hlen (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact hbound i)
    simpa only [Program, List.length_map, List.all_map, Function.comp_def] using h
  | succ k ih =>
    let left := program.1.1
    let right := program.1.2
    let leftGates := conjunction offset (left.map refs)
    let rightOffset := offset + left.length + 1
    let rightGates := conjunction rightOffset (right.map refs)
    let orWire := rightOffset + right.length + 1
    let orGate : Gate := ⟨.or, [offset + left.length, rightOffset + right.length]⟩
    let before := leftGates ++ rightGates ++ [orGate]
    let next := run before w
    have hleftlen : (run leftGates w).length = rightOffset := by
      simp [leftGates, run_length, conjunction_length, hlen, rightOffset, Nat.add_assoc]
    have hprelen : (run (leftGates ++ rightGates) w).length = orWire := by
      simp [run_length, leftGates, rightGates, conjunction_length, hlen,
        orWire, rightOffset, Nat.add_assoc]
    have hnextlen : next.length = orWire + 1 := by
      simp [next, before, run_length, leftGates, rightGates, conjunction_length, hlen,
        orWire, rightOffset, Nat.add_assoc]
    have hkeep (i : Fin n) : next.getD (refs i) false = w.getD (refs i) false :=
      run_keep before w (refs i) (by rw [hlen]; exact hbound i)
    have hleft : (run (leftGates ++ rightGates) w).getD (offset + left.length) false =
        left.all (fun i => w.getD (refs i) false) := by
      rw [run_append, run_keep _ _ _ (by rw [hleftlen]; simp [rightOffset])]
      have h := conjunction_output offset (left.map refs) w hlen (by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        exact hbound i)
      simpa only [leftGates, List.length_map, List.all_map, Function.comp_def] using h
    have hright : (run (leftGates ++ rightGates) w).getD (rightOffset + right.length) false =
        right.all (fun i => w.getD (refs i) false) := by
      rw [run_append]
      have h := conjunction_output rightOffset (right.map refs) (run leftGates w) hleftlen (by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hb := hbound i
        dsimp [rightOffset]
        omega)
      have hold (i : Fin n) : (run leftGates w).getD (refs i) false = w.getD (refs i) false :=
        run_keep leftGates w _ (by rw [hlen]; exact hbound i)
      simpa only [rightGates, List.length_map, List.all_map, Function.comp_def, hold] using h
    have hnew : next.getD orWire false =
        (left.all (fun i => w.getD (refs i) false) ||
          right.all (fun i => w.getD (refs i) false)) := by
      dsimp only [next, before]
      rw [run_snoc, ← hprelen, getD_snoc_eq]
      simp only [orGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, hleft, hright]
      rfl
    have hnextbound : ∀ i : Fin (n + 1),
        (Fin.snoc refs orWire : Fin (n + 1) → Nat) i < orWire + 1 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.snoc_castSucc]
        have hb := hbound j
        dsimp [orWire, rightOffset]
        omega
    have hvalues : (fun i => next.getD ((Fin.snoc refs orWire : Fin (n + 1) → Nat) i) false) =
        Fin.snoc (fun i => w.getD (refs i) false)
          (left.all (fun i => w.getD (refs i) false) ||
            right.all (fun i => w.getD (refs i) false)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hnew
      · simpa only [Fin.snoc_castSucc] using hkeep j
    change (run (before ++ (compile k program.2 (orWire + 1) (Fin.snoc refs orWire)).gates) w).getD
        (compile k program.2 (orWire + 1) (Fin.snoc refs orWire)).output false = _
    rw [run_append]
    change (compile k program.2 (orWire + 1) (Fin.snoc refs orWire)).eval next = _
    rw [ih program.2 (orWire + 1) (Fin.snoc refs orWire) next hnextlen hnextbound, hvalues]
    rfl

lemma compile_circuitFun {n : Nat} (k : Nat) (program : Program n k)
    (input : Fin n → Bool) :
    circuitFun n (compile k program n Fin.val) input = evaluate k program input := by
  have h := compile_eval k program n Fin.val (List.ofFn input)
    (by simp) (fun i => i.isLt)
  simpa [circuitFun, List.getD_eq_getElem?_getD] using h

lemma compile_circuitFun_map {n m : Nat} (k : Nat) (program : Program n k)
    (refs : Fin n → Fin m) (input : Fin m → Bool) :
    circuitFun m (compile k program m (fun i => (refs i).val)) input =
      evaluate k program (fun i => input (refs i)) := by
  have h := compile_eval k program m (fun i => (refs i).val) (List.ofFn input)
    (by simp) (fun i => (refs i).isLt)
  simpa [circuitFun, List.getD_eq_getElem?_getD] using h

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

def conjunctionMasks {n : Nat} (truthMask : Nat) (values : Fin n → Nat)
    (xs : List (Fin n)) : Nat :=
  xs.foldr (fun i mask => values i &&& mask) truthMask

def evaluateMasks {n : Nat} : (k : Nat) → Program n k → Nat → (Fin n → Nat) → Nat
  | 0, output, truthMask, values => conjunctionMasks truthMask values output
  | k + 1, program, truthMask, values =>
      evaluateMasks k program.2 truthMask
        (Fin.snoc values
          (conjunctionMasks truthMask values program.1.1 |||
            conjunctionMasks truthMask values program.1.2))

lemma conjunctionMasks_testBit {n : Nat} (truthMask : Nat) (values : Fin n → Nat)
    (xs : List (Fin n)) (r : Nat) (htruth : truthMask.testBit r = true) :
    (conjunctionMasks truthMask values xs).testBit r = xs.all (fun i => (values i).testBit r) := by
  induction xs with
  | nil => simpa [conjunctionMasks] using htruth
  | cons i xs ih =>
    simpa only [conjunctionMasks, List.foldr_cons, Nat.testBit_land, List.all_cons] using
      congrArg (fun b => (values i).testBit r && b) ih

lemma evaluateMasks_testBit {n : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (values : Fin n → Nat) (r : Nat)
    (htruth : truthMask.testBit r = true) :
    (evaluateMasks k program truthMask values).testBit r =
      evaluate k program (fun i => (values i).testBit r) := by
  induction k generalizing n with
  | zero => exact conjunctionMasks_testBit truthMask values program r htruth
  | succ k ih =>
    simp only [evaluateMasks, evaluate]
    rw [ih]
    apply congrArg (evaluate k program.2)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Nat.testBit_lor,
        conjunctionMasks_testBit truthMask values _ r htruth]
    · simp only [Fin.snoc_castSucc]


def checkMasks {n : Nat} :
    (k : Nat) → Program n k → Nat → (Fin n → Nat) → List Nat → Nat → Bool
  | 0, output, truthMask, values, certificates, result =>
      certificates.isEmpty && (conjunctionMasks truthMask values output == result)
  | _ + 1, _, _, _, [], _ => false
  | k + 1, program, truthMask, values, expected :: certificates, result =>
      ((conjunctionMasks truthMask values program.1.1 |||
          conjunctionMasks truthMask values program.1.2) == expected) &&
        checkMasks k program.2 truthMask (Fin.snoc values expected) certificates result

lemma checkMasks_sound {n : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (values : Fin n → Nat) (certificates : List Nat) (result : Nat)
    (hcheck : checkMasks k program truthMask values certificates result = true) :
    evaluateMasks k program truthMask values = result := by
  induction k generalizing n certificates with
  | zero =>
    simp only [checkMasks, Bool.and_eq_true, beq_iff_eq] at hcheck
    exact hcheck.2
  | succ k ih =>
    cases certificates with
    | nil => simp [checkMasks] at hcheck
    | cons expected certificates =>
      simp only [checkMasks, Bool.and_eq_true, beq_iff_eq] at hcheck
      rw [evaluateMasks, hcheck.1]
      exact ih (program := program.2) (values := Fin.snoc values expected)
        (certificates := certificates) hcheck.2

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma compile_samples {n m : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (inputMasks : Fin n → Nat) (certificates : List Nat) (result : Nat)
    (samples : Fin m → Fin n → Bool)
    (htruth : ∀ r : Fin m, truthMask.testBit r.val = true)
    (hinputs : ∀ r : Fin m, ∀ i : Fin n, (inputMasks i).testBit r.val = samples r i)
    (hcheck : checkMasks k program truthMask inputMasks certificates result = true) :
    ∀ r : Fin m, circuitFun n (compile k program n Fin.val) (samples r) =
      result.testBit r.val := by
  intro r
  have hmask := checkMasks_sound k program truthMask inputMasks certificates result hcheck
  have hbit := congrArg (fun mask : Nat => mask.testBit r.val) hmask
  rw [evaluateMasks_testBit k program truthMask inputMasks r.val (htruth r)] at hbit
  have henv : (fun i => (inputMasks i).testBit r.val) = samples r := by
    funext i
    exact hinputs r i
  rw [henv] at hbit
  exact (compile_circuitFun k program (samples r)).trans hbit

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

