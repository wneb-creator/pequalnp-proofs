import CanonicalCompilerDefs

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
