import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

lemma monotone_context_is_bit {n : ℕ} (G : (Fin n → Bool) → Bool → Bool)
    (hG : Monotone (fun y : (Fin n → Bool) × Bool => G y.1 y.2))
    (lo : G (fun _ => false) true = true)
    (hi : G (fun _ => true) false = false) :
    ∀ (x : Fin n → Bool) (b : Bool), G x b = b := by
  intro x b
  cases b with
  | false =>
    have h := hG (show (x, false) ≤ ((fun _ => true), false) by
      constructor
      · intro i
        exact Bool.le_true _
      · exact le_rfl)
    change G x false ≤ G (fun _ => true) false at h
    rw [hi] at h
    exact le_antisymm h (Bool.false_le _)
  | true =>
    have h := hG (show ((fun _ => false), true) ≤ (x, true) by
      constructor
      · intro i
        exact Bool.false_le _
      · exact le_rfl)
    change G (fun _ => false) true ≤ G x true at h
    rw [lo] at h
    exact le_antisymm (Bool.le_true _) h

lemma double_negation_context {n : ℕ} (G : (Fin n → Bool) → Bool → Bool)
    (H : (Fin n → Bool) → Bool)
    (hG : Monotone (fun y : (Fin n → Bool) × Bool => G y.1 y.2))
    (lo : (!G (fun _ => false) (!H (fun _ => false))) = false)
    (hi : (!G (fun _ => true) (!H (fun _ => true))) = true) :
    ∀ x : Fin n → Bool, (!G x (!H x)) = H x := by
  have hlo : G (fun _ => false) true = true := by
    have h := hG (show ((fun _ => false), !H (fun _ => false)) ≤
        ((fun _ => false), true) by
      exact ⟨le_rfl, Bool.le_true _⟩)
    change G (fun _ => false) (!H (fun _ => false)) ≤ G (fun _ => false) true at h
    have hz : G (fun _ => false) (!H (fun _ => false)) = true := by simpa using lo
    rw [hz] at h
    exact le_antisymm (Bool.le_true _) h
  have hhi : G (fun _ => true) false = false := by
    have h := hG (show ((fun _ => true), false) ≤
        ((fun _ => true), !H (fun _ => true)) by
      exact ⟨le_rfl, Bool.false_le _⟩)
    change G (fun _ => true) false ≤ G (fun _ => true) (!H (fun _ => true)) at h
    have hz : G (fun _ => true) (!H (fun _ => true)) = false := by simpa using hi
    rw [hz] at h
    exact le_antisymm h (Bool.false_le _)
  intro x
  rw [monotone_context_is_bit G hG hlo hhi x (!H x)]
  simp

open PEqualNP.CircuitLowerBounds

def functionWires {α : Type} (gs : List Gate) (init : List (α → Bool)) : List (α → Bool) :=
  gs.foldl (fun w g => w ++ [fun x =>
    g.op.eval (g.inputs.map fun i => w.getD i (fun _ => false) x)]) init

lemma monotone_getD {α : Type} [Preorder α] (fs : List (α → Bool))
    (hfs : ∀ f ∈ fs, Monotone f) (i : ℕ) : Monotone (fs.getD i (fun _ => false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : fs[i]? with
  | none => simp [Monotone]
  | some f =>
    simp only [Option.getD_some]
    exact hfs f (List.mem_of_getElem? h)

lemma monotone_gate {α : Type} [Preorder α] (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (fs : List (α → Bool)) (hfs : ∀ f ∈ fs, Monotone f) :
    Monotone (fun x => g.op.eval (g.inputs.map fun i => fs.getD i (fun _ => false) x)) := by
  intro x y hxy
  rw [Bool.le_iff_imp]
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro hx i hi
    exact Bool.le_iff_imp.mp (monotone_getD fs hfs i hxy) (hx i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, Bool.le_iff_imp.mp (monotone_getD fs hfs i hxy) hx⟩

lemma monotone_functionWires {α : Type} [Preorder α] (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (init : List (α → Bool)) (hinit : ∀ f ∈ init, Monotone f) :
    ∀ f ∈ functionWires gs init, Monotone f := by
  induction gs generalizing init with
  | nil => exact hinit
  | cons g gs ih =>
    apply ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hinit f hf
    · obtain rfl := List.mem_singleton.mp hf
      exact monotone_gate g (hgs g List.mem_cons_self) init hinit

lemma functionWires_eval {α : Type} (gs : List Gate) (init : List (α → Bool)) (x : α) :
    (functionWires gs init).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (init.map fun f => f x) := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [functionWires, List.foldl_cons] at *
    rw [ih]
    congr 1
    simp only [List.map_append, List.map_singleton]
    congr 2
    congr 1
    apply List.map_congr_left
    intro i hi
    exact (List.getD_map (l := init) (d := fun _ => false) (n := i) (fun f => f x)).symm

lemma fold_wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma not_read (w : List Bool) (ins : List ℕ) :
    GateOp.not.eval (ins.map fun i => w.getD i false) = !(w.getD (ins.headD w.length) false) := by
  cases ins with
  | nil => simp [GateOp.eval]
  | cons i is => rfl

lemma not_output_eval (gs : List Gate) (ins : List ℕ) (x : List Bool) :
    Circuit.eval ⟨gs ++ [⟨GateOp.not, ins⟩], x.length + gs.length⟩ x =
      !(Circuit.eval ⟨gs, ins.headD (x.length + gs.length)⟩ x) := by
  let w := Circuit.wires ⟨gs, 0⟩ x
  have hl : w.length = x.length + gs.length := fold_wires_length gs x
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (w ++ [GateOp.not.eval (ins.map fun i => w.getD i false)]).getD
    (x.length + gs.length) false = !(w.getD (ins.headD (x.length + gs.length)) false)
  rw [← hl]
  simpa [List.getD_eq_getElem?_getD] using not_read w ins

lemma two_not_output_redundant (n : ℕ) (pre mid : List Gate) (a b : List ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hmid : ∀ g ∈ mid, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lo : Circuit.eval ⟨pre ++ ⟨GateOp.not, a⟩ :: mid ++ [⟨GateOp.not, b⟩],
      n + pre.length + mid.length + 1⟩ (List.ofFn (fun _ : Fin n => false)) = false)
    (hi : Circuit.eval ⟨pre ++ ⟨GateOp.not, a⟩ :: mid ++ [⟨GateOp.not, b⟩],
      n + pre.length + mid.length + 1⟩ (List.ofFn (fun _ : Fin n => true)) = true) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, a⟩ :: mid ++ [⟨GateOp.not, b⟩],
        n + pre.length + mid.length + 1⟩ (List.ofFn x) =
      Circuit.eval ⟨pre, a.headD (n + pre.length)⟩ (List.ofFn x) := by
  let inputs : List (((Fin n → Bool) × Bool) → Bool) :=
    List.ofFn (fun i : Fin n => fun y => y.1 i)
  let pf := functionWires pre inputs
  let mf := functionWires mid (pf ++ [fun y => y.2])
  let idx := b.headD (n + pre.length + mid.length + 1)
  let G (x : Fin n → Bool) (z : Bool) := mf.getD idx (fun _ => false) (x,z)
  let H (x : Fin n → Bool) := Circuit.eval ⟨pre, a.headD (n + pre.length)⟩ (List.ofFn x)
  have hpmono : ∀ f ∈ pf, Monotone f := by
    apply monotone_functionWires pre hpre
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact fun x y hxy => hxy.1 i
  have hmmono : ∀ f ∈ mf, Monotone f := by
    apply monotone_functionWires mid hmid
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hpmono f hf
    · obtain rfl := List.mem_singleton.mp hf
      exact fun x y hxy => hxy.2
  have gmono : Monotone (fun y : (Fin n → Bool) × Bool => G y.1 y.2) :=
    monotone_getD mf hmmono idx
  have pbridge (x : Fin n → Bool) (z : Bool) :
      pf.map (fun f => f (x,z)) = Circuit.wires ⟨pre, 0⟩ (List.ofFn x) := by
    rw [show pf = functionWires pre inputs from rfl, functionWires_eval]
    simp only [inputs, List.map_ofFn, Circuit.wires, Function.comp_def]
  have mbridge (x : Fin n → Bool) (z : Bool) :
      mf.map (fun f => f (x,z)) =
        Circuit.wires ⟨mid,0⟩ (Circuit.wires ⟨pre,0⟩ (List.ofFn x) ++ [z]) := by
    rw [show mf = functionWires mid (pf ++ [fun y => y.2]) from rfl,
      functionWires_eval, List.map_append, List.map_singleton, pbridge]
    rfl
  have gb (x : Fin n → Bool) (z : Bool) : G x z =
      (Circuit.wires ⟨mid,0⟩ (Circuit.wires ⟨pre,0⟩ (List.ofFn x) ++ [z])).getD idx false := by
    rw [← mbridge]
    exact (List.getD_map (l := mf) (d := fun _ => false) (n := idx) (fun f => f (x,z))).symm
  have factor (x : Fin n → Bool) :
      Circuit.eval ⟨pre ++ ⟨GateOp.not, a⟩ :: mid ++ [⟨GateOp.not, b⟩],
        n + pre.length + mid.length + 1⟩ (List.ofFn x) = !G x (!H x) := by
    have hlen : (List.ofFn x).length + (pre ++ (⟨GateOp.not,a⟩ : Gate) :: mid).length =
        n + pre.length + mid.length + 1 := by simp; omega
    rw [← hlen, not_output_eval]
    rw [hlen]
    rw [gb]
    congr 1
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
    congr 2
    congr 1
    have len : (Circuit.wires ⟨pre,0⟩ (List.ofFn x)).length = n + pre.length := by
      simpa [Circuit.wires] using fold_wires_length pre (List.ofFn x)
    rw [not_read]
    simp only [fold_wires_length, List.length_ofFn]
    rfl
  have collapse := double_negation_context G H gmono
    ((factor (fun _ => false)).symm.trans lo) ((factor (fun _ => true)).symm.trans hi)
  intro x
  exact (factor x).trans (collapse x)

end PEqualNP.Outside.L_meta_2592
