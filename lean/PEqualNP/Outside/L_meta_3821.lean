import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i n)⟩

def capGates (n : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => capGate n g :: capGates (n + 1) gs

def capCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨capGates n C.gates, min C.output (n + C.gates.length)⟩

lemma getD_min_length (w : List Bool) (i : ℕ) :
    w.getD (min i w.length) false = w.getD i false := by
  by_cases h : i < w.length
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (Nat.le_of_not_gt h)]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma capGate_eval (w : List Bool) (g : Gate) :
    (capGate w.length g).op.eval
      ((capGate w.length g).inputs.map (fun i => w.getD i false)) =
    g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [capGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact getD_min_length w i

lemma capGates_length (n : ℕ) (gs : List Gate) :
    (capGates n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp only [capGates, List.length_cons, ih]

lemma capGates_wires (gs : List Gate) (w : List Bool) :
    (capGates w.length gs).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [capGates, List.foldl_cons, capGate_eval]
    have hn : (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).length =
        w.length + 1 := by simp
    rw [← hn]
    exact ih _

lemma capCircuit_wires (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (capCircuit n C).wires x = C.wires x := by
  subst n
  exact capGates_wires C.gates x

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨gs, o⟩ := C
  unfold Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma capCircuit_eval (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (capCircuit n C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [capCircuit_wires n C x hx]
  change (C.wires x).getD (min C.output (n + C.gates.length)) false =
    (C.wires x).getD C.output false
  rw [← hx, ← wires_length]
  exact getD_min_length _ _

lemma capCircuit_size (n : ℕ) (C : Circuit) :
    (capCircuit n C).size = C.size :=
  capGates_length n C.gates

lemma capGates_legal (n : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ capGates n gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [capGates]
  | cons g gs ih =>
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · simpa [capGate] using h g List.mem_cons_self
    · exact ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) g' hg'

lemma capCircuit_legal (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (capCircuit n C) :=
  capGates_legal n C.gates h

lemma capGates_inputs_bound (n : ℕ) (gs : List Gate) :
    ∀ g ∈ capGates n gs, ∀ i ∈ g.inputs, i ≤ n + gs.length := by
  induction gs generalizing n with
  | nil => simp [capGates]
  | cons g gs ih =>
    intro g' hg' i hi
    rcases List.mem_cons.mp hg' with rfl | hg'
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      have := Nat.min_le_right j n
      simp only [List.length_cons]
      omega
    · have := ih (n + 1) g' hg' i hi
      simp only [List.length_cons]
      omega

lemma capCircuit_bounded (n s : ℕ) (C : Circuit) (h : C.size ≤ s) :
    (capCircuit n C).output ≤ n + s ∧
    ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + s := by
  have hs : C.gates.length ≤ s := h
  constructor
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left hs n)
  · intro g hg i hi
    exact le_trans (capGates_inputs_bound n C.gates g hg i hi)
      (Nat.add_le_add_left hs n)

lemma capCircuit_read (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (i : ℕ) :
    ((capCircuit n C).wires x).getD (min i (n + C.size)) false =
      (C.wires x).getD i false := by
  rw [capCircuit_wires n C x hx]
  change (C.wires x).getD (min i (n + C.gates.length)) false = _
  rw [← hx, ← wires_length]
  exact getD_min_length _ _

lemma bounded_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s) :
    ∃ (D : Circuit) (a' b' : ℕ),
      FanInTwo D ∧ D.size = C.size ∧ D.output ≤ n + s ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
      a' ≤ n + s ∧ b' ≤ n + s ∧
      ∀ x : List Bool, x.length = n →
        (D.wires x).getD a' false = (C.wires x).getD a false ∧
        (D.wires x).getD b' false = (C.wires x).getD b false := by
  refine ⟨capCircuit n C, min a (n + C.size), min b (n + C.size),
    capCircuit_legal n C legal, capCircuit_size n C,
    (capCircuit_bounded n s C budget).1, (capCircuit_bounded n s C budget).2,
    ?_, ?_, ?_⟩
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
  · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
  · intro x hx
    exact ⟨capCircuit_read n C x hx a, capCircuit_read n C x hx b⟩

def gateChoices (bound : ℕ) : List Gate :=
  [GateOp.and, GateOp.or, GateOp.not].flatMap fun op =>
    ⟨op, []⟩ :: ((List.range (bound + 1)).map (fun a => ⟨op, [a]⟩) ++
      (List.range (bound + 1)).flatMap fun a =>
        (List.range (bound + 1)).map (fun b => ⟨op, [a, b]⟩))

lemma mem_gateChoices (bound : ℕ) (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) (bounded : ∀ i ∈ g.inputs, i ≤ bound) :
    g ∈ gateChoices bound := by
  obtain ⟨op, inputs⟩ := g
  have hop : op ∈ [GateOp.and, GateOp.or, GateOp.not] := by
    simpa using legal
  simp only [gateChoices, List.mem_flatMap]
  refine ⟨op, hop, ?_⟩
  match inputs with
  | [] => exact List.mem_cons_self
  | [a] =>
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨a, List.mem_range.mpr (by have := bounded a (by simp); omega), rfl⟩
  | [a, b] =>
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_range.mpr (by have := bounded a (by simp); omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨b, List.mem_range.mpr (by have := bounded b (by simp); omega), rfl⟩
  | a :: b :: c :: rest => simp only [List.length_cons] at arity; omega

lemma gateChoices_length (bound : ℕ) :
    (gateChoices bound).length = 3 * (1 + (bound + 1) + (bound + 1) ^ 2) := by
  simp [gateChoices, List.length_flatMap, pow_two, Nat.mul_add, Nat.add_mul]
  omega

def padCircuit (s : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ List.replicate (s - C.size) ⟨GateOp.or, []⟩, C.output⟩

lemma fold_padding (k : ℕ) (w : List Bool) :
    (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
      w ++ List.replicate k false := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    change (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
      (w ++ [false]) = _
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]

lemma padCircuit_wires (s : ℕ) (C : Circuit) (x : List Bool) :
    (padCircuit s C).wires x = C.wires x ++ List.replicate (s - C.size) false := by
  unfold Circuit.wires padCircuit
  rw [List.foldl_append, fold_padding]

lemma getD_append_false (w : List Bool) (k i : ℕ) :
    (w ++ List.replicate k false).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_eq_default w false (by omega : w.length ≤ i)]
    simp [List.getD_eq_getElem?_getD]

lemma padCircuit_read (s : ℕ) (C : Circuit) (x : List Bool) (i : ℕ) :
    ((padCircuit s C).wires x).getD i false = (C.wires x).getD i false := by
  rw [padCircuit_wires]
  exact getD_append_false _ _ _

lemma padCircuit_size (s : ℕ) (C : Circuit) (h : C.size ≤ s) :
    (padCircuit s C).size = s := by
  have : C.gates.length ≤ s := h
  simp only [padCircuit, Circuit.size, List.length_append, List.length_replicate]
  omega

lemma padCircuit_legal (s : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (padCircuit s C) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · have heq := (List.mem_replicate.mp hg).2
    subst g
    simp

lemma fixed_bounded_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s) :
    ∃ (D : Circuit) (a' b' : ℕ),
      FanInTwo D ∧ D.size = s ∧ D.output ≤ n + s ∧
      (∀ g ∈ D.gates, g ∈ gateChoices (n + s)) ∧
      a' ≤ n + s ∧ b' ≤ n + s ∧
      ∀ x : List Bool, x.length = n →
        (D.wires x).getD a' false = (C.wires x).getD a false ∧
        (D.wires x).getD b' false = (C.wires x).getD b false := by
  have hsize := padCircuit_size s C budget
  obtain ⟨D, a', b', hD, hlen, hout, hbound, ha, hb, heval⟩ :=
    bounded_pair n s (padCircuit s C) a b (padCircuit_legal s C legal) (by omega)
  refine ⟨D, a', b', hD, hlen.trans hsize, hout, ?_, ha, hb, ?_⟩
  · intro g hg
    exact mem_gateChoices (n + s) g (hD g hg).1 (hD g hg).2 (hbound g hg)
  · intro x hx
    exact ⟨((heval x hx).1).trans (padCircuit_read s C x a),
      ((heval x hx).2).trans (padCircuit_read s C x b)⟩

lemma gateChoices_inputs_bound (bound : ℕ) (g : Gate) (hg : g ∈ gateChoices bound) :
    ∀ i ∈ g.inputs, i ≤ bound := by
  obtain ⟨op, _, hg⟩ := List.mem_flatMap.mp hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      intro i hi
      have hi' : i = a := List.mem_singleton.mp hi
      subst i
      have := List.mem_range.mp ha
      omega
    · obtain ⟨a, ha, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      intro i hi
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have hi' : i = b := List.mem_singleton.mp hi
        omega

lemma wire_true_lt (n : ℕ) (C : Circuit) (i : ℕ)
    (h : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false = true) :
    i < n + C.size := by
  obtain ⟨x, hx⟩ := h
  by_contra hi
  have hlen : (C.wires (List.ofFn x)).length ≤ i := by
    rw [wires_length, List.length_ofFn]
    change n + C.size ≤ i
    omega
  rw [List.getD_eq_default _ _ hlen] at hx
  contradiction

lemma finite_source_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
    (budget : C.size ≤ s)
    (ha : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD a false = true)
    (hb : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD b false = true) :
    ∃ (D : Circuit) (a' b' : Fin (n + s)),
      D.output = 0 ∧ FanInTwo D ∧ D.size = s ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
      ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD a'.val false =
          (C.wires (List.ofFn x)).getD a false ∧
        (D.wires (List.ofFn x)).getD b'.val false =
          (C.wires (List.ofFn x)).getD b false := by
  obtain ⟨D, a', b', hD, hsize, _, hchoices, _, _, heval⟩ :=
    fixed_bounded_pair n s C a b legal budget
  have ha' : a' < n + s := by
    rw [← hsize]
    apply wire_true_lt
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, ((heval _ (by simp)).1).trans hx⟩
  have hb' : b' < n + s := by
    rw [← hsize]
    apply wire_true_lt
    obtain ⟨x, hx⟩ := hb
    exact ⟨x, ((heval _ (by simp)).2).trans hx⟩
  refine ⟨⟨D.gates, 0⟩, ⟨a', ha'⟩, ⟨b', hb'⟩, rfl, hD, hsize, ?_, ?_⟩
  · intro g hg
    exact gateChoices_inputs_bound (n + s) g (hchoices g hg)
  · intro x
    exact heval _ (by simp)

end PEqualNP.Outside.L_meta_3821_aux
