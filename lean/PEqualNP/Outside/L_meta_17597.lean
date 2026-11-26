import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_17597_aux

section SourceLinearTranspose

namespace PlaneArcTranspose

inductive LinearOp where
  | add (u v : ℕ)
  | scale (u scalar : ℕ)
  | copy (u : ℕ)
  | zero

def LinearOp.edge (op : LinearOp) (scalar : ℕ → Prop) (src : ℕ) : Prop :=
  match op with
  | .add u v => src = u ∨ src = v
  | .scale u s => src = u ∧ scalar s
  | .copy u => src = u
  | .zero => False

def LinearOp.eval (op : LinearOp) (scalar state : ℕ → Prop) : Prop :=
  match op with
  | .add u v => state u ∨ state v
  | .scale u s => state u ∧ scalar s
  | .copy u => state u
  | .zero => False

theorem eval_iff_edge (op : LinearOp) (scalar state : ℕ → Prop) :
    op.eval scalar state ↔ ∃ src, op.edge scalar src ∧ state src := by
  cases op with
  | add u v =>
    simp only [LinearOp.eval, LinearOp.edge]
    constructor
    · rintro (h | h)
      · exact ⟨u, Or.inl rfl, h⟩
      · exact ⟨v, Or.inr rfl, h⟩
    · rintro ⟨j, (rfl | rfl), hj⟩
      · exact Or.inl hj
      · exact Or.inr hj
  | scale u s => simp [LinearOp.eval, LinearOp.edge, and_assoc, and_comm]
  | copy u => simp [LinearOp.eval, LinearOp.edge]
  | zero => simp [LinearOp.eval, LinearOp.edge]

structure Assignment where
  dst : ℕ
  op : LinearOp

def Assignment.push (a : Assignment) (scalar state : ℕ → Prop) (w : ℕ) : Prop :=
  if w = a.dst then a.op.eval scalar state else state w

def Assignment.pull (a : Assignment) (scalar demand : ℕ → Prop) (w : ℕ) : Prop :=
  (w ≠ a.dst ∧ demand w) ∨ (demand a.dst ∧ a.op.edge scalar w)

def forward (scalar : ℕ → Prop) (ops : List Assignment) (state : ℕ → Prop) : ℕ → Prop :=
  ops.foldl (fun st a => a.push scalar st) state

def reverse (scalar : ℕ → Prop) (ops : List Assignment) (demand : ℕ → Prop) : ℕ → Prop :=
  ops.foldr (fun a st => a.pull scalar st) demand

theorem transpose_step (a : Assignment) (scalar state demand : ℕ → Prop) :
    (∃ w, demand w ∧ a.push scalar state w) ↔ (∃ w, a.pull scalar demand w ∧ state w) := by
  constructor
  · rintro ⟨w, hd, hv⟩
    by_cases h : w = a.dst
    · subst w
      obtain ⟨src, he, hs⟩ := (eval_iff_edge _ _ _).mp
        (show a.op.eval scalar state from by simpa [Assignment.push] using hv)
      exact ⟨src, Or.inr ⟨hd, he⟩, hs⟩
    · exact ⟨w, Or.inl ⟨h, hd⟩, by simpa [Assignment.push, h] using hv⟩
  · rintro ⟨w, (⟨hne, hd⟩ | ⟨hd, he⟩), hs⟩
    · exact ⟨w, hd, by simpa [Assignment.push, hne] using hs⟩
    · exact ⟨a.dst, hd, by simpa [Assignment.push] using
        (eval_iff_edge a.op scalar state).mpr ⟨w, he, hs⟩⟩

theorem transpose (ops : List Assignment) (scalar state demand : ℕ → Prop) :
    (∃ w, demand w ∧ forward scalar ops state w) ↔
      (∃ w, reverse scalar ops demand w ∧ state w) := by
  induction ops generalizing state with
  | nil => rfl
  | cons a ops ih =>
    change (∃ w, demand w ∧ forward scalar ops (a.push scalar state) w) ↔
        ∃ w, a.pull scalar (reverse scalar ops demand) w ∧ state w
    exact (ih _).trans (transpose_step a _ _ _)

theorem transpose_coefficient (ops : List Assignment) (scalar : ℕ → Prop) (src dst : ℕ) :
    forward scalar ops (fun w => w = src) dst ↔ reverse scalar ops (fun w => w = dst) src := by
  simpa using transpose ops scalar (fun w => w = src) (fun w => w = dst)

theorem reverse_adds {ι : Type*} (V : Finset ι) (uses : ι → ℕ)
    (inputs adds scales aliases : ℕ)
    (live : ∀ v ∈ V, 1 ≤ uses v)
    (vertices : V.card = inputs + adds + scales + aliases)
    (edges : ∑ v ∈ V, uses v = 2 * adds + scales + aliases + 1) :
    (∑ v ∈ V, (uses v - 1)) + inputs = adds + 1 := by
  have h : ∑ v ∈ V, ((uses v - 1) + 1) = ∑ v ∈ V, uses v :=
    Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (live v hv))
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  omega

end PlaneArcTranspose

end SourceLinearTranspose

namespace CircuitNormalization

namespace Deg2

open PEqualNP.CircuitLowerBounds

inductive G where
  | and (a b : ℕ)
  | or (a b : ℕ)
  | cst (v : Bool)
  deriving DecidableEq, Repr

def G.kids : G → List ℕ
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .cst _ => []

structure Dag (N : ℕ) where

  gates : List G

  out : ℕ

namespace Dag

variable {N : ℕ}

def size (D : Dag N) : ℕ := D.gates.length

def gateAt (D : Dag N) (i : ℕ) : Option G :=
  if N + N ≤ i then D.gates[i - (N + N)]? else none

def val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) : Bool :=
  if h : i < N + N then x ⟨i, h⟩ else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.val x a else false) && (if _ : b < i then D.val x b else false)
  | some (.or a b) =>
      (if _ : a < i then D.val x a else false) || (if _ : b < i then D.val x b else false)
  | some (.cst v) => v
  | none => false
termination_by i

def deg (D : Dag N) (i : ℕ) : ℕ :=
  if i < N + N then (if N ≤ i then 1 else 0) else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.deg a else 0) + (if _ : b < i then D.deg b else 0)
  | some (.or a b) =>
      max (if _ : a < i then D.deg a else 0) (if _ : b < i then D.deg b else 0)
  | some (.cst _) => 0
  | none => 0
termination_by i

def WF (D : Dag N) : Prop := ∀ i g, D.gateAt i = some g → ∀ c ∈ g.kids, c < i

end Dag

def trGate (i : ℕ) (g : Gate) : G :=
  match g.op, g.inputs with
  | .and, [] => .cst true
  | .or, [] => .cst false
  | .and, [a] => if a < i then .or a a else .cst false
  | .or, [a] => if a < i then .or a a else .cst false
  | .and, [a, b] => if a < i ∧ b < i then .and a b else .cst false
  | .or, [a, b] =>
      if a < i ∧ b < i then .or a b else if a < i then .or a a
      else if b < i then .or b b else .cst false
  | _, _ => .cst false

def ofCircuit (N : ℕ) (C : Circuit) : Dag N :=
  { gates := C.gates.mapIdx (fun j g => trGate (N + N + j) g), out := C.output }

def lineMarks (N : ℕ) : Finset ℕ := Finset.Ico N (N + N)

end Deg2

namespace Deg2.Api

open PEqualNP.CircuitLowerBounds

variable {N : ℕ}

theorem gateAt_some {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ D.gates[i - (N + N)]? = some g := by
  unfold Dag.gateAt at h
  split_ifs at h with hi
  exact ⟨hi, h⟩

theorem card03a_size (C : Circuit) : (ofCircuit N C).size = C.size := by
  simp [Dag.size, ofCircuit, Circuit.size]

theorem trGate_kids (i : ℕ) (g : Gate) : ∀ c ∈ (trGate i g).kids, c < i := by
  intro c hc
  unfold trGate at hc
  split at hc <;> (try split_ifs at hc) <;> simp_all [G.kids] <;> omega

theorem card03b_wf (C : Circuit) : (ofCircuit N C).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg⟩ := gateAt_some hg
  simp only [ofCircuit, List.getElem?_mapIdx] at hg
  cases h : C.gates[i - (N + N)]? with
  | none => rw [h] at hg; cases hg
  | some g0 =>
    rw [h] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    subst hg
    have := trGate_kids _ g0 c hc
    omega

end Deg2.Api

namespace LineDegTest

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Dg (gs : List Gate) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem Dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ [g]) n marked = Dg gs n marked ++ [g.lineDegree (Dg gs n marked)] := by
  simp [Dg, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem Dg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Dg gs n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton gs g ih => rw [Dg_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

end LineDegTest

namespace Deg2.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

theorem api_prefix (D D' : Dag N) (h : D.gates <+: D'.gates) (i : ℕ) (hi : i < N + N + D.size)
    (x : Fin (N + N) → Bool) : D'.val x i = D.val x i ∧ D'.deg i = D.deg i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hv : ∀ a, (if _ : a < i then D'.val x a else false) =
        (if _ : a < i then D.val x a else false) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).1
      · rfl
    have hd : ∀ a, (if _ : a < i then D'.deg a else 0) = (if _ : a < i then D.deg a else 0) := by
      intro a
      split_ifs with ha
      · exact (ih a ha (by omega)).2
      · rfl
    have hg : ¬ i < N + N → D'.gates[i - (N + N)]? = D.gates[i - (N + N)]? := by
      intro h0
      obtain ⟨t, ht⟩ := h
      rw [← ht, List.getElem?_append_left (by unfold Dag.size at hi; omega)]
    constructor
    · conv_lhs => rw [Dag.val]
      conv_rhs => rw [Dag.val]
      split_ifs with h0
      · rfl
      · rw [hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hv a, hv b]
          | or a b => dsimp only; rw [hv a, hv b]
          | cst v => rfl
    · conv_lhs => rw [Dag.deg]
      conv_rhs => rw [Dag.deg]
      by_cases h0 : i < N + N
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hg h0]
        cases D.gates[i - (N + N)]? with
        | none => rfl
        | some g =>
          cases g with
          | and a b => dsimp only; rw [hd a, hd b]
          | or a b => dsimp only; rw [hd a, hd b]
          | cst v => rfl

def gval (r : ℕ → Bool) : G → Bool
  | .and a b => r a && r b
  | .or a b => r a || r b
  | .cst v => v

def gdeg (r : ℕ → ℕ) : G → ℕ
  | .and a b => r a + r b
  | .or a b => max (r a) (r b)
  | .cst _ => 0

theorem val_deg_ge (D : Dag N) {i : ℕ} (hi : N + N + D.size ≤ i) (x : Fin (N + N) → Bool) :
    D.val x i = false ∧ D.deg i = 0 := by
  have hn : D.gates[i - (N + N)]? = none := by
    rw [List.getElem?_eq_none]; unfold Dag.size at hi; omega
  constructor
  · rw [Dag.val, dif_neg (by omega), hn]
  · rw [Dag.deg, if_neg (by omega), hn]

theorem top_snoc (D D' : Dag N) (g : G) (h : D'.gates = D.gates ++ [g]) (x : Fin (N + N) → Bool) :
    D'.val x (N + N + D.size) =
        gval (fun a => if _ : a < N + N + D.size then D.val x a else false) g ∧
      D'.deg (N + N + D.size) = gdeg (fun a => if _ : a < N + N + D.size then D.deg a else 0) g := by
  have hp : D.gates <+: D'.gates := h ▸ List.prefix_append _ _
  have hv : ∀ a, (if _ : a < N + N + D.size then D'.val x a else false) =
      (if _ : a < N + N + D.size then D.val x a else false) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).1
    · rfl
  have hd : ∀ a, (if _ : a < N + N + D.size then D'.deg a else 0) =
      (if _ : a < N + N + D.size then D.deg a else 0) := by
    intro a
    split_ifs with ha
    · exact (api_prefix D D' hp a ha x).2
    · rfl
  have hg : D'.gates[N + N + D.size - (N + N)]? = some g := by
    rw [h, Nat.add_sub_cancel_left, List.getElem?_append_right (by unfold Dag.size; omega)]
    simp [Dag.size]
  constructor
  · rw [Dag.val, dif_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hv a, hv b]; rfl
    | or a b => dsimp only; rw [hv a, hv b]; rfl
    | cst v => rfl
  · rw [Dag.deg, if_neg (by omega), hg]
    cases g with
    | and a b => dsimp only; rw [hd a, hd b]; rfl
    | or a b => dsimp only; rw [hd a, hd b]; rfl
    | cst v => rfl

theorem getD_ge_false {l : List Bool} {k : ℕ} (h : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_ge_zero {l : List ℕ} {k : ℕ} (h : l.length ≤ k) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem trGate_val (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (r : ℕ → Bool) (hr : ∀ k, i ≤ k → r k = false) :
    gval r (trGate i g) = g.op.eval (g.inputs.map r) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gval, GateOp.eval]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;>
      (split_ifs with ha
       · simp [gval, GateOp.eval]
       · simp [gval, GateOp.eval, hr a (by omega)])
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp only [gval, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.any_cons,
        List.all_nil, List.any_nil, id, Bool.and_true, Bool.or_false]
    · by_cases ha : a < i
      · rw [hr b (by omega), Bool.and_false]
      · rw [hr a (by omega), Bool.false_and]
    · rw [hr b (by omega), Bool.or_false, Bool.or_self]
    · rw [hr a (by omega), Bool.false_or, Bool.or_self]
    · rw [hr a (by omega), hr b (by omega), Bool.or_false]
  · simp at hl

theorem gdeg_mono {r r' : ℕ → ℕ} (h : ∀ k, r k ≤ r' k) (g : G) : gdeg r g ≤ gdeg r' g := by
  cases g with
  | and a b => exact Nat.add_le_add (h a) (h b)
  | or a b => exact max_le_max (h a) (h b)
  | cst v => exact le_rfl

theorem trGate_deg (i : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (d : List ℕ) : gdeg (fun k => d.getD k 0) (trGate i g) ≤ g.lineDegree d := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [trGate, gdeg]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with ha <;>
      simp [gdeg, Gate.lineDegree]
  · rcases hop with rfl | rfl <;> simp only [trGate] <;> split_ifs with h1 h2 h3 <;>
      simp [gdeg, Gate.lineDegree]
  · simp at hl

open LineDegTest in

theorem card03c_val (C : Circuit) (hC : Monotone2 C) (x : Fin (N + N) → Bool) (i : ℕ) :
    (ofCircuit N C).val x i = (C.wires (List.ofFn x)).getD i false := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ = (List.ofFn x).getD i false
    rw [ofFn_getD, Dag.val]
    split_ifs with h
    · rfl
    · simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (W gs (List.ofFn x)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [W_length, hsz]; simp
    change _ = (W (gs ++ [g]) (List.ofFn x)).getD i false
    rw [W_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h x).1]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates x).1]
      have hr : (fun a => if _ : a < N + N + (ofCircuit N ⟨gs, o⟩).size then
          (ofCircuit N ⟨gs, o⟩).val x a else false) = fun a => (W gs (List.ofFn x)).getD a false := by
        funext a
        split_ifs with ha
        · exact ih a
        · exact (getD_ge_false (by omega)).symm
      rw [hr]
      exact trGate_val _ g hgC _ (fun k hk => getD_ge_false (by omega))
    · rw [if_neg (by omega), if_neg (by omega)]
      refine (val_deg_ge _ ?_ x).1
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

open LineDegTest in

theorem card03d_deg (C : Circuit) (hC : Monotone2 C) (i : ℕ) :
    (ofCircuit N C).deg i ≤ (C.lineDegrees (N + N) (lineMarks N)).getD i 0 := by
  obtain ⟨gs, o⟩ := C
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change _ ≤ (Dg [] (N + N) (lineMarks N)).getD i 0
    rw [Dag.deg]
    by_cases h : i < N + N
    · rw [if_pos h]
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, lineMarks]
    · rw [if_neg h]
      simp [ofCircuit]
  | append_singleton gs g ih =>
    have ih := fun k => ih k (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hgC := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    have hsz : (ofCircuit N ⟨gs, o⟩).size = gs.length := by simp [ofCircuit, Dag.size]
    have hgates : (ofCircuit N ⟨gs ++ [g], o⟩).gates =
        (ofCircuit N ⟨gs, o⟩).gates ++ [trGate (N + N + (ofCircuit N ⟨gs, o⟩).size) g] := by
      rw [hsz]; simp [ofCircuit, List.mapIdx_concat]
    have hlen : (Dg gs (N + N) (lineMarks N)).length = N + N + (ofCircuit N ⟨gs, o⟩).size := by
      rw [Dg_length, hsz]
    change _ ≤ (Dg (gs ++ [g]) (N + N) (lineMarks N)).getD i 0
    rw [Dg_snoc, getD_snoc, hlen]
    rcases lt_trichotomy i (N + N + (ofCircuit N ⟨gs, o⟩).size) with h | rfl | h
    · rw [if_pos h, (api_prefix _ _ (hgates ▸ List.prefix_append _ _) i h (fun _ => false)).2]
      exact ih i
    · rw [if_neg (lt_irrefl _), if_pos rfl, (top_snoc _ _ _ hgates (fun _ => false)).2]
      refine le_trans (gdeg_mono (r' := fun k => (Dg gs (N + N) (lineMarks N)).getD k 0) ?_ _)
        (trGate_deg _ g hgC _)
      intro a
      split_ifs with ha
      · exact ih a
      · exact Nat.zero_le _
    · rw [(val_deg_ge _ ?_ (fun _ => false)).2]
      · exact Nat.zero_le _
      unfold Dag.size; rw [hgates]; simp only [List.length_append, List.length_singleton]
      unfold Dag.size at h; omega

end Deg2.Bridge

namespace Deg2

variable {N : ℕ}

theorem circ_val_input (D : Dag N) (x : Fin (N + N) → Bool) {i : ℕ} (hi : i < N + N) :
    D.val x i = x ⟨i, hi⟩ := by
  rw [Dag.val, dif_pos hi]

theorem circ_deg_input (D : Dag N) {i : ℕ} (hi : i < N + N) :
    D.deg i = if N ≤ i then 1 else 0 := by
  rw [Dag.deg, if_pos hi]

end Deg2

namespace Deg2.Forms

variable {N : ℕ}

theorem val_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a && D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem val_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) (x : Fin (N + N) → Bool) : D.val x i = (D.val x a || D.val x b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.val, dif_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem deg_and {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.and a b)) (ha : a < i)
    (hb : b < i) : D.deg i = D.deg a + D.deg b := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

theorem deg_or {D : Dag N} {i a b : ℕ} (hg : D.gateAt i = some (.or a b)) (ha : a < i)
    (hb : b < i) : D.deg i = max (D.deg a) (D.deg b) := by
  obtain ⟨hi, hg⟩ := Api.gateAt_some hg
  rw [Dag.deg, if_neg (by omega), hg]
  simp only [dif_pos ha, dif_pos hb]

end Deg2.Forms

end CircuitNormalization

section SourceNormalizedCompile

namespace PlaneArcTranspose

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.CircuitNormalization.Deg2

def codeGate (degree : ℕ → ℕ) : G → LinearOp
  | .cst _ => .zero
  | .and a b =>
    if degree a = 0 then
      if degree b = 0 then .zero else .scale b a
    else if degree b = 0 then .scale a b else .zero
  | .or a b =>
    if degree a = 0 then
      if degree b = 0 then .zero else .copy b
    else if degree b = 0 then .copy a else .add a b

def codeAt {N : ℕ} (D : Dag N) (w : ℕ) : LinearOp :=
  match D.gateAt w with
  | some gate => codeGate D.deg gate
  | none => .zero

def compilePrefix {N : ℕ} (D : Dag N) : ℕ → List Assignment
  | 0 => []
  | t+1 => compilePrefix D t ++ [⟨N+N+t, codeAt D (N+N+t)⟩]

def compile {N : ℕ} (D : Dag N) := compilePrefix D D.size

def zeroLines {N : ℕ} (x : Fin (N+N) → Bool) (p : Fin (N+N)) : Bool :=
  if p.val < N then x p else false

def activeLines {N : ℕ} (x : Fin (N+N) → Bool) (w : ℕ) : Prop :=
  ∃ h : w < N+N, N ≤ w ∧ x ⟨w,h⟩ = true

def scalarVal {N : ℕ} (D : Dag N) (x : Fin (N+N) → Bool) (w : ℕ) : Prop :=
  D.val (zeroLines x) w = true

private def Invariant (d : ℕ) (v z f : Prop) : Prop :=
  (d = 0 → (v ↔ z) ∧ ¬ f) ∧ (d ≤ 1 → (v ↔ z ∨ f))

private theorem join_and {a b : ℕ} (d : ℕ → ℕ) (v z f : ℕ → Prop)
    (ha : Invariant (d a) (v a) (z a) (f a))
    (hb : Invariant (d b) (v b) (z b) (f b)) :
    Invariant (d a+d b) (v a ∧ v b) (z a ∧ z b) ((codeGate d (.and a b)).eval z f) := by
  unfold Invariant at *
  by_cases h₁ : d a = 0 <;> by_cases h₂ : d b = 0 <;>
    simp [codeGate, h₁, h₂, LinearOp.eval] <;> grind

private theorem join_or {a b : ℕ} (d : ℕ → ℕ) (v z f : ℕ → Prop)
    (ha : Invariant (d a) (v a) (z a) (f a))
    (hb : Invariant (d b) (v b) (z b) (f b)) :
    Invariant (max (d a) (d b)) (v a ∨ v b) (z a ∨ z b) ((codeGate d (.or a b)).eval z f) := by
  unfold Invariant at *
  by_cases h₁ : d a = 0 <;> by_cases h₂ : d b = 0 <;>
    simp [codeGate, h₁, h₂, LinearOp.eval, max_le_iff] <;> grind

private theorem prefix_correct {N : ℕ} (D : Dag N) (wf : D.WF) (x : Fin (N+N) → Bool)
    (t w : ℕ) (hw : w < N+N+t) :
    Invariant (D.deg w) (D.val x w = true) (scalarVal D x w)
      (forward (scalarVal D x) (compilePrefix D t) (activeLines x) w) := by
  induction t generalizing w with
  | zero =>
    have hinput : w < N+N := by omega
    by_cases hp : w < N <;>
      simp [compilePrefix, forward, scalarVal, circ_val_input D _ hinput,
        circ_deg_input D hinput, zeroLines, activeLines, Invariant, hp,
        show (N ≤ w) = (¬ w < N) from propext (by omega), hinput]
  | succ t ih =>
    let u := N+N+t
    let st := forward (scalarVal D x) (compilePrefix D t) (activeLines x)
    have hstep (r) : forward (scalarVal D x) (compilePrefix D (t+1)) (activeLines x) r =
        (if r = u then (codeAt D u).eval (scalarVal D x) st else st r) := by
      simp [compilePrefix, forward, List.foldl_append, Assignment.push, st, u]
    rw [hstep]
    by_cases h : w = u
    · subst w
      rw [ite_eq_left rfl]
      cases hg : D.gateAt u with
      | none =>
        have hn : N+N ≤ u := by dsimp [u]; omega
        have hl : D.gates[u-(N+N)]? = none := by simpa [Dag.gateAt, hn] using hg
        simp [codeAt, hg, LinearOp.eval, Invariant, Dag.deg, Dag.val, scalarVal, hn.not_gt, hl]
      | some g =>
        cases g with
        | cst b =>
          obtain ⟨hn, hl⟩ := Api.gateAt_some hg
          simp [codeAt, hg, codeGate, LinearOp.eval, Invariant, Dag.deg, Dag.val, scalarVal,
            hn.not_gt, hl]
        | and a b =>
          have ha := wf u _ hg a (by simp [G.kids])
          have hb := wf u _ hg b (by simp [G.kids])
          have he := @join_and a b D.deg (fun r => D.val x r = true) (scalarVal D x) st
            (ih a ha) (ih b hb)
          simpa only [codeAt, hg, Forms.deg_and hg ha hb, Forms.val_and hg ha hb,
            scalarVal, Bool.and_eq_true_iff] using he
        | or a b =>
          have ha := wf u _ hg a (by simp [G.kids])
          have hb := wf u _ hg b (by simp [G.kids])
          have he := @join_or a b D.deg (fun r => D.val x r = true) (scalarVal D x) st
            (ih a ha) (ih b hb)
          simpa only [codeAt, hg, Forms.deg_or hg ha hb, Forms.val_or hg ha hb,
            scalarVal, Bool.or_eq_true] using he
    · rw [ite_eq_right h]
      exact ih w (by dsimp [u] at h; omega)

theorem compiled_value {N : ℕ} (D : Dag N) (wf : D.WF) (x : Fin (N+N) → Bool)
    (w : ℕ) (hw : w < N+N+D.size) (hdeg : D.deg w ≤ 1) :
    D.val x w = true ↔ scalarVal D x w ∨ forward (scalarVal D x) (compile D) (activeLines x) w :=
  (prefix_correct D wf x D.size w hw).2 hdeg

def pointOnly {N : ℕ} (x : Fin N → Bool) : Fin (N+N) → Bool := Fin.addCases x (fun _ => false)

def oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) : Fin (N+N) → Bool :=
  Fin.addCases x (fun j => decide (j = i))

theorem zero_oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    zeroLines (oneLine x i) = pointOnly x := by
  funext k
  refine Fin.addCases (fun p => ?_) (fun w => ?_) k
  · simp [zeroLines, oneLine, pointOnly]
  · simp only [zeroLines, pointOnly, Fin.val_natAdd, Fin.addCases_right]
    rw [ite_eq_right (by omega)]

theorem active_oneLine {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    activeLines (oneLine x i) = (fun w => w = N+i.val) := by
  funext w; apply propext; constructor
  · rintro ⟨hw, hn, hv⟩
    let j : Fin N := ⟨w-N,by omega⟩
    have eq : (⟨w,hw⟩ : Fin (N+N)) = Fin.natAdd N j := Fin.ext (by dsimp [j]; omega)
    rw [eq] at hv
    have he : j = i := by simpa only [oneLine, Fin.addCases_right, decide_eq_true_eq] using hv
    have hi := congrArg Fin.val he
    dsimp [j] at hi
    omega
  · rintro rfl
    refine ⟨by omega,by omega,?_⟩
    change oneLine x i (Fin.natAdd N i) = true
    simp only [oneLine, Fin.addCases_right, decide_eq_true_eq]

def pointScalar {N : ℕ} (D : Dag N) (x : Fin N → Bool) (w : ℕ) : Prop :=
  D.val (pointOnly x) w = true

theorem circuit_coefficient {N : ℕ} (C : Circuit) (x : Fin N → Bool) (i : Fin N)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdeg : HasLineDegree (N+N) (Finset.Ico N (N+N)) C 1)
    (hw : C.output < N+N+C.size) (hoff : C.eval (List.ofFn (pointOnly x)) = false) :
    let D := ofCircuit N C
    C.eval (List.ofFn (oneLine x i)) = true ↔
      forward (pointScalar D x) (compile D) (fun w => w = N+i.val) C.output := by
  let D := ofCircuit N C
  have hd : D.deg C.output ≤ 1 := (Bridge.card03d_deg C mono C.output).trans hdeg
  have hv := compiled_value D (Api.card03b_wf C) (oneLine x i) C.output
    (by simpa [D, Api.card03a_size] using hw) hd
  have hz : scalarVal D (oneLine x i) = pointScalar D x := by
    funext w; simp only [scalarVal, pointScalar, zero_oneLine]
  rw [hz, active_oneLine] at hv
  have hdead : ¬ pointScalar D x C.output := by
    change ¬ (ofCircuit N C).val (pointOnly x) C.output = true
    rw [Bridge.card03c_val C mono]
    change ¬ C.eval (List.ofFn (pointOnly x)) = true
    simp [hoff]
  rw [or_iff_right hdead] at hv
  have hactual := Bridge.card03c_val C mono (oneLine x i) C.output
  change D.val (oneLine x i) C.output = C.eval (List.ofFn (oneLine x i)) at hactual
  rw [hactual] at hv
  exact hv

end PlaneArcTranspose

end SourceNormalizedCompile

namespace RowStructure

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma card_line (w : Fin 13) : (line w).card = 4 := by
  revert w; decide

lemma card_inter_line (w₁ w₂ : Fin 13) (h : w₁ ≠ w₂) : (line w₁ ∩ line w₂).card = 1 := by
  revert w₁ w₂ h; decide

lemma line_eq_of_subset_two {S : Finset (Fin 13)} {w₁ w₂ : Fin 13}
    (h1 : S ⊆ line w₁) (h2 : S ⊆ line w₂) (hc : 2 ≤ S.card) : w₁ = w₂ := by
  by_contra hne
  have hsub : S ⊆ line w₁ ∩ line w₂ := Finset.subset_inter h1 h2
  have hle := Finset.card_le_card hsub
  rw [card_inter_line w₁ w₂ hne] at hle
  omega

lemma line_eq_of_superset_le6 {S : Finset (Fin 13)} {w₁ w₂ : Fin 13}
    (h1 : line w₁ ⊆ S) (h2 : line w₂ ⊆ S) (hc : S.card ≤ 6) : w₁ = w₂ := by
  by_contra hne
  have hun : line w₁ ∪ line w₂ ⊆ S := Finset.union_subset h1 h2
  have hle := Finset.card_le_card hun
  have hci := Finset.card_union_add_card_inter (line w₁) (line w₂)
  rw [card_line w₁, card_line w₂, card_inter_line w₁ w₂ hne] at hci
  omega

lemma lines_in_card7_le2 (S : Finset (Fin 13)) (hc : S.card = 7) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 2 := by
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  by_contra hgt
  have h3 : 2 < T.card := by omega
  obtain ⟨w₁, hw₁, w₂, hw₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hrem : (T.erase w₁ |>.erase w₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hcard : (T.erase w₁ |>.erase w₂).card = 0 := by rw [hemp]; rfl
    have h1 : (T.erase w₁).card = T.card - 1 := Finset.card_erase_of_mem hw₁
    have hw2' : w₂ ∈ T.erase w₁ := Finset.mem_erase.mpr ⟨h12.symm, hw₂⟩
    have h2 : (T.erase w₁ |>.erase w₂).card = (T.erase w₁).card - 1 := Finset.card_erase_of_mem hw2'
    omega
  obtain ⟨w₃, hw₃⟩ := hrem
  have hw3_2 : w₃ ≠ w₂ := (Finset.mem_erase.mp hw₃).1
  have hw3_1 : w₃ ≠ w₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hw₃).2).1
  have hw3_T : w₃ ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp hw₃).2).2
  have hL1 : line w₁ ⊆ S := (Finset.mem_filter.mp hw₁).2
  have hL2 : line w₂ ⊆ S := (Finset.mem_filter.mp hw₂).2
  have hL3 : line w₃ ⊆ S := (Finset.mem_filter.mp hw3_T).2
  have hun : (line w₁ ∪ line w₂) ∪ line w₃ ⊆ S :=
    Finset.union_subset (Finset.union_subset hL1 hL2) hL3
  have h12u : (line w₁ ∪ line w₂).card = 7 := by
    have hci := Finset.card_union_add_card_inter (line w₁) (line w₂)
    rw [card_line w₁, card_line w₂, card_inter_line w₁ w₂ h12] at hci
    omega
  have hinter : ((line w₁ ∪ line w₂) ∩ line w₃).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have hu := Finset.card_union_le (line w₁ ∩ line w₃) (line w₂ ∩ line w₃)
    rw [card_inter_line w₁ w₃ hw3_1.symm, card_inter_line w₂ w₃ hw3_2.symm] at hu
    omega
  have htot := Finset.card_union_add_card_inter (line w₁ ∪ line w₂) (line w₃)
  rw [h12u, card_line w₃] at htot
  have hle := Finset.card_le_card hun
  omega

def e1 (v : Fin 13) : Fin 13 → Bool := fun k => decide (k = v)
def e2 (a b : Fin 13) : Fin 13 → Bool := fun k => decide (k = a ∨ k = b)

def WeightLe2 (x : Fin 13 → Bool) : Prop :=
  ∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k

lemma e1_weightLe2 (v : Fin 13) : WeightLe2 (e1 v) := by
  intro i j k hi hj hk
  simp only [e1, decide_eq_true_eq] at hi hj hk
  left; exact hi.trans hj.symm

lemma e2_weightLe2 (a b : Fin 13) : WeightLe2 (e2 a b) := by
  intro i j k hi hj hk
  simp only [e2, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> tauto

def MonoFun (f : (Fin 13 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 13 → Bool, (∀ k, x k = true → y k = true) → f x = true → f y = true

def Safe (w : Fin 13) (f : (Fin 13 → Bool) → Bool) : Prop :=
  ∀ x : Fin 13 → Bool, WeightLe2 x → f x = true → ∃ v ∈ line w, x v = true

lemma prime_weight2 (w : Fin 13) (f₁ f₂ : (Fin 13 → Bool) → Bool)
    (hm₁ : MonoFun f₁) (hm₂ : MonoFun f₂)
    (hs : Safe w (fun x => f₁ x && f₂ x)) :
    (∀ v : Fin 13, f₁ (e1 v) = true → v ∈ line w) ∨
    (∀ v : Fin 13, f₂ (e1 v) = true → v ∈ line w) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨a, ha1, haL⟩, ⟨b, hb2, hbL⟩⟩ := h
  have h1 : f₁ (e2 a b) = true := hm₁ (e1 a) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk) ha1
  have h2 : f₂ (e2 a b) = true := hm₂ (e1 b) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk) hb2
  obtain ⟨v, hvL, hvx⟩ := hs (e2 a b) (e2_weightLe2 a b) (by simp [h1, h2])
  simp only [e2, decide_eq_true_eq] at hvx
  rcases hvx with rfl | rfl
  · exact haL hvL
  · exact hbL hvL

def wval (gates : List Gate) (i : ℕ) (x : Fin 13 → Bool) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD i false

def wvalAt (gates : List Gate) (k i : ℕ) (x : Fin 13 → Bool) : Bool :=
  if i < 13 + k then wval gates i x else false

def V (gates : List Gate) (i : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => wval gates i (e1 v) = true)

def VAt (gates : List Gate) (k i : ℕ) : Finset (Fin 13) :=
  if i < 13 + k then V gates i else ∅

lemma mem_V (gates : List Gate) (i : ℕ) (v : Fin 13) :
    v ∈ V gates i ↔ wval gates i (e1 v) = true := by
  simp [V]

lemma mem_VAt (gates : List Gate) (k i : ℕ) (v : Fin 13) :
    v ∈ VAt gates k i ↔ wvalAt gates k i (e1 v) = true := by
  unfold VAt wvalAt
  split_ifs with h
  · exact mem_V gates i v
  · simp

lemma wval_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ) :
    MonoFun (wval gates i) := by
  intro x y hle hx
  apply wiresFrom_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp) _ i hx
  intro j hj
  by_cases hjlt : j < 13
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

lemma wvalAt_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (k i : ℕ) :
    MonoFun (wvalAt gates k i) := by
  intro x y hle hx
  unfold wvalAt at hx ⊢
  split_ifs at hx ⊢ with h
  exact wval_mono gates hmono i x y hle hx

lemma wval_input (gates : List Gate) (i : ℕ) (hi : i < 13) (x : Fin 13 → Bool) :
    wval gates i x = x ⟨i, hi⟩ := by
  unfold wval
  have hlen : (List.ofFn x).length = 13 := List.length_ofFn
  rw [getD_wiresFrom_lt gates (List.ofFn x) i (by omega)]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_ofFn (f := x) (i := i) (by omega)

lemma V_input (gates : List Gate) (i : ℕ) (hi : i < 13) :
    V gates i = {⟨i, hi⟩} := by
  ext v
  rw [mem_V, wval_input gates i hi, Finset.mem_singleton]
  simp [e1, Fin.ext_iff, eq_comm]

lemma card_V_input (gates : List Gate) (i : ℕ) (hi : i < 13) :
    (V gates i).card = 1 := by
  rw [V_input gates i hi, Finset.card_singleton]

lemma V_ge_len (gates : List Gate) (i : ℕ) (hi : 13 + gates.length ≤ i) :
    V gates i = ∅ := by
  ext v
  rw [mem_V]
  simp only [Finset.notMem_empty, iff_false]
  unfold wval
  rw [List.getD_eq_default]
  · simp
  · rw [length_wiresFrom, List.length_ofFn]; omega

lemma gate_idx_of_VAt_ge2 (gates : List Gate) (k i : ℕ) (hc : 2 ≤ (VAt gates k i).card) :
    ∃ g' < k, i = 13 + g' := by
  unfold VAt at hc
  split_ifs at hc with hlt
  · have hge13 : 13 ≤ i := by
      by_contra h13
      have hcard := card_V_input gates i (by omega)
      omega
    exact ⟨i - 13, by omega, by omega⟩
  · simp at hc

lemma gate_idx_of_V_ge2 (gates : List Gate) (i : ℕ) (hc : 2 ≤ (V gates i).card) :
    ∃ g < gates.length, i = 13 + g := by
  have hlt : i < 13 + gates.length := by
    by_contra hge
    have he := V_ge_len gates i (by omega)
    rw [he] at hc; simp at hc
  have hge13 : 13 ≤ i := by
    by_contra h13
    have hcard := card_V_input gates i (by omega)
    omega
  exact ⟨i - 13, by omega, by omega⟩

lemma wval_gate_eq (gates : List Gate) (k : ℕ) (hk : k < gates.length) (x : Fin 13 → Bool) :
    wval gates (13 + k) x =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => wvalAt gates k i x) := by
  have h := getD_wiresFrom_gate gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  exact h

lemma V_gate_nil_and (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = []) :
    V gates (13 + k) = Finset.univ := by
  ext v
  rw [mem_V, wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_nil_or (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = []) :
    V gates (13 + k) = ∅ := by
  ext v
  rw [mem_V, wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = wvalAt gates k a x := by
  rw [wval_gate_eq gates k hk, hin]
  rcases hop with h | h <;> simp [h, GateOp.eval]

lemma wval_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = (wvalAt gates k a x && wvalAt gates k b x) := by
  rw [wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = (wvalAt gates k a x || wvalAt gates k b x) := by
  rw [wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) :
    V gates (13 + k) = VAt gates k a := by
  ext v; rw [mem_V, mem_VAt, wval_gate_one gates k hk a hop hin]

lemma V_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) :
    V gates (13 + k) = VAt gates k a ∩ VAt gates k b := by
  ext v; rw [mem_V, Finset.mem_inter, mem_VAt, mem_VAt, wval_gate_two_and gates k hk a b hop hin]
  simp [Bool.and_eq_true]

lemma V_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) :
    V gates (13 + k) = VAt gates k a ∪ VAt gates k b := by
  ext v; rw [mem_V, Finset.mem_union, mem_VAt, mem_VAt, wval_gate_two_or gates k hk a b hop hin]
  simp [Bool.or_eq_true]

def GwUp (gates : List Gate) (w : Fin 13) (g : ℕ) : Finset ℕ :=
  (Finset.range (g + 1)).filter (fun j => V gates (13 + j) ⊆ line w ∧ 2 ≤ (V gates (13 + j)).card)

def Gw (gates : List Gate) (w : Fin 13) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => V gates (13 + j) ⊆ line w ∧ 2 ≤ (V gates (13 + j)).card)

def HasTriple (gates : List Gate) (w : Fin 13) : Prop :=
  ∃ ga gb gc : ℕ,
    ga < gates.length ∧ gb < gates.length ∧ gc < gates.length ∧
    line w ⊂ V gates (13 + ga) ∧ line w ⊂ V gates (13 + gb) ∧ line w ⊂ V gates (13 + gc) ∧
    Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gb) \ line w) ∧
    Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gc) \ line w) ∧
    Disjoint (V gates (13 + gb) \ line w) (V gates (13 + gc) \ line w)

lemma GwUp_subset_Gw (gates : List Gate) (w : Fin 13) (g : ℕ) (hg : g < gates.length) :
    GwUp gates w g ⊆ Gw gates w := by
  intro j hj
  simp only [GwUp, Gw, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma card_ge3_of_three {S : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac])]
    rw [Finset.card_insert_of_notMem (by simp [hbc])]
    simp
  linarith [Finset.card_le_card hsub]

lemma card_ge2_of_two {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    2 ≤ S.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab])]; simp
  linarith [Finset.card_le_card hsub]

lemma card_ge3_of_sub (gates : List Gate) (w : Fin 13) (g' g : ℕ)
    (hlt : g' < g) (hg : g ∈ GwUp gates w g) (h2 : 2 ≤ (GwUp gates w g').card) :
    3 ≤ (GwUp gates w g).card := by
  have hnot : g ∉ GwUp gates w g' := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    omega
  have hsub : insert g (GwUp gates w g') ⊆ GwUp gates w g := by
    intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact hg
    · simp only [GwUp, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

lemma exists_child_of_card3 (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (g' : ℕ) (hg' : g' < gates.length)
    (hsub : V gates (13 + g') ⊆ line w) (hcard : (V gates (13 + g')).card = 3)
    (hsafe : Safe w (wval gates (13 + g'))) :
    ∃ g'' < g', V gates (13 + g'') ⊆ line w ∧ 2 ≤ (V gates (13 + g'')).card := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  obtain ⟨hop, hlen⟩ := hvalid (gates[g']) (List.getElem_mem hg')
  match hin : (gates[g']).inputs with
  | [] =>
    rcases hop with h | h
    · have hV := V_gate_nil_and gates g' hg' h hin
      rw [hV] at hcard; simp at hcard
    · have hV := V_gate_nil_or gates g' hg' h hin
      rw [hV] at hcard; simp at hcard
  | [a] =>
    have hV := V_gate_one gates g' hg' a hop hin
    have ha3 : (VAt gates g' a).card = 3 := by rw [← hV]; exact hcard
    obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
    have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
    rw [hVeq] at hV ha3
    exact ⟨g'', hg''lt, by rw [← hV]; exact hsub, by omega⟩
  | [a, b] =>
    rcases hop with h | h
    · have hw : ∀ x, wval gates (13 + g') x = (wvalAt gates g' a x && wvalAt gates g' b x) :=
        wval_gate_two_and gates g' hg' a b h hin
      have hsafe' : Safe w (fun x => wvalAt gates g' a x && wvalAt gates g' b x) := by
        intro x hx hv; exact hsafe x hx (by rw [hw]; exact hv)
      have hV := V_gate_two_and gates g' hg' a b h hin
      have hpr := prime_weight2 w (wvalAt gates g' a) (wvalAt gates g' b)
        (wvalAt_mono gates hmono g' a) (wvalAt_mono gates hmono g' b) hsafe'
      rcases hpr with haL | hbL
      · have hasub : VAt gates g' a ⊆ line w := by
          intro v hv; exact haL v ((mem_VAt gates g' a v).mp hv)
        have hge : 3 ≤ (VAt gates g' a).card := by
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := VAt gates g' a) (s₂ := VAt gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        rw [hVeq] at hasub hge
        exact ⟨g'', hg''lt, hasub, by omega⟩
      · have hbsub : VAt gates g' b ⊆ line w := by
          intro v hv; exact hbL v ((mem_VAt gates g' b v).mp hv)
        have hge : 3 ≤ (VAt gates g' b).card := by
          have := Finset.card_le_card (Finset.inter_subset_right (s₁ := VAt gates g' a) (s₂ := VAt gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by omega)
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        rw [hVeq] at hbsub hge
        exact ⟨g'', hg''lt, hbsub, by omega⟩
    · have hV := V_gate_two_or gates g' hg' a b h hin
      have hsum : 3 ≤ (VAt gates g' a).card + (VAt gates g' b).card := by
        have := Finset.card_union_le (VAt gates g' a) (VAt gates g' b)
        rw [← hV, hcard] at this; exact this
      by_cases ha2 : 2 ≤ (VAt gates g' a).card
      · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a ha2
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        have hasub : V gates (13 + g'') ⊆ line w := by
          rw [← hVeq]; exact Finset.subset_union_left.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hasub, by rw [← hVeq]; exact ha2⟩
      · have hb2 : 2 ≤ (VAt gates g' b).card := by omega
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b hb2
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        have hbsub : V gates (13 + g'') ⊆ line w := by
          rw [← hVeq]; exact Finset.subset_union_right.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hbsub, by rw [← hVeq]; exact hb2⟩
  | _ :: _ :: _ :: _ =>
    rw [hin] at hlen; simp at hlen

lemma and_case_core (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (g : ℕ) (hg : g < gates.length)
    (hVg : V gates (13 + g) = line w)
    (hsafe : Safe w (wval gates (13 + g)))
    (ih : ∀ m < g, V gates (13 + m) = line w → Safe w (wval gates (13 + m)) →
      3 ≤ (GwUp gates w m).card ∨ (2 ≤ (GwUp gates w m).card ∧ HasTriple gates w))
    (i j : ℕ) (hwg : ∀ x, wval gates (13 + g) x = (wvalAt gates g i x && wvalAt gates g j x))
    (hVi : VAt gates g i = line w) (hVj_sub : line w ⊆ VAt gates g j) :
    3 ≤ (GwUp gates w g).card ∨ (2 ≤ (GwUp gates w g).card ∧ HasTriple gates w) := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  have hgw : g ∈ GwUp gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
  have hi2 : 2 ≤ (VAt gates g i).card := by rw [hVi, card_line]; omega
  obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i hi2
  have hVi_eq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
  rw [hVi_eq] at hVi
  have hg'w : g' ∈ GwUp gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [hVi], by rw [hVi, card_line]; omega⟩

  by_cases hVj_eq : VAt gates g j = line w
  · by_cases hji : j = 13 + g'
    · subst hji
      have hsafe' : Safe w (wval gates (13 + g')) := by
        intro x hx hv
        have h1 : wvalAt gates g (13 + g') x = true := by
          unfold wvalAt; rw [if_pos (by omega)]; exact hv
        exact hsafe x hx (by rw [hwg]; simp [h1])
      have hih := ih g' hg'lt hVi hsafe'
      have h2' : 2 ≤ (GwUp gates w g').card := by
        rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    · have hj2 : 2 ≤ (VAt gates g j).card := by rw [hVj_eq, card_line]; omega
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j hj2
      have hVj_eq2 : VAt gates g (13 + g'') = V gates (13 + g'') := if_pos (by omega)
      rw [hVj_eq2] at hVj_eq
      have hg''w : g'' ∈ GwUp gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hVj_eq], by rw [hVj_eq, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg'w hg''w hgw (by omega) (by omega) (by omega))

  · have hVj_ssub : line w ⊂ VAt gates g j := Finset.ssubset_iff_subset_ne.mpr ⟨hVj_sub, fun he => hVj_eq he.symm⟩
    have hj5 : 5 ≤ (VAt gates g j).card := by
      have := Finset.card_lt_card hVj_ssub
      rw [card_line] at this; omega
    obtain ⟨gj, hgjlt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
    have hVj_eq2 : VAt gates g (13 + gj) = V gates (13 + gj) := if_pos (by omega)
    rw [hVj_eq2] at hVj_ssub

    have hg'_len : g' < gates.length := by omega
    obtain ⟨hop', hlen'⟩ := hvalid (gates[g']) (List.getElem_mem hg'_len)
    match hin' : (gates[g']).inputs with
    | [] =>
      rcases hop' with h | h
      · have hV := V_gate_nil_and gates g' hg'_len h hin'
        rw [hV] at hVi
        have := congrArg Finset.card hVi
        rw [card_line] at this; simp at this
      · have hV := V_gate_nil_or gates g' hg'_len h hin'
        rw [hV] at hVi
        have := congrArg Finset.card hVi
        rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one gates g' hg'_len a hop' hin'
      rw [hVi] at hV
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by rw [← hV, card_line]; omega)
      have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
      rw [hVeq] at hV
      have hg''w : g'' ∈ GwUp gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [← hV], by rw [← hV, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | [a, b] =>
      rcases hop' with h | h
      · have hV := V_gate_two_and gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have ha_sub : line w ⊆ VAt gates g' a := by
          rw [hV]; exact Finset.inter_subset_left
        have hb_sub : line w ⊆ VAt gates g' b := by
          rw [hV]; exact Finset.inter_subset_right
        by_cases ha_eq : VAt gates g' a = line w
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by rw [ha_eq, card_line]; omega)
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          rw [hVeq] at ha_eq
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, by rw [ha_eq], by rw [ha_eq, card_line]; omega⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · by_cases hb_eq : VAt gates g' b = line w
          · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by rw [hb_eq, card_line]; omega)
            have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
            rw [hVeq] at hb_eq
            have hg''w : g'' ∈ GwUp gates w g := by
              simp only [GwUp, Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by rw [hb_eq], by rw [hb_eq, card_line]; omega⟩
            exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
          ·
            have ha_ssub : line w ⊂ VAt gates g' a := Finset.ssubset_iff_subset_ne.mpr ⟨ha_sub, fun he => ha_eq he.symm⟩
            have hb_ssub : line w ⊂ VAt gates g' b := Finset.ssubset_iff_subset_ne.mpr ⟨hb_sub, fun he => hb_eq he.symm⟩
            have ha5 : 5 ≤ (VAt gates g' a).card := by
              have := Finset.card_lt_card ha_ssub; rw [card_line] at this; omega
            have hb5 : 5 ≤ (VAt gates g' b).card := by
              have := Finset.card_lt_card hb_ssub; rw [card_line] at this; omega
            obtain ⟨ga, hgalt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
            obtain ⟨gb, hgblt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by omega)
            have hVa_eq : VAt gates g' (13 + ga) = V gates (13 + ga) := if_pos (by omega)
            have hVb_eq : VAt gates g' (13 + gb) = V gates (13 + gb) := if_pos (by omega)
            rw [hVa_eq] at ha_ssub
            rw [hVb_eq] at hb_ssub
            rw [hVa_eq, hVb_eq] at hV
            have hdisj_ab : Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gb) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpb
              rw [Finset.mem_sdiff] at hpa hpb
              have hp_in : p ∈ V gates (13 + ga) ∩ V gates (13 + gb) := Finset.mem_inter.mpr ⟨hpa.1, hpb.1⟩
              rw [← hV] at hp_in
              exact hpa.2 hp_in
            have hwg' : ∀ x, wval gates (13 + g') x = (wval gates (13 + ga) x && wval gates (13 + gb) x) := by
              intro x
              rw [wval_gate_two_and gates g' hg'_len (13 + ga) (13 + gb) h hin']
              unfold wvalAt
              rw [if_pos (by omega), if_pos (by omega)]
            have hdisj_aj : Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gj) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpj
              rw [Finset.mem_sdiff] at hpa hpj
              obtain ⟨q, hqb, hqL⟩ := Finset.exists_of_ssubset hb_ssub
              have h1 : wval gates (13 + ga) (e2 p q) = true :=
                wval_mono gates hmono (13 + ga) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + ga) p).mp hpa.1)
              have h2 : wval gates (13 + gb) (e2 p q) = true :=
                wval_mono gates hmono (13 + gb) (e1 q) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gb) q).mp hqb)
              have h3 : wval gates (13 + gj) (e2 p q) = true :=
                wval_mono gates hmono (13 + gj) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + gj) p).mp hpj.1)
              have hval : wval gates (13 + g) (e2 p q) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 p q) (e2_weightLe2 p q) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hpa.2 hvL
              · exact hqL hvL
            have hdisj_bj : Disjoint (V gates (13 + gb) \ line w) (V gates (13 + gj) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpb hpj
              rw [Finset.mem_sdiff] at hpb hpj
              obtain ⟨q, hqa, hqL⟩ := Finset.exists_of_ssubset ha_ssub
              have h1 : wval gates (13 + ga) (e2 q p) = true :=
                wval_mono gates hmono (13 + ga) (e1 q) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + ga) q).mp hqa)
              have h2 : wval gates (13 + gb) (e2 q p) = true :=
                wval_mono gates hmono (13 + gb) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gb) p).mp hpb.1)
              have h3 : wval gates (13 + gj) (e2 q p) = true :=
                wval_mono gates hmono (13 + gj) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gj) p).mp hpj.1)
              have hval : wval gates (13 + g) (e2 q p) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 q p) (e2_weightLe2 q p) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hqL hvL
              · exact hpb.2 hvL
            exact Or.inr ⟨card_ge2_of_two hg'w hgw (by omega),
              ⟨ga, gb, gj, by omega, by omega, by omega,
                ha_ssub, hb_ssub, hVj_ssub, hdisj_ab, hdisj_aj, hdisj_bj⟩⟩
      · have hV := V_gate_two_or gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have hsum : 4 ≤ (VAt gates g' a).card + (VAt gates g' b).card := by
          have := Finset.card_union_le (VAt gates g' a) (VAt gates g' b)
          rw [← hV, card_line] at this; exact this
        by_cases ha2 : 2 ≤ (VAt gates g' a).card
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a ha2
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          have hasub : V gates (13 + g'') ⊆ line w := by
            rw [← hVeq, hV]; exact Finset.subset_union_left
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hasub, by rw [← hVeq]; exact ha2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · have hb2 : 2 ≤ (VAt gates g' b).card := by omega
          obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b hb2
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          have hbsub : V gates (13 + g'') ⊆ line w := by
            rw [← hVeq, hV]; exact Finset.subset_union_right
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hbsub, by rw [← hVeq]; exact hb2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin'] at hlen'; simp at hlen'

lemma line_structure (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) :
    ∀ g : ℕ, g < gates.length → V gates (13 + g) = line w → Safe w (wval gates (13 + g)) →
      3 ≤ (GwUp gates w g).card ∨ (2 ≤ (GwUp gates w g).card ∧ HasTriple gates w) := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg hVg hsafe
    have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
    have hgw : g ∈ GwUp gates w g := by
      simp only [GwUp, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
    obtain ⟨hop, hlen⟩ := hvalid (gates[g]) (List.getElem_mem hg)
    match hin : (gates[g]).inputs with
    | [] =>
      rcases hop with h | h
      · have hV := V_gate_nil_and gates g hg h hin
        rw [hV] at hVg
        have := congrArg Finset.card hVg; rw [card_line] at this; simp at this
      · have hV := V_gate_nil_or gates g hg h hin
        rw [hV] at hVg
        have := congrArg Finset.card hVg; rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one gates g hg a hop hin
      rw [hVg] at hV
      obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g a (by rw [← hV, card_line]; omega)
      have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
      rw [hVeq] at hV
      have hsafe' : Safe w (wval gates (13 + g')) := by
        intro x hx hv
        apply hsafe x hx
        rw [wval_gate_one gates g hg (13 + g') hop hin]
        unfold wvalAt; rw [if_pos (by omega)]; exact hv
      have hih := ih g' hg'lt (by omega) hV.symm hsafe'
      have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    | [i, j] =>
      rcases hop with h | h
      ·
        have hwg := wval_gate_two_and gates g hg i j h hin
        have hsafe' : Safe w (fun x => wvalAt gates g i x && wvalAt gates g j x) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; exact hv)
        have hV := V_gate_two_and gates g hg i j h hin
        rw [hVg] at hV
        have hpr := prime_weight2 w (wvalAt gates g i) (wvalAt gates g j)
          (wvalAt_mono gates hmono g i) (wvalAt_mono gates hmono g j) hsafe'
        have ih' : ∀ m < g, V gates (13 + m) = line w → Safe w (wval gates (13 + m)) →
            3 ≤ (GwUp gates w m).card ∨ (2 ≤ (GwUp gates w m).card ∧ HasTriple gates w) :=
          fun m hm => ih m hm (by omega)
        rcases hpr with hiL | hjL
        · have hisub : VAt gates g i ⊆ line w := fun v hv => hiL v ((mem_VAt gates g i v).mp hv)
          have hVi : VAt gates g i = line w :=
            Finset.Subset.antisymm hisub (by rw [hV]; exact Finset.inter_subset_left)
          have hVj_sub : line w ⊆ VAt gates g j := by rw [hV]; exact Finset.inter_subset_right
          exact and_case_core gates hvalid w g hg hVg hsafe ih' i j hwg hVi hVj_sub
        · have hjsub : VAt gates g j ⊆ line w := fun v hv => hjL v ((mem_VAt gates g j v).mp hv)
          have hVj : VAt gates g j = line w :=
            Finset.Subset.antisymm hjsub (by rw [hV]; exact Finset.inter_subset_right)
          have hVi_sub : line w ⊆ VAt gates g i := by rw [hV]; exact Finset.inter_subset_left
          have hwg_comm : ∀ x, wval gates (13 + g) x = (wvalAt gates g j x && wvalAt gates g i x) := by
            intro x; rw [hwg, Bool.and_comm]
          exact and_case_core gates hvalid w g hg hVg hsafe ih' j i hwg_comm hVj hVi_sub
      ·
        have hwg := wval_gate_two_or gates g hg i j h hin
        have hV := V_gate_two_or gates g hg i j h hin
        rw [hVg] at hV
        have hi_sub : VAt gates g i ⊆ line w := by rw [hV]; exact Finset.subset_union_left
        have hj_sub : VAt gates g j ⊆ line w := by rw [hV]; exact Finset.subset_union_right
        have hsafe_i : Safe w (wvalAt gates g i) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hsafe_j : Safe w (wvalAt gates g j) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hci_le : (VAt gates g i).card ≤ 4 := by
          have := Finset.card_le_card hi_sub; rw [card_line] at this; exact this
        have hcj_le : (VAt gates g j).card ≤ 4 := by
          have := Finset.card_le_card hj_sub; rw [card_line] at this; exact this
        have hsum : 4 ≤ (VAt gates g i).card + (VAt gates g j).card := by
          have := Finset.card_union_le (VAt gates g i) (VAt gates g j)
          rw [← hV, card_line] at this; exact this
        by_cases hi4 : (VAt gates g i).card = 4
        · have hVi : VAt gates g i = line w :=
            Finset.eq_of_subset_of_card_le hi_sub (by rw [card_line, hi4])
          obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
          have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
          rw [hVeq] at hVi
          have hsafe' : Safe w (wval gates (13 + g')) := by
            intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
          have hih := ih g' hg'lt (by omega) hVi hsafe'
          have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
          exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
        · by_cases hj4 : (VAt gates g j).card = 4
          · have hVj : VAt gates g j = line w :=
              Finset.eq_of_subset_of_card_le hj_sub (by rw [card_line, hj4])
            obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
            have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
            rw [hVeq] at hVj
            have hsafe' : Safe w (wval gates (13 + g')) := by
              intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
            have hih := ih g' hg'lt (by omega) hVj hsafe'
            have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
            exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
          · by_cases hi3 : (VAt gates g i).card = 3
            · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
              have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
              rw [hVeq] at hi_sub hi3
              have hsafe' : Safe w (wval gates (13 + g')) := by
                intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
              obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                exists_child_of_card3 gates hvalid w g' (by omega) hi_sub hi3 hsafe'
              have hg'w : g' ∈ GwUp gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hi_sub, by omega⟩
              have hg''w : g'' ∈ GwUp gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hsub'', hc''⟩
              exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
            · by_cases hj3 : (VAt gates g j).card = 3
              · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
                have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
                rw [hVeq] at hj_sub hj3
                have hsafe' : Safe w (wval gates (13 + g')) := by
                  intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
                obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                  exists_child_of_card3 gates hvalid w g' (by omega) hj_sub hj3 hsafe'
                have hg'w : g' ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                have hg''w : g'' ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hsub'', hc''⟩
                exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
              ·
                have hi2 : (VAt gates g i).card = 2 := by omega
                have hj2 : (VAt gates g j).card = 2 := by omega
                have hij_ne : i ≠ j := by
                  intro he; subst he
                  rw [Finset.union_idempotent] at hV
                  have := congrArg Finset.card hV
                  rw [card_line, hi2] at this; omega
                obtain ⟨g₁, hg₁lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
                obtain ⟨g₂, hg₂lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
                have hV1 : VAt gates g (13 + g₁) = V gates (13 + g₁) := if_pos (by omega)
                have hV2 : VAt gates g (13 + g₂) = V gates (13 + g₂) := if_pos (by omega)
                rw [hV1] at hi_sub hi2
                rw [hV2] at hj_sub hj2
                have hg1w : g₁ ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hi_sub, by omega⟩
                have hg2w : g₂ ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                exact Or.inl (card_ge3_of_three hg1w hg2w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen; simp at hlen

def B56 (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => 5 ≤ (V gates (13 + j)).card ∧ (V gates (13 + j)).card ≤ 6)

def B7 (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => (V gates (13 + j)).card = 7)

lemma card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

lemma triple_split (gates : List Gate) (w : Fin 13) (ht : HasTriple gates w) :
    (∃ j ∈ B56 gates, line w ⊆ V gates (13 + j)) ∨
    3 ≤ ((B7 gates).filter (fun j => line w ⊆ V gates (13 + j))).card := by
  obtain ⟨ga, gb, gc, ha_lt, hb_lt, hc_lt, ha_ss, hb_ss, hc_ss, hab, hac, hbc⟩ := ht
  set Da := V gates (13 + ga) \ line w
  set Db := V gates (13 + gb) \ line w
  set Dc := V gates (13 + gc) \ line w
  have ha_sub : line w ⊆ V gates (13 + ga) := ha_ss.subset
  have hb_sub : line w ⊆ V gates (13 + gb) := hb_ss.subset
  have hc_sub : line w ⊆ V gates (13 + gc) := hc_ss.subset
  have hra_pos : 1 ≤ Da.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset ha_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrb_pos : 1 ≤ Db.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hb_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrc_pos : 1 ≤ Dc.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hc_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hca : (V gates (13 + ga)).card = 4 + Da.card := by
    have hle := Finset.card_le_card ha_sub
    have hsd : Da.card = (V gates (13 + ga)).card - (line w).card := card_sdiff_eq ha_sub
    rw [card_line] at hsd hle; omega
  have hcb : (V gates (13 + gb)).card = 4 + Db.card := by
    have hle := Finset.card_le_card hb_sub
    have hsd : Db.card = (V gates (13 + gb)).card - (line w).card := card_sdiff_eq hb_sub
    rw [card_line] at hsd hle; omega
  have hcc : (V gates (13 + gc)).card = 4 + Dc.card := by
    have hle := Finset.card_le_card hc_sub
    have hsd : Dc.card = (V gates (13 + gc)).card - (line w).card := card_sdiff_eq hc_sub
    rw [card_line] at hsd hle; omega
  have hsum : Da.card + Db.card + Dc.card ≤ 9 := by
    have hsub : (Da ∪ Db) ∪ Dc ⊆ Finset.univ \ line w := by
      intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with (hx | hx) | hx
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hd_ab_c : Disjoint (Da ∪ Db) Dc := Finset.disjoint_union_left.mpr ⟨hac, hbc⟩
    have hc_u : ((Da ∪ Db) ∪ Dc).card = Da.card + Db.card + Dc.card := by
      rw [Finset.card_union_of_disjoint hd_ab_c, Finset.card_union_of_disjoint hab]
    have hc_comp : (Finset.univ \ line w).card = 9 := by
      rw [card_sdiff_eq (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, card_line]
    have := Finset.card_le_card hsub
    omega
  by_cases ha2 : Da.card ≤ 2
  · left
    exact ⟨ga, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, by omega, by omega⟩, ha_sub⟩
  · by_cases hb2 : Db.card ≤ 2
    · left
      exact ⟨gb, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, by omega, by omega⟩, hb_sub⟩
    · by_cases hc2 : Dc.card ≤ 2
      · left
        exact ⟨gc, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, by omega, by omega⟩, hc_sub⟩
      · right
        have ha7 : (V gates (13 + ga)).card = 7 := by omega
        have hb7 : (V gates (13 + gb)).card = 7 := by omega
        have hc7 : (V gates (13 + gc)).card = 7 := by omega
        have hne_ab : ga ≠ gb := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hab hp (by simpa [Da, Db, he] using hp)
        have hne_ac : ga ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hac hp (by simpa [Da, Dc, he] using hp)
        have hne_bc : gb ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hrb_pos
          exact Finset.disjoint_left.mp hbc hp (by simpa [Db, Dc, he] using hp)
        have hma : ga ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha7⟩, ha_sub⟩
        have hmb : gb ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, hb7⟩, hb_sub⟩
        have hmc : gc ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, hc7⟩, hc_sub⟩
        exact card_ge3_of_three hma hmb hmc hne_ab hne_ac hne_bc

end RowStructure

section SourcePlaneArcCharge

open PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.CircuitLowerBounds

namespace PlaneArcCharge

def Owner (w : Fin 13) (T : Finset (Fin 13)) : Prop :=
  (2 ≤ T.card ∧ T ⊆ line w) ∨
  (3 ≤ (T ∩ line w).card ∧ (T \ line w).card ≤ 1) ∨
  (line w ⊆ T ∧ T.card ≤ 6)

noncomputable def weight (w : Fin 13) (T : Finset (Fin 13)) : ℕ := by
  classical
  exact if Owner w T then 3 else if T.card = 7 ∧ line w ⊆ T then 1 else 0

lemma owner_card {w : Fin 13} {T : Finset (Fin 13)} (h : Owner w T) : T.card ≤ 6 := by
  rcases h with ⟨_,hs⟩ | ⟨_,hd⟩ | ⟨_,hc⟩
  · have hle := Finset.card_le_card hs
    rw [card_line] at hle
    omega
  · have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := line w))
    rw [card_line] at hle
    have := Finset.card_sdiff_add_card_inter T (line w)
    omega
  · exact hc

private lemma other_inter {i j : Fin 13} (hij : i ≠ j) (T : Finset (Fin 13)) :
    (T ∩ line j).card ≤ (T \ line i).card + 1 := by
  have sub : T ∩ line j ⊆ (T \ line i) ∪ (line i ∩ line j) := by
    intro p hp
    obtain ⟨ht,hj⟩ := Finset.mem_inter.mp hp
    by_cases hi : p ∈ line i
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi,hj⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht,hi⟩)
  have hle := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  simpa [card_inter_line i j hij] using hle

private lemma few_outside {i j : Fin 13} (hij : i ≠ j) {T : Finset (Fin 13)}
    (hd : (T \ line i).card ≤ 1) (hi : 2 ≤ (T ∩ line i).card) : ¬ Owner j T := by
  intro hj
  rcases hj with ⟨_,hs⟩ | ⟨hthree,_⟩ | ⟨hs,_⟩
  · have sub : T ∩ line i ⊆ line j ∩ line i := Finset.inter_subset_inter hs (by rfl)
    have h := Finset.card_le_card sub
    rw [card_inter_line j i hij.symm] at h
    omega
  · have := other_inter hij T
    omega
  · have h := other_inter hij T
    rw [Finset.inter_eq_right.mpr hs, card_line] at h
    omega

lemma owner_unique {i j : Fin 13} {T : Finset (Fin 13)}
    (hi : Owner i T) (hj : Owner j T) : i = j := by
  by_contra ne
  rcases hi with ⟨hc,hs⟩ | ⟨hc,hd⟩ | ⟨hs,hc⟩
  · exact few_outside ne (by simp [Finset.sdiff_eq_empty_iff_subset.mpr hs])
      (by rwa [Finset.inter_eq_left.mpr hs]) hj
  · exact few_outside ne hd (by omega) hj
  · rcases hj with ⟨h,ht⟩ | ⟨h,hd⟩ | ⟨ht,_⟩
    · have eq := line_eq_of_subset_two (S := line i) (by rfl) (hs.trans ht)
        (by rw [card_line]; omega)
      exact ne eq
    · exact few_outside (Ne.symm ne) hd (by omega) (Or.inr (Or.inr ⟨hs,hc⟩))
    · exact ne (line_eq_of_superset_le6 hs ht hc)

lemma weight_capacity (T : Finset (Fin 13)) : (∑ i : Fin 13, weight i T) ≤ 3 := by
  classical
  by_cases hex : ∃ i, Owner i T
  · obtain ⟨i,hi⟩ := hex
    have he : ∀ j : Fin 13, weight j T = if j = i then 3 else 0 := by
      intro j
      by_cases eq : j = i
      · subst j; simp [weight,hi]
      · have hn : ¬Owner j T := fun hj => eq (owner_unique hj hi)
        have hc : T.card ≠ 7 := by have := owner_card hi; omega
        simp [weight, hn, eq, hc]
    simp [he]
  · have hn : ∀ i, ¬ Owner i T := not_exists.mp hex
    by_cases h7 : T.card = 7
    · have eq : (∑ i : Fin 13, weight i T) =
          (Finset.univ.filter (fun i : Fin 13 => line i ⊆ T)).card := by
        simp [weight, hn, h7]
      rw [eq]
      have := lines_in_card7_le2 T h7
      omega
    · simp [weight, hn, h7]

lemma matching {γ : Type*} (pick : Fin 13 → γ) (rows points : γ → Finset (Fin 13))
    (rectangle : ∀ g i, i ∈ rows g → points g ⊆ line i)
    (diagonal : ∀ i, i ∈ rows (pick i) ∧ i ∈ points (pick i)) :
    Function.Injective pick := by
  intro i j eq
  by_contra ne
  have hj : j ∈ rows (pick i) ∧ j ∈ points (pick i) := eq ▸ diagonal j
  have big : 2 ≤ (points (pick i)).card :=
    Finset.one_lt_card.mpr ⟨i,(diagonal i).2,j,hj.2,ne⟩
  exact ne (line_eq_of_subset_two (rectangle _ i (diagonal i).1) (rectangle _ j hj.1) big)

def signature (gs : List Gate) (g : ℕ) : Finset (Fin 13) := V gs (13+g)

theorem baseline (gs : List Gate) (w : Fin 13) (g : ℕ) (U : Finset ℕ)
    (hg : g < gs.length)
    (valid : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2)
    (out : V gs (13+g) = line w) (safe : Safe w (wval gs (13+g)))
    (hG : GwUp gs w g ⊆ U) (h56 : B56 gs ⊆ U) (h7 : B7 gs ⊆ U) :
    9 ≤ ∑ k ∈ U, weight w (signature gs k) := by
  classical
  let G := GwUp gs w g
  let W := fun k => weight w (signature gs k)
  have gsum : (∑ k ∈ G, W k) = 3*G.card := by
    calc
      _ = ∑ _k ∈ G, 3 := Finset.sum_congr rfl (fun k hk => by
        have h := (Finset.mem_filter.mp hk).2
        have ho : Owner w (signature gs k) := Or.inl ⟨h.2,h.1⟩
        simp [W, weight, ho])
      _ = _ := by simp [mul_comm]
  have below (A : Finset ℕ) (ha : A ⊆ U) :
      (∑ k ∈ A, W k) ≤ ∑ k ∈ U, W k := Finset.sum_le_sum_of_subset ha
  rcases line_structure gs valid w g hg out safe with h | ⟨h,ht⟩
  · have z := below G hG
    rw [gsum] at z
    change 3 ≤ G.card at h
    change 9 ≤ ∑ k ∈ U, W k
    omega
  change 2 ≤ G.card at h
  have small (k) (hk : k ∈ G) : (signature gs k).card ≤ 4 := by
    have hc := Finset.card_le_card (Finset.mem_filter.mp hk).2.1
    simpa [signature, card_line] using hc
  rcases triple_split gs w ht with ⟨j,hj,hL⟩ | hmany
  · have hcard := (Finset.mem_filter.mp hj).2
    have hnot : j ∉ G := by
      intro hin
      have h4 := small j hin
      change (V gs (13+j)).card ≤ 4 at h4
      omega
    have ho : Owner w (signature gs j) := Or.inr (Or.inr ⟨hL,hcard.2⟩)
    have z := below (insert j G) (Finset.insert_subset (h56 hj) hG)
    rw [Finset.sum_insert hnot, gsum] at z
    have : W j = 3 := by simp [W, weight, ho]
    change 9 ≤ ∑ k ∈ U, W k
    omega
  · let B := (B7 gs).filter (fun k => line w ⊆ V gs (13+k))
    have dis : Disjoint G B := by
      refine Finset.disjoint_left.mpr ?_
      intro k hk hB
      have b := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2
      have s := small k hk
      change (V gs (13+k)).card ≤ 4 at s
      omega
    have bsum : B.card ≤ ∑ k ∈ B, W k := by
      calc
        _ = ∑ _k ∈ B, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k hk => by
          have b := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
          have inc := (Finset.mem_filter.mp hk).2
          have nc : ¬ Owner w (signature gs k) := by
            intro hown
            have six := owner_card hown
            change (V gs (13+k)).card ≤ 6 at six
            omega
          change ¬ Owner w (V gs (13+k)) at nc
          simp [W, weight, signature, nc, b, inc])
    have sub : B ⊆ U := (Finset.filter_subset _ _).trans h7
    have z := below (G ∪ B) (Finset.union_subset hG sub)
    rw [Finset.sum_union dis, gsum] at z
    change 3 ≤ B.card at hmany
    change 9 ≤ ∑ k ∈ U, W k
    omega

theorem global_bound {n r : ℕ} (skipped : Finset (Fin 13))
    (labels : Fin r → Finset (Fin 13)) (cost : r + 12 + skipped.card ≤ n)
    (per_row : ∀ i, (if i ∈ skipped then 9 else 12) ≤ ∑ k, weight i (labels k)) :
    64 ≤ n := by
  classical
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => per_row i)
  rw [Finset.sum_comm] at total
  have cap := Finset.sum_le_sum (s := Finset.univ) (fun k _ => weight_capacity (labels k))
  have terms : (∑ i : Fin 13, if i ∈ skipped then 9 else 12) + 3*skipped.card = 156 := by
    have split : ∀ i : Fin 13, (if i ∈ skipped then 9 else 12) + (if i ∈ skipped then 3 else 0) = 12 := by
      intro i; by_cases h : i ∈ skipped <;> simp [h]
    have := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 13))) rfl (fun i _ => split i)
    simpa [Finset.sum_add_distrib, Finset.sum_ite_mem, mul_comm] using this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at cap
  omega

end PlaneArcCharge

end SourcePlaneArcCharge

section SourceEmitter

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_17597_aux.RowStructure

namespace PlaneArcEmit

inductive Ref where
  | zero
  | one
  | wire (index : ℕ)
deriving DecidableEq

def Ref.val (gs : List Gate) (x : Fin 13 → Bool) : Ref → Bool
  | .zero => false
  | .one => true
  | .wire i => wval gs i x

def Ref.Valid (gs : List Gate) : Ref → Prop
  | .wire i => i < 13 + gs.length
  | _ => True

def GatesOk (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def binGate (isAnd : Bool) (a b : ℕ) : Gate :=
  ⟨if isAnd then .and else .or, [a,b]⟩

def boolOp (isAnd a b : Bool) := if isAnd then a && b else a || b

structure Result where
  added : List Gate
  ref : Ref

def pushWire (gs : List Gate) (isAnd : Bool) (a b : ℕ) : Result :=
  ⟨[binGate isAnd a b], .wire (13 + gs.length)⟩

def combine (gs : List Gate) (isAnd : Bool) (a b : Ref) : Result :=
  match isAnd, a, b with
  | true, .zero, _ | true, _, .zero => ⟨[], .zero⟩
  | true, .one, r | true, r, .one => ⟨[],r⟩
  | false, .one, _ | false, _, .one => ⟨[], .one⟩
  | false, .zero, r | false, r, .zero => ⟨[],r⟩
  | op, .wire u, .wire v => pushWire gs op u v

theorem prior_value (gs more : List Gate) {i : ℕ} (hi : i < 13 + gs.length) (x : Fin 13 → Bool) :
    wval (gs ++ more) i x = wval gs i x := by
  unfold wval
  rw [wiresFrom_append, getD_wiresFrom_lt]
  simpa [length_wiresFrom] using hi

theorem ref_weaken {r : Ref} {gs : List Gate} (more : List Gate) (h : Ref.Valid gs r) :
    Ref.Valid (gs ++ more) r := by
  cases r with
  | zero | one => trivial
  | wire i =>
    change i < 13 + gs.length at h
    change i < 13 + (gs ++ more).length
    simp only [List.length_append]; omega

theorem ref_stable {r : Ref} {gs : List Gate} (more : List Gate) (hr : Ref.Valid gs r)
    (x : Fin 13 → Bool) : Ref.val (gs ++ more) x r = Ref.val gs x r := by
  cases r with
  | zero | one => rfl
  | wire i => exact prior_value gs more hr x

theorem push_value (gs : List Gate) (isAnd : Bool) {i j : ℕ}
    (hi : i < 13 + gs.length) (hj : j < 13 + gs.length) (x : Fin 13 → Bool) :
    Ref.val (gs ++ (pushWire gs isAnd i j).added) x (pushWire gs isAnd i j).ref =
    boolOp isAnd (wval gs i x) (wval gs j x) := by
  let g := binGate isAnd i j
  change wval (gs ++ [g]) (13+gs.length) x = _
  have hk : gs.length < (gs ++ [g]).length := by simp
  have he := wval_gate_eq (gs ++ [g]) gs.length hk x
  have hget : (gs ++ [g])[gs.length] = g := by simp
  rw [he, hget]
  simp only [g, binGate, List.map_cons, List.map_nil, wvalAt, ite_eq_left hi, ite_eq_left hj,
    prior_value gs _ hi, prior_value gs _ hj]
  cases isAnd <;> simp [GateOp.eval, boolOp]

theorem combine_spec (gs : List Gate) (op : Bool) (a b : Ref)
    (ha : Ref.Valid gs a) (hb : Ref.Valid gs b) :
    let next := combine gs op a b
    Ref.Valid (gs ++ next.added) next.ref ∧ GatesOk next.added ∧ next.added.length ≤ 1 ∧
      ∀ x, Ref.val (gs ++ next.added) x next.ref =
        boolOp op (Ref.val gs x a) (Ref.val gs x b) := by
  cases op <;> cases a <;> cases b <;>
    simp_all [combine, Ref.Valid, Ref.val, GatesOk, boolOp, pushWire, binGate]
  all_goals intro x
  · exact push_value gs false ha hb x
  · exact push_value gs true ha hb x

def termSupport (gs : List Gate) (a b : Ref) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => Ref.val gs (e1 p) a && Ref.val gs (e1 p) b)

noncomputable def scale (gs : List Gate) (a b : Ref) : Result := by
  classical
  let T := termSupport gs a b
  exact if h : T.Nonempty then
    if T.card = 1 then ⟨[], .wire h.choose.val⟩ else combine gs true a b
  else ⟨[],.zero⟩

theorem ref_mono (gs : List Gate) (ok : GatesOk gs) (r : Ref) : MonoFun (fun x => Ref.val gs x r) := by
  cases r with
  | zero => simp [Ref.val, MonoFun]
  | one => simp [Ref.val, MonoFun]
  | wire i => exact wval_mono gs (fun g hg => (ok g hg).1) i

lemma support_iff (gs : List Gate) (a b : Ref) (p : Fin 13) :
    p ∈ termSupport gs a b ↔ Ref.val gs (e1 p) a = true ∧ Ref.val gs (e1 p) b = true := by
  simp [termSupport]

theorem scale_spec (gs : List Gate) (a b : Ref) (ok : GatesOk gs)
    (ha : Ref.Valid gs a) (hb : Ref.Valid gs b) :
    let next := scale gs a b
    Ref.Valid (gs ++ next.added) next.ref ∧ GatesOk next.added ∧ next.added.length ≤ 1 ∧
    (∀ x, Ref.val (gs ++ next.added) x next.ref = true →
        Ref.val gs x a = true ∧ Ref.val gs x b = true) ∧
    (∀ p, Ref.val (gs ++ next.added) (e1 p) next.ref =
        (Ref.val gs (e1 p) a && Ref.val gs (e1 p) b)) ∧
    ((termSupport gs a b).card ≤ 1 → next.added = []) := by
  classical
  let T := termSupport gs a b
  by_cases h : T.Nonempty
  · by_cases hc : T.card = 1
    · let p := h.choose
      have hp : p ∈ T := h.choose_spec
      have hs : T = {p} := (Finset.eq_of_subset_of_card_le
        (Finset.singleton_subset_iff.mpr hp) (by simp [hc])).symm
      have hv := (support_iff gs a b p).mp hp
      have he : scale gs a b = ⟨[], .wire p.val⟩ := by
        unfold scale
        change (if h' : T.Nonempty then if T.card = 1 then (⟨[], .wire h'.choose.val⟩ : Result) else combine gs true a b else ⟨[],.zero⟩) = _
        simp [h,hc,p]
      rw [he]
      refine ⟨by simpa [Ref.Valid] using (show p.val < 13 + gs.length by have := p.isLt; omega),
        by simp [GatesOk], by simp, ?_, ?_, fun _ => rfl⟩
      · intro x hx
        have hx' : x p = true := by simpa [Ref.val,wval_input _ _ p.isLt] using hx
        have hle : ∀ v, e1 p v = true → x v = true := by
          intro v hv
          have eq : v = p := by simpa [e1] using hv
          simpa [eq] using hx'
        exact ⟨ref_mono gs ok a _ _ hle hv.1, ref_mono gs ok b _ _ hle hv.2⟩
      · intro q
        apply Bool.eq_iff_iff.mpr
        simp only [List.append_nil, Ref.val, wval_input gs p p.isLt, e1, decide_eq_true_eq,
          Bool.and_eq_true]
        change p = q ↔ Ref.val gs (e1 q) a = true ∧ Ref.val gs (e1 q) b = true
        rw [← support_iff gs a b q]
        change p = q ↔ q ∈ T
        simp [hs, eq_comm]
    · have he : scale gs a b = combine gs true a b := by
        unfold scale
        change (if h' : T.Nonempty then if T.card = 1 then (⟨[], .wire h'.choose.val⟩ : Result) else combine gs true a b else ⟨[],.zero⟩) = _
        simp [h,hc]
      rw [he]
      obtain ⟨v,g,l,ev⟩ := combine_spec gs true a b ha hb
      refine ⟨v,g,l,fun x hx => ?_,fun p => ev (e1 p),fun h1 => ?_⟩
      · simpa [ev, boolOp] using hx
      · have hp := Finset.card_pos.mpr h
        change T.card ≤ 1 at h1
        omega
  · have he : scale gs a b = ⟨[],.zero⟩ := by
      unfold scale
      change (if h' : T.Nonempty then if T.card = 1 then (⟨[], .wire h'.choose.val⟩ : Result) else combine gs true a b else ⟨[],.zero⟩) = _
      simp [h]
    rw [he]
    refine ⟨trivial,by simp [GatesOk],by simp,by simp [Ref.val],?_,fun _ => rfl⟩
    intro p
    have hp : p ∉ termSupport gs a b := fun hm => h ⟨p,hm⟩
    rw [support_iff] at hp
    change false = (_ && _)
    simpa [Bool.and_eq_true] using hp

end PlaneArcEmit

end SourceEmitter

section SourceScalarAllocation

namespace PlaneArcTranspose

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.CircuitNormalization.Deg2
open PlaneArcEmit PEqualNP.Outside.L_meta_17597_aux.RowStructure

def LinearOp.cost : LinearOp → ℕ
  | .add _ _ | .scale _ _ => 1
  | .copy _ | .zero => 0

def opCost (ops : List Assignment) : ℕ := (ops.map (fun a => a.op.cost)).sum

private theorem cost_le_one (op : LinearOp) : op.cost ≤ 1 := by cases op <;> simp [LinearOp.cost]

private theorem alloc_step (D : Dag 13) (wf : D.WF) (w : ℕ) (hw : 26 ≤ w)
    (gs : List Gate) (refs : ℕ → Ref) (valid : ∀ r, Ref.Valid gs (refs r))
    (prior : ∀ r < w, D.deg r = 0 → ∀ x, Ref.val gs x (refs r) = D.val (pointOnly x) r) :
    ∃ step : Result, Ref.Valid (gs ++ step.added) step.ref ∧ GatesOk step.added ∧
      step.added.length + (codeAt D w).cost ≤ 1 ∧
      (D.deg w = 0 → ∀ x, Ref.val (gs ++ step.added) x step.ref = D.val (pointOnly x) w) := by
  by_cases hd : D.deg w = 0
  · cases hg : D.gateAt w with
    | none =>
      have hl : D.gates[w-(13+13)]? = none := by simpa [Dag.gateAt, hw] using hg
      refine ⟨⟨[], .zero⟩, trivial, by simp [GatesOk], by simp [codeAt,hg,LinearOp.cost], ?_⟩
      intro _ x
      simp [Ref.val, Dag.val, show ¬ w < 13+13 from by omega, hl]
    | some g =>
      cases g with
      | cst b =>
        obtain ⟨hlo, hl⟩ := Api.gateAt_some hg
        cases b with
        | false =>
          exact ⟨⟨[], .zero⟩, trivial, by simp [GatesOk],
              by simp [codeAt, hg, codeGate, LinearOp.cost],
              by intro _ x; simp [Ref.val, Dag.val, hlo.not_gt, hl]⟩
        | true =>
          exact ⟨⟨[], .one⟩, trivial, by simp [GatesOk],
              by simp [codeAt, hg, codeGate, LinearOp.cost],
              by intro _ x; simp [Ref.val, Dag.val, hlo.not_gt, hl]⟩
      | and a b =>
        have ha := wf w _ hg a (by simp [G.kids])
        have hb := wf w _ hg b (by simp [G.kids])
        have he := (Forms.deg_and hg ha hb).symm.trans hd
        have da : D.deg a = 0 := by omega
        have db : D.deg b = 0 := by omega
        obtain ⟨v, ok, cost, ev⟩ := combine_spec gs true (refs a) (refs b) (valid a) (valid b)
        refine ⟨combine gs true (refs a) (refs b), v, ok, ?_, ?_⟩
        · simpa [codeAt,hg,codeGate,da,db,LinearOp.cost] using cost
        · intro _ x
          simp only [ev, boolOp, ite_true, prior a ha da, prior b hb db, Forms.val_and hg ha hb]
      | or a b =>
        have ha := wf w _ hg a (by simp [G.kids])
        have hb := wf w _ hg b (by simp [G.kids])
        have he := (Forms.deg_or hg ha hb).symm.trans hd
        have da : D.deg a = 0 := by omega
        have db : D.deg b = 0 := by omega
        obtain ⟨v, ok, cost, ev⟩ := combine_spec gs false (refs a) (refs b) (valid a) (valid b)
        refine ⟨combine gs false (refs a) (refs b), v, ok, ?_, ?_⟩
        · simpa [codeAt,hg,codeGate,da,db,LinearOp.cost] using cost
        · intro _ x
          simp only [ev, boolOp, Bool.false_eq_true, ite_false, prior a ha da, prior b hb db,
            Forms.val_or hg ha hb]
  · exact ⟨⟨[],.zero⟩, trivial, by simp [GatesOk], by simpa using cost_le_one (codeAt D w),
      fun h => False.elim (hd h)⟩

theorem allocate_prefix (D : Dag 13) (wf : D.WF) (t : ℕ) :
    ∃ (gs : List Gate) (refs : ℕ → Ref), GatesOk gs ∧
      (∀ w, Ref.Valid gs (refs w)) ∧
      (∀ w < 26+t, D.deg w = 0 → ∀ x, Ref.val gs x (refs w) = D.val (pointOnly x) w) ∧
      gs.length + opCost (compilePrefix D t) ≤ t := by
  classical
  induction t with
  | zero =>
    let refs : ℕ → Ref := fun w => if w < 13 then .wire w else .zero
    refine ⟨[], refs, by simp [GatesOk], ?_, ?_, by simp [compilePrefix, opCost]⟩
    · intro w; by_cases h : w < 13 <;> simp [refs, h, Ref.Valid]
    · intro w hw _ x
      have hw' : w < 13+13 := by omega
      rw [circ_val_input D _ hw']
      by_cases hp : w < 13
      · rw [show refs w = .wire w by simp [refs,hp]]
        change wval [] w x = _
        rw [wval_input _ _ hp]
        change x ⟨w,hp⟩ = pointOnly x (Fin.castAdd 13 ⟨w,hp⟩)
        simp only [pointOnly, Fin.addCases_left]
      · rw [show refs w = .zero by simp [refs,hp]]
        let j : Fin 13 := ⟨w-13,by omega⟩
        have he : (⟨w,hw'⟩ : Fin (13+13)) = Fin.natAdd 13 j := Fin.ext (by dsimp [j]; omega)
        rw [he]
        simp only [Ref.val, pointOnly, Fin.addCases_right]
  | succ t ih =>
    obtain ⟨gs,refs,ok,valid,ev,cost⟩ := ih
    let w := 26+t
    obtain ⟨step, v', ok', co', ev'⟩ := alloc_step D wf w (by dsimp [w]; omega) gs refs valid ev
    let new : ℕ → Ref := fun r => if r = w then step.ref else refs r
    refine ⟨gs ++ step.added, new, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ok g hg
      · exact ok' g hg
    · intro r; by_cases hr : r = w
      · simpa [new,hr] using v'
      · simpa [new,hr] using ref_weaken step.added (valid r)
    · intro r hr hd x; by_cases he : r = w
      · subst r; simpa [new] using ev' hd x
      · simp only [new,ite_eq_right he,ref_stable _ (valid _) x]
        exact ev r (by dsimp [w] at he; omega) hd x
    · have hsum : opCost (compilePrefix D (t+1)) =
            opCost (compilePrefix D t) + (codeAt D w).cost := by
        simp [compilePrefix, opCost, w]
      rw [hsum, List.length_append]; omega

theorem allocate_scalars (D : Dag 13) (wf : D.WF) :
    ∃ (gs : List Gate) (refs : ℕ → Ref), GatesOk gs ∧
      (∀ w, Ref.Valid gs (refs w)) ∧
      (∀ w < 26+D.size, D.deg w = 0 → ∀ x, Ref.val gs x (refs w) = D.val (pointOnly x) w) ∧
      gs.length + opCost (compile D) ≤ D.size := allocate_prefix D wf D.size

private theorem scale_kid (deg : ℕ → ℕ) (g : G) {u s : ℕ} (h : codeGate deg g = .scale u s) :
    s ∈ g.kids ∧ deg s = 0 := by
  cases g <;> simp only [codeGate] at h
  all_goals (try split_ifs at h) <;> cases h <;> simp_all [G.kids]

private theorem prefix_scaled {N : ℕ} (D : Dag N) (wf : D.WF) (t : ℕ) (a : Assignment)
    (ha : a ∈ compilePrefix D t) {u s : ℕ} (hop : a.op = .scale u s) :
    s < a.dst ∧ a.dst < N+N+t ∧ D.deg s = 0 := by
  induction t with
  | zero => simp [compilePrefix] at ha
  | succ t ih =>
    rw [compilePrefix, List.mem_append] at ha
    rcases ha with hp | h
    · obtain ⟨h₁, h₂, h₃⟩ := ih hp
      exact ⟨h₁, by omega, h₃⟩
    · obtain rfl := List.mem_singleton.mp h
      change codeAt D (N+N+t) = .scale u s at hop
      cases hg : D.gateAt (N+N+t) with
      | none => simp [codeAt,hg] at hop
      | some g =>
        rw [codeAt,hg] at hop
        obtain ⟨mem, pure⟩ := scale_kid D.deg g hop
        exact ⟨wf _ _ hg _ mem, by dsimp; omega, pure⟩

theorem compiled_scale_source {N : ℕ} (D : Dag N) (wf : D.WF) (a : Assignment)
    (ha : a ∈ compile D) {u s : ℕ} (hop : a.op = .scale u s) :
    s < a.dst ∧ a.dst < N+N+D.size ∧ D.deg s = 0 :=
  prefix_scaled D wf D.size a ha hop

theorem forward_read_congr (ops : List Assignment) {s₁ s₂ : ℕ → Prop}
    (h : ∀ a ∈ ops, ∀ u s, a.op = .scale u s → (s₁ s ↔ s₂ s)) (state : ℕ → Prop) :
    forward s₁ ops state = forward s₂ ops state := by
  induction ops generalizing state with
  | nil => rfl
  | cons a tail ih =>
    change forward s₁ tail (a.push s₁ state) = forward s₂ tail (a.push s₂ state)
    have he : a.push s₁ state = a.push s₂ state := by
      funext w
      unfold Assignment.push
      cases hg : a.op with
      | scale u s => simp only [LinearOp.eval, propext (h a (by simp) u s hg)]
      | add u v | copy u | zero => rfl
    rw [he]; exact ih (fun b hb => h b (by simp [hb])) _

theorem physical_coefficients (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdeg : HasLineDegree 26 (Finset.Ico 13 26) C 1) (hw : C.output < 26+C.size) :
    let D := ofCircuit 13 C
    ∃ (gs : List Gate) (refs : ℕ → Ref), GatesOk gs ∧ (∀ w, Ref.Valid gs (refs w)) ∧
      gs.length + opCost (compile D) ≤ C.size ∧
      ∀ (x : Fin 13 → Bool) (i : Fin 13), C.eval (List.ofFn (pointOnly x)) = false →
        (C.eval (List.ofFn (oneLine x i)) = true ↔
          forward (fun s => Ref.val gs x (refs s) = true) (compile D) (fun w => w = 13+i.val) C.output) := by
  let D := ofCircuit 13 C
  have wf : D.WF := Api.card03b_wf C
  obtain ⟨gs, refs, ok, valid, correct, bound⟩ := allocate_scalars D wf
  refine ⟨gs, refs, ok, valid, ?_, ?_⟩
  · simpa only [D, Api.card03a_size] using bound
  · intro x i off
    have he := circuit_coefficient C x i mono hdeg hw off
    have same : forward (pointScalar D x) (compile D) (fun w => w = 13+i.val) =
        forward (fun s => Ref.val gs x (refs s) = true) (compile D) (fun w => w = 13+i.val) := by
      apply forward_read_congr
      intro a ha u s hop
      obtain ⟨hlt,hlt',hpure⟩ := compiled_scale_source D wf a ha hop
      rw [correct s (hlt.trans hlt') hpure]
      rfl
    change C.eval (List.ofFn (oneLine x i)) = true ↔
        forward (pointScalar D x) (compile D) (fun w => w = 13+i.val) C.output at he
    rw [same] at he
    exact he

end PlaneArcTranspose

end SourceScalarAllocation

section SourceFirstMultiplier

namespace PlaneArcFirst

open PlaneArcTranspose

def disabled : ℕ → Prop := fun _ => False

lemma eval_mono (op : LinearOp) {f g a b : ℕ → Prop}
    (hf : ∀ i, f i → g i) (ha : ∀ i, a i → b i) :
    op.eval f a → op.eval g b := by
  cases op with
  | add u v => exact Or.imp (ha u) (ha v)
  | scale u s => exact And.imp (ha u) (hf s)
  | copy u => exact ha u
  | zero => exact id

lemma push_mono (a : Assignment) {f g x y : ℕ → Prop}
    (hf : ∀ i, f i → g i) (hx : ∀ i, x i → y i) :
    ∀ w, a.push f x w → a.push g y w := by
  intro w
  by_cases eq : w = a.dst
  · simpa [Assignment.push, eq] using (eval_mono a.op hf hx)
  · simpa [Assignment.push, eq] using hx w

lemma forward_mono (ops : List Assignment) {f g x y : ℕ → Prop}
    (hf : ∀ i, f i → g i) (hx : ∀ i, x i → y i) :
    ∀ w, forward f ops x w → forward g ops y w := by
  induction ops generalizing x y with
  | nil => exact hx
  | cons a l ih => exact ih (push_mono a hf hx)

structure Cut (ops : List Assignment) where
  pre : List Assignment
  a : Assignment
  post : List Assignment
  ordered : ops = pre ++ a :: post

def Cut.idx {ops} (k : Cut ops) : Fin ops.length :=
  ⟨k.pre.length, lt_of_lt_of_eq (b := (k.pre ++ k.a :: k.post).length)
    (by simp) (congrArg List.length k.ordered.symm)⟩

lemma Cut.idx_injective (ops) : Function.Injective (Cut.idx (ops := ops)) := by
  rintro ⟨p,a,q,h⟩ ⟨p',a',q',h'⟩ he
  have hl : p.length = p'.length := congrArg Fin.val he
  have eq : p ++ a :: q = p' ++ a' :: q' := h.symm.trans h'
  have hp := congrArg (List.take p.length) eq
  have lhs : (p ++ a :: q).take p.length = p := by simp
  have rhs : (p' ++ a' :: q').take p.length = p' := by rw [hl]; simp
  rw [lhs,rhs] at hp
  subst p'
  have rest := List.append_cancel_left eq
  obtain ⟨rfl,rfl⟩ := List.cons.inj rest
  rfl

def Cut.raw {ops} (k : Cut ops) (src : ℕ) : Prop :=
  ∃ u s, k.a.op = .scale u s ∧ forward disabled k.pre (fun w => w = src) u

def Cut.active {ops} (k : Cut ops) (scalar : ℕ → Prop) (out : ℕ) : Prop :=
  ∃ u s, k.a.op = .scale u s ∧ scalar s ∧
    reverse scalar k.post (fun w => w = out) k.a.dst

theorem trace_first (ops : List Assignment) (scalar state demand : ℕ → Prop)
    (yes : ∃ w, demand w ∧ forward scalar ops state w)
    (no : ¬ ∃ w, demand w ∧ forward disabled ops state w) :
    ∃ (k : Cut ops) (u s : ℕ), k.a.op = .scale u s ∧ forward disabled k.pre state u ∧
      scalar s ∧ reverse scalar k.post demand k.a.dst := by
  classical
  induction ops generalizing state with
  | nil => exact False.elim (no yes)
  | cons a rest ih =>
    by_cases mixed : ∃ w, demand w ∧ forward scalar rest (a.push disabled state) w
    · obtain ⟨k,u,s,ho,hpre,hscalar,hsuf⟩ := ih _ mixed no
      exact ⟨⟨a :: k.pre,k.a,k.post,by simpa using congrArg (List.cons a) k.ordered⟩,
        u,s,ho,hpre,hscalar,hsuf⟩
    · have y := (transpose rest scalar (a.push scalar state) demand).mp yes
      have n : ¬ ∃ w, reverse scalar rest demand w ∧ a.push disabled state w :=
        fun h => mixed ((transpose rest scalar (a.push disabled state) demand).mpr h)
      obtain ⟨w, hsuf, hval⟩ := y
      have eq : w = a.dst := by
        by_contra ne
        exact n ⟨w, hsuf, by simpa [Assignment.push, ne] using hval⟩
      subst w
      have eg : a.op.eval scalar state := by simpa [Assignment.push] using hval
      have en : ¬ a.op.eval disabled state := fun h =>
        n ⟨a.dst, hsuf, by simpa [Assignment.push] using h⟩
      cases ho : a.op with
      | add u v => exact False.elim (en (by simpa [ho,LinearOp.eval] using eg))
      | copy u => exact False.elim (en (by simpa [ho,LinearOp.eval] using eg))
      | zero => exact False.elim (by simpa [ho,LinearOp.eval] using eg)
      | scale u s =>
        obtain ⟨hv,hscalar⟩ : state u ∧ scalar s := by simpa [ho,LinearOp.eval] using eg
        exact ⟨⟨[],a,rest,rfl⟩,u,s,ho,hv,hscalar,hsuf⟩

theorem combine {ops} (k : Cut ops) (src out : ℕ) (scalar : ℕ → Prop)
    (hr : k.raw src) (hp : k.active scalar out) :
    forward scalar ops (fun i => i = src) out := by
  obtain ⟨u,s,ho,hraw⟩ := hr
  obtain ⟨u',s',ho',hs,hpath⟩ := hp
  obtain ⟨rfl,rfl⟩ := LinearOp.scale.inj (ho.symm.trans ho')
  have pref : forward scalar k.pre (fun i => i = src) u :=
    forward_mono k.pre (fun _ h => False.elim h) (fun _ h => h) u hraw
  let st := forward scalar k.pre (fun i => i = src)
  have pushed : k.a.push scalar st k.a.dst :=
    by simpa [Assignment.push,ho,LinearOp.eval,st] using And.intro pref hs
  have tail := (transpose k.post scalar (k.a.push scalar st) (fun w => w = out)).mpr
    ⟨k.a.dst,hpath,pushed⟩
  obtain ⟨_,rfl,good⟩ := tail
  rw [k.ordered]
  simpa [forward, List.foldl_append, st] using good

theorem scale_cover {ι : Type*} (ops : List Assignment) (src : ι → ℕ) (out : ℕ)
    (scalar : ι → ℕ → Prop) (M : ι → ι → Prop)
    (sound : ∀ i p, forward (scalar p) ops (fun w => w = src i) out → M i p)
    (diag : ∀ i, forward (scalar i) ops (fun w => w = src i) out)
    (missing : ∀ i, ∃ p, ¬ M i p) :
    (∀ (k : Cut ops) i p, k.raw (src i) → k.active (scalar p) out → M i p) ∧
    (∀ i, ∃ k : Cut ops, k.raw (src i) ∧ k.active (scalar i) out) := by
  constructor
  · intro k i p hr ha
    exact sound i p (combine k _ _ _ hr ha)
  · intro i
    obtain ⟨p,neg⟩ := missing i
    have no : ¬ forward disabled ops (fun w => w = src i) out :=
      fun y => neg (sound i p (forward_mono ops (fun _ h => False.elim h) (fun _ h => h) out y))
    have ey : ∃ w, (w = out) ∧ forward (scalar i) ops (fun w => w = src i) w :=
      ⟨out, rfl, diag i⟩
    have en : ¬ ∃ w, (w = out) ∧ forward disabled ops (fun w => w = src i) w := by
      rintro ⟨_,rfl,h⟩
      exact no h
    obtain ⟨k,u,s,ho,hw,hp,hr⟩ := trace_first ops (scalar i) _ _ ey en
    exact ⟨k,⟨u,s,ho,hw⟩,⟨u,s,ho,hp,hr⟩⟩

def isScale (a : Assignment) : Bool :=
  match a.op with
  | .scale _ _ => true
  | _ => false

theorem Cut.get_idx {ops} (k : Cut ops) : ops[k.idx] = k.a := by
  obtain ⟨pre,a,post,rfl⟩ := k
  simp [Cut.idx]

theorem count_scales {ι : Type*} [Fintype ι] (ops : List Assignment)
    (src : ι → ℕ) (out : ℕ) (scalar : ι → ℕ → Prop) (M : ι → ι → Prop)
    (sound : ∀ i p, forward (scalar p) ops (fun w => w = src i) out → M i p)
    (diag : ∀ i, forward (scalar i) ops (fun w => w = src i) out)
    (missing : ∀ i, ∃ p, ¬ M i p) (cross : ∀ i j, M i j → M j i → i = j) :
    Fintype.card ι ≤ (Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])).card := by
  classical
  obtain ⟨hr,hd⟩ := scale_cover ops src out scalar M sound diag missing
  choose pick hraw hact using hd
  let B := Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])
  have mem (i : ι) : (pick i).idx ∈ B := by
    obtain ⟨u,s,ho,_⟩ := hraw i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change isScale ops[(pick i).idx] = true
    rw [Cut.get_idx]
    simp [isScale,ho]
  let f : ι → B := fun i => ⟨(pick i).idx,mem i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have eq := Cut.idx_injective ops (show (pick i).idx = (pick j).idx from
      congrArg Subtype.val hij)
    exact cross i j (hr (pick i) _ _ (hraw i) (eq ▸ hact j))
      (hr (pick j) j i (hraw j) (by rw [←eq]; exact hact i))
  calc
    Fintype.card ι ≤ Fintype.card B := Fintype.card_le_of_injective f hinj
    _ = B.card := Fintype.card_coe B

end PlaneArcFirst

end SourceFirstMultiplier

section SourcePlaneCount

namespace PlaneArcFirst

open PlaneArcTranspose

abbrev Incident (w p : Fin 13) : Prop :=
  ∃ d : ℕ, d ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (w.val + d) % 13 = p.val

def incDec (w p : Fin 13) : Decidable (Incident w p) := by
  unfold Incident
  infer_instance

theorem plane_scales (ops : List Assignment) (src : Fin 13 → ℕ) (out : ℕ)
    (scalar : Fin 13 → ℕ → Prop)
    (sound : ∀ i p, forward (scalar p) ops (fun w => w = src i) out → Incident i p)
    (diag : ∀ i, forward (scalar i) ops (fun w => w = src i) out) :
    13 ≤ (Finset.univ.filter (fun j : Fin ops.length => isScale ops[j])).card := by
  letI : DecidableRel Incident := incDec
  have missing : ∀ i, ∃ p, ¬ Incident i p := by decide
  have cross : ∀ i j, Incident i j → Incident j i → i = j := by decide
  simpa using count_scales ops src out scalar Incident sound diag missing cross

end PlaneArcFirst

end SourcePlaneCount

section SourceRowCharges

namespace ArcTerminal

variable {α : Type*} [DecidableEq α]

def Own (L T : Finset α) :=
  (2 ≤ T.card ∧ T ⊆ L) ∨ (3 ≤ (T ∩ L).card ∧ (T \ L).card ≤ 1) ∨
  (L ⊆ T ∧ T.card ≤ 6)

def tagged (L : Finset α) (G : Finset ℕ) (V : ℕ → Finset α) (i : ℕ) :=
  i ∈ G ∧ Own L (V i)

lemma low {L T : Finset α} (hc : 2 ≤ T.card) (hsub : T ⊆ L) : Own L T :=
  Or.inl ⟨hc,hsub⟩

lemma four {L : Finset α} {G : Finset ℕ} {V : ℕ → Finset α}
    {a b c d : ℕ} (ha : tagged L G V a) (hb : tagged L G V b)
    (hc : tagged L G V c) (hd : tagged L G V d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ H : Finset ℕ, H ⊆ G ∧ H.card = 4 ∧ ∀ z ∈ H, Own L (V z) := by
  refine ⟨{a,b,c,d}, ?_, by simp [hab,hac,had,hbc,hbd,hcd], ?_⟩
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [ha.1,hb.1,hc.1,hd.1]
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [ha.2,hb.2,hc.2,hd.2]

abbrev FourOwned (L : Finset α) (G : Finset ℕ) (V : ℕ → Finset α) :=
  ∃ H : Finset ℕ, H ⊆ G ∧ H.card = 4 ∧ ∀ z ∈ H, Own L (V z)

theorem size_two {L : Finset α} {G : Finset ℕ} {V : ℕ → Finset α}
    {B T O : ℕ} (hG : ∀ k, 2 ≤ (V k).card → k ∈ G)
    (hL : L.card = 4) (hO : V O = L) (ht : (V T).card = 2)
    (htb : V T ⊆ V B) (hb : V B ⊆ L) (hbt : B<T) (hto : T<O)
    (hpath : (∃ U, T<U ∧ U<O ∧ V T ⊆ V U ∧ V U ⊆ L) ∨
      ∃ U, U<O ∧ V O = V T ∪ V U ∧ U ≠ B) :
    FourOwned L G V := by
  have vtc : 2 ≤ (V T).card := ht.ge
  have vbc := vtc.trans (Finset.card_le_card htb)
  have voc : 2 ≤ (V O).card := by rw [hO,hL]; decide
  have btag : tagged L G V B := ⟨hG _ vbc, low vbc hb⟩
  have ttag : tagged L G V T := ⟨hG _ vtc, low vtc (htb.trans hb)⟩
  have otag : tagged L G V O := ⟨hG _ voc, low voc hO.le⟩
  rcases hpath with ⟨U,htu,huo,htU,hu⟩ | ⟨U,huo,hu,hub⟩
  · have huc := vtc.trans (Finset.card_le_card htU)
    have utag : tagged L G V U := ⟨hG _ huc, low huc hu⟩
    exact four btag ttag utag otag (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · have huc : 2 ≤ (V U).card := by
      have hc := Finset.card_union_le (V T) (V U)
      rw [←hu,hO,hL,ht] at hc
      omega
    have hsub : V U ⊆ L := hO ▸ hu ▸ Finset.subset_union_right
    have hut : U ≠ T := by
      rintro rfl
      rw [Finset.union_idempotent] at hu
      have hh := congrArg Finset.card hu
      rw [ht,hO,hL] at hh
      omega
    exact four btag ttag ⟨hG _ huc,low huc hsub⟩ otag (by omega) hub.symm
      (by omega) hut.symm (by omega) (by omega)

theorem size_three {L : Finset α} {G : Finset ℕ} {V : ℕ → Finset α}
    {A B T O : ℕ} (hG : ∀ k, 2 ≤ (V k).card → k ∈ G)
    (hL : L.card = 4) (hO : V O = L) (ht : (V T).card = 3)
    (htb : V T ⊆ V B) (hb : V B ⊆ L) (hbt : B<T) (hto : T<O)
    (hre : (∃ U, U<B ∧ 2 ≤ (V U).card ∧ V U ⊆ L) ∨
      (A ≠ B ∧ A<T ∧ V T ⊆ V A ∧ (V A \ L).card ≤ 1)) :
    FourOwned L G V := by
  have vtc : 2 ≤ (V T).card := by omega
  have vbc := vtc.trans (Finset.card_le_card htb)
  have voc : 2 ≤ (V O).card := by rw [hO,hL]; decide
  have btag : tagged L G V B := ⟨hG _ vbc, low vbc hb⟩
  have ttag : tagged L G V T := ⟨hG _ vtc, low vtc (htb.trans hb)⟩
  have otag : tagged L G V O := ⟨hG _ voc, low voc hO.le⟩
  rcases hre with ⟨U,hub,huc,hu⟩ | ⟨hab,hat,hta,ha⟩
  · exact four ⟨hG _ huc,low huc hu⟩ btag ttag otag (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · have ac := Finset.card_le_card (Finset.subset_inter hta (htb.trans hb))
    have vAc := vtc.trans (Finset.card_le_card hta)
    have atag : tagged L G V A := ⟨hG _ vAc, Or.inr (Or.inl ⟨by omega,ha⟩)⟩
    exact four atag btag ttag otag hab (by omega) (by omega)
      (by omega) (by omega) (by omega)

theorem size_four_irreducible {L : Finset α} {G : Finset ℕ} {V : ℕ → Finset α}
    {A B T U : ℕ} (hG : ∀ k, 2 ≤ (V k).card → k ∈ G)
    (hL : L.card = 4) (ht : V T = L) (hb : V B = L) (ha : L ⊆ V A)
    (ha1 : (V A \ L).card ≤ 1) (hab : A ≠ B) (hat : A<T) (hbt : B<T)
    (hu : U<B ∧ U ≠ A ∧ ((2 ≤ (V U).card ∧ V U ⊆ L) ∨
      (L ⊆ V U ∧ (V U).card ≤ 6))) :
    FourOwned L G V := by
  have hcL : 2 ≤ L.card := by omega
  have vtc : 2 ≤ (V T).card := ht ▸ hcL
  have vbc : 2 ≤ (V B).card := hb ▸ hcL
  have vac := hcL.trans (Finset.card_le_card ha)
  have eo : V A ∩ L = L := Finset.inter_eq_right.mpr ha
  have atag : tagged L G V A := ⟨hG _ vac, Or.inr (Or.inl ⟨by rw [eo,hL]; decide,ha1⟩)⟩
  have btag : tagged L G V B := ⟨hG _ vbc,low vbc hb.le⟩
  have ttag : tagged L G V T := ⟨hG _ vtc,low vtc ht.le⟩
  obtain ⟨hub,hua,hh⟩ := hu
  have utag : tagged L G V U := by
    rcases hh with ⟨hc,hl⟩ | ⟨hl,hc⟩
    · exact ⟨hG _ hc,low hc hl⟩
    · exact ⟨hG _ (hcL.trans (Finset.card_le_card hl)),Or.inr (Or.inr ⟨hl,hc⟩)⟩
  exact four utag atag btag ttag hua (by omega) (by omega) hab (by omega) (by omega)

def PairSafe (L : Finset α) (f : Finset α → Prop) :=
  ∀ x : Finset α, x.card ≤ 2 → Disjoint x L → ¬ f x

lemma prime_pair {L : Finset α} {F G : Finset α → Prop} {U V : Finset α}
    (hmF : Monotone F) (hmG : Monotone G)
    (hU : ∀ p, p ∈ U ↔ F {p}) (hV : ∀ p, p ∈ V ↔ G {p})
    (hs : PairSafe L (fun x => F x ∧ G x)) : U ⊆ L ∨ V ⊆ L := by
  by_contra! bad
  obtain ⟨hu,hv⟩ := bad
  obtain ⟨u,hu,hul⟩ := Finset.not_subset.mp hu
  obtain ⟨v,hv,hvl⟩ := Finset.not_subset.mp hv
  have hd : Disjoint ({u,v} : Finset α) L := by simp [hul,hvl]
  have hF : F {u,v} := hmF (Finset.singleton_subset_iff.mpr (by simp)) ((hU _).mp hu)
  have hG : G {u,v} := hmG (Finset.singleton_subset_iff.mpr (by simp)) ((hV _).mp hv)
  exact hs _ Finset.card_le_two hd ⟨hF,hG⟩

theorem safe_child {L : Finset α} {F : ℕ → Finset α → Prop} {V : ℕ → Finset α}
    {B k h : ℕ} (hs : PairSafe L (F B)) (hB : V B ⊆ L) (hc : 3 ≤ (V B).card)
    (hmon : ∀ w, Monotone (F w)) (hv : ∀ w p, p ∈ V w ↔ F w {p})
    (hk : k<B) (hh : h<B)
    (hop : (∀ x, F B x ↔ F k x ∧ F h x) ∨ (∀ x, F B x ↔ F k x ∨ F h x)) :
    ∃ U, U<B ∧ 2 ≤ (V U).card ∧ V U ⊆ L := by
  rcases hop with he | he
  · have hVB : V B = V k ∩ V h := by ext p; simp [hv,he]
    have hpk : V B ⊆ V k := hVB ▸ Finset.inter_subset_left
    have hph : V B ⊆ V h := hVB ▸ Finset.inter_subset_right
    rcases prime_pair (hmon k) (hmon h) (hv k) (hv h)
      (fun x h1 h2 hh => hs x h1 h2 ((he x).mpr hh)) with hkl | hhl
    · exact ⟨k,hk,(by omega : 2 ≤ (V B).card) |>.trans (Finset.card_le_card hpk),hkl⟩
    · exact ⟨h,hh,(by omega : 2 ≤ (V B).card) |>.trans (Finset.card_le_card hph),hhl⟩
  · have hVB : V B = V k ∪ V h := by ext p; simp [hv,he]
    have hsum := Finset.card_union_le (V k) (V h)
    rw [←hVB] at hsum
    by_cases hk2 : 2 ≤ (V k).card
    · exact ⟨k,hk,hk2,(by rw [hVB] at hB; exact Finset.subset_union_left.trans hB)⟩
    · exact ⟨h,hh,by omega,(by rw [hVB] at hB; exact Finset.subset_union_right.trans hB)⟩

end ArcTerminal

end SourceRowCharges

section SourceAffineCut

namespace ArcAffineCut
open PEqualNP.Outside.L_meta_17597_aux.RowStructure

abbrev P := Fin 13
abbrev Arc (x : Finset P) := ∀ w : P, (line w ∩ x).card ≤ 2

def Morph (f : P → P) : Prop :=
  Function.Injective f ∧ ∀ w, ∃ k, (line w).image f = line k

lemma morph_comp {f g : P → P} (hf : Morph f) (hg : Morph g) : Morph (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro w
  obtain ⟨k,hk⟩ := hf.2 w
  obtain ⟨j,hj⟩ := hg.2 k
  exact ⟨j,by rw [←Finset.image_image,hk,hj]⟩

lemma arc_of_image {f : P → P} (hf : Morph f) {x : Finset P} (hx : Arc (x.image f)) : Arc x := by
  intro w
  obtain ⟨j,hj⟩ := hf.2 w
  have h := hx j
  rw [←hj,←Finset.image_inter _ _ hf.1,Finset.card_image_of_injective _ hf.1] at h
  exact h

def aMap : P → P := ![0,1,4,3,10,6,8,11,5,9,2,12,7]
def bMap : P → P := ![9,3,2,0,5,12,4,10,6,1,11,8,7]
def aLines : P → P := ![0,1,3,7,10,5,8,2,9,6,12,11,4]
def bLines : P → P := ![0,2,12,4,9,3,1,10,5,11,8,7,6]

lemma ma : Morph aMap := by
  refine ⟨by decide +kernel,fun w => ⟨aLines w,?_⟩⟩
  revert w
  decide +kernel

lemma mb : Morph bMap := by
  refine ⟨by decide +kernel,fun w => ⟨bLines w,?_⟩⟩
  revert w
  decide +kernel

def move : List Bool → P → P
  | [], p => p
  | false :: xs, p => aMap (move xs p)
  | true :: xs, p => bMap (move xs p)

lemma movement (xs : List Bool) : Morph (move xs) ∧ (line 0).image (move xs) = line 0 := by
  induction xs with
  | nil => exact ⟨⟨Function.injective_id,fun k => ⟨k,by simp [move]⟩⟩,by simp [move]⟩
  | cons a xs ih =>
    cases a
    · refine ⟨morph_comp ih.1 ma,?_⟩
      change (line 0).image (aMap ∘ move xs) = _
      rw [←Finset.image_image,ih.2]
      decide +kernel
    · refine ⟨morph_comp ih.1 mb,?_⟩
      change (line 0).image (bMap ∘ move xs) = _
      rw [←Finset.image_image,ih.2]
      decide +kernel

def code : P → P → List Bool := ![
  ![[], [], [], [], [], [], [], [], [], [], [], [], []],
  ![[], [], [], [], [], [], [], [], [], [], [], [], []],
  ![[], [], [], [], [], [true,true,true,true,true,true,true], [true], [true,true,true,true,true], [true,true], [], [true,true,true,true], [true,true,true], [true,true,true,true,true,true]],
  ![[], [], [], [], [], [], [], [], [], [], [], [], []],
  ![[], [], [false,true,true,true,true], [], [], [true,true,false,false], [true,true,true,false,true,true,true,true], [true,true,false,true,true,true,true], [true,false,false], [], [false,false], [true,false,true,true,true,true], [false,true,false,true,true]],
  ![[], [], [false,true,true,true], [], [true,true,true,false,true,true,true], [], [true,true,true,true,true,false,true,true,true], [false,true,false,true], [true,false,true,true,true], [], [true,true,false,true,true,true], [true,true,true,true,false,true,true,true], [false,false,true,false]],
  ![[], [], [false,true,true,true,true,true], [], [true,true,false,false,true], [false,true,false,true,true,true], [], [false,false,true], [true,true,true,false,true,true,true,true,true], [], [true,false,true,true,true,true,true], [true,false,false,true], [true,true,false,true,true,true,true,true]],
  ![[], [], [false,true], [], [true,false,true], [true,true,true,true,true,false,true], [true,true,true,true,false,true], [], [true,true,false,true], [], [true,true,true,true,true,true,false,true], [true,true,true,true,true,true,true,false,true], [true,true,true,false,true]],
  ![[], [], [false,true,true,true,true,true,true], [], [false,true,false,true,true,true,true], [true,true,false,true,true,true,true,true,true], [true,false,true,true,true,false], [true,false,true,true,true,true,true,true], [], [], [false,true,true,true,false], [false,false,true,false,false], [false,false,true,true]],
  ![[], [], [], [], [], [], [], [], [], [], [], [], []],
  ![[], [], [false], [], [true,true,true,true,false], [true,false], [true,true,false], [true,true,true,false], [true,true,true,true,true,true,true,false], [], [], [true,true,true,true,true,true,false], [true,true,true,true,true,false]],
  ![[], [], [false,true,true,true,true,true,true,true], [], [false,true,false,false], [false,false,true,true,true], [false,true,false,true,true,true,true,true], [false,true,true,true,false,true], [true,false,true,true,true,false,true], [], [false,true,true,false], [], [true,false,true,true,true,true,true,true,true]],
  ![[], [], [false,true,true], [], [true,true,true,true,true,false,true,true], [true,true,true,false,true,true], [true,false,true,true], [true,true,true,true,true,true,false,true,true], [true,true,true,true,false,true,true], [], [false,true,false], [true,true,false,true,true], []]]

lemma code_ok : ∀ a b : P, a ∉ line 0 → b ∉ line 0 → a ≠ b →
    move (code a b) a = 2 ∧ move (code a b) b = 4 := by decide +kernel

lemma rotate_lines : ∀ w i : P, (line i).image (fun p => p-w) = line (i-w) := by decide +kernel

lemma normalize (w a b : P) (ha : a ∉ line w) (hb : b ∉ line w) (hne : a ≠ b) :
    ∃ f : P → P, Morph f ∧ (line w).image f = line 0 ∧ f a = 2 ∧ f b = 4 := by
  let r : P → P := fun p => p-w
  have rinj : Function.Injective r := fun _ _ h => sub_left_injective h
  have rim : ∀ i : P, (line i).image r = line (i-w) := rotate_lines w
  have rz : (line w).image r = line 0 := by simpa using rim w
  have off (p : P) (h : p ∉ line w) : r p ∉ line 0 := by
    intro hh
    rw [←rz] at hh
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hh
    exact h (rinj he ▸ hk)
  have h₁ := off a ha
  have h₂ := off b hb
  let xs := code (r a) (r b)
  have hc := code_ok (r a) (r b) h₁ h₂ (fun e => hne (rinj e))
  exact ⟨move xs ∘ r,morph_comp ⟨rinj,fun i => ⟨i-w,rim i⟩⟩ (movement xs).1,
    by rw [←Finset.image_image,rz,(movement xs).2],hc.1,hc.2⟩

abbrev fail (u v : P) : Prop := ¬ Arc {2,4,u,v}

set_option maxHeartbeats 12000000 in
lemma canonical_common : ∀ u r : P, u ∉ line 0 → r ∉ line 0 → u ≠ 10 → r ≠ 10 → u ≠ r →
    (Finset.univ.filter (fun v : P => v ∉ line 0 ∧ fail u v ∧ fail r v)).card ≤ 2 := by
  decide +kernel

lemma canonical {U V : Finset P} (hu : 3 ≤ U.card) (hv : 3 ≤ V.card)
    (huo : Disjoint U (line 0)) (hvo : Disjoint V (line 0)) :
    ∃ u ∈ U, ∃ v ∈ V, Arc {2,4,u,v} := by
  by_contra! h
  have huer : 1 < (U.erase 10).card := by
    by_cases he : (10:P) ∈ U
    · rw [Finset.card_erase_of_mem he]; omega
    · rw [Finset.erase_eq_of_notMem he]; omega
  obtain ⟨u,hu',r,hr',hneq⟩ := Finset.one_lt_card.mp huer
  obtain ⟨hu10,hU⟩ := Finset.mem_erase.mp hu'
  obtain ⟨hr10,hR⟩ := Finset.mem_erase.mp hr'
  have hk := canonical_common u r (Finset.disjoint_left.mp huo hU)
    (Finset.disjoint_left.mp huo hR) hu10 hr10 hneq
  have hs : V ⊆ Finset.univ.filter (fun v : P => v ∉ line 0 ∧ fail u v ∧ fail r v) := by
    intro v hv'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hvo hv',h u hU v hv',h r hR v hv'⟩
  have := Finset.card_le_card hs
  omega

theorem affine_cut (w a b : P) (ha : a ∉ line w) (hb : b ∉ line w) (hne : a ≠ b)
    {U V : Finset P} (hu : 3 ≤ U.card) (hv : 3 ≤ V.card)
    (huo : Disjoint U (line w)) (hvo : Disjoint V (line w)) :
    ∃ u ∈ U, ∃ v ∈ V, Arc {a,b,u,v} := by
  obtain ⟨f,hf,hL,hfa,hfb⟩ := normalize w a b ha hb hne
  have dis (X : Finset P) (hd : Disjoint X (line w)) : Disjoint (X.image f) (line 0) := by
    rw [←hL, Finset.disjoint_image hf.1]
    exact hd
  obtain ⟨u',hu',v',hv',hx⟩ := canonical
    (by simpa [Finset.card_image_of_injective _ hf.1] using hu : 3 ≤ (U.image f).card)
    (by simpa [Finset.card_image_of_injective _ hf.1] using hv : 3 ≤ (V.image f).card)
    (dis U huo) (dis V hvo)
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hu'
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hv'
  exact ⟨u,hu,v,hv,arc_of_image hf (by simpa [hfa,hfb] using hx)⟩

end ArcAffineCut

end SourceAffineCut

section SourcePrune

namespace PlaneArcPruning

theorem pair_safe_of_two_extras {α ι : Type*} [DecidableEq α]
    (lines : ι → Finset α) (target : Finset α)
    (hthin : ∀ i j, i ≠ j → ((lines i) ∩ (lines j)).card ≤ 1)
    (hout : ∀ i, (lines i \ target).card ≤ 3)
    (F G : Finset α → Prop) (hF : Monotone F) (hG : Monotone G)
    (hsafe : ∀ T : Finset α, Disjoint T target →
      (∀ i, ((lines i) ∩ T).card ≤ 2) → F T → ¬ G T)
    (p₁ p₂ : α) (hne : p₁ ≠ p₂) (hp₁ : p₁ ∉ target) (hp₂ : p₂ ∉ target)
    (hf₁ : F {p₁}) (hf₂ : F {p₂}) :
    ∀ T : Finset α, T.card ≤ 2 → Disjoint T target → ¬ G T := by
  classical
  intro T ht hd hg
  have extend (p : α) (hp : p ∉ target) (hf : F {p}) :
      ∃ i, p ∉ T ∧ T.card = 2 ∧ insert p T ⊆ lines i := by
    let U := insert p T
    have hd' : Disjoint U target := Finset.disjoint_insert_left.mpr ⟨hp,hd⟩
    have huF : F U := hF (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self p T)) hf
    have huG : G U := hG (Finset.subset_insert p T) hg
    have hn : ¬ ∀ i, ((lines i) ∩ U).card ≤ 2 := fun h => hsafe U hd' h huF huG
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    have ha := Finset.card_le_card (Finset.inter_subset_right (s₁ := lines i) (s₂ := U))
    have hnot : p ∉ T := by
      intro hpT
      have he : U = T := Finset.insert_eq_of_mem hpT
      rw [he] at ha hi
      omega
    have hc : U.card = T.card+1 := Finset.card_insert_of_notMem hnot
    have hs : (lines i) ∩ U = U := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hsub : U ⊆ lines i := hs ▸ Finset.inter_subset_left
    exact ⟨i,hnot,by omega,hsub⟩
  obtain ⟨i, hp₁T, hcard, hi⟩ := extend p₁ hp₁ hf₁
  obtain ⟨j, hp₂T, _, hj⟩ := extend p₂ hp₂ hf₂
  have same : i = j := by
    by_contra ne
    have sub : T ⊆ lines i ∩ lines j := fun a ha => Finset.mem_inter.mpr
      ⟨hi (Finset.mem_insert_of_mem ha), hj (Finset.mem_insert_of_mem ha)⟩
    have := Finset.card_le_card sub
    have := hthin i j ne
    omega
  subst j
  have both : insert p₂ (insert p₁ T) ⊆ lines i \ target := by
    intro a ha
    rcases Finset.mem_insert.mp ha with hp | hr
    · subst a; exact Finset.mem_sdiff.mpr ⟨hj (Finset.mem_insert_self _ _),hp₂⟩
    rcases Finset.mem_insert.mp hr with hp | hr
    · subst a; exact Finset.mem_sdiff.mpr ⟨hi (Finset.mem_insert_self _ _),hp₁⟩
    · exact Finset.mem_sdiff.mpr ⟨hi (Finset.mem_insert_of_mem hr),Finset.disjoint_left.mp hd hr⟩
  have hp₂' : p₂ ∉ insert p₁ T := by simp [hne.symm, hp₂T]
  have hcard' := Finset.card_le_card both
  rw [Finset.card_insert_of_notMem hp₂', Finset.card_insert_of_notMem hp₁T, hcard] at hcard'
  have := hout i
  omega

end PlaneArcPruning

end SourcePrune

section SourceTerminalBridge

namespace ArcTerminalBridge

open PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.CircuitLowerBounds
open ArcTerminal ArcAffineCut

abbrev Pt := Fin 13
abbrev FunP := Finset Pt → Prop

def Sound (w : Pt) (f : FunP) := ∀ x, Disjoint x (line w) → Arc x → ¬ f x

lemma arc_small {x : Finset Pt} (h : x.card ≤ 2) : Arc x :=
  fun i => (Finset.card_le_card (Finset.inter_subset_right (s₁:=line i))).trans h

lemma unsound_witness {w : Pt} {A : FunP} (hA : Monotone A)
    (hbad : ¬ PairSafe (line w) A) :
    ∃ a b : Pt, a ∉ line w ∧ b ∉ line w ∧ a ≠ b ∧ A {a,b} := by
  unfold PairSafe at hbad
  push Not at hbad
  obtain ⟨x,hc,hd,hx⟩ := hbad
  have hsub : x ⊆ (line w)ᶜ := fun v hv => Finset.mem_compl.mpr (Finset.disjoint_left.mp hd hv)
  have c : 2 ≤ (line w)ᶜ.card := by simp [Finset.card_compl,card_line]
  obtain ⟨y,hxy,hy,c2⟩ := Finset.exists_subsuperset_card_eq hsub hc c
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp c2
  exact ⟨a,b,Finset.mem_compl.mp (hy (by simp)), Finset.mem_compl.mp (hy (by simp)),hab,hA hxy hx⟩

lemma small_excess {w : Pt} {A B : FunP} {U : Finset Pt}
    (hA : Monotone A) (hB : Monotone B) (hv : ∀ p, p ∈ U ↔ A {p})
    (hs : Sound w (fun x => A x ∧ B x)) (hb : ¬ PairSafe (line w) B) :
    (U \ line w).card ≤ 1 := by
  by_contra! hex
  obtain ⟨p,hp,q,hq,hn⟩ := Finset.one_lt_card.mp hex
  have thin (i j : Pt) (h : i ≠ j) : (line i ∩ line j).card ≤ 1 := (card_inter_line i j h).le
  have hout (i : Pt) : (line i \ line w).card ≤ 3 := by
    by_cases he : i = w
    · simp [he]
    · rw [Finset.card_sdiff,card_line,card_inter_line w i (Ne.symm he)]
  exact hb (PlaneArcPruning.pair_safe_of_two_extras line (line w) thin hout A B hA hB
    (fun x hd hh hf hg => hs x hd hh ⟨hf,hg⟩) p q hn (Finset.mem_sdiff.mp hp).2
    (Finset.mem_sdiff.mp hq).2 ((hv _).mp (Finset.mem_sdiff.mp hp).1)
    ((hv _).mp (Finset.mem_sdiff.mp hq).1))

lemma full_and_small {w : Pt} {A U V : FunP} {u v : Finset Pt}
    (hA : Monotone A) (hU : Monotone U) (hV : Monotone V)
    (hu : ∀ p, p ∈ u ↔ U {p}) (hv : ∀ p, p ∈ v ↔ V {p})
    (hs : Sound w (fun x => A x ∧ (U x ∧ V x))) (ha : ¬ PairSafe (line w) A) :
    (u \ line w).card ≤ 2 ∨ (v \ line w).card ≤ 2 := by
  by_contra! hex
  obtain ⟨a,b,hao,hbo,hab,hAab⟩ := unsound_witness hA ha
  have dis (z : Finset Pt) : Disjoint (z \ line w) (line w) :=
    Finset.disjoint_left.mpr fun _ h => (Finset.mem_sdiff.mp h).2
  obtain ⟨p,hp,q,hq,arc⟩ := affine_cut w a b hao hbo hab hex.1 hex.2 (dis u) (dis v)
  obtain ⟨hp,hpo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hq,hqo⟩ := Finset.mem_sdiff.mp hq
  let x : Finset Pt := {a,b,p,q}
  have hd : Disjoint x (line w) := by simp [x,hao,hbo,hpo,hqo]
  exact hs x hd arc ⟨hA (by simp [x]) hAab,
    hU (by simp [x]) ((hu p).mp hp),hV (by simp [x]) ((hv q).mp hq)⟩

lemma incomparable {w : Pt} {A B : FunP} (hs : Sound w (fun x => A x ∧ B x))
    (ha : ¬ PairSafe (line w) A) (hb : ¬ PairSafe (line w) B) :
    (¬ ∀ x, A x → B x) ∧ (¬ ∀ x, B x → A x) := by
  exact ⟨fun h => ha (fun x hc hd hx => hs x hd (arc_small hc) ⟨hx,h x hx⟩),
    fun h => hb (fun x hc hd hx => hs x hd (arc_small hc) ⟨h x hx,hx⟩)⟩

lemma fourth_child {w : Pt} {F : ℕ → FunP} {V : ℕ → Finset Pt} {A B k h : ℕ}
    (mon : ∀ r, Monotone (F r)) (vone : ∀ r p, p ∈ V r ↔ F r {p})
    (hs : Sound w (fun x => F A x ∧ F B x))
    (ba : ¬ PairSafe (line w) (F A)) (bb : ¬ PairSafe (line w) (F B))
    (hB : V B = line w) (hk : k<B) (hh : h<B)
    (op : (∀ x, F B x ↔ F k x ∧ F h x) ∨ (∀ x, F B x ↔ F k x ∨ F h x)) :
    ∃ U, U<B ∧ U ≠ A ∧ ((2 ≤ (V U).card ∧ V U ⊆ line w) ∨
      (line w ⊆ V U ∧ (V U).card ≤ 6)) := by
  have hi := incomparable hs ba bb
  rcases op with he | he
  · have vB : V B = V k ∩ V h := by ext p; simp [vone,he]
    have lsub : line w ⊆ V k ∩ V h := hB ▸ vB.le
    have hal := full_and_small (mon A) (mon k) (mon h) (vone k) (vone h)
      (fun x hd arc hf => hs x hd arc ⟨hf.1,(he x).mpr hf.2⟩) ba
    have card (z : Finset Pt) (h : (z \ line w).card ≤ 2) : z.card ≤ 6 := by
      have h0 : z.card ≤ (z \ line w).card + (line w).card := Finset.card_le_card_sdiff_add_card
      rw [card_line] at h0
      omega
    rcases hal with ha | ha
    · exact ⟨k,hk,fun eq => hi.2 (fun x hx => eq ▸ ((he x).mp hx).1),
        Or.inr ⟨lsub.trans Finset.inter_subset_left,card _ ha⟩⟩
    · exact ⟨h,hh,fun eq => hi.2 (fun x hx => eq ▸ ((he x).mp hx).2),
        Or.inr ⟨lsub.trans Finset.inter_subset_right,card _ ha⟩⟩
  · have vB : V B = V k ∪ V h := by ext p; simp [vone,he]
    have hl : V k ∪ V h ⊆ line w := vB ▸ hB.le
    have hd := Finset.card_union_le (V k) (V h)
    rw [←vB,hB,card_line] at hd
    by_cases hc : 2 ≤ (V k).card
    · exact ⟨k,hk,fun eq => hi.1 (fun x hx => (he x).mpr (Or.inl (eq ▸ hx))),
        Or.inl ⟨hc,Finset.subset_union_left.trans hl⟩⟩
    · exact ⟨h,hh,fun eq => hi.1 (fun x hx => (he x).mpr (Or.inr (eq ▸ hx))),
        Or.inl ⟨by omega,Finset.subset_union_right.trans hl⟩⟩

theorem four_to_mass (w : Pt) (G : Finset ℕ) (V : ℕ → Finset Pt)
    (h : FourOwned (line w) G V) : 12 ≤ ∑ k ∈ G, PlaneArcCharge.weight w (V k) := by
  classical
  obtain ⟨H,hs,hc,hh⟩ := h
  have hsum : (∑ k ∈ H, PlaneArcCharge.weight w (V k)) = 12 := by
    calc
      _ = ∑ _ ∈ H, 3 := Finset.sum_congr rfl fun k hk => by
        have hO : PlaneArcCharge.Owner w (V k) := hh k hk
        simp [PlaneArcCharge.weight,hO]
      _ = 12 := by simp [hc]
  rw [←hsum]
  exact Finset.sum_le_sum_of_subset hs

theorem three_terminal {w : Pt} {G : Finset ℕ} {F : ℕ → FunP} {V : ℕ → Finset Pt}
    {A B T O k h : ℕ} (hG : ∀ i, 2 ≤ (V i).card → i ∈ G)
    (mon : ∀ i, Monotone (F i)) (vone : ∀ i p, p ∈ V i ↔ F i {p})
    (hs : Sound w (fun x => F A x ∧ F B x))
    (hprod : V T = V A ∩ V B) (clean : V B ⊆ line w) (out : V O = line w)
    (npts : (V T).card = 3) (hat : A<T) (hbt : B<T) (hto : T<O)
    (hk : k<B) (hh : h<B)
    (op : (∀ x, F B x ↔ F k x ∧ F h x) ∨ (∀ x, F B x ↔ F k x ∨ F h x)) :
    FourOwned (line w) G V := by
  have tB : V T ⊆ V B := hprod ▸ Finset.inter_subset_right
  apply size_three (A:=A) hG (card_line w) out npts tB clean hbt hto
  by_cases hb : PairSafe (line w) (F B)
  · left
    apply safe_child hb clean _ mon vone hk hh op
    have := Finset.card_le_card tB
    omega
  · right
    have ha1 := small_excess (mon A) (mon B) (vone A) hs hb
    refine ⟨?_,hat,hprod ▸ Finset.inter_subset_left,ha1⟩
    rintro rfl
    exact hb (fun x hc hd hx => hs x hd (arc_small hc) ⟨hx,hx⟩)

theorem full_terminal_bad_pair {w : Pt} {G : Finset ℕ} {F : ℕ → FunP} {V : ℕ → Finset Pt}
    {A B T k h : ℕ} (hG : ∀ i, 2 ≤ (V i).card → i ∈ G)
    (mon : ∀ i, Monotone (F i)) (vone : ∀ i p, p ∈ V i ↔ F i {p})
    (hs : Sound w (fun x => F A x ∧ F B x)) (hprod : V T = V A ∩ V B)
    (clean : V B ⊆ line w) (hfull : V T = line w)
    (ba : ¬ PairSafe (line w) (F A)) (bb : ¬ PairSafe (line w) (F B))
    (hat : A<T) (hbt : B<T) (hk : k<B) (hh : h<B)
    (op : (∀ x, F B x ↔ F k x ∧ F h x) ∨ (∀ x, F B x ↔ F k x ∨ F h x)) :
    FourOwned (line w) G V := by
  have lAB : line w = V A ∩ V B := hfull.symm.trans hprod
  have subA : line w ⊆ V A := lAB ▸ Finset.inter_subset_left
  have subB : line w ⊆ V B := lAB ▸ Finset.inter_subset_right
  have vB : V B = line w := Finset.Subset.antisymm clean subB
  obtain ⟨u,hu⟩ := fourth_child mon vone hs ba bb vB hk hh op
  apply size_four_irreducible (U:=u) hG (card_line w) hfull vB subA
    (small_excess (mon A) (mon B) (vone A) hs bb) _ hat hbt hu
  rintro rfl
  exact bb (fun x hc hd hx => hs x hd (arc_small hc) ⟨hx,hx⟩)

theorem earlier_safe_factor (gs : List Gate) (w : Pt) (g t : ℕ) (hgt : g<t) (ht : t<gs.length)
    (valid : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2)
    (out : V gs (13+g) = line w) (safe : Safe w (wval gs (13+g)))
    (term : V gs (13+t) ⊆ line w) (term2 : 2 ≤ (V gs (13+t)).card) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  classical
  let R := Finset.range gs.length
  let U := R.erase t
  have hc : (V gs (13+t)).card ≤ 4 := by simpa [card_line] using Finset.card_le_card term
  have hG : GwUp gs w g ⊆ U := by
    intro j hj
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩
  have h56 : B56 gs ⊆ U := by
    intro j hj
    have h := Finset.mem_filter.mp hj
    apply Finset.mem_erase.mpr
    refine ⟨?_,h.1⟩
    rintro rfl
    have h5 := h.2.1
    omega
  have h7 : B7 gs ⊆ U := by
    intro j hj
    have h := Finset.mem_filter.mp hj
    refine Finset.mem_erase.mpr ⟨?_,h.1⟩
    rintro rfl
    have h7 := h.2
    omega
  have z := PlaneArcCharge.baseline gs w g U (by omega) valid out safe hG h56 h7
  have ho : PlaneArcCharge.Owner w (PlaneArcCharge.signature gs t) :=
    Or.inl ⟨term2,term⟩
  have wt : PlaneArcCharge.weight w (PlaneArcCharge.signature gs t) = 3 := by
    simp [PlaneArcCharge.weight,ho]
  have htR : t ∈ R := Finset.mem_range.mpr ht
  have total := Finset.sum_erase_add R (fun k => PlaneArcCharge.weight w (PlaneArcCharge.signature gs k)) htR
  change 12 ≤ ∑ k ∈ R, _
  change 9 ≤ ∑ k ∈ R.erase t, _ at z
  omega

theorem size_four_safe_factor (gs : List Gate) (w : Pt) (g t : ℕ) (hgt : g<t) (ht : t<gs.length)
    (valid : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2)
    (out : V gs (13+g) = line w) (safe : Safe w (wval gs (13+g)))
    (term : V gs (13+t) = line w) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) :=
  earlier_safe_factor gs w g t hgt ht valid out safe term.le (by rw [term,card_line]; decide)

end ArcTerminalBridge

end SourceTerminalBridge

section SourceRawTerminal

namespace ArcRawTerminal

open PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.CircuitLowerBounds
open ArcTerminal ArcTerminalBridge ArcAffineCut

abbrev valid (gs : List Gate) :=
  ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2

def sig (gs : List Gate) (r : ℕ) (x : Finset Pt) : Prop :=
  wval gs r (fun p => decide (p ∈ x)) = true

lemma single (gs : List Gate) (r : ℕ) (p : Pt) : p ∈ V gs r ↔ sig gs r {p} := by
  rw [mem_V]
  unfold sig e1
  simp

lemma mono (gs : List Gate) (ho : valid gs) (r : ℕ) : Monotone (sig gs r) := by
  intro X Y hs hx
  exact wval_mono gs (fun g hg => (ho g hg).1) r _ _
    (fun i hi => decide_eq_true ((hs (of_decide_eq_true hi)))) hx

lemma pair_safe_to_bool {gs : List Gate} {r : ℕ} {w : Pt} (h : PairSafe (line w) (sig gs r)) :
    Safe w (wval gs r) := by
  intro x hw hex
  by_contra! hn
  let X := Finset.univ.filter (fun i => x i = true)
  have memX (i : Pt) : i ∈ X ↔ x i = true := by simp [X]
  have hc : X.card ≤ 2 := by
    by_contra! h3
    obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp h3
    exact (hw a b c ((memX _).mp ha) ((memX _).mp hb) ((memX _).mp hc)).elim hab
      (fun e => e.elim hbc hac)
  have eqx : (fun i => decide (i ∈ X)) = x := by funext i; simp [memX]
  have hd : Disjoint X (line w) := Finset.disjoint_left.mpr
    (fun i hi hl => hn i hl ((memX _).mp hi))
  exact h X hc hd (by simpa [sig,eqx] using hex)

lemma eligible {gs : List Gate} {r : ℕ} (h : 2 ≤ (V gs r).card) :
    r ∈ Finset.Ico 13 (13+gs.length) := by
  obtain ⟨g,hg,rfl⟩ := gate_idx_of_V_ge2 gs r h
  simp [hg]

lemma earlier {gs : List Gate} (ho : valid gs) {w : Pt} {B T : ℕ}
    (hbt : B<T) (hB : V gs B = line w) (ht : V gs T ⊆ line w) (htc : 2 ≤ (V gs T).card)
    (hBs : PairSafe (line w) (sig gs B)) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  obtain ⟨b,hb,rfl⟩ := gate_idx_of_V_ge2 gs B (by rw [hB,card_line]; decide)
  obtain ⟨t,hT,rfl⟩ := gate_idx_of_V_ge2 gs T htc
  exact earlier_safe_factor gs w b t (by omega) hT ho hB (pair_safe_to_bool hBs) ht htc

lemma mass_of_four {gs : List Gate} {w : Pt}
    (h : FourOwned (line w) (Finset.Ico 13 (13+gs.length)) (V gs)) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  have m := four_to_mass w _ _ h
  rw [Finset.sum_Ico_eq_sum_range] at m
  simpa [PlaneArcCharge.signature, Nat.add_comm] using m

def ParentForm (gs : List Gate) (B : ℕ) := ∃ k h, k<B ∧ h<B ∧
  ((∀ x, sig gs B x ↔ sig gs k x ∧ sig gs h x) ∨
   (∀ x, sig gs B x ↔ sig gs k x ∨ sig gs h x))

lemma parent_form (gs : List Gate) (ho : valid gs) (B : ℕ)
    (lo : 2 ≤ (V gs B).card) (hi : (V gs B).card ≤ 4) : ParentForm gs B := by
  obtain ⟨g,hg,rfl⟩ := gate_idx_of_V_ge2 gs B lo
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (V gs (13+g)).card)
  have live := (single gs _ _).mp hp
  obtain ⟨hop,hlen⟩ := ho (gs[g]) (List.getElem_mem hg)
  let Rd (a : ℕ) (x : Finset Pt) := wvalAt gs g a (fun v => decide (v ∈ x)) = true
  have rd (a : ℕ) (x : Finset Pt) : Rd a x ↔ a < 13+g ∧ sig gs a x := by
    by_cases h : a < 13+g <;> simp [Rd,wvalAt,h,sig]
  have normCopy (a : ℕ) (hlt : a<13+g) (he : ∀ x, sig gs (13+g) x ↔ sig gs a x) :
      ParentForm gs (13+g) :=
    ⟨a,a,hlt,hlt,Or.inr (fun x => by simpa using he x)⟩
  rcases hinput : (gs[g]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · rcases hop with hop | hop
    · rw [V_gate_nil_and gs g hg hop hinput] at hi
      simp at hi
    · rw [V_gate_nil_or gs g hg hop hinput] at lo
      simp at lo
  · have he (x) : sig gs (13+g) x ↔ Rd a x := by
      unfold sig Rd
      rw [wval_gate_one gs g hg a hop hinput]
    have hlt := ((rd a _).mp ((he _).mp live)).1
    exact normCopy a hlt (fun x => by rw [he,rd]; simp [hlt])
  · rcases hop with hop | hop
    · have he (x) : sig gs (13+g) x ↔ Rd a x ∧ Rd b x := by
        unfold sig Rd
        rw [wval_gate_two_and gs g hg a b hop hinput]
        simp
      obtain ⟨xa,xb⟩ := (he _).mp live
      have hla := ((rd a _).mp xa).1
      have hlb := ((rd b _).mp xb).1
      exact ⟨a,b,hla,hlb,Or.inl (fun x => by rw [he,rd,rd]; simp [hla,hlb])⟩
    · have he (x) : sig gs (13+g) x ↔ Rd a x ∨ Rd b x := by
        unfold sig Rd
        rw [wval_gate_two_or gs g hg a b hop hinput]
        simp
      by_cases hla : a<13+g <;> by_cases hlb : b<13+g
      · exact ⟨a,b,hla,hlb,Or.inr (fun x => by rw [he,rd,rd]; simp [hla,hlb])⟩
      · exact normCopy a hla (fun x => by rw [he,rd,rd]; simp [hla,hlb])
      · exact normCopy b hlb (fun x => by rw [he,rd,rd]; simp [hla,hlb])
      · have := (he _).mp live
        simp [rd,hla,hlb] at this
  · simp [hinput] at hlen

theorem terminal (gs : List Gate) (w : Pt) (A B T O : ℕ) (ho : valid gs)
    (hprod : ∀ x, sig gs T x ↔ sig gs A x ∧ sig gs B x)
    (hs : Sound w (sig gs T)) (hsO : PairSafe (line w) (sig gs O))
    (hO : V gs O = line w) (hb : V gs B ⊆ line w)
    (hcnt : 2 ≤ (V gs T).card) (hat : A<T) (hbt : B<T) (hto : T≤O)
    (path : T=O ∨ (∃ U, T<U ∧ U<O ∧ V gs T ⊆ V gs U ∧ V gs U ⊆ line w) ∨
       ∃ U, U<O ∧ (∀ x, sig gs O x ↔ sig gs T x ∨ sig gs U x)) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  have hv : V gs T = V gs A ∩ V gs B := by ext p; simp [single,hprod]
  have tB : V gs T ⊆ V gs B := hv ▸ Finset.inter_subset_right
  have tL := tB.trans hb
  have nle := Finset.card_le_card tL
  rw [card_line] at nle
  have hsab : Sound w (fun x => sig gs A x ∧ sig gs B x) :=
    fun x hd hArc hx => hs x hd hArc ((hprod x).mpr hx)
  have eh (r : ℕ) (h : 2 ≤ (V gs r).card) := eligible h
  obtain ⟨k,h,hk,hh,op⟩ := parent_form gs ho B (hcnt.trans (Finset.card_le_card tB))
    (by simpa [card_line] using Finset.card_le_card hb)
  have full (hc : (V gs T).card = 4) : V gs T = line w :=
    Finset.eq_of_subset_of_card_le tL (by rw [hc,card_line])
  by_cases four : (V gs T).card = 4
  · have hfull := full four
    have lB : line w ⊆ V gs B := hfull ▸ tB
    have hBe := Finset.Subset.antisymm hb lB
    by_cases bs : PairSafe (line w) (sig gs B)
    · exact earlier ho hbt hBe tL hcnt bs
    by_cases asf : PairSafe (line w) (sig gs A)
    · have hAc : V gs A ⊆ line w := by
        intro p hp
        by_contra hn
        exact asf {p} (by simp) (by simpa using hn) ((single _ _ _).mp hp)
      have lA : line w ⊆ V gs A := hfull ▸ hv ▸ Finset.inter_subset_left
      exact earlier ho hat (Finset.Subset.antisymm hAc lA) tL hcnt asf
    exact mass_of_four (full_terminal_bad_pair eh (mono gs ho) (single gs) hsab hv hb hfull asf bs hat hbt hk hh op)
  have ltTO : T<O := by
    apply lt_of_le_of_ne hto
    rintro rfl
    exact four (by rw [hO,card_line])
  by_cases three : (V gs T).card = 3
  · exact mass_of_four (three_terminal eh (mono gs ho) (single gs) hsab hv hb hO three hat hbt ltTO hk hh op)
  have two : (V gs T).card = 2 := by omega
  rcases path with h | hi | ⟨U,hu,he⟩
  · omega
  · exact mass_of_four (size_two eh (card_line w) hO two tB hb hbt ltTO (Or.inl hi))
  · have vu : V gs O = V gs T ∪ V gs U := by ext p; simp [single,he]
    by_cases hU : U=B
    · subst U
      have eO : ∀ x, sig gs O x ↔ sig gs B x := by
        intro x
        rw [he,hprod]
        tauto
      have eV : V gs O = V gs B := by ext p; simp [single,eO]
      exact earlier ho hbt (eV.symm.trans hO) tL hcnt
        (fun x hc hd hx => hsO x hc hd ((eO x).mpr hx))
    exact mass_of_four (size_two eh (card_line w) hO two tB hb hbt ltTO (Or.inr ⟨U,hu,vu,hU⟩))

theorem terminal_from_product (gs : List Gate) (w : Pt) (A B T O : ℕ) (ho : valid gs)
    (hprod : ∀ x, sig gs T x ↔ sig gs A x ∧ sig gs B x)
    (hs : Sound w (sig gs T)) (hsO : PairSafe (line w) (sig gs O))
    (hO : V gs O = line w)
    (hcnt : 2 ≤ (V gs T).card) (hat : A<T) (hbt : B<T) (hto : T≤O)
    (path : T=O ∨ (∃ U, T<U ∧ U<O ∧ V gs T ⊆ V gs U ∧ V gs U ⊆ line w) ∨
       ∃ U, U<O ∧ (∀ x, sig gs O x ↔ sig gs T x ∨ sig gs U x)) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  have hp : PairSafe (line w) (fun x => sig gs A x ∧ sig gs B x) :=
    fun x hc hd hx => hs x hd (arc_small hc) ((hprod x).mpr hx)
  rcases prime_pair (mono gs ho A) (mono gs ho B) (single gs A) (single gs B) hp with ha | hb
  · exact terminal gs w B A T O ho (fun x => (hprod x).trans and_comm) hs hsO hO ha hcnt hbt hat hto path
  · exact terminal gs w A B T O ho hprod hs hsO hO hb hcnt hat hbt hto path

end ArcRawTerminal

end SourceRawTerminal

section SourceAssemblyInputs

namespace PlaneArcAssembly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PlaneArcFirst PlaneArcTranspose ArcAffineCut

abbrev Points := Finset (Fin 13)
def bits (X : Points) (p : Fin 13) := decide (p ∈ X)

def OrigSound (C : Circuit) :=
  (∀ X : Points, Arc X → C.eval (List.ofFn (pointOnly (bits X))) = false) ∧
  ∀ (X : Points) (i : Fin 13), Arc X → C.eval (List.ofFn (oneLine (bits X) i)) = true →
    ∃ p ∈ line i, p ∈ X

def OrigPositive (C : Circuit) := ∀ p w : Fin 13, Incident w p →
  circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true

theorem mem_line_iff (w p : Fin 13) : p ∈ line w ↔ Incident w p := by
  revert w p
  decide

theorem filtered (X : Points) (w : Fin 13) :
    (Finset.univ.filter (fun p : Fin 13 => Incident w p ∧ bits X p = true)) = line w ∩ X := by
  ext p; simp [bits, mem_line_iff]

theorem orig_off {C : Circuit} (h : OrigSound C) {X : Points} (hx : Arc X) :
    C.eval (List.ofFn (pointOnly (bits X))) = false := h.1 X hx

theorem orig_sound {C : Circuit} (h : OrigSound C) {X : Points} (hx : Arc X) (i : Fin 13)
    (he : C.eval (List.ofFn (oneLine (bits X) i)) = true) : ∃ p ∈ line i, p ∈ X :=
  h.2 X i hx he

theorem bits_one (p : Fin 13) : bits {p} = e1 p := by funext k; simp [bits,e1]

theorem orig_pos {C : Circuit} (h : OrigPositive C) (p w : Fin 13) (inc : p ∈ line w) :
    C.eval (List.ofFn (oneLine (e1 p) w)) = true := by
  have eq : oneLine (e1 p) w = (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) := by
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [oneLine,Fin.addCases_left,e1]; congr 1; apply propext
      constructor
      · rintro rfl; exact Or.inl rfl
      · rintro (he|he) <;> have hh := congrArg Fin.val he <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
        · exact Fin.ext hh
        · omega
    · simp only [oneLine,Fin.addCases_right]; congr 1; apply propext
      constructor
      · rintro rfl; exact Or.inr rfl
      · rintro (he|he) <;> have hh := congrArg Fin.val he <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
        · omega
        · apply Fin.ext; omega
  rw [eq]; exact h p w ((mem_line_iff w p).mp inc)

theorem output_lt {C : Circuit} (h : OrigPositive C) : C.output < 26 + C.size := by
  have he := orig_pos h 0 0 (by decide)
  by_contra! hh
  rw [Circuit.eval, wires_eq, List.getD_eq_default] at he
  · contradiction
  · simpa [length_wiresFrom,Circuit.size] using hh

end PlaneArcAssembly

end SourceAssemblyInputs

section SourceReverse

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PlaneArcTranspose

namespace PlaneArcEmit

variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

structure Back where
  gs : List Gate
  reg : ℕ →₀ Ref
  skipped : Finset ℕ

def Back.Ok (s : Back) : Prop := GatesOk s.gs ∧ ∀ w, Ref.Valid s.gs (s.reg w)

def Back.eval (s : Back) (x : Fin 13 → Bool) (w : ℕ) : Prop :=
  Ref.val s.gs x (s.reg w) = true

noncomputable def Back.clear (s : Back) (w : ℕ) : Back := {s with reg := s.reg.erase w}

noncomputable def Back.merge (s : Back) (w : ℕ) (v : Ref) : Back :=
  let p := combine s.gs false (s.reg w) v
  {s with gs := s.gs ++ p.added, reg := s.reg.update w p.ref}

noncomputable def product (scalar : ℕ → Ref) (s : Back) (dst f : ℕ) : Result :=
  scale s.gs (s.reg dst) (scalar f)

noncomputable def scaled (scalar : ℕ → Ref) (s : Back) (dst f : ℕ) : Back :=
  let p := product scalar s dst f
  { gs := s.gs ++ p.added
    reg := s.reg.erase dst
    skipped := if p.added.isEmpty then insert dst s.skipped else s.skipped}

noncomputable def step (scalar : ℕ → Ref) (a : Assignment) (s : Back) : Back :=
  let r := s.reg a.dst
  let start := s.clear a.dst
  match a.op with
  | .zero => start
  | .copy u => start.merge u r
  | .add u v => (start.merge u r).merge v r
  | .scale u f => (scaled scalar s a.dst f).merge u (product scalar s a.dst f).ref

noncomputable def sweep (scalar : ℕ → Ref) (ops : List Assignment) (s : Back) : Back :=
  ops.foldr (step scalar) s

def Ext (s t : Back) : Prop := ∃ extra, t.gs = s.gs ++ extra

theorem Ext.trans {a b c : Back} (hab : Ext a b) (hbc : Ext b c) : Ext a c := by
  obtain ⟨x,hx⟩ := hab
  obtain ⟨y,hy⟩ := hbc
  exact ⟨x++y,by rw [hy,hx,List.append_assoc]⟩

theorem Ext.valid {a b : Back} (h : Ext a b) {r : Ref} (hr : Ref.Valid a.gs r) :
    Ref.Valid b.gs r := by obtain ⟨x,hx⟩ := h; rw [hx]; exact ref_weaken x hr

theorem Ext.stable {a b : Back} (h : Ext a b) {r : Ref} (hr : Ref.Valid a.gs r)
    (x : Fin 13 → Bool) : Ref.val b.gs x r = Ref.val a.gs x r := by
  obtain ⟨e,he⟩ := h; rw [he]; exact ref_stable e hr x

theorem clear_ok {s : Back} (hs : s.Ok) (w : ℕ) : (s.clear w).Ok := by
  refine ⟨hs.1,fun j => ?_⟩
  by_cases he : j = w
  · subst j; change Ref.Valid s.gs ((s.reg.erase w) w); rw [Finsupp.erase_same, (Fact.out : (0 : Ref) = Ref.zero)]; trivial
  · change Ref.Valid s.gs ((s.reg.erase w) j)
    rw [Finsupp.erase_ne he]; exact hs.2 j

theorem clear_eval (s : Back) (dst w : ℕ) (x : Fin 13 → Bool) :
    (s.clear dst).eval x w ↔ w ≠ dst ∧ s.eval x w := by
  by_cases h : w = dst
  · subst w; simp [Back.eval,Back.clear,Ref.val,(Fact.out : (0 : Ref) = Ref.zero)]
  · simp [Back.eval,Back.clear,h]

theorem merge_ext (s : Back) (w : ℕ) (v : Ref) : Ext s (s.merge w v) :=
  ⟨_,rfl⟩

theorem merge_ok {s : Back} (hs : s.Ok) (w : ℕ) {v : Ref} (hv : Ref.Valid s.gs v) :
    (s.merge w v).Ok := by
  obtain ⟨out,valid,_,_⟩ := combine_spec s.gs false (s.reg w) v (hs.2 w) hv
  refine ⟨?_,fun j => ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact hs.1 g hg
    · exact valid g hg
  · by_cases he : j = w
    · subst j; simpa [Back.merge] using out
    · simpa [Back.merge, Function.update_of_ne he] using ref_weaken (combine s.gs false (s.reg w) v).added (hs.2 j)

theorem merge_eval {s : Back} (hs : s.Ok) (w : ℕ) {v : Ref} (hv : Ref.Valid s.gs v)
    (x : Fin 13 → Bool) (j : ℕ) :
    (s.merge w v).eval x j ↔ s.eval x j ∨ (j = w ∧ Ref.val s.gs x v = true) := by
  by_cases he : j = w
  · subst j
    have ev := (combine_spec s.gs false (s.reg w) v (hs.2 w) hv).2.2.2 x
    simp [Back.merge, Back.eval, ev, boolOp]
  · have ht := (merge_ext s w v).stable (hs.2 j) x
    simp [Back.merge] at ht
    simp [Back.merge, Back.eval, Function.update_of_ne he, he, ht]

end PlaneArcEmit

end SourceReverse

section SourceReverseSem

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.RowStructure PlaneArcTranspose

namespace PlaneArcEmit
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

theorem scaled_ok (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (dst f : ℕ)
    (hf : Ref.Valid s.gs (sc f)) : (scaled sc s dst f).Ok ∧
      Ref.Valid (scaled sc s dst f).gs (product sc s dst f).ref := by
  obtain ⟨v,g,_,_,_,_⟩ := scale_spec s.gs _ _ hs.1 (hs.2 dst) hf
  refine ⟨⟨?_,fun j => ref_weaken _ ((clear_ok hs dst).2 j)⟩,v⟩
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact hs.1 a ha
  · exact g a ha

theorem scaled_eval (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (dst f : ℕ) (x) (j) :
    (scaled sc s dst f).eval x j ↔ j ≠ dst ∧ s.eval x j := by
  rw [← clear_eval]
  unfold Back.eval
  exact Eq.to_iff (congrArg (· = true) (ref_stable _ ((clear_ok hs dst).2 j) x))

theorem step_ext (sc : ℕ → Ref) (a : Assignment) (s : Back) : Ext s (step sc a s) := by
  cases a with | mk dst op =>
    cases op with
    | zero => exact ⟨[], by simp [step,Back.clear]⟩
    | copy u => exact ⟨_,rfl⟩
    | add u v =>
      exact (show Ext s ((s.clear dst).merge u (s.reg dst)) from ⟨_,rfl⟩).trans (merge_ext _ v _)
    | scale u f => exact (show Ext s (scaled sc s dst f) from ⟨_,rfl⟩).trans (merge_ext _ u _)

theorem step_ok (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f))
    (a : Assignment) : (step sc a s).Ok := by
  cases a with | mk dst op =>
    cases op with
    | zero => exact clear_ok hs dst
    | copy u => exact merge_ok (clear_ok hs dst) u (hs.2 dst)
    | add u v =>
      exact merge_ok (merge_ok (clear_ok hs dst) u (hs.2 dst)) v
        ((merge_ext (s.clear dst) u _).valid (hs.2 dst))
    | scale u f =>
      have h := scaled_ok sc hs dst f (hf f)
      exact merge_ok h.1 u h.2

def delivered (sc : ℕ → Ref) (s : Back) (a : Assignment) (x : Fin 13 → Bool) (w : ℕ) : Prop :=
  match a.op with
  | .zero => False
  | .copy u => s.eval x a.dst ∧ w = u
  | .add u v => s.eval x a.dst ∧ (w = u ∨ w = v)
  | .scale u f => w = u ∧ Ref.val (scaled sc s a.dst f).gs x (product sc s a.dst f).ref = true

theorem step_eval (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f))
    (a : Assignment) (x : Fin 13 → Bool) (w : ℕ) :
    (step sc a s).eval x w ↔ (w ≠ a.dst ∧ s.eval x w) ∨ delivered sc s a x w := by
  cases a with | mk dst op =>
    cases op with
    | zero => simp [step, delivered, clear_eval]
    | copy u =>
      change ((s.clear dst).merge u (s.reg dst)).eval x w ↔ _ ∨ (s.eval x dst ∧ w = u)
      rw [merge_eval (clear_ok hs dst) u (hs.2 dst),clear_eval]
      change _ ∨ (w = u ∧ s.eval x dst) ↔ _
      tauto
    | add u v =>
      let mid := (s.clear dst).merge u (s.reg dst)
      have valid : Ref.Valid mid.gs (s.reg dst) := (merge_ext (s.clear dst) u _).valid (hs.2 dst)
      have stable := (merge_ext (s.clear dst) u (s.reg dst)).stable (hs.2 dst) x
      change (mid.merge v (s.reg dst)).eval x w ↔ _ ∨ (s.eval x dst ∧ (w=u ∨ w=v))
      rw [merge_eval (merge_ok (clear_ok hs dst) u (hs.2 dst)) v valid]
      change mid.eval x w ∨ (w = v ∧ Ref.val mid.gs x (s.reg dst) = true) ↔ _
      rw [show Ref.val mid.gs x (s.reg dst) = Ref.val s.gs x (s.reg dst) from stable]
      rw [show mid.eval x w ↔ _ from merge_eval (clear_ok hs dst) u (hs.2 dst) x w, clear_eval]
      change ((_ ∨ (w=u ∧ s.eval x dst)) ∨ (w=v ∧ s.eval x dst)) ↔ _
      tauto
    | scale u f =>
      have hp := scaled_ok sc hs dst f (hf f)
      change ((scaled sc s dst f).merge u _).eval x w ↔ _ ∨ (w = u ∧ _)
      rw [merge_eval hp.1 u hp.2, scaled_eval sc hs]

theorem step_sound (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f))
    (a : Assignment) (x : Fin 13 → Bool) (w : ℕ) :
    (step sc a s).eval x w →
      a.pull (fun f => Ref.val s.gs x (sc f) = true) (s.eval x) w := by
  rw [step_eval sc hs hf]
  rintro (old|new)
  · exact Or.inl old
  apply Or.inr
  cases a with | mk dst op =>
    cases op with
    | zero => exact False.elim new
    | copy | add => exact new
    | scale u f =>
      obtain ⟨hw,hv⟩ := new
      have h := (scale_spec s.gs _ _ hs.1 (hs.2 dst) (hf f)).2.2.2.1 x hv
      exact ⟨h.1,hw,h.2⟩

theorem step_singleton (sc : ℕ → Ref) {s : Back} (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f))
    (a : Assignment) (p : Fin 13) (w : ℕ) :
    (step sc a s).eval (e1 p) w ↔
      a.pull (fun f => Ref.val s.gs (e1 p) (sc f) = true) (s.eval (e1 p)) w := by
  refine ⟨step_sound sc hs hf a _ w,?_⟩
  rw [step_eval sc hs hf]
  rintro (old|⟨hd,new⟩)
  · exact Or.inl old
  apply Or.inr
  cases a with | mk dst op =>
    cases op with
    | zero => exact False.elim new
    | copy | add => exact ⟨hd,new⟩
    | scale u f =>
      obtain ⟨hw,hfval⟩ := new
      have h := (scale_spec s.gs _ _ hs.1 (hs.2 dst) (hf f)).2.2.2.2.1 p
      change Ref.val s.gs (e1 p) (s.reg dst) = true at hd
      exact ⟨hw,h.trans (by simp [hd,hfval])⟩

theorem sweep_ext (sc : ℕ → Ref) (ops : List Assignment) (s : Back) : Ext s (sweep sc ops s) := by
  induction ops with
  | nil => exact ⟨[],by simp [sweep]⟩
  | cons a rest ih => exact ih.trans (step_ext sc a _)

theorem sweep_ok (sc : ℕ → Ref) (ops : List Assignment) {s : Back}
    (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f)) : (sweep sc ops s).Ok := by
  induction ops with
  | nil => exact hs
  | cons a rest ih => exact step_ok sc ih (fun f => (sweep_ext sc rest s).valid (hf f)) a

private theorem pull_mono (a : Assignment) (σ : ℕ → Prop) {d d' : ℕ → Prop}
    (hh : ∀ i, d i → d' i) (i : ℕ) : a.pull σ d i → a.pull σ d' i := by
  rintro (⟨hn,h⟩|⟨h,he⟩)
  · exact Or.inl ⟨hn,hh i h⟩
  · exact Or.inr ⟨hh _ h,he⟩

theorem sweep_sound (sc : ℕ → Ref) (ops : List Assignment) {s : Back}
    (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f)) (x : Fin 13 → Bool) (w : ℕ) :
    (sweep sc ops s).eval x w →
      reverse (fun f => Ref.val s.gs x (sc f) = true) ops (s.eval x) w := by
  induction ops generalizing w with
  | nil => exact id
  | cons a rest ih =>
    let mid := sweep sc rest s
    have ex := sweep_ext sc rest s
    have hh : (fun f => Ref.val mid.gs x (sc f) = true) =
        (fun f => Ref.val s.gs x (sc f) = true) := by
      funext f; rw [ex.stable (hf f)]
    intro h
    have stepH := step_sound sc (sweep_ok sc rest hs hf) (fun f => ex.valid (hf f)) a x w h
    change a.pull (fun f => Ref.val mid.gs x (sc f) = true) (mid.eval x) w at stepH
    rw [hh] at stepH
    exact pull_mono a _ ih w stepH

theorem sweep_singleton (sc : ℕ → Ref) (ops : List Assignment) {s : Back}
    (hs : s.Ok) (hf : ∀ f, Ref.Valid s.gs (sc f)) (p : Fin 13) (w : ℕ) :
    (sweep sc ops s).eval (e1 p) w ↔
      reverse (fun f => Ref.val s.gs (e1 p) (sc f) = true) ops (s.eval (e1 p)) w := by
  induction ops generalizing w with
  | nil => rfl
  | cons a rest ih =>
    let mid := sweep sc rest s
    have ex := sweep_ext sc rest s
    have hh : (fun f => Ref.val mid.gs (e1 p) (sc f) = true) =
        (fun f => Ref.val s.gs (e1 p) (sc f) = true) := by
      funext f; rw [ex.stable (hf f)]
    have hh' : mid.eval (e1 p) =
        reverse (fun f => Ref.val s.gs (e1 p) (sc f) = true) rest (s.eval (e1 p)) :=
      funext (fun v => propext (ih v))
    change (step sc a mid).eval (e1 p) w ↔ a.pull _ _ w
    rw [step_singleton sc (sweep_ok sc rest hs hf) (fun f => ex.valid (hf f)),hh,hh']
    rfl

noncomputable def seed (gs : List Gate) (o : ℕ) : Back := ⟨gs,Finsupp.single o .one,∅⟩

theorem seed_ok (gs : List Gate) (o : ℕ) (ok : GatesOk gs) : (seed gs o).Ok := by
  refine ⟨ok,fun w => ?_⟩
  by_cases h : o = w
  · subst w; simp [seed,Ref.Valid]
  · change Ref.Valid gs ((Finsupp.single o Ref.one) w)
    rw [Finsupp.single_eq_of_ne (Ne.symm h), (Fact.out : (0 : Ref) = Ref.zero)]
    trivial

theorem seed_eval (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) :
    (seed gs o).eval x = (fun w => w = o) := by
  funext w
  by_cases h : o = w
  · subst w; simp [Back.eval,seed,Ref.val]
  · simp [Back.eval,seed,Ref.val,Ne.symm h,(Fact.out : (0 : Ref) = Ref.zero)]

end PlaneArcEmit

end SourceReverseSem

section SourceReverseBudget

namespace PlaneArcBudget
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcEmit PlaneArcTranspose

theorem update_budget {α β : Type*} [DecidableEq α] [Zero β]
    (regs : α →₀ β) (key : α) (value : β) (cost : ℕ)
    (at_most_one : cost ≤ 1) (free_at_zero : regs key = 0 → cost = 0) :
    cost + (regs.update key value).support.card ≤ regs.support.card + 1 := by
  have hle := Finset.card_le_card (Finsupp.support_update_subset (b := value) regs key)
  by_cases hk : key ∈ regs.support
  · rw [Finset.insert_eq_of_mem hk] at hle
    omega
  · have hz : regs key = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hk
    rw [free_at_zero hz,zero_add]
    exact hle.trans (Finset.card_insert_le _ _)

theorem erase_live {α β : Type*} [DecidableEq α] [Zero β]
    (regs : α →₀ β) {key : α} (live : regs key ≠ 0) :
    (regs.erase key).support.card + 1 = regs.support.card := by
  rw [Finsupp.support_erase]
  exact Finset.card_erase_add_one (Finsupp.mem_support_iff.mpr live)

theorem erase_idle {α β : Type*} [DecidableEq α] [Zero β]
    (regs : α →₀ β) {key : α} (dead : regs key = 0) :
    regs.erase key = regs := by
  rw [Finsupp.erase_eq_update_zero, ←dead, Finsupp.update_self]

theorem combine_or_zero_left (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : Ref) :
    combine gs false .zero v = ⟨[],v⟩ := by cases v <;> rfl

theorem combine_or_zero_right (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : Ref) :
    combine gs false v .zero = ⟨[],v⟩ := by cases v <;> rfl

theorem combine_or_one_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : Ref) :
    (combine gs false a b).added.length ≤ 1 := by cases a <;> cases b <;> simp [combine,pushWire]

theorem merge_budget (zero_eq : (0 : Ref) = .zero)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (regs : ℕ →₀ Ref) (key : ℕ) (v : Ref) :
    let next := combine gs false (regs key) v
    next.added.length + (regs.update key next.ref).support.card ≤
      regs.support.card + (if v = .zero then 0 else 1) := by
  by_cases hv : v = .zero
  · subst v
    simp [combine_or_zero_right]
  · simp only [hv,ite_false]
    apply update_budget
    · exact combine_or_one_gate _ _ _
    · intro hz
      rw [hz,zero_eq,combine_or_zero_left]
      rfl

theorem merge_budget_one (zero_eq : (0 : Ref) = .zero)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (regs : ℕ →₀ Ref) (key : ℕ) (v : Ref) :
    let next := combine gs false (regs key) v
    next.added.length + (regs.update key next.ref).support.card ≤ regs.support.card + 1 := by
  have h := merge_budget zero_eq gs regs key v
  split at h <;> omega

def credit (a : Assignment) : ℕ :=
  match a.op with
  | .add _ _ | .scale _ _ => 1
  | .copy _ | .zero => 0

theorem fold_budget {S : Type*} (ops : List Assignment) (step : Assignment → S → S)
    (potential : S → ℕ) (initial : S)
    (within : ∀ a s, potential (step a s) ≤ potential s + credit a) :
    potential (ops.foldr step initial) ≤ potential initial + (ops.map credit).sum := by
  induction ops with
  | nil => simp
  | cons a ops ih =>
    have h := within a (ops.foldr step initial)
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    omega

theorem fold_budget_count (ops : List Assignment) : (ops.map credit).sum ≤ ops.length := by
  induction ops with
  | nil => simp
  | cons a rest ih =>
    have ca : credit a ≤ 1 := by unfold credit; split <;> decide
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

end PlaneArcBudget

end SourceReverseBudget

section SourceReverseCount

namespace PlaneArcBudget
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcEmit PlaneArcTranspose PEqualNP.CircuitLowerBounds

def potential (s : Back) : ℕ := s.gs.length + s.reg.support.card + s.skipped.card

def occupied (v : Ref) : ℕ := if v = .zero then 0 else 1

theorem clear_potential (s : Back) (key : ℕ) :
    potential (s.clear key) + occupied (s.reg key) = potential s := by
  by_cases hz : s.reg key = 0
  · have eq := erase_idle s.reg hz
    simp [potential,Back.clear,eq,occupied,show s.reg key = .zero from hz.trans (Fact.out : (0 : Ref) = Ref.zero)]
  · have eq := erase_live s.reg hz
    simp only [potential,Back.clear,occupied,show s.reg key ≠ .zero from fun hh => hz (hh.trans (Fact.out : (0 : Ref) = Ref.zero).symm),ite_false]
    omega

theorem merge_potential (s : Back) (key : ℕ) (v : Ref) :
    potential (s.merge key v) ≤ potential s + occupied v := by
  have h := merge_budget Fact.out s.gs s.reg key v
  simp only [potential, Back.merge, List.length_append, occupied]
  omega

theorem scale_length (gs : List Gate) (a b : Ref) :
    (scale gs a b).added.length ≤ 1 := by
  classical
  dsimp only [scale]
  split
  · split
    · exact Nat.zero_le _
    · cases a <;> cases b <;> simp [combine,pushWire]
  · decide

theorem scale_zero_left (gs : List Gate) (b : Ref) :
    scale gs .zero b = ⟨[],.zero⟩ := by
  have hem : termSupport gs .zero b = ∅ := by
    ext p
    simp [support_iff,Ref.val]
  simp [scale,hem]

theorem scaled_potential (scalar : ℕ → Ref) (s : Back) (dst f : ℕ) :
    potential (scaled scalar s dst f) ≤ potential (s.clear dst) + 1 := by
  let p := product scalar s dst f
  have hle : p.added.length ≤ 1 := scale_length _ _ _
  change (s.gs ++ p.added).length + (s.reg.erase dst).support.card +
      (if p.added.isEmpty then insert dst s.skipped else s.skipped).card ≤
        s.gs.length + (s.reg.erase dst).support.card + s.skipped.card + 1
  rw [List.length_append]
  by_cases hz : p.added.isEmpty = true
  · simp only [hz,ite_true]
    have empty := List.isEmpty_iff.mp hz
    rw [empty] at *
    have := Finset.card_insert_le dst s.skipped
    simp only [List.length_nil] at *
    omega
  · simp [hz]
    omega

theorem occupied_product_le (scalar : ℕ → Ref) (s : Back) (dst f : ℕ) :
    occupied (product scalar s dst f).ref ≤ occupied (s.reg dst) := by
  by_cases hz : s.reg dst = .zero
  · simp [occupied,product,hz,scale_zero_left]
  · simp only [occupied, hz, ite_false]
    split <;> decide

theorem step_potential (scalar : ℕ → Ref) (a : Assignment) (s : Back) :
    potential (step scalar a s) ≤ potential s + credit a := by
  have hc := clear_potential s a.dst
  have cap : occupied (s.reg a.dst) ≤ 1 := by unfold occupied; split <;> decide
  cases ho : a.op with
  | zero =>
    simp only [step,ho,credit,Nat.add_zero]
    omega
  | copy u =>
    simp only [step,ho,credit,Nat.add_zero]
    have := merge_potential (s.clear a.dst) u (s.reg a.dst)
    omega
  | add u v =>
    simp only [step,ho,credit]
    have h1 := merge_potential (s.clear a.dst) u (s.reg a.dst)
    have h2 := merge_potential ((s.clear a.dst).merge u (s.reg a.dst)) v (s.reg a.dst)
    omega
  | scale u f =>
    simp only [step,ho,credit]
    have h1 := scaled_potential scalar s a.dst f
    have h2 := merge_potential (scaled scalar s a.dst f) u (product scalar s a.dst f).ref
    have h3 := occupied_product_le scalar s a.dst f
    omega

theorem sweep_potential (scalar : ℕ → Ref) (ops : List Assignment) (s : Back) :
    potential (sweep scalar ops s) ≤ potential s + (ops.map credit).sum :=
  fold_budget ops (step scalar) potential s (step_potential scalar)

theorem support_le_of_demanded {N : ℕ} (regs : ℕ →₀ Ref) (src : Fin N → ℕ)
    (inj : Function.Injective src) (hne : ∀ i, regs (src i) ≠ 0) :
    N ≤ regs.support.card := by
  let f : Fin N → regs.support := fun i => ⟨src i,Finsupp.mem_support_iff.mpr (hne i)⟩
  have hi : Function.Injective f := fun _ _ he => inj (congrArg Subtype.val he)
  calc
    N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
    _ ≤ Fintype.card regs.support := Fintype.card_le_of_injective f hi
    _ = regs.support.card := Fintype.card_coe _

end PlaneArcBudget

end SourceReverseCount

section SourceAssemblyRows

namespace PlaneArcAssembly
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.Outside.L_meta_17597_aux.CircuitNormalization.Deg2
open PlaneArcFirst PlaneArcTranspose PlaneArcEmit PlaneArcBudget ArcAffineCut

abbrev ops (C : Circuit) := compile (ofCircuit 13 C)
abbrev src (i : Fin 13) := 13+i.val

structure Program (C : Circuit) where
  gs : List Gate
  sc : ℕ → Ref
  ok : GatesOk gs
  valid : ∀ w, Ref.Valid gs (sc w)
  cost : gs.length + opCost (ops C) ≤ C.size
  coeff : ∀ (x : Fin 13 → Bool) (w : Fin 13), C.eval (List.ofFn (pointOnly x)) = false →
    (C.eval (List.ofFn (oneLine x w)) = true ↔
      forward (fun f => Ref.val gs x (sc f) = true) (ops C) (fun i => i = src w) C.output)

theorem program_exists {C : Circuit} (m : Monotone2 C) (d : HasLineDegree 26 (Finset.Ico 13 26) C 1)
    (p : OrigPositive C) : Nonempty (Program C) := by
  obtain ⟨gs,sc,h1,h2,h3,h4⟩ := physical_coefficients C m d (output_lt p)
  exact ⟨⟨gs,sc,h1,h2,h3,h4⟩⟩

variable {C : Circuit}
noncomputable abbrev Program.initial (P : Program C) := seed P.gs C.output
noncomputable abbrev Program.finalState (P : Program C) := sweep P.sc (ops C) P.initial
def Program.scalar (P : Program C) (p : Fin 13) (f : ℕ) := Ref.val P.gs (e1 p) (P.sc f) = true

theorem Program.final_ok (P : Program C) : P.finalState.Ok :=
  sweep_ok P.sc (ops C) (seed_ok _ _ P.ok) P.valid

theorem Program.forward_one (P : Program C) (hs : OrigSound C) (hp : OrigPositive C)
    (w p : Fin 13) :
    forward (P.scalar p) (ops C) (fun i => i = src w) C.output ↔ p ∈ line w := by
  have ha : Arc ({p} : Points) := ArcTerminalBridge.arc_small (by simp)
  have hoff := orig_off hs ha
  rw [bits_one] at hoff
  unfold Program.scalar
  rw [← P.coeff _ w hoff]
  constructor
  · intro hx
    rw [←bits_one] at hx
    obtain ⟨v,hv,he⟩ := orig_sound hs ha w hx
    simpa only [Finset.mem_singleton.mp he] using hv
  · exact orig_pos hp p w

theorem Program.final_one (P : Program C) (hs : OrigSound C) (hp : OrigPositive C)
    (w p : Fin 13) : P.finalState.eval (e1 p) (src w) ↔ p ∈ line w := by
  rw [←P.forward_one hs hp w p, transpose_coefficient]
  have hh := sweep_singleton P.sc (ops C) (seed_ok _ C.output P.ok) P.valid p (src w)
  rw [seed_eval] at hh
  exact hh

theorem Program.final_sound (P : Program C) (hs : OrigSound C) (w : Fin 13) {X : Points}
    (hx : Arc X) (hd : Disjoint X (line w)) : ¬ P.finalState.eval (bits X) (src w) := by
  intro h
  have hh := sweep_sound P.sc (ops C) (seed_ok _ _ P.ok) P.valid _ _ h
  rw [seed_eval, ←transpose_coefficient] at hh
  have accepted := (P.coeff (bits X) w (orig_off hs hx)).mpr hh
  obtain ⟨p,hp,hX⟩ := orig_sound hs hx w accepted
  exact Finset.disjoint_left.mp hd hX hp

theorem Program.row_wire (P : Program C) (hs : OrigSound C) (hp : OrigPositive C) (w : Fin 13) :
    ∃ o, P.finalState.reg (src w) = .wire o ∧ V P.finalState.gs o = line w ∧
      ArcTerminalBridge.Sound w (ArcRawTerminal.sig P.finalState.gs o) := by
  have sing := P.final_one hs hp w
  cases hh : P.finalState.reg (src w) with
  | zero =>
    have hdiag : ∀ i : Fin 13, i ∈ line i := by decide
    have hw := hdiag w
    have z := (sing w).mpr hw
    simp only [Back.eval,hh,Ref.val,Bool.false_eq_true] at z
  | one =>
    have h := P.final_sound hs w (X := ∅) (ArcTerminalBridge.arc_small (by simp)) (by simp)
    exact False.elim (h (by simp [Back.eval,hh,Ref.val]))
  | wire o =>
    refine ⟨o,rfl,?_,?_⟩
    · ext p
      rw [mem_V]; simpa only [Back.eval,hh,Ref.val] using sing p
    · intro X hd hx haccepted
      apply P.final_sound hs w hx hd
      change Ref.val _ _ _ = true
      rw [hh]
      exact haccepted

theorem baseline_row {gs : List Gate} (ok : GatesOk gs) {w : Fin 13} {o : ℕ}
    (hv : V gs o = line w) (hs : ArcTerminalBridge.Sound w (ArcRawTerminal.sig gs o)) :
    9 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  obtain ⟨g,hg,rfl⟩ := gate_idx_of_V_ge2 gs o (by rw [hv,card_line]; decide)
  apply PlaneArcCharge.baseline gs w g _ hg ok hv (ArcRawTerminal.pair_safe_to_bool
    (fun X hX hd => hs X hd (ArcTerminalBridge.arc_small hX)))
  · exact (Finset.filter_subset _ _).trans (Finset.range_mono (by omega))
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _

theorem Program.final_budget (P : Program C)
    (live : ∀ w : Fin 13, P.finalState.reg (src w) ≠ 0) :
    P.finalState.gs.length + 12 + P.finalState.skipped.card ≤ C.size := by
  have hc := sweep_potential P.sc (ops C) P.initial
  have cap := P.cost
  have same : ((ops C).map credit).sum = opCost (ops C) := by
    rfl
  have nz : (Ref.one : Ref) ≠ 0 := by rw [(Fact.out : (0 : Ref) = Ref.zero)]; decide
  have regs := support_le_of_demanded P.finalState.reg src (fun _ _ h => Fin.ext (by simpa [src] using h)) live
  change potential P.finalState ≤ potential (seed P.gs C.output) + _ at hc
  rw [same] at hc
  simp only [potential,seed,Finsupp.support_single _ nz,Finset.card_singleton,Finset.card_empty,Nat.add_zero] at hc
  omega

end PlaneArcAssembly

end SourceAssemblyRows

section SourceCutBridge

namespace PlaneArcFirst
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcTranspose PlaneArcEmit PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.Outside.L_meta_17597_aux.CircuitNormalization.Deg2

lemma skipped_step (sc : ℕ → Ref) (a : Assignment) (s : Back) :
    s.skipped ⊆ (step sc a s).skipped := by
  cases a with | mk dst op =>
    cases op with
    | zero | add | copy => exact Finset.Subset.rfl
    | scale u f =>
      change s.skipped ⊆ (if (product sc s dst f).added.isEmpty then insert dst s.skipped else s.skipped)
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.rfl

lemma skipped_sweep (sc : ℕ → Ref) (l : List Assignment) (s : Back) :
    s.skipped ⊆ (sweep sc l s).skipped := by
  induction l with
  | nil => exact Finset.Subset.rfl
  | cons a l ih => exact ih.trans (skipped_step sc a (sweep sc l s))

lemma Cut.split_sweep {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back) :
    sweep sc ops s = sweep sc k.pre (step sc k.a (sweep sc k.post s)) := by
  obtain ⟨pre,a,post,rfl⟩ := k
  simp [sweep,List.foldr_append]

theorem cut_skipped {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back) {u f : ℕ}
    (ho : k.a.op = .scale u f)
    (empty : (product sc (sweep sc k.post s) k.a.dst f).added = []) :
    k.a.dst ∈ (sweep sc ops s).skipped := by
  rw [k.split_sweep]
  apply skipped_sweep
  simp [step,ho,scaled,Back.merge,empty]

lemma scale_shape {gs : List Gate} {a b : Ref} (h : (scale gs a b).added ≠ []) :
    ∃ i j : ℕ, a = .wire i ∧ b = .wire j ∧ scale gs a b = pushWire gs true i j := by
  classical
  have he : scale gs a b = PlaneArcEmit.combine gs true a b := by
    unfold scale at *
    dsimp only at *
    split at *
    · split at *
      · contradiction
      · simp_all
    · contradiction
  rw [he] at h ⊢
  cases a <;> cases b <;> simp_all [PlaneArcEmit.combine,pushWire]

lemma cut_product_ext {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back)
    (ext : ∀ ops st, Ext st (sweep sc ops st)) {u f : ℕ} (ho : k.a.op = .scale u f) :
    Ext (scaled sc (sweep sc k.post s) k.a.dst f) (sweep sc ops s) := by
  rw [k.split_sweep]
  have e := ext k.pre (step sc k.a (sweep sc k.post s))
  apply Ext.trans _ e
  simp only [step,ho]
  exact merge_ext _ _ _

theorem cut_emitted {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back)
    (ext : ∀ ops st, Ext st (sweep sc ops st)) {u f : ℕ} (ho : k.a.op = .scale u f)
    (ok : (sweep sc k.post s).Ok) (vf : Ref.Valid (sweep sc k.post s).gs (sc f))
    (emitted : (product sc (sweep sc k.post s) k.a.dst f).added ≠ []) :
    let mid := sweep sc k.post s
    let fin := sweep sc ops s
    ∃ A B : ℕ, mid.reg k.a.dst = .wire A ∧ sc f = .wire B ∧
      product sc mid k.a.dst f = pushWire mid.gs true A B ∧
      A < 13 + mid.gs.length ∧ B < 13 + mid.gs.length ∧
      mid.gs.length < fin.gs.length ∧ fin.gs[mid.gs.length]? = some (binGate true A B) ∧
      2 ≤ (termSupport mid.gs (mid.reg k.a.dst) (sc f)).card := by
  let mid := sweep sc k.post s
  obtain ⟨A,B,hA,hB,hp⟩ := scale_shape emitted
  have ha := ok.2 k.a.dst
  rw [hA] at ha
  rw [hB] at vf
  have ext' := cut_product_ext k sc s ext ho
  obtain ⟨suffix,hsuf⟩ := ext'
  change (sweep sc ops s).gs =
    (mid.gs ++ (product sc mid k.a.dst f).added) ++ suffix at hsuf
  change product sc mid k.a.dst f = pushWire mid.gs true A B at hp
  rw [hp] at hsuf
  refine ⟨A,B,hA,hB,hp,ha,vf,?_,?_,?_⟩
  · change mid.gs.length < (sweep sc ops s).gs.length
    rw [hsuf]; simp [pushWire]
  · change (sweep sc ops s).gs[mid.gs.length]? = some (binGate true A B)
    rw [hsuf,List.append_assoc]; simp [pushWire]
  · change 2 ≤ (termSupport mid.gs (mid.reg k.a.dst) (sc f)).card
    by_contra! hsmall
    apply emitted
    apply (scale_spec mid.gs _ _ ok.1 (ok.2 k.a.dst) (hB ▸ vf)).2.2.2.2.2
    exact Nat.le_of_lt_succ hsmall

theorem cut_active_iff {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back)
    (coeff : Fin 13 → ℕ → Prop) (out : ℕ) {u f : ℕ}
    (ho : k.a.op = .scale u f)
    (hval : ∀ p, (sweep sc k.post s).eval (e1 p) k.a.dst ↔
      reverse (coeff p) k.post (fun i => i = out) k.a.dst)
    (hco : ∀ p, Ref.val (sweep sc k.post s).gs (e1 p) (sc f) = true ↔ coeff p f)
    (p : Fin 13) :
    p ∈ termSupport (sweep sc k.post s).gs
      ((sweep sc k.post s).reg k.a.dst) (sc f) ↔ k.active (coeff p) out := by
  rw [support_iff]
  change ((sweep sc k.post s).eval (e1 p) k.a.dst ∧ _) ↔ _
  rw [hval,hco]
  constructor
  · rintro ⟨hd,hf⟩
    exact ⟨u,f,ho,hf,hd⟩
  · rintro ⟨u',f',ho',hf,hd⟩
    obtain ⟨rfl,rfl⟩ := LinearOp.scale.inj (ho.symm.trans ho')
    exact ⟨hd,hf⟩

theorem cut_wire_support {ops} (k : Cut ops) (sc : ℕ → Ref) (s : Back)
    (ext : ∀ ops st, Ext st (sweep sc ops st)) {u f : ℕ} (ho : k.a.op = .scale u f)
    (ok : (sweep sc k.post s).Ok) (vf : Ref.Valid (sweep sc k.post s).gs (sc f))
    {A B : ℕ} (hp : product sc (sweep sc k.post s) k.a.dst f =
      pushWire (sweep sc k.post s).gs true A B) (p : Fin 13) :
    let mid := sweep sc k.post s
    wval (sweep sc ops s).gs (13 + mid.gs.length) (e1 p) = true ↔
      p ∈ termSupport mid.gs (mid.reg k.a.dst) (sc f) := by
  let mid := sweep sc k.post s
  have hs := scale_spec mid.gs (mid.reg k.a.dst) (sc f) ok.1 (ok.2 k.a.dst) vf
  have he := cut_product_ext k sc s ext ho
  let r := product sc mid k.a.dst f
  have valid : Ref.Valid (scaled sc mid k.a.dst f).gs r.ref := hs.1
  have sat := he.stable valid (e1 p)
  have ev := hs.2.2.2.2.1 p
  change Ref.val (scaled sc mid k.a.dst f).gs (e1 p) r.ref = _ at ev
  have idr : r.ref = .wire (13 + mid.gs.length) := congrArg Result.ref hp
  change wval _ (13+mid.gs.length) _ = true ↔ _
  rw [support_iff]
  change Ref.val (sweep sc ops s).gs (e1 p) (.wire (13+mid.gs.length)) = true ↔ _
  rw [←idr,sat,ev,Bool.and_eq_true]

theorem compilePrefix_dsts {N : ℕ} (D : Dag N) (t : ℕ) :
    (compilePrefix D t).map Assignment.dst = (List.range t).map (fun i => N+N+i) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [compilePrefix,ih,List.range_succ]

theorem Cut.compile_dst {N : ℕ} {D : Dag N} (k : Cut (compile D)) :
    k.a.dst = N+N+k.idx.val := by
  have eq := compilePrefix_dsts D D.size
  change (compile D).map Assignment.dst = _ at eq
  have get := congrArg (fun l : List ℕ => l[k.idx.val]?) eq
  have hi : k.idx.val < (compile D).length := k.idx.isLt
  have hl := congrArg List.length eq
  simp only [List.length_map,List.length_range] at hl
  have hi' : k.idx.val < D.size := hl ▸ hi
  rw [← k.get_idx]
  simpa [List.getElem?_map,hi,hi'] using get

theorem compile_cut_dest_injective {N : ℕ} (D : Dag N) :
    Function.Injective (fun k : Cut (compile D) => k.a.dst) := by
  intro k p he
  change k.a.dst = p.a.dst at he
  rw [k.compile_dst,p.compile_dst] at he
  apply Cut.idx_injective (compile D)
  exact Fin.ext (by omega)

end PlaneArcFirst

end SourceCutBridge

section SourceRowChoice

namespace PlaneArcFirst
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcEmit PlaneArcTranspose PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PEqualNP.Outside.L_meta_17597_aux.CircuitNormalization.Deg2

structure Selection (ops : List Assignment) (src : Fin 13 → ℕ) (out : ℕ)
    (coeff : Fin 13 → ℕ → Prop) where
  pick : Fin 13 → Cut ops
  inj : Function.Injective pick
  raw : ∀ i, (pick i).raw (src i)
  pos : ∀ i, (pick i).active (coeff i) out
  row : ∀ i p, (pick i).active (coeff p) out → Incident i p

theorem choose_rows (ops : List Assignment) (src : Fin 13 → ℕ) (out : ℕ)
    (coeff : Fin 13 → ℕ → Prop)
    (sound : ∀ i p, forward (coeff p) ops (fun w => w = src i) out → Incident i p)
    (diag : ∀ i, forward (coeff i) ops (fun w => w = src i) out) :
    Nonempty (Selection ops src out coeff) := by
  letI : DecidableRel Incident := incDec
  have missing : ∀ i, ∃ p, ¬ Incident i p := by decide
  have cross : ∀ i j, Incident i j → Incident j i → i = j := by decide
  obtain ⟨rect,all⟩ := scale_cover ops src out coeff _ sound diag missing
  choose pick raw act using all
  have row (i p : Fin 13) (yes : (pick i).active (coeff p) out) :=
    rect (pick i) i p (raw i) yes
  refine ⟨⟨pick,?_,raw,act,row⟩⟩
  intro i j he
  exact cross i j (row i j (by rw [he]; exact act j)) (row j i (by rw [←he]; exact act i))

def skippedRows {ops src out coeff} (sel : Selection ops src out coeff) (skips : Finset ℕ) :
    Finset (Fin 13) := Finset.univ.filter (fun i => (sel.pick i).a.dst ∈ skips)

theorem skippedRows_card {D : Dag 13} {src out coeff}
    (sel : Selection (compile D) src out coeff) (skips : Finset ℕ) :
    (skippedRows sel skips).card ≤ skips.card := by
  apply Finset.card_le_card_of_injOn (fun i => (sel.pick i).a.dst)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · exact ((compile_cut_dest_injective D).comp sel.inj).injOn

def singletonCoeff (gs : List Gate) (sc : ℕ → Ref) (p : Fin 13) (f : ℕ) : Prop :=
  Ref.val gs (e1 p) (sc f) = true

theorem cut_seed_active {ops} (k : Cut ops) (sc : ℕ → Ref) (gs : List Gate) (out : ℕ)
    (ok : GatesOk gs) (valid : ∀ f, Ref.Valid gs (sc f))
    {u f : ℕ} (ho : k.a.op = .scale u f) (p : Fin 13) :
    let mid := sweep sc k.post (seed gs out)
    p ∈ termSupport mid.gs (mid.reg k.a.dst) (sc f) ↔
      k.active (singletonCoeff gs sc p) out := by
  apply cut_active_iff k sc (seed gs out) (singletonCoeff gs sc) out ho
  · intro q
    have h := sweep_singleton sc k.post (seed_ok gs out ok) valid q k.a.dst
    rw [seed_eval] at h
    exact h
  · intro q
    have e := (sweep_ext sc k.post (seed gs out)).stable (valid f) (e1 q)
    change Ref.val _ _ _ = true ↔ Ref.val gs _ _ = true
    rw [e]
    rfl

theorem kept_row {ops src out} (gs : List Gate) (sc : ℕ → Ref)
    (sel : Selection ops src out (singletonCoeff gs sc))
    (ok : GatesOk gs) (valid : ∀ f, Ref.Valid gs (sc f)) (i : Fin 13)
    (kept : i ∉ skippedRows sel (sweep sc ops (seed gs out)).skipped) :
    let k := sel.pick i
    let mid := sweep sc k.post (seed gs out)
    let fin := sweep sc ops (seed gs out)
    ∃ u f A B : ℕ, k.a.op = .scale u f ∧
      k.raw (src i) ∧
      product sc mid k.a.dst f = pushWire mid.gs true A B ∧
      A < 13 + mid.gs.length ∧ B < 13 + mid.gs.length ∧
      mid.gs.length < fin.gs.length ∧ fin.gs[mid.gs.length]? = some (binGate true A B) ∧
      2 ≤ (V fin.gs (13+mid.gs.length)).card ∧
      ∀ p, p ∈ V fin.gs (13+mid.gs.length) ↔ k.active (singletonCoeff gs sc p) out := by
  let k := sel.pick i
  let mid := sweep sc k.post (seed gs out)
  let fin := sweep sc ops (seed gs out)
  have hi : k.a.dst ∉ fin.skipped := fun h => kept (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨u,f,ho,hraw⟩ := sel.raw i
  have notempty : (product sc mid k.a.dst f).added ≠ [] :=
    fun he => hi (cut_skipped k sc _ ho he)
  have hm := sweep_ok sc k.post (seed_ok gs out ok) valid
  have hv : Ref.Valid mid.gs (sc f) := (sweep_ext sc k.post (seed gs out)).valid (valid f)
  obtain ⟨A,B,_,_,hp,hA,hB,ht,hget,hsize⟩ :=
    cut_emitted k sc _ (sweep_ext sc) ho hm hv notempty
  have sig : V fin.gs (13+mid.gs.length) = termSupport mid.gs (mid.reg k.a.dst) (sc f) := by
    ext p
    have h := cut_wire_support k sc (seed gs out) (sweep_ext sc) ho hm hv hp p
    simpa [V,fin,mid] using h
  refine ⟨u,f,A,B,ho,sel.raw i,hp,hA,hB,ht,hget,?_,?_⟩
  · change 2 ≤ (V fin.gs (13+mid.gs.length)).card
    rw [sig]
    exact hsize
  · intro p
    change p ∈ V fin.gs (13+mid.gs.length) ↔ _
    rw [sig]
    exact cut_seed_active k sc gs out ok valid ho p

end PlaneArcFirst

end SourceRowChoice

section SourceOrPath

namespace PlaneArcEmit
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PEqualNP.CircuitLowerBounds

def OrEdge (gs : List Gate) (u v : ℕ) : Prop :=
  ∃ j l r, v = 13+j ∧ gs[j]? = some (binGate false l r) ∧
    (u=l ∨ u=r) ∧ l<v ∧ r<v

def RefPath (gs : List Gate) : Ref → Ref → Prop
  | .zero, _ => True
  | _, .one => True
  | .wire a, .wire b => Relation.ReflTransGen (OrEdge gs) a b
  | _, _ => False

theorem RefPath.refl (gs : List Gate) (a : Ref) : RefPath gs a a := by
  cases a with
  | zero | one => trivial
  | wire a => exact Relation.ReflTransGen.refl

theorem RefPath.trans {gs : List Gate} {a b c : Ref} (hab : RefPath gs a b)
    (hbc : RefPath gs b c) : RefPath gs a c := by
  cases a <;> cases b <;> cases c <;> simp_all only [RefPath]
  exact hab.trans hbc

theorem RefPath.append {gs : List Gate} (more : List Gate) {a b : Ref} (h : RefPath gs a b) :
    RefPath (gs ++ more) a b := by
  cases a <;> cases b <;> simp_all only [RefPath]
  have liftEdge {i k : ℕ} : OrEdge gs i k → OrEdge (gs++more) i k := by
    rintro ⟨j,l,r,rfl,hget,hu,hl,hr⟩
    refine ⟨j,l,r,rfl,?_,hu,hl,hr⟩
    obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hget
    rw [List.getElem?_append_left hj]; exact hget
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ e ih => exact ih.tail (liftEdge e)

theorem Ext.path {s t : Back} (h : Ext s t) {a b : Ref} (hp : RefPath s.gs a b) :
    RefPath t.gs a b := by obtain ⟨more,hm⟩ := h; rw [hm]; exact hp.append more

private theorem combine_or_trace (gs : List Gate) (a b : Ref)
    (ha : Ref.Valid gs a) (hb : Ref.Valid gs b) :
    let p := combine gs false a b
    RefPath (gs ++ p.added) a p.ref ∧ RefPath (gs ++ p.added) b p.ref := by
  cases a with
  | zero => cases b <;> exact ⟨trivial, RefPath.refl _ _⟩
  | one => cases b <;> exact ⟨trivial, trivial⟩
  | wire u =>
    cases b with
    | zero => exact ⟨RefPath.refl _ _, trivial⟩
    | one => exact ⟨trivial, trivial⟩
    | wire v =>
      change Relation.ReflTransGen (OrEdge (gs ++ [binGate false u v])) u (13+gs.length) ∧
        Relation.ReflTransGen (OrEdge (gs ++ [binGate false u v])) v (13+gs.length)
      constructor
      · exact Relation.ReflTransGen.single ⟨gs.length,u,v,rfl,by simp,Or.inl rfl,ha,hb⟩
      · exact Relation.ReflTransGen.single ⟨gs.length,u,v,rfl,by simp,Or.inr rfl,ha,hb⟩

theorem merge_path_old {s : Back} (hs : s.Ok) (w : ℕ) (v : Ref) (hv : Ref.Valid s.gs v)
    (j : ℕ) : RefPath (s.merge w v).gs (s.reg j) ((s.merge w v).reg j) := by
  by_cases h : j=w
  · subst j
    simpa [Back.merge] using (combine_or_trace s.gs (s.reg w) v (hs.2 w) hv).1
  · simpa [Back.merge, Finsupp.update, Function.update_of_ne h, h] using
      RefPath.refl (s.merge w v).gs (s.reg j)

theorem merge_path_new {s : Back} (hs : s.Ok) (w : ℕ) (v : Ref) (hv : Ref.Valid s.gs v) :
    RefPath (s.merge w v).gs v ((s.merge w v).reg w) := by
  simpa [Back.merge] using (combine_or_trace s.gs (s.reg w) v (hs.2 w) hv).2

end PlaneArcEmit

end SourceOrPath

section SourcePhysicalTerminal

namespace ArcPhysicalTerminal
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_17597_aux.RowStructure
open ArcRawTerminal ArcTerminal ArcTerminalBridge ArcAffineCut PlaneArcEmit

lemma bin_and (gs : List Gate) (j a b : ℕ)
    (hget : gs[j]? = some (binGate true a b)) (ha : a<13+j) (hb : b<13+j) :
    ∀ x, sig gs (13+j) x ↔ sig gs a x ∧ sig gs b x := by
  intro x
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp hget
  unfold sig
  rw [wval_gate_eq gs j hj,he]
  simp [binGate,GateOp.eval,wvalAt,ha,hb]

lemma bin_or (gs : List Gate) (j a b : ℕ)
    (hget : gs[j]? = some (binGate false a b)) (ha : a<13+j) (hb : b<13+j) :
    ∀ x, sig gs (13+j) x ↔ sig gs a x ∨ sig gs b x := by
  intro x
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp hget
  unfold sig
  rw [wval_gate_eq gs j hj,he]
  simp [binGate,GateOp.eval,wvalAt,ha,hb]

lemma edge (gs : List Gate) {u v : ℕ} (h : OrEdge gs u v) :
    u<v ∧ ∃ p<v, ∀ x, sig gs v x ↔ sig gs u x ∨ sig gs p x := by
  obtain ⟨j,a,b,rfl,hget,hp,ha,hb⟩ := h
  have op := bin_or gs j a b hget ha hb
  rcases hp with rfl | rfl
  · exact ⟨ha,b,hb,op⟩
  · exact ⟨hb,a,ha,fun x => (op x).trans or_comm⟩

lemma walk {gs : List Gate} {t o : ℕ} (h : Relation.ReflTransGen (OrEdge gs) t o) :
    t≤o ∧ ∀ x, sig gs t x → sig gs o x := by
  induction h with
  | refl => exact ⟨le_rfl,fun _ h => h⟩
  | tail _ step ih =>
    obtain ⟨hlt,_,_,hop⟩ := edge gs step
    exact ⟨ih.1.trans hlt.le,fun x hx => (hop _).mpr (Or.inl (ih.2 x hx))⟩

lemma classify (gs : List Gate) (w : Pt) {t o : ℕ}
    (path : Relation.ReflTransGen (OrEdge gs) t o) (hO : V gs o = line w) :
    t=o ∨ (∃ u, t<u ∧ u<o ∧ V gs t ⊆ V gs u ∧ V gs u ⊆ line w) ∨
      ∃ u, u<o ∧ (∀ x, sig gs o x ↔ sig gs t x ∨ sig gs u x) := by
  obtain rfl | ⟨u,hp,edge'⟩ := path.cases_tail
  · exact Or.inl rfl
  obtain ⟨hu,z,hz,he⟩ := edge gs edge'
  by_cases h : t=u
  · exact Or.inr (Or.inr ⟨z,hz,h ▸ he⟩)
  have reach := walk hp
  refine Or.inr (Or.inl ⟨u,lt_of_le_of_ne reach.1 h,hu,?_,?_⟩)
  · intro p h
    exact (single gs _ _).mpr (reach.2 _ ((single gs _ _).mp h))
  · intro p h
    rw [←hO]
    exact (single gs _ _).mpr ((he _).mpr (Or.inl ((single gs _ _).mp h)))

theorem terminal_mass (gs : List Gate) (w : Pt) (j a b o : ℕ) (ho : valid gs)
    (hget : gs[j]? = some (binGate true a b)) (ha : a<13+j) (hb : b<13+j)
    (hO : V gs o = line w) (hcount : 2 ≤ (V gs (13+j)).card)
    (safe : Sound w (sig gs o)) (p : RefPath gs (.wire (13+j)) (.wire o)) :
    12 ≤ ∑ k ∈ Finset.range gs.length, PlaneArcCharge.weight w (PlaneArcCharge.signature gs k) := by
  change Relation.ReflTransGen (OrEdge gs) (13+j) o at p
  have walk' := walk p
  apply terminal_from_product gs w a b (13+j) o ho (bin_and gs j a b hget ha hb)
    _ _ hO hcount ha hb walk'.1 (classify gs w p hO)
  · exact fun x hd hArc hx => safe x hd hArc (walk'.2 x hx)
  · exact fun x hc hd => safe x hd (arc_small hc)

end ArcPhysicalTerminal

end SourcePhysicalTerminal

section SourceTermTrace

namespace PlaneArcEmit
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcTranspose PlaneArcFirst PEqualNP.CircuitLowerBounds

private theorem clear_reg_of_ne (s : Back) {dst w : ℕ} (hne : w ≠ dst) :
    (s.clear dst).reg w = s.reg w := Finsupp.erase_ne hne

private theorem scaled_reg_of_ne (sc : ℕ → Ref) (s : Back) {dst w : ℕ} (f : ℕ) (hne : w ≠ dst) :
    (scaled sc s dst f).reg w = s.reg w := Finsupp.erase_ne hne

private theorem step_path_old (sc : ℕ → Ref) {s : Back} (ok : s.Ok)
    (valid : ∀ f, Ref.Valid s.gs (sc f)) (a : Assignment) (j : ℕ) (hne : j ≠ a.dst) :
    RefPath (step sc a s).gs (s.reg j) ((step sc a s).reg j) := by
  obtain ⟨d,op⟩ := a
  change j ≠ d at hne
  have ht := clear_reg_of_ne s hne
  cases op with
  | zero =>
    change RefPath _ (s.reg j) ((s.clear d).reg j)
    rw [ht]; apply RefPath.refl
  | copy u =>
    exact ht ▸ merge_path_old (clear_ok ok d) u (s.reg d) (ok.2 d) j
  | add u v =>
    let a := (s.clear d).merge u (s.reg d)
    have ea : Ext (s.clear d) a := merge_ext _ _ _
    have pa : RefPath a.gs (s.reg j) (a.reg j) :=
      ht ▸ merge_path_old (clear_ok ok d) u (s.reg d) (ok.2 d) j
    have va : Ref.Valid a.gs (s.reg d) := ea.valid (ok.2 d)
    have oka : a.Ok := merge_ok (clear_ok ok d) u (ok.2 d)
    exact ((merge_ext a v (s.reg d)).path pa).trans (merge_path_old oka v _ va j)
  | scale u f =>
    have h := scaled_ok sc ok d f (valid f)
    have ht' := scaled_reg_of_ne sc s f hne
    exact ht' ▸ merge_path_old h.1 u _ h.2 j

private theorem step_path_new (sc : ℕ → Ref) {s : Back} (ok : s.Ok) (a : Assignment) (j : ℕ)
    (he : a.op.edge disabled j) :
    RefPath (step sc a s).gs (s.reg a.dst) ((step sc a s).reg j) := by
  obtain ⟨d,op⟩ := a
  cases op with
  | zero => exact False.elim he
  | scale u f => exact False.elim he.2
  | copy u =>
    change j = u at he
    subst j
    exact merge_path_new (clear_ok ok d) u _ (ok.2 d)
  | add u v =>
    let a := (s.clear d).merge u (s.reg d)
    have ea : Ext (s.clear d) a := merge_ext _ _ _
    have va : Ref.Valid a.gs (s.reg d) := ea.valid (ok.2 d)
    have oka : a.Ok := merge_ok (clear_ok ok d) u (ok.2 d)
    rcases he with je | je
    · subst j
      have p : RefPath a.gs (s.reg d) (a.reg u) := merge_path_new (clear_ok ok d) u _ (ok.2 d)
      exact ((merge_ext a v (s.reg d)).path p).trans (merge_path_old oka v _ va u)
    · subst j
      exact merge_path_new oka v _ va

theorem sweep_disabled_paths (sc : ℕ → Ref) (ops : List Assignment) {s : Back} (ok : s.Ok)
    (valid : ∀ f, Ref.Valid s.gs (sc f)) (root : Ref) (demand : ℕ → Prop)
    (seed : ∀ j, demand j → RefPath s.gs root (s.reg j)) (w : ℕ)
    (h : reverse disabled ops demand w) :
    RefPath (sweep sc ops s).gs root ((sweep sc ops s).reg w) := by
  induction ops generalizing w with
  | nil => exact seed w h
  | cons a tail ih =>
    let t := sweep sc tail s
    have okay : t.Ok := sweep_ok sc tail ok valid
    have hv : ∀ f, Ref.Valid t.gs (sc f) := fun f => (sweep_ext sc tail s).valid (valid f)
    change a.pull disabled (reverse disabled tail demand) w at h
    change RefPath (step sc a t).gs root ((step sc a t).reg w)
    rcases h with ⟨hne,hold⟩ | ⟨hnew,he⟩
    · exact ((step_ext sc a t).path (ih w hold)).trans (step_path_old sc okay hv a w hne)
    · exact ((step_ext sc a t).path (ih a.dst hnew)).trans (step_path_new sc okay a w he)

theorem cut_or_trace (sc : ℕ → Ref) (init : Back) (ok : init.Ok)
    (valid : ∀ f, Ref.Valid init.gs (sc f)) {ops : List Assignment}
    (k : Cut ops) (u f src : ℕ) (hop : k.a.op = .scale u f)
    (hraw : forward disabled k.pre (fun j => j = src) u) :
    let after := sweep sc k.post init
    let final := sweep sc ops init
    RefPath final.gs (product sc after k.a.dst f).ref (final.reg src) := by
  let after := sweep sc k.post init
  let next := step sc k.a after
  let term := (product sc after k.a.dst f).ref
  have okA : after.Ok := sweep_ok sc k.post ok valid
  have vA : ∀ f, Ref.Valid after.gs (sc f) := fun f => (sweep_ext sc k.post init).valid (valid f)
  have okN : next.Ok := step_ok sc okA vA k.a
  have vN : ∀ f, Ref.Valid next.gs (sc f) := fun f => (step_ext sc k.a after).valid (vA f)
  have seed : RefPath next.gs term (next.reg u) := by
    have hs := scaled_ok sc okA k.a.dst f (vA f)
    simpa only [next, step, hop, term] using merge_path_new hs.1 u _ hs.2
  have p := sweep_disabled_paths sc k.pre okN vN term (fun w => w = u)
    (fun w hw => hw.symm ▸ seed) src ((transpose_coefficient k.pre disabled src u).mp hraw)
  have finalEq : sweep sc ops init = sweep sc k.pre next := by
    calc
      _ = sweep sc (k.pre ++ k.a :: k.post) init := congrArg (fun p => sweep sc p init) k.ordered
      _ = _ := by simp only [sweep, List.foldr_append, List.foldr_cons, next, after]
  change RefPath (sweep sc ops init).gs term ((sweep sc ops init).reg src)
  rw [finalEq]; exact p

end PlaneArcEmit

end SourceTermTrace

section SourceBillable

namespace PlaneArcEmit
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PlaneArcTranspose PlaneArcFirst PEqualNP.Outside.L_meta_17597_aux.RowStructure PEqualNP.CircuitLowerBounds
open ArcRawTerminal ArcTerminalBridge

theorem billable {ops src out} (gs : List Gate) (sc : ℕ → Ref)
    (sel : Selection ops src out (singletonCoeff gs sc))
    (ok : GatesOk gs) (valid : ∀ f, Ref.Valid gs (sc f)) (i : Fin 13)
    (kept : i ∉ skippedRows sel (sweep sc ops (seed gs out)).skipped)
    {o : ℕ} (row : (sweep sc ops (seed gs out)).reg (src i) = .wire o)
    (hO : V (sweep sc ops (seed gs out)).gs o = line i)
    (safe : Sound i (sig (sweep sc ops (seed gs out)).gs o)) :
    12 ≤ ∑ j ∈ Finset.range (sweep sc ops (seed gs out)).gs.length,
      PlaneArcCharge.weight i (PlaneArcCharge.signature (sweep sc ops (seed gs out)).gs j) := by
  let k := sel.pick i
  let init := seed gs out
  let mid := sweep sc k.post init
  let fin := sweep sc ops init
  obtain ⟨u,f,a,b,hop,raw,hp,ha,hb,_,hget,size,_⟩ := kept_row gs sc sel ok valid i kept
  obtain ⟨u',f',hop',trace⟩ := raw
  obtain ⟨rfl,rfl⟩ := LinearOp.scale.inj (hop.symm.trans hop')
  have initOk := seed_ok gs out ok
  have path := cut_or_trace sc init initOk valid k _ _ (src i) hop trace
  change RefPath fin.gs (product sc mid k.a.dst _).ref (fin.reg (src i)) at path
  change fin.reg (src i) = .wire o at row
  change product sc mid k.a.dst _ = pushWire mid.gs true a b at hp
  rw [hp,row] at path
  exact ArcPhysicalTerminal.terminal_mass fin.gs i mid.gs.length a b o
    (sweep_ok sc ops initOk valid).1 hget ha hb hO size safe path

end PlaneArcEmit

end SourceBillable

section SourceAssembly

namespace PlaneArcAssembly
variable [zinst : Zero PlaneArcEmit.Ref] [Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero)]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17597_aux.RowStructure
open PlaneArcFirst PlaneArcTranspose PlaneArcEmit

theorem lower_bound {C : Circuit} (m : Monotone2 C) (d : HasLineDegree 26 (Finset.Ico 13 26) C 1)
    (hs : OrigSound C) (hp : OrigPositive C) : 64 ≤ C.size := by
  classical
  obtain ⟨P⟩ := program_exists m d hp
  have diag : ∀ i : Fin 13, i ∈ line i := by decide
  obtain ⟨sel⟩ := choose_rows (ops C) src C.output (singletonCoeff P.gs P.sc)
    (fun i p h => (mem_line_iff i p).mp ((P.forward_one hs hp i p).mp h))
    (fun i => (P.forward_one hs hp i i).mpr (diag i))
  let S := skippedRows sel P.finalState.skipped
  have skips : S.card ≤ P.finalState.skipped.card := skippedRows_card sel _
  have nonzero (i : Fin 13) : P.finalState.reg (src i) ≠ 0 := by
    obtain ⟨o,hr,_,_⟩ := P.row_wire hs hp i
    rw [hr]
    rw [(Fact.out : (0 : Ref) = Ref.zero)]; exact Ref.noConfusion
  have cost := P.final_budget nonzero
  apply PlaneArcCharge.global_bound S (fun k : Fin P.finalState.gs.length =>
    PlaneArcCharge.signature P.finalState.gs k.val) (by omega)
  intro i
  obtain ⟨o,hr,hv,safe⟩ := P.row_wire hs hp i
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    PlaneArcCharge.weight i (PlaneArcCharge.signature P.finalState.gs k)) P.finalState.gs.length]
  by_cases h : i ∈ S
  · rw [ite_eq_left h]
    exact baseline_row P.final_ok.1 hv safe
  · rw [ite_eq_right h]
    exact billable P.gs P.sc sel P.ok P.valid i h hr hv safe

end PlaneArcAssembly

end SourceAssembly

end PEqualNP.Outside.L_meta_17597_aux

namespace PEqualNP.Outside.L_meta_17597_aux

namespace Geometry5254

abbrev D : Finset (Fin 13) := {0,1,3,9}
abbrev Arc (S : Finset (Fin 13)) : Prop := ∀ l : Fin 13, (S.filter (fun p => p-l ∈ D)).card ≤ 2

abbrev Inc (p w : Fin 13) : Prop := ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d

def pt (w d : ℕ) : ℕ := (w + d) % 13

def missB (a w : ℕ) : Bool :=
  !a.testBit (pt w 0) && !a.testBit (pt w 1) && !a.testBit (pt w 3) && !a.testBit (pt w 9)

def no3 (x y z : Bool) : Bool := !(x && y && z)

def arcB (a : ℕ) : Bool :=
  (List.range 13).all fun w =>
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 1)) (a.testBit (pt w 3)) &&
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 1)) (a.testBit (pt w 9)) &&
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 3)) (a.testBit (pt w 9)) &&
    no3 (a.testBit (pt w 1)) (a.testBit (pt w 3)) (a.testBit (pt w 9))

def lm (w : ℕ) : ℕ := 2 ^ pt w 0 + 2 ^ pt w 1 + 2 ^ pt w 3 + 2 ^ pt w 9

def ncB (l m n : ℕ) : Bool := (lm l &&& lm m &&& lm n) == 0

def onB (p w : ℕ) : Bool := p == pt w 0 || p == pt w 1 || p == pt w 3 || p == pt w 9

def goodB (a : ℕ) : Bool :=
  (List.range 13).any (fun l => missB a l) &&
  (List.range 13).all (fun l => !missB a l ||
    (List.range 13).any fun m => missB a m && (List.range 13).any fun n => missB a n && ncB l m n)

def chk (a : ℕ) : Bool := !arcB a || goodB a

theorem chk_all : ∀ k < 64, ∀ j < 128, chk (128 * k + j) = true := by decide +kernel

theorem chk_at (a : ℕ) (h : a < 8192) : chk a = true := by
  have := chk_all (a / 128) (by omega) (a % 128) (by omega)
  rwa [Nat.div_add_mod] at this

def msk (f : Fin 13 → Bool) : ℕ := Nat.ofBits f

theorem msk_bit (f : Fin 13 → Bool) (i : ℕ) (h : i < 13) : (msk f).testBit i = f ⟨i, h⟩ :=
  Nat.testBit_ofBits_lt f i h

theorem msk_lt (f : Fin 13 → Bool) : msk f < 8192 :=
  lt_of_lt_of_eq (Nat.ofBits_lt_two_pow f) (by norm_num)

theorem miss_complete (f : Fin 13 → Bool) (w : Fin 13) (h : ∀ p, Inc p w → f p = false) :
    missB (msk f) w.val = true := by
  have key : ∀ k : Fin 13, k ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      (msk f).testBit (pt w.val k.val) = false := by
    intro k hk
    have hlt : pt w.val k.val < 13 := Nat.mod_lt _ (by norm_num)
    rw [msk_bit f _ hlt]
    apply h
    exact ⟨k, hk, Fin.ext (by simp [Fin.val_add, pt])⟩
  have h0 := key 0 (by decide)
  have h1 := key 1 (by decide)
  have h3 := key 3 (by decide)
  have h9 := key 9 (by decide)
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩

theorem miss_sound (f : Fin 13 → Bool) (w p : Fin 13) (hm : missB (msk f) w.val = true)
    (hp : Inc p w) : f p = false := by
  obtain ⟨d, hd, rfl⟩ := hp
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := hm
  have key : ∀ k : Fin 13, (msk f).testBit (pt w.val k.val) = false → f (w + k) = false := by
    intro k h
    have hlt : pt w.val k.val < 13 := Nat.mod_lt _ (by norm_num)
    rw [msk_bit f _ hlt] at h
    have e : (w + k : Fin 13) = ⟨pt w.val k.val, hlt⟩ := Fin.ext (by simp [Fin.val_add, pt])
    rw [e]; exact h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact key 0 h0
  · exact key 1 h1
  · exact key 3 h3
  · exact key 9 h9

theorem good_spec (a : ℕ) (h : goodB a = true) :
    (∃ l, l < 13 ∧ missB a l = true) ∧
      ∀ l, l < 13 → missB a l = true →
        ∃ m, m < 13 ∧ missB a m = true ∧ ∃ n, n < 13 ∧ missB a n = true ∧ ncB l m n = true := by
  simp only [goodB, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨l, hl, hm⟩, h2⟩ := h
  refine ⟨⟨l, hl, hm⟩, fun l hl hm => ?_⟩
  rcases h2 l hl with h | ⟨m, hm1, hm2, n, hn1, hn2, hn3⟩
  · rw [hm] at h; exact Bool.noConfusion h
  · exact ⟨m, hm1, hm2, n, hn1, hn2, hn3⟩

theorem arc_bridge (x : Fin 26 → Bool)
    (harc : ∀ wa : Fin 13, (Finset.univ.filter (fun pa : Fin 13 => (∃ da : ℕ, da ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true)).card ≤ 2) :
    arcB (msk (fun p => x (Fin.castAdd 13 p))) = true := by
  have key : ∀ (w : ℕ) (hw : w < 13) (d1 d2 d3 : ℕ), d1 ∈ ({0, 1, 3, 9} : Finset ℕ) →
      d2 ∈ ({0, 1, 3, 9} : Finset ℕ) → d3 ∈ ({0, 1, 3, 9} : Finset ℕ) → d1 < d2 → d2 < d3 →
      no3 ((msk (fun p => x (Fin.castAdd 13 p))).testBit (pt w d1))
        ((msk (fun p => x (Fin.castAdd 13 p))).testBit (pt w d2))
        ((msk (fun p => x (Fin.castAdd 13 p))).testBit (pt w d3)) = true := by
    intro w hw d1 d2 d3 h1 h2 h3 h12 h23
    have l1 : pt w d1 < 13 := Nat.mod_lt _ (by norm_num)
    have l2 : pt w d2 < 13 := Nat.mod_lt _ (by norm_num)
    have l3 : pt w d3 < 13 := Nat.mod_lt _ (by norm_num)
    rw [msk_bit _ _ l1, msk_bit _ _ l2, msk_bit _ _ l3]
    by_cases hb : x (Fin.castAdd 13 ⟨pt w d1, l1⟩) = true ∧ x (Fin.castAdd 13 ⟨pt w d2, l2⟩) = true ∧
        x (Fin.castAdd 13 ⟨pt w d3, l3⟩) = true
    · exfalso
      obtain ⟨b1, b2, b3⟩ := hb
      have hcard : ({⟨pt w d1, l1⟩, ⟨pt w d2, l2⟩, ⟨pt w d3, l3⟩} : Finset (Fin 13)).card = 3 := by
        have g1 := h1
        have g2 := h2
        have g3 := h3
        simp only [Finset.mem_insert, Finset.mem_singleton] at g1 g2 g3
        apply Finset.card_eq_three.mpr
        refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
          (intro h; have hv := congrArg Fin.val h; simp only [pt] at hv; omega)
      have hle : ({⟨pt w d1, l1⟩, ⟨pt w d2, l2⟩, ⟨pt w d3, l3⟩} : Finset (Fin 13)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card ?_) (harc ⟨w, hw⟩)
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hq with rfl | rfl | rfl
        · exact ⟨⟨d1, h1, rfl⟩, b1⟩
        · exact ⟨⟨d2, h2, rfl⟩, b2⟩
        · exact ⟨⟨d3, h3, rfl⟩, b3⟩
      omega
    · revert hb
      generalize x (Fin.castAdd 13 ⟨pt w d1, l1⟩) = u1
      generalize x (Fin.castAdd 13 ⟨pt w d2, l2⟩) = u2
      generalize x (Fin.castAdd 13 ⟨pt w d3, l3⟩) = u3
      revert u1 u2 u3
      decide
  unfold arcB
  rw [List.all_eq_true]
  intro w hw
  have hwlt : w < 13 := List.mem_range.mp hw
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨key w hwlt 0 1 3 (by decide) (by decide) (by decide) (by norm_num) (by norm_num),
    key w hwlt 0 1 9 (by decide) (by decide) (by decide) (by norm_num) (by norm_num)⟩,
    key w hwlt 0 3 9 (by decide) (by decide) (by decide) (by norm_num) (by norm_num)⟩,
    key w hwlt 1 3 9 (by decide) (by decide) (by decide) (by norm_num) (by norm_num)⟩

theorem inc_iff : ∀ p w : Fin 13, Inc p w ↔ p-w ∈ D := by decide +kernel

theorem incNat_iff : ∀ p w : Fin 13,
    (∃ d : ℕ, d ∈ ({0,1,3,9} : Finset ℕ) ∧ (w.val+d)%13 = p.val) ↔ p-w ∈ D := by
  decide +kernel

def tri (a b c : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun p => p-a ∉ D ∧ p-b ∉ D ∧ p-c ∉ D

set_option maxRecDepth 8000 in
theorem tri_arc : ∀ a b c : Fin 13, ncB a.val b.val c.val = true →
    (tri a b c).card = 4 ∧ Arc (tri a b c) := by decide +kernel

theorem geometry_check (S : Finset (Fin 13)) (h : Arc S) :
    goodB (msk (fun p => decide (p ∈ S))) = true := by
  let x (j : Fin 26) : Bool := Fin.addCases (motive := fun _ : Fin (13+13) => Bool) (fun p : Fin 13 => decide (p ∈ S)) (fun _ : Fin 13 => false) j
  have ar := arc_bridge x (by
    intro w
    have eq : (Finset.univ.filter (fun p : Fin 13 => (∃ d : ℕ, d ∈ ({0,1,3,9} : Finset ℕ) ∧
        (w.val+d)%13=p.val) ∧ x (Fin.castAdd 13 p) = true)) = S.filter (fun p => p-w ∈ D) := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,x,Fin.addCases_left,decide_eq_true_eq,incNat_iff]
      exact and_comm
    rw [eq]; exact h w)
  have eq : (fun p : Fin 13 => x (Fin.castAdd 13 p)) = (fun p => decide (p ∈ S)) := by
    funext p
    exact Fin.addCases_left ..
  rw [eq] at ar
  have ok := chk_at _ (msk_lt fun p => decide (p ∈ S))
  simpa [chk,ar] using ok

theorem extend_avoiding (S : Finset (Fin 13)) (l : Fin 13) (h : Arc S) (off : ∀ p ∈ S, p-l ∉ D) :
    ∃ Q, S ⊆ Q ∧ Q.card = 4 ∧ Arc Q ∧ ∀ p ∈ Q, p-l ∉ D := by
  let f (p : Fin 13) := decide (p ∈ S)
  have miss : missB (msk f) l.val = true := miss_complete f l (by
    intro p hp
    exact decide_eq_false (fun hm => off p hm ((inc_iff p l).mp hp)))
  obtain ⟨m,hm,sm,n,hn,sn,ok⟩ := (good_spec _ (geometry_check S h)).2 _ l.isLt miss
  let b : Fin 13 := ⟨m,hm⟩
  let c : Fin 13 := ⟨n,hn⟩
  have shape := tri_arc l b c ok
  refine ⟨tri l b c,?_,shape.1,shape.2,fun p hp => (Finset.mem_filter.mp hp).2.1⟩
  intro p hp
  have hit : f p = true := decide_eq_true hp
  have away (w : Fin 13) (hw : missB (msk f) w.val = true) : p-w ∉ D := by
    intro inc
    have ex := miss_sound f w p hw ((inc_iff p w).mpr inc)
    rw [hit] at ex
    cases ex
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,away l miss,away b sm,away c sn⟩

theorem extend (S : Finset (Fin 13)) (h : Arc S) : ∃ Q, S ⊆ Q ∧ Q.card = 4 ∧ Arc Q := by
  obtain ⟨l,hl,sm⟩ := (good_spec _ (geometry_check S h)).1
  let w : Fin 13 := ⟨l,hl⟩
  obtain ⟨Q,ss,sz,aq,_⟩ := extend_avoiding S w h (by
    intro p hp inc
    have ex := miss_sound (fun t => decide (t ∈ S)) w p sm ((inc_iff p w).mpr inc)
    simp [hp] at ex)
  exact ⟨Q,ss,sz,aq⟩

end Geometry5254

end PEqualNP.Outside.L_meta_17597_aux

namespace PEqualNP.Outside.L_meta_17597_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open RowStructure ArcAffineCut PlaneArcAssembly PlaneArcFirst PlaneArcTranspose

theorem eval_mono2 (C : Circuit) (mono : Monotone2 C) {n : ℕ} (x y : Fin n → Bool)
    (hle : ∀ k, x k = true → y k = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (mono g hg).1
    simpa using h
  refine RowStructure.wiresFrom_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) ?_
    C.output hx
  intro j hj
  by_cases hjlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

def quadRow (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (bits Q) (fun l => decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13))))

theorem arc_translate (S : Finset (Fin 13)) (h : Arc S) :
    ∀ l : Fin 13, (S.filter (fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13)))).card ≤ 2 := by
  have inc : ∀ p l : Fin 13, p ∈ line l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide +kernel
  intro l
  have e : S.filter (fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13))) = line l ∩ S := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_inter,inc,and_comm]
  rw [e]
  exact h l

theorem ofQuad {C : Circuit} (mono : Monotone2 C)
    (gm : ∀ (S : Finset (Fin 13)), Geometry5254.Arc S → ∃ Q, S ⊆ Q ∧ Q.card=4 ∧ Geometry5254.Arc Q)
    (ga : ∀ (S : Finset (Fin 13)) (l : Fin 13), Geometry5254.Arc S → (∀ p∈S, p-l ∉ Geometry5254.D) →
      ∃ Q, S ⊆ Q ∧ Q.card=4 ∧ Geometry5254.Arc Q ∧ ∀ p∈Q, p-l ∉ Geometry5254.D)
    (neg : ∀ Q : Finset (Fin 13), Q.card=4 → Geometry5254.Arc Q → C.eval (List.ofFn (quadRow Q)) = false) :
    OrigSound C := by
  classical
  constructor
  · intro X arc
    obtain ⟨Q,sub,card,qArc⟩ := gm X (arc_translate X arc)
    apply Bool.eq_false_iff.mpr
    intro he
    have eq := eval_mono2 C mono (pointOnly (bits X)) (quadRow Q) (by
      intro k
      refine Fin.addCases (fun p => ?_) (fun l => ?_) k
      · simp only [pointOnly,Fin.addCases_left,quadRow,Fin.append_left,bits,decide_eq_true_eq]
        exact fun h => sub h
      · simp only [pointOnly, Fin.addCases_right, Bool.false_eq_true, false_implies]) he
    exact Bool.noConfusion ((neg Q card qArc).symm.trans eq)
  · intro X l arc he
    by_contra! none
    have inc : ∀ p l : Fin 13, p ∈ line l ↔ p-l ∈ Geometry5254.D := by decide +kernel
    obtain ⟨Q,sub,card,qArc,off⟩ := ga X l (arc_translate X arc) (by
      intro p hp hi
      exact none p ((inc p l).mpr hi) hp)
    have eq := eval_mono2 C mono (oneLine (bits X) l) (quadRow Q) (by
      intro k
      refine Fin.addCases (fun p => ?_) (fun w => ?_) k
      · simp only [oneLine,Fin.addCases_left,quadRow,Fin.append_left,bits,decide_eq_true_eq]
        exact fun h => sub h
      · simp only [oneLine,Fin.addCases_right,quadRow,Fin.append_right,decide_eq_true_eq]
        rintro rfl
        exact off) he
    exact Bool.noConfusion ((neg Q card qArc).symm.trans eq)

end PEqualNP.Outside.L_meta_17597_aux

open PEqualNP.Outside.L_meta_17597_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_17597_aux

theorem finiteLower : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Bool) (x6 : List Bool), x2 x5 x6 → x3.eval x6 = x5) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x3 (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  dsimp only
  intro C mono tests degree
  let zr : Zero PlaneArcEmit.Ref := ⟨PlaneArcEmit.Ref.zero⟩
  have zf : Fact ((0 : PlaneArcEmit.Ref) = PlaneArcEmit.Ref.zero) := ⟨rfl⟩
  apply PlaneArcAssembly.lower_bound mono degree
  · apply ofQuad mono Geometry5254.extend Geometry5254.extend_avoiding
    intro Q card arc
    apply tests false
    change ∃ S : Finset (Fin 13), S.card=4 ∧ Geometry5254.Arc S ∧ _
    refine ⟨Q,card,arc,?_⟩
    exact List.ofFn_fin_append _ _
  · intro p w ipw
    have inc : ∀ p w : Fin 13, p ∈ RowStructure.line w → p-w ∈ Geometry5254.D := by decide +kernel
    apply tests true
    refine ⟨p,w,inc p w ((PlaneArcAssembly.mem_line_iff w p).mpr ipw),?_⟩
    revert p w
    decide +kernel

open PEqualNP.HeptadCover

private abbrev baseDifferences : Finset (Fin 13) := {0,1,3,9}

private theorem incident_iff : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ baseDifferences := by
  decide +kernel

private theorem intersection (Q : Finset (Fin 13)) (l : Fin 13) :
    Q ∩ singerLines3 l = Q.filter (fun p => p-l ∈ baseDifferences) := by
  ext p
  simp only [Finset.mem_inter,Finset.mem_filter,incident_iff]

private theorem misses (Q : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p-l ∉ baseDifferences := by
  simp only [missLines,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
  constructor
  · intro h p hp hd
    exact h ((incident_iff p l).2 hd) hp
  · intro h p hp hq
    exact h p hq ((incident_iff p l).1 hp)

end PEqualNP.Outside.L_meta_17597_aux

open PEqualNP.Outside.L_meta_17597_aux PEqualNP.HeptadCover PEqualNP.GenericRejection in
theorem PEqualNP.Outside.L_meta_17597 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x1 → (∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x4 → x1.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) → (64 : ℕ) ≤ x1.size := by
  intro C mono positive negative degree
  apply finiteLower C mono ?_ degree
  intro b row hr
  cases b with
  | false =>
    obtain ⟨Q, hc, hn, rfl⟩ := hr
    have hquad : IsQuadrangle singerLines3 Q := ⟨hc, fun l => by rw [intersection]; exact hn l⟩
    simpa only [incidenceInput,misses] using negative Q hquad
  | true =>
    obtain ⟨p,l,hp,rfl⟩ := hr
    simpa only [incidenceInput,Finset.mem_singleton] using positive l p ((incident_iff p l).2 hp)
