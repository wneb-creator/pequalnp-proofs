import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i bound)⟩

def capCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate (n + C.size)), min C.output (n + C.size)⟩

lemma getD_cap (w : List Bool) (bound i : ℕ) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega

lemma fold_cap (gs : List Gate) (w : List Bool) (bound : ℕ)
    (h : w.length + gs.length ≤ bound) :
    ((gs.map (capGate bound)).foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w) =
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, capGate, List.map_map, Function.comp_def]
      have he : g.inputs.map (fun i => w.getD (min i bound) false) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact getD_cap w bound i (by simp at h; omega)
      rw [he]
      apply ih
      simp at h ⊢
      omega

lemma capCircuit_size (n : ℕ) (C : Circuit) :
    (capCircuit n C).size = C.size := by
  simp [capCircuit, Circuit.size]

lemma capCircuit_wires (n : ℕ) (C : Circuit) (w : List Bool) (h : w.length = n) :
    (capCircuit n C).wires w = C.wires w := by
  apply fold_cap
  simp [Circuit.size, h]

lemma capCircuit_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (capCircuit n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  unfold Circuit.eval
  rw [capCircuit_wires n C _ (by simp)]
  apply getD_cap
  unfold Circuit.wires
  rw [fold_length]
  simp [Circuit.size]

lemma capCircuit_fanInTwo (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (capCircuit n C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [capGate] using h g' hg'

lemma capCircuit_not (n : ℕ) (C : Circuit) :
    (∃ g ∈ (capCircuit n C).gates, g.op = GateOp.not) ↔
      ∃ g ∈ C.gates, g.op = GateOp.not := by
  constructor
  · rintro ⟨g, hg, hn⟩
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨g', hg', hn⟩
  · rintro ⟨g, hg, hn⟩
    exact ⟨capGate (n + C.size) g, List.mem_map.mpr ⟨g, hg, rfl⟩, hn⟩

lemma capCircuit_inputs (n : ℕ) (C : Circuit) :
    ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + C.size := by
  intro g hg i hi
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

lemma capCircuit_output (n : ℕ) (C : Circuit) :
    (capCircuit n C).output ≤ n + C.size := Nat.min_le_right _ _

lemma finite_normalization (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      (∃ g ∈ D.gates, g.op = GateOp.not) ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + C.size) ∧
      D.output ≤ n + C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  exact ⟨capCircuit n C, capCircuit_fanInTwo n C hfan, capCircuit_size n C,
    (capCircuit_not n C).2 hnot, capCircuit_inputs n C, capCircuit_output n C,
    capCircuit_eval n C⟩

def GateCode (bound : ℕ) := Fin 3 × Fin 3 × Fin (bound + 1) × Fin (bound + 1)

def decodeOp (q : Fin 3) : GateOp :=
  if q.val = 0 then GateOp.and else if q.val = 1 then GateOp.or else GateOp.not

def decodeArgs (bound : ℕ) (q : Fin 3 × Fin (bound + 1) × Fin (bound + 1)) : List ℕ :=
  if q.1.val = 0 then [] else if q.1.val = 1 then [q.2.1.val]
    else [q.2.1.val, q.2.2.val]

def decodeGate (bound : ℕ) (q : GateCode bound) : Gate :=
  ⟨decodeOp q.1, decodeArgs bound q.2⟩

lemma decodeOp_surjective (op : GateOp)
    (h : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∃ q : Fin 3, decodeOp q = op := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

lemma decodeArgs_surjective (bound : ℕ) (is : List ℕ)
    (hsize : is.length ≤ 2) (hbound : ∀ i ∈ is, i ≤ bound) :
    ∃ q : Fin 3 × Fin (bound + 1) × Fin (bound + 1), decodeArgs bound q = is := by
  cases is with
  | nil => exact ⟨⟨0, 0, 0⟩, rfl⟩
  | cons a is =>
      have ha : a < bound + 1 := by have := hbound a (by simp); omega
      cases is with
      | nil => exact ⟨⟨1, ⟨a, ha⟩, 0⟩, rfl⟩
      | cons b is =>
          have hb : b < bound + 1 := by have := hbound b (by simp); omega
          cases is with
          | nil => exact ⟨⟨2, ⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
          | cons c is => simp at hsize

lemma decodeGate_surjective (bound : ℕ) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) (hbound : ∀ i ∈ g.inputs, i ≤ bound) :
    ∃ q : GateCode bound, decodeGate bound q = g := by
  obtain ⟨op, hop⟩ := decodeOp_surjective g.op hfan.1
  obtain ⟨args, hargs⟩ := decodeArgs_surjective bound g.inputs hfan.2 hbound
  refine ⟨⟨op, args⟩, ?_⟩
  cases g
  simp_all [decodeGate]

lemma decodeGate_fanInTwo (bound : ℕ) (q : GateCode bound) :
    (decodeGate bound q).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (decodeGate bound q).inputs.length ≤ 2 := by
  constructor
  · simp only [decodeGate, decodeOp]
    split_ifs <;> simp
  · simp only [decodeGate, decodeArgs]
    split_ifs <;> simp

def CircuitCode (n s : ℕ) :=
  (m : Fin (s + 1)) × (Fin m.val → GateCode (n + s)) × Fin (n + s + 1)

def decodeCircuit {n s : ℕ} (q : CircuitCode n s) : Circuit :=
  ⟨List.ofFn (fun i => decodeGate (n + s) (q.2.1 i)), q.2.2.val⟩

lemma decodeCircuit_fanInTwo {n s : ℕ} (q : CircuitCode n s) :
    FanInTwo (decodeCircuit q) := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact decodeGate_fanInTwo _ _

lemma decodeCircuit_size {n s : ℕ} (q : CircuitCode n s) :
    (decodeCircuit q).size ≤ s := by
  simpa [decodeCircuit, Circuit.size] using Nat.le_of_lt_succ q.1.isLt

lemma decodeCircuit_surjective (n s : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hsize : C.size ≤ s) (houtput : C.output ≤ n + s)
    (hbound : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ n + s) :
    ∃ q : CircuitCode n s, decodeCircuit q = C := by
  classical
  have hg : ∀ i : Fin C.gates.length,
      ∃ q : GateCode (n + s), decodeGate (n + s) q = C.gates[i] := by
    intro i
    apply decodeGate_surjective
    · exact hfan _ (List.getElem_mem i.isLt)
    · exact hbound _ (List.getElem_mem i.isLt)
  choose qs hqs using hg
  let m : Fin (s + 1) := ⟨C.gates.length, by simpa [Circuit.size] using hsize⟩
  refine ⟨⟨m, qs, ⟨C.output, by omega⟩⟩, ?_⟩
  have hgs : List.ofFn (fun i => decodeGate (n + s) (qs i)) = C.gates := by
    simp only [hqs]
    exact List.ofFn_getElem
  cases C with
  | mk gates output =>
      change Circuit.mk _ output = Circuit.mk gates output
      rw [hgs]

lemma finite_lower_bound (n s : ℕ) (f : (Fin n → Bool) → Bool) :
    (∀ C : Circuit, FanInTwo C → C.size ≤ s →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ¬∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) ↔
    (∀ q : CircuitCode n s,
      (∃ g ∈ (decodeCircuit q).gates, g.op = GateOp.not) →
      ¬∀ x : Fin n → Bool, (decodeCircuit q).eval (List.ofFn x) = f x) := by
  constructor
  · intro h q
    exact h _ (decodeCircuit_fanInTwo q) (decodeCircuit_size q)
  · intro h C hfan hsize hnot heval
    have hcap : FanInTwo (capCircuit n C) := capCircuit_fanInTwo n C hfan
    have hs : (capCircuit n C).size ≤ s := by rwa [capCircuit_size]
    have ho : (capCircuit n C).output ≤ n + s :=
      (capCircuit_output n C).trans (by omega)
    have hb : ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + s := by
      intro g hg i hi
      exact (capCircuit_inputs n C g hg i hi).trans (by omega)
    obtain ⟨q, hq⟩ := decodeCircuit_surjective n s (capCircuit n C) hcap hs ho hb
    apply h q
    · rw [hq]
      exact (capCircuit_not n C).2 hnot
    · intro x
      rw [hq, capCircuit_eval]
      exact heval x

end PEqualNP.Outside.L_meta_2592_aux

