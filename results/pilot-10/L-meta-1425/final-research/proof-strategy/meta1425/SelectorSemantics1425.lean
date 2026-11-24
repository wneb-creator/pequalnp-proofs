import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1425.Selectors

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

/-- The value of the gate at position `t` of `G` as read in the wires. -/
theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

/-- The value of gate `t`: its operation on the wires it reads, among those that exist. -/
theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)


def extended (n : Nat) (wires : List Bool) (w : Nat) : Bool :=
  if w < n then wires.getD w false else
  if w = n then false else if w = n+1 then true else wires.getD (w-2) false

def sourceRef (n j w : Nat) : Nat :=
  if w < n then w else if w < n+j then w+2 else n

theorem sourceRef_lt (n j w : Nat) : sourceRef n j w < n+2+j := by
  unfold sourceRef
  split_ifs <;> omega

theorem extended_false (n : Nat) (ws : List Bool) : extended n ws n = false := by
  simp [extended]

theorem extended_true (n : Nat) (ws : List Bool) : extended n ws (n+1) = true := by
  simp [extended]

theorem extended_gate (n j : Nat) (ws : List Bool) :
    extended n ws (n+2+j) = ws.getD (n+j) false := by
  have h0 : ¬ n+2+j < n := by omega
  have h1 : n+2+j ≠ n := by omega
  have h2 : n+2+j ≠ n+1 := by omega
  have h3 : n+2+j-2 = n+j := by omega
  simp [extended,h0,h1,h2,h3]

theorem extended_sourceRef (n j w : Nat) (ws : List Bool) :
    extended n ws (sourceRef n j w) =
      if w < n+j then ws.getD w false else false := by
  by_cases h0 : w < n
  · have h1 : w < n+j := by omega
    simp [sourceRef,extended,h0,h1]
  · by_cases h1 : w < n+j
    · have h2 : ¬ w+2 < n := by omega
      have h3 : w+2 ≠ n := by omega
      have h4 : w+2 ≠ n+1 := by omega
      simp [sourceRef,extended,h0,h1,h2,h3,h4]
    · simp [sourceRef,h0,h1,extended_false]

def gateCode (g : Gate) : Nat :=
  match g.op with
  | .and => 0
  | .or => 1
  | .not => 2
  | _ => 0

def gateArgs (n j : Nat) (g : Gate) : Nat × Nat :=
  match g.inputs with
  | [] => if g.op = .and then (n+1,n+1) else (n,n)
  | [a] => (sourceRef n j a, sourceRef n j a)
  | a::b::_ => (sourceRef n j a, sourceRef n j b)

def gateValue (code : Nat) (a b : Bool) : Bool :=
  if code = 0 then a && b else if code = 1 then a || b else !a

theorem gateCode_lt (g : Gate) : gateCode g < 3 := by
  cases g with | mk op inputs => cases op <;> decide

theorem gateArgs_lt (n j : Nat) (g : Gate) :
    (gateArgs n j g).1 < n+2+j ∧ (gateArgs n j g).2 < n+2+j := by
  rcases g with ⟨op,inputs⟩
  cases inputs with
  | nil => simp only [gateArgs]; split_ifs <;> simp <;> omega
  | cons a rest =>
    cases rest with
    | nil => exact ⟨sourceRef_lt n j a,sourceRef_lt n j a⟩
    | cons b rest => exact ⟨sourceRef_lt n j a,sourceRef_lt n j b⟩

theorem gateCode_not_iff (g : Gate) : gateCode g = 2 ↔ g.op = .not := by
  rcases g with ⟨op,inputs⟩
  cases op <;> simp [gateCode]

theorem gateArgs_eval (n j : Nat) (g : Gate) (ws : List Bool)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2) :
    gateValue (gateCode g) (extended n ws (gateArgs n j g).1)
      (extended n ws (gateArgs n j g).2) =
      g.op.eval (g.inputs.map fun w => if w < n+j then ws.getD w false else false) := by
  rcases g with ⟨op,inputs⟩
  rcases hop with hop | hop | hop <;> subst op
  all_goals
    cases inputs with
    | nil => simp [gateArgs,gateCode,gateValue,GateOp.eval,extended_false,extended_true]
    | cons a rest =>
      cases rest with
      | nil => simp [gateArgs,gateCode,gateValue,GateOp.eval,extended_sourceRef]
      | cons b rest =>
        cases rest with
        | nil => simp [gateArgs,gateCode,gateValue,GateOp.eval,extended_sourceRef]
        | cons c rest => simp at hlen

theorem circuit_gate_constraint (G : List Gate) (x : List Bool) (j : Nat)
    (hj : j < G.length)
    (hop : (G[j]).op = .and ∨ (G[j]).op = .or ∨ (G[j]).op = .not)
    (hlen : (G[j]).inputs.length ≤ 2) :
    extended x.length (G.foldl step x) (x.length+2+j) =
      gateValue (gateCode G[j])
        (extended x.length (G.foldl step x) (gateArgs x.length j G[j]).1)
        (extended x.length (G.foldl step x) (gateArgs x.length j G[j]).2) := by
  rw [extended_gate,gateArgs_eval _ _ _ _ hop hlen]
  exact gate_value G x j hj

end PEqualNP.Outside.L_meta_1425.Selectors
