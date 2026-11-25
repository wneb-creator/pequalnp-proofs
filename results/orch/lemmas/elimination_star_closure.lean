import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.StarClosure

def initial : List ℕ := 0 :: (List.range 10).map (fun i => 2 ^ (i + 1) + 2048)

def targets : Fin 8 → List ℕ
  | 0 => [2144, 2186, 2088, 2120, 2256, 2464]
  | 1 => [2148, 2184, 2088, 2120, 2256, 2464]
  | 2 => [2144, 2186, 2600, 2120, 2240, 2464]
  | 3 => [2148, 2184, 2600, 2120, 2240, 2464]
  | 4 => [2144, 2186, 2088, 3144, 2256, 2208]
  | 5 => [2148, 2184, 2088, 3144, 2256, 2208]
  | 6 => [2144, 2186, 2600, 3144, 2240, 2208]
  | 7 => [2148, 2184, 2600, 3144, 2240, 2208]

def products (state : List ℕ) : List ℕ :=
  ((state.map (fun a => Nat.xor 4095 a)) ++
    state.flatMap (fun a => state.flatMap (fun b => [Nat.land a b, Nat.lor a b]))).eraseDups

def canMake (state : List ℕ) (v : ℕ) : Bool :=
  state.any (fun a => Nat.xor 4095 a == v) ||
    state.any (fun a => state.any (fun b => Nat.land a b == v || Nat.lor a b == v))

def closePass (wanted state : List ℕ) : List ℕ :=
  wanted.foldl (fun current v =>
    if current.contains v || !canMake current v then current else v :: current) state

def closeSteps (wanted : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, state => state
  | fuel + 1, state =>
    let next := closePass wanted state
    if next == state then state else closeSteps wanted fuel next

def close (wanted state : List ℕ) : List ℕ := closeSteps wanted 6 state

def complete (wanted state : List ℕ) : Bool := wanted.all state.contains

def rejectOne (wanted state : List ℕ) : Bool :=
  !complete wanted state && (products state).all (fun v =>
    if state.contains v || wanted.contains v then true
    else !complete wanted (close wanted (v :: state)))

def rejectTwo (wanted : List ℕ) : Bool :=
  let state := close wanted initial
  !complete wanted state && (products state).all (fun v =>
    if state.contains v || wanted.contains v then true
    else rejectOne wanted (close wanted (v :: state)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma orientation_zero : rejectTwo (targets 0) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.StarClosure
