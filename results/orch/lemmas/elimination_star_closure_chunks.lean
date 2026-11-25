import Mathlib.Data.Nat.Bitwise

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
  state.contains (Nat.xor 4095 v) ||
    (state.filter (fun a => Nat.land a v == v)).any (fun a =>
      (state.filter (fun b => Nat.land b v == v)).any (fun b => Nat.land a b == v)) ||
    (state.filter (fun a => Nat.lor a v == v)).any (fun a =>
      (state.filter (fun b => Nat.lor b v == v)).any (fun b => Nat.lor a b == v))

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

def firstBranch (wanted : List ℕ) (v : ℕ) : Bool :=
  let state := close wanted initial
  if state.contains v || wanted.contains v then true
  else rejectOne wanted (close wanted (v :: state))

def rejectTwo (wanted : List ℕ) : Bool :=
  let state := close wanted initial
  !complete wanted state && (products state).all (firstBranch wanted)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma products_zero : products (close (targets 0) initial) = [1975, 2007, 1951, 4095, 2045, 2043, 2039, 2031, 2015, 1983, 1919, 1791, 1535, 1023, 2120, 2056, 2152, 2112, 0, 2048, 2122, 2124, 2136, 2248, 2376, 2632, 3144, 2088, 2080, 2090, 2092, 2104, 2216, 2344, 2600, 3112, 2144, 2146, 2148, 2160, 2272, 2400, 2656, 3168, 2050, 2052, 2064, 2176, 2304, 2560, 3072, 2054, 2058, 2066, 2082, 2114, 2178, 2306, 2562, 3074, 2060, 2068, 2084, 2116, 2180, 2308, 2564, 3076, 2072, 2184, 2312, 2568, 3080, 2096, 2128, 2192, 2320, 2576, 3088, 2208, 2336, 2592, 3104, 2240, 2368, 2624, 3136, 2432, 2688, 3200, 2816, 3328, 3584] := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1975 : firstBranch (targets 0) 1975 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2007 : firstBranch (targets 0) 2007 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1951 : firstBranch (targets 0) 1951 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_4095 : firstBranch (targets 0) 4095 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2045 : firstBranch (targets 0) 2045 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2043 : firstBranch (targets 0) 2043 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2039 : firstBranch (targets 0) 2039 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2031 : firstBranch (targets 0) 2031 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2015 : firstBranch (targets 0) 2015 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1983 : firstBranch (targets 0) 1983 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1919 : firstBranch (targets 0) 1919 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1791 : firstBranch (targets 0) 1791 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1535 : firstBranch (targets 0) 1535 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_1023 : firstBranch (targets 0) 1023 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2120 : firstBranch (targets 0) 2120 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2056 : firstBranch (targets 0) 2056 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2152 : firstBranch (targets 0) 2152 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2112 : firstBranch (targets 0) 2112 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_0 : firstBranch (targets 0) 0 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2048 : firstBranch (targets 0) 2048 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2122 : firstBranch (targets 0) 2122 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2124 : firstBranch (targets 0) 2124 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2136 : firstBranch (targets 0) 2136 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2248 : firstBranch (targets 0) 2248 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2376 : firstBranch (targets 0) 2376 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2632 : firstBranch (targets 0) 2632 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3144 : firstBranch (targets 0) 3144 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2088 : firstBranch (targets 0) 2088 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2080 : firstBranch (targets 0) 2080 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2090 : firstBranch (targets 0) 2090 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2092 : firstBranch (targets 0) 2092 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2104 : firstBranch (targets 0) 2104 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2216 : firstBranch (targets 0) 2216 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2344 : firstBranch (targets 0) 2344 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2600 : firstBranch (targets 0) 2600 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3112 : firstBranch (targets 0) 3112 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2144 : firstBranch (targets 0) 2144 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2146 : firstBranch (targets 0) 2146 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2148 : firstBranch (targets 0) 2148 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2160 : firstBranch (targets 0) 2160 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2272 : firstBranch (targets 0) 2272 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2400 : firstBranch (targets 0) 2400 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2656 : firstBranch (targets 0) 2656 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3168 : firstBranch (targets 0) 3168 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2050 : firstBranch (targets 0) 2050 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2052 : firstBranch (targets 0) 2052 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2064 : firstBranch (targets 0) 2064 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2176 : firstBranch (targets 0) 2176 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2304 : firstBranch (targets 0) 2304 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2560 : firstBranch (targets 0) 2560 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3072 : firstBranch (targets 0) 3072 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2054 : firstBranch (targets 0) 2054 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2058 : firstBranch (targets 0) 2058 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2066 : firstBranch (targets 0) 2066 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2082 : firstBranch (targets 0) 2082 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2114 : firstBranch (targets 0) 2114 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2178 : firstBranch (targets 0) 2178 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2306 : firstBranch (targets 0) 2306 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2562 : firstBranch (targets 0) 2562 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3074 : firstBranch (targets 0) 3074 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2060 : firstBranch (targets 0) 2060 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2068 : firstBranch (targets 0) 2068 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2084 : firstBranch (targets 0) 2084 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2116 : firstBranch (targets 0) 2116 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2180 : firstBranch (targets 0) 2180 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2308 : firstBranch (targets 0) 2308 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2564 : firstBranch (targets 0) 2564 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3076 : firstBranch (targets 0) 3076 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2072 : firstBranch (targets 0) 2072 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2184 : firstBranch (targets 0) 2184 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2312 : firstBranch (targets 0) 2312 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2568 : firstBranch (targets 0) 2568 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3080 : firstBranch (targets 0) 3080 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2096 : firstBranch (targets 0) 2096 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2128 : firstBranch (targets 0) 2128 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2192 : firstBranch (targets 0) 2192 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2320 : firstBranch (targets 0) 2320 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2576 : firstBranch (targets 0) 2576 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3088 : firstBranch (targets 0) 3088 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2208 : firstBranch (targets 0) 2208 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2336 : firstBranch (targets 0) 2336 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2592 : firstBranch (targets 0) 2592 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3104 : firstBranch (targets 0) 3104 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2240 : firstBranch (targets 0) 2240 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2368 : firstBranch (targets 0) 2368 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2624 : firstBranch (targets 0) 2624 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3136 : firstBranch (targets 0) 3136 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2432 : firstBranch (targets 0) 2432 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2688 : firstBranch (targets 0) 2688 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3200 : firstBranch (targets 0) 3200 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_2816 : firstBranch (targets 0) 2816 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3328 : firstBranch (targets 0) 3328 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_zero_3584 : firstBranch (targets 0) 3584 = true := by
  decide +kernel

lemma orientation_zero : rejectTwo (targets 0) = true := by
  simp only [rejectTwo, products_zero, List.all_cons, List.all_nil,
    first_zero_1975, first_zero_2007, first_zero_1951, first_zero_4095, first_zero_2045, first_zero_2043, first_zero_2039, first_zero_2031, first_zero_2015, first_zero_1983, first_zero_1919, first_zero_1791, first_zero_1535, first_zero_1023, first_zero_2120, first_zero_2056, first_zero_2152, first_zero_2112, first_zero_0, first_zero_2048, first_zero_2122, first_zero_2124, first_zero_2136, first_zero_2248, first_zero_2376, first_zero_2632, first_zero_3144, first_zero_2088, first_zero_2080, first_zero_2090, first_zero_2092, first_zero_2104, first_zero_2216, first_zero_2344, first_zero_2600, first_zero_3112, first_zero_2144, first_zero_2146, first_zero_2148, first_zero_2160, first_zero_2272, first_zero_2400, first_zero_2656, first_zero_3168, first_zero_2050, first_zero_2052, first_zero_2064, first_zero_2176, first_zero_2304, first_zero_2560, first_zero_3072, first_zero_2054, first_zero_2058, first_zero_2066, first_zero_2082, first_zero_2114, first_zero_2178, first_zero_2306, first_zero_2562, first_zero_3074, first_zero_2060, first_zero_2068, first_zero_2084, first_zero_2116, first_zero_2180, first_zero_2308, first_zero_2564, first_zero_3076, first_zero_2072, first_zero_2184, first_zero_2312, first_zero_2568, first_zero_3080, first_zero_2096, first_zero_2128, first_zero_2192, first_zero_2320, first_zero_2576, first_zero_3088, first_zero_2208, first_zero_2336, first_zero_2592, first_zero_3104, first_zero_2240, first_zero_2368, first_zero_2624, first_zero_3136, first_zero_2432, first_zero_2688, first_zero_3200, first_zero_2816, first_zero_3328, first_zero_3584, Bool.and_true]
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.StarClosure
