import Mathlib

namespace PEqualNP.Outside.L_meta_5112_aux

def gateStep (xs : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

def clipGate (n : Nat) (g : Bool × Nat × Nat) : Bool × Nat × Nat :=
  (g.1, min g.2.1 n, min g.2.2 n)

def clipProgram (n : Nat) : List (Bool × Nat × Nat) → List (Bool × Nat × Nat)
  | [] => []
  | g :: gs => clipGate n g :: clipProgram (n + 1) gs

theorem getD_default (xs : List Nat) (i : Nat) (h : xs.length ≤ i) : xs.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_clip (xs : List Nat) (i : Nat) :
    xs.getD (min i xs.length) 0 = xs.getD i 0 := by
  by_cases h : i ≤ xs.length
  · rw [Nat.min_eq_left h]
  · have h' : xs.length ≤ i := by omega
    rw [Nat.min_eq_right h', getD_default _ _ (by omega),
      getD_default _ _ h']

theorem gateStep_clip (xs : List Nat) (g : Bool × Nat × Nat) :
    gateStep xs (clipGate xs.length g) = gateStep xs g := by
  simp only [gateStep, clipGate, getD_clip]

theorem clipProgram_length (n : Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [clipProgram, ih]

theorem gateStep_length (xs : List Nat) (g : Bool × Nat × Nat) :
    (gateStep xs g).length = xs.length + 1 := by
  simp [gateStep]

theorem eval_clipProgram (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram xs.length gs).foldl gateStep xs = gs.foldl gateStep xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [clipProgram, List.foldl_cons, gateStep_clip]
    rw [← gateStep_length xs g]
    exact ih _

theorem clipProgram_sources (n : Nat) (gs : List (Bool × Nat × Nat)) :
    ∀ g ∈ clipProgram n gs, g.2.1 < n + gs.length + 1 ∧
      g.2.2 < n + gs.length + 1 := by
  induction gs generalizing n with
  | nil => simp [clipProgram]
  | cons g gs ih =>
    intro a ha
    simp only [clipProgram, List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [clipGate, List.length_cons]
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
    · have h := ih (n + 1) a ha
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem gateStep_repeat (xs : List Nat) (i : Nat) :
    gateStep xs (true, i, i) = xs ++ [xs.getD i 0] := by
  simp [gateStep]

theorem eval_length (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    (gs.foldl gateStep xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, gateStep_length, List.length_cons]
    omega

theorem foldl_replicate_repeat (xs : List Nat) (i k : Nat) (hi : i < xs.length) :
    (List.replicate k (true, i, i)).foldl gateStep xs =
      xs ++ List.replicate k (xs.getD i 0) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, gateStep_repeat,
      ih (xs ++ [xs.getD i 0]) (by simpa using Nat.lt_succ_of_lt hi)]
    rw [List.getD_append xs [xs.getD i 0] 0 i hi]
    simp [List.replicate_succ, List.append_assoc]

theorem getD_extend_last (xs : List Nat) (k : Nat) (hx : 0 < xs.length) :
    (xs ++ List.replicate k (xs.getD (xs.length - 1) 0)).getD
      (xs.length + k - 1) 0 = xs.getD (xs.length - 1) 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [List.getD_append_right xs _ 0 _ (by omega)]
    exact List.getD_replicate (x := xs.getD (xs.length - 1) 0) (by omega)

theorem padded_output (xs : List Nat) (gs : List (Bool × Nat × Nat)) (k : Nat)
    (h : 0 < xs.length + gs.length) :
    let ys := gs.foldl gateStep xs
    let more := List.replicate k (true, xs.length + gs.length - 1,
      xs.length + gs.length - 1)
    ((gs ++ more).foldl gateStep xs).getD
      (xs.length + (gs ++ more).length - 1) 0 =
        ys.getD (xs.length + gs.length - 1) 0 := by
  dsimp only
  rw [List.foldl_append, List.length_append, List.length_replicate]
  rw [foldl_replicate_repeat _ _ _ (by rw [eval_length]; omega)]
  have he : (gs.foldl gateStep xs).length = xs.length + gs.length := eval_length xs gs
  have ht := getD_extend_last (gs.foldl gateStep xs) k (by rw [he]; exact h)
  simpa only [he, Nat.add_assoc] using ht

theorem bounded_pad (xs : List Nat) (gs : List (Bool × Nat × Nat)) (s : Nat)
    (hpos : 0 < xs.length + gs.length) (hlen : gs.length ≤ s) :
    ∃ hs : List (Bool × Nat × Nat), hs.length = s ∧
      (∀ g ∈ hs, g.2.1 < xs.length + s + 1 ∧ g.2.2 < xs.length + s + 1) ∧
      (hs.foldl gateStep xs).getD (xs.length + s - 1) 0 =
        (gs.foldl gateStep xs).getD (xs.length + gs.length - 1) 0 := by
  let more := List.replicate (s - gs.length)
    (true, xs.length + gs.length - 1, xs.length + gs.length - 1)
  let raw := gs ++ more
  have hraw : raw.length = s := by
    simp only [raw, more, List.length_append, List.length_replicate]
    omega
  refine ⟨clipProgram xs.length raw, ?_, ?_, ?_⟩
  · rw [clipProgram_length, hraw]
  · simpa only [hraw] using clipProgram_sources xs.length raw
  · rw [eval_clipProgram]
    have ho := padded_output xs gs (s - gs.length) hpos
    change (raw.foldl gateStep xs).getD (xs.length + raw.length - 1) 0 = _ at ho
    simpa only [hraw] using ho

theorem eval_extends (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    ∃ zs : List Nat, gs.foldl gateStep xs = xs ++ zs := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨zs, hz⟩ := ih (gateStep xs g)
    refine ⟨[if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
      else xs.getD g.2.1 0 &&& xs.getD g.2.2 0] ++ zs, ?_⟩
    rw [List.foldl_cons, hz]
    simp only [gateStep, List.append_assoc]

theorem eval_preserves (xs : List Nat) (gs : List (Bool × Nat × Nat)) (i : Nat)
    (hi : i < xs.length) :
    (gs.foldl gateStep xs).getD i 0 = xs.getD i 0 := by
  obtain ⟨zs, hz⟩ := eval_extends xs gs
  rw [hz, List.getD_append xs zs 0 i hi]

theorem take_eval_length (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j : Nat)
    (hj : j ≤ gs.length) :
    ((gs.take j).foldl gateStep xs).length = xs.length + j := by
  rw [eval_length, List.length_take, Nat.min_eq_left hj]

theorem take_eval_preserves (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j k : Nat)
    (hj : j ≤ gs.length) (hk : k < xs.length + j) :
    (gs.foldl gateStep xs).getD k 0 = ((gs.take j).foldl gateStep xs).getD k 0 := by
  have hh : k < ((gs.take j).foldl gateStep xs).length := by
    rw [take_eval_length xs gs j hj]
    exact hk
  simpa only [← List.foldl_append, List.take_append_drop] using
    eval_preserves ((gs.take j).foldl gateStep xs) (gs.drop j) k hh

theorem take_eval_source (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j k : Nat)
    (hj : j ≤ gs.length) :
    ((gs.take j).foldl gateStep xs).getD k 0 =
      if k < xs.length + j then (gs.foldl gateStep xs).getD k 0 else 0 := by
  split
  · exact (take_eval_preserves xs gs j k hj ‹_›).symm
  · exact getD_default _ _ (by rw [take_eval_length xs gs j hj]; omega)

theorem gate_eq (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j : Nat)
    (hj : j < gs.length) :
    (gs.foldl gateStep xs).getD (xs.length + j) 0 =
      let front := (gs.take j).foldl gateStep xs
      let g := gs[j]
      if g.1 = true then front.getD g.2.1 0 ||| front.getD g.2.2 0
        else front.getD g.2.1 0 &&& front.getD g.2.2 0 := by
  rw [take_eval_preserves xs gs (j + 1) (xs.length + j) (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, gateStep]
  rw [List.getD_append_right _ _ 0 _ (by rw [take_eval_length xs gs j (by omega)])]
  rw [take_eval_length xs gs j (by omega), Nat.sub_self]
  rfl

def inputData : List Nat :=
  [256463372304, 8521482511360, 14003410187716736, 55389823206179104,
    155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864,
    270286071508729856, 288160007409369088, 192860064594267704,
    288166778660192704, 283797140973809664]

def opVar (i : Nat) : Nat := 1 + 231 * i
def selVar (i : Nat) (side : Bool) (j : Nat) : Nat :=
  (if side then 30 else 2) + 231 * i + j
def argVar (i : Nat) (side : Bool) (r : Nat) : Nat :=
  (if side then 116 else 58) + 231 * i + r
def outVar (i r : Nat) : Nat := 174 + 231 * i + r

def positive (n : Nat) : Nat × Bool := (n, true)
def negative (n : Nat) : Nat × Bool := (n, false)

def onehotClauses (i : Nat) (side : Bool) : List (List (Nat × Bool)) :=
  [(List.range 28).map fun k => positive (selVar i side k)] ++
  (List.range 28).flatMap fun j =>
    (List.range (27 - j)).map fun d =>
      [negative (selVar i side j), negative (selVar i side (j + 1 + d))]

def sourceClauses (i source r : Nat) (side : Bool) : List (List (Nat × Bool)) :=
  let s := selVar i side source
  let a := argVar i side r
  if source < 13 then
    [[negative s, (a, (inputData.getD source 0).testBit r)]]
  else if 13 + i ≤ source then [[negative s, negative a]]
  else [[negative s, negative a, positive (outVar (source - 13) r)],
    [negative s, positive a, negative (outVar (source - 13) r)]]

def gateClauses (i r : Nat) : List (List (Nat × Bool)) :=
  let o := opVar i
  let a := argVar i false r
  let b := argVar i true r
  let v := outVar i r
  [[negative o, negative a, positive v],
    [negative o, negative b, positive v],
    [negative o, positive a, positive b, negative v],
    [positive o, positive a, negative v],
    [positive o, positive b, negative v],
    [positive o, negative a, negative b, positive v]]

def allClauses : List (List (Nat × Bool)) :=
  (List.range 14).flatMap (fun i =>
    onehotClauses i false ++ onehotClauses i true ++
    (List.range 28).flatMap (fun source =>
      (List.range 58).flatMap (fun r =>
        [false, true].flatMap fun side => sourceClauses i source r side)) ++
    (List.range 58).flatMap (fun r => gateClauses i r)) ++
  (List.range 58).map (fun r => [(outVar 13 r, (1764784 : Nat).testBit r)])

def formula : Std.Sat.CNF Nat :=
  ⟨(allClauses.map Std.Sat.CNF.Clause.ofLiterals).toArray⟩

def sourceOf (g : Bool × Nat × Nat) (side : Bool) : Nat :=
  if side then g.2.2 else g.2.1

def rowArg (gs : List (Bool × Nat × Nat)) (i : Nat) (side : Bool) (r : Nat) : Bool :=
  (((gs.take i).foldl gateStep inputData).getD
    (sourceOf (gs.getD i (false, 0, 0)) side) 0).testBit r

def rowOut (gs : List (Bool × Nat × Nat)) (i r : Nat) : Bool :=
  ((gs.foldl gateStep inputData).getD (13 + i) 0).testBit r

def assignment (gs : List (Bool × Nat × Nat)) (v : Nat) : Bool :=
  let i := (v - 1) / 231
  let p := (v - 1) % 231
  let g := gs.getD i (false, 0, 0)
  if p = 0 then g.1
  else if p < 29 then decide (g.2.1 = p - 1)
  else if p < 57 then decide (g.2.2 = p - 29)
  else if p < 115 then rowArg gs i false (p - 57)
  else if p < 173 then rowArg gs i true (p - 115)
  else rowOut gs i (p - 173)

theorem assignment_op (gs : List (Bool × Nat × Nat)) (i : Nat) :
    assignment gs (opVar i) = (gs.getD i (false, 0, 0)).1 := by
  simp [assignment, opVar]

theorem assignment_sel (gs : List (Bool × Nat × Nat)) (i j : Nat) (side : Bool)
    (hj : j < 28) :
    assignment gs (selVar i side j) = decide (sourceOf (gs.getD i (false, 0, 0)) side = j) := by
  cases side
  · have hd : (2 + 231 * i + j - 1) / 231 = i := by omega
    have hm : (2 + 231 * i + j - 1) % 231 = j + 1 := by omega
    simp only [assignment, selVar, Bool.false_eq_true, ↓reduceIte, hd, hm, sourceOf]
    simp only [show j + 1 ≠ 0 by omega, show j + 1 < 29 by omega, ↓reduceIte]
    simp
  · have hd : (30 + 231 * i + j - 1) / 231 = i := by omega
    have hm : (30 + 231 * i + j - 1) % 231 = j + 29 := by omega
    simp only [assignment, selVar, ↓reduceIte, hd, hm, sourceOf]
    simp only [show j + 29 ≠ 0 by omega, show ¬ j + 29 < 29 by omega,
      show j + 29 < 57 by omega, ↓reduceIte]
    simp

theorem assignment_arg (gs : List (Bool × Nat × Nat)) (i r : Nat) (side : Bool)
    (hr : r < 58) :
    assignment gs (argVar i side r) = rowArg gs i side r := by
  cases side
  · have hd : (58 + 231 * i + r - 1) / 231 = i := by omega
    have hm : (58 + 231 * i + r - 1) % 231 = r + 57 := by omega
    simp only [assignment, argVar, Bool.false_eq_true, ↓reduceIte, hd, hm]
    simp only [show r + 57 ≠ 0 by omega, show ¬ r + 57 < 29 by omega,
      show ¬ r + 57 < 57 by omega, show r + 57 < 115 by omega, ↓reduceIte]
    simp
  · have hd : (116 + 231 * i + r - 1) / 231 = i := by omega
    have hm : (116 + 231 * i + r - 1) % 231 = r + 115 := by omega
    simp only [assignment, argVar, ↓reduceIte, hd, hm]
    simp only [show r + 115 ≠ 0 by omega, show ¬ r + 115 < 29 by omega,
      show ¬ r + 115 < 57 by omega, show ¬ r + 115 < 115 by omega,
      show r + 115 < 173 by omega, ↓reduceIte]
    simp

theorem assignment_out (gs : List (Bool × Nat × Nat)) (i r : Nat) (hr : r < 58) :
    assignment gs (outVar i r) = rowOut gs i r := by
  have hd : (174 + 231 * i + r - 1) / 231 = i := by omega
  have hm : (174 + 231 * i + r - 1) % 231 = r + 173 := by omega
  simp only [assignment, outVar, hd, hm]
  simp only [show r + 173 ≠ 0 by omega, show ¬ r + 173 < 29 by omega,
    show ¬ r + 173 < 57 by omega, show ¬ r + 173 < 115 by omega,
    show ¬ r + 173 < 173 by omega, ↓reduceIte]
  simp

def clauseSat (a : Nat → Bool) (c : List (Nat × Bool)) : Prop :=
  ∃ lit ∈ c, a lit.1 = lit.2

theorem clauseSat_nil (a : Nat → Bool) : ¬ clauseSat a [] := by
  rintro ⟨lit, hl, _⟩
  exact List.not_mem_nil hl

theorem clauseSat_cons (a : Nat → Bool) (lit : Nat × Bool) (cs : List (Nat × Bool)) :
    clauseSat a (lit :: cs) ↔ a lit.1 = lit.2 ∨ clauseSat a cs := by
  constructor
  · rintro ⟨l, hl, ha⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl ha
    · exact Or.inr ⟨l, hl, ha⟩
  · rintro (h | ⟨l, hl, ha⟩)
    · exact ⟨lit, by simp, h⟩
    · exact ⟨l, List.mem_cons_of_mem _ hl, ha⟩

def sourceBit (a : Nat → Bool) (i source r : Nat) : Bool :=
  if source < 13 then (inputData.getD source 0).testBit r
  else if 13 + i ≤ source then false else a (outVar (source - 13) r)

theorem onehot_sat (a : Nat → Bool) (i : Nat) (side : Bool) (k : Nat) (hk : k < 28)
    (ha : ∀ j < 28, a (selVar i side j) = decide (k = j)) :
    ∀ c ∈ onehotClauses i side, clauseSat a c := by
  intro c hc
  simp only [onehotClauses, List.mem_append, List.mem_singleton] at hc
  rcases hc with rfl | hc
  · refine ⟨positive (selVar i side k), List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ?_⟩
    simp [positive, ha k hk]
  · obtain ⟨j, hj, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hj' : j < 28 := List.mem_range.mp hj
    have hd' : d < 27 - j := List.mem_range.mp hd
    have hjd : j + 1 + d < 28 := by omega
    by_cases he : k = j
    · refine ⟨negative (selVar i side (j + 1 + d)), by simp, ?_⟩
      simp only [negative, ha _ hjd, decide_eq_false_iff_not]
      omega
    · refine ⟨negative (selVar i side j), by simp, ?_⟩
      simp only [negative, ha j hj', decide_eq_false_iff_not]
      exact he

theorem source_sat (a : Nat → Bool) (i source r : Nat) (side : Bool)
    (h : a (selVar i side source) = false ∨
      a (argVar i side r) = sourceBit a i source r) :
    ∀ c ∈ sourceClauses i source r side, clauseSat a c := by
  by_cases hs : source < 13
  · simp only [sourceClauses, hs, ↓reduceIte, List.mem_singleton]
    intro c hc
    subst c
    simpa [clauseSat_cons, clauseSat_nil, sourceBit, hs, positive, negative] using h
  · by_cases hz : 13 + i ≤ source
    · simp only [sourceClauses, hs, hz, ↓reduceIte, List.mem_singleton]
      intro c hc
      subst c
      simp only [sourceBit, hs, hz, ↓reduceIte] at h
      simpa [clauseSat_cons, clauseSat_nil, positive, negative] using h
    · simp only [sourceBit, hs, hz, ↓reduceIte] at h
      intro c hc
      simp only [sourceClauses, hs, hz, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases h with h | h
      · rcases hc with rfl | rfl <;> exact ⟨negative (selVar i side source), by simp, h⟩
      · rcases hc with rfl | rfl <;>
          cases hv : a (outVar (source - 13) r) <;>
          simp_all [clauseSat_cons, clauseSat_nil, positive, negative]

theorem gate_sat (a : Nat → Bool) (i r : Nat)
    (h : a (outVar i r) = if a (opVar i) then
      a (argVar i false r) || a (argVar i true r)
      else a (argVar i false r) && a (argVar i true r)) :
    ∀ c ∈ gateClauses i r, clauseSat a c := by
  cases ho : a (opVar i) <;> cases ha : a (argVar i false r) <;>
    cases hb : a (argVar i true r) <;>
    simp_all [gateClauses, clauseSat_cons, clauseSat_nil, positive, negative]

end PEqualNP.Outside.L_meta_5112_aux
