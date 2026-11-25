import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4675.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def vals (gs : List Gate) (xs : List Bool) : List Bool := gs.foldl step xs

def optionalValue (ws : List Bool) (o : Option ℕ) : Bool :=
  o.elim false (fun i => ws.getD i false)

def pairOp (a : Bool) (x y : Bool) : Bool := if a then x && y else x || y

def pairGate (a : Bool) (i j : ℕ) : Gate :=
  ⟨if a then GateOp.and else GateOp.or, [i, j]⟩

def emitPair (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) : List Gate × Option ℕ :=
  match x, y with
  | some i, some j => (gs ++ [pairGate a i j], some (n + gs.length))
  | some i, none => (gs, if a then none else some i)
  | none, some j => (gs, if a then none else some j)
  | none, none => (gs, none)

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def compileStep (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  if s.2.length = n + q then (s.1, s.2 ++ [none])
  else
    let r := emitPair n s.1 (isAnd g.op)
      (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
    (r.1, s.2 ++ [r.2])

def initial (n : ℕ) : List Gate × List (Option ℕ) := ([], (List.range n).map some)

def compiled (n q : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (compileStep n q) (initial n)

def forceStep (n q : ℕ) (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [if ws.length = n + q then false else g.op.eval (g.inputs.map fun i => ws.getD i false)]

def forcedValues (n q : ℕ) (C : Circuit) (xs : List Bool) : List Bool :=
  C.gates.foldl (forceStep n q) xs

def pruned (n q : ℕ) (C : Circuit) : Circuit :=
  let s := compiled n q C.gates
  ⟨s.1, (s.2.getD C.output none).getD (n + s.1.length)⟩

def Bounded (n : ℕ) (gs : List Gate) (o : Option ℕ) : Prop :=
  ∀ i, o = some i → i < n + gs.length

def Valid (n : ℕ) (s : List Gate × List (Option ℕ)) : Prop :=
  IsAO2 n ⟨s.1, 0⟩ ∧ ∀ o ∈ s.2, Bounded n s.1 o

def Related (xs old : List Bool) (s : List Gate × List (Option ℕ)) : Prop :=
  s.2.length = old.length ∧
    ∀ i, optionalValue (vals s.1 xs) (s.2.getD i none) = old.getD i false

lemma vals_length (gs : List Gate) (xs : List Bool) : (vals gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [vals]
  | cons g gs ih =>
    simp only [vals, List.foldl_cons] at *
    rw [ih]
    simp [step]
    omega

lemma vals_append (gs hs : List Gate) (xs : List Bool) : vals (gs ++ hs) xs = vals hs (vals gs xs) := by
  simp [vals, List.foldl_append]

lemma vals_snoc (gs : List Gate) (g : Gate) (xs : List Bool) : vals (gs ++ [g]) xs = step (vals gs xs) g := by
  rw [vals_append]
  rfl

lemma getD_append_lt {α : Type*} (ws ys : List α) (i : ℕ) (d : α) (hi : i < ws.length) :
    (ws ++ ys).getD i d = ws.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_last {α : Type*} (ws : List α) (x d : α) :
    (ws ++ [x]).getD ws.length d = x := by simp [List.getD_eq_getElem?_getD]

lemma getD_ge {α : Type*} (ws : List α) (i : ℕ) (d : α) (hi : ws.length ≤ i) : ws.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma pairGate_eval (a x y : Bool) : (pairGate a 0 1).op.eval [x, y] = pairOp a x y := by
  cases a <;> cases x <;> cases y <;> rfl

lemma emitPair_length_le (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    (emitPair n gs a x y).1.length ≤ gs.length + 1 := by
  cases x <;> cases y <;> simp [emitPair]

lemma emitPair_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (i : ℕ) (hi : i < n + gs.length) :
    (vals (emitPair n gs a x y).1 xs).getD i false = (vals gs xs).getD i false := by
  cases x <;> cases y <;> simp only [emitPair]
  rw [vals_snoc]
  exact getD_append_lt _ _ _ _ (by rw [vals_length, hx]; exact hi)

lemma emitPair_optional_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (ho : Bounded n gs o) :
    optionalValue (vals (emitPair n gs a x y).1 xs) o = optionalValue (vals gs xs) o := by
  cases o with
  | none => rfl
  | some i => exact emitPair_prefix n gs a x y xs hx i (ho i rfl)

lemma emitPair_semantics (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) :
    optionalValue (vals (emitPair n gs a x y).1 xs) (emitPair n gs a x y).2 =
      pairOp a (optionalValue (vals gs xs) x) (optionalValue (vals gs xs) y) := by
  cases x with
  | none => cases y <;> cases a <;> simp [emitPair, optionalValue, pairOp]
  | some i =>
    cases y with
    | none => cases a <;> simp [emitPair, optionalValue, pairOp]
    | some j =>
      simp only [emitPair, optionalValue, Option.elim_some, vals_snoc, step]
      have hl : (vals gs xs).length = n + gs.length := by rw [vals_length, hx]
      rw [← hl, getD_append_last]
      cases a <;> simp [pairGate, pairOp, GateOp.eval]

lemma emitPair_bounded (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (hx : Bounded n gs x) (hy : Bounded n gs y) :
    Bounded n (emitPair n gs a x y).1 (emitPair n gs a x y).2 := by
  cases x <;> cases y <;> cases a <;> simp_all [emitPair, Bounded]

lemma bounded_getD (n : ℕ) (s : List Gate × List (Option ℕ))
    (h : ∀ o ∈ s.2, Bounded n s.1 o) (i : ℕ) : Bounded n s.1 (s.2.getD i none) := by
  by_cases hi : i < s.2.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h s.2[i] (List.getElem_mem hi)
  · rw [getD_ge _ _ _ (by omega)]
    simp [Bounded]

lemma gateAt_snoc_old (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := getD_append_lt gs [g] j _ hj

lemma gateAt_snoc_last (gs : List Gate) (g : Gate) :
    gateAt ⟨gs ++ [g], 0⟩ gs.length = g := getD_append_last gs g _

lemma append_pair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (i j : ℕ) (hi : i < n + gs.length) (hj : j < n + gs.length) :
    IsAO2 n ⟨gs ++ [pairGate a i j], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · cases a <;> simp [pairGate]
  · intro k hk w hw
    have hkl : k < gs.length + 1 := by simpa using hk
    by_cases hkold : k < gs.length
    · rw [gateAt_snoc_old gs _ k hkold] at hw
      exact h.2.1 k hkold w hw
    · have hke : k = gs.length := by omega
      subst k
      rw [gateAt_snoc_last] at hw
      simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.2.2 g hg
    · rfl

lemma emitPair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y) :
    IsAO2 n ⟨(emitPair n gs a x y).1, 0⟩ := by
  cases x with
  | none => cases y <;> exact h
  | some i =>
    cases y with
    | none => exact h
    | some j => exact append_pair_ao n gs h a i j (hx i rfl) (hy j rfl)

lemma emitPair_length_ge (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    gs.length ≤ (emitPair n gs a x y).1.length := by
  cases x <;> cases y <;> simp [emitPair]

lemma compileStep_map_length (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).2.length = s.2.length + 1 := by
  unfold compileStep
  split_ifs <;> simp

lemma compileStep_size (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).1.length ≤ s.1.length + 1 := by
  unfold compileStep
  split_ifs
  · simp
  · exact emitPair_length_le _ _ _ _ _

lemma compileStep_valid (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (hs : Valid n s) :
    Valid n (compileStep n q s g) := by
  have h0 := bounded_getD n s hs.2 (g.inputs.getD 0 0)
  have h1 := bounded_getD n s hs.2 (g.inputs.getD 1 0)
  unfold compileStep
  split_ifs <;> dsimp only [Valid]
  · refine ⟨hs.1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs.2 o ho
    · simp [Bounded]
  · refine ⟨emitPair_ao _ _ hs.1 _ _ _ h0 h1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · intro i hi
      have hb := hs.2 o ho i hi
      have hl := emitPair_length_ge n s.1 (isAnd g.op)
        (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
      omega
    · exact emitPair_bounded _ _ _ _ _ h0 h1

lemma form_eval (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (ws : List Bool) :
    g.op.eval (g.inputs.map fun i => ws.getD i false) =
      pairOp (isAnd g.op) (ws.getD (g.inputs.getD 0 0) false)
        (ws.getD (g.inputs.getD 1 0) false) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop <;> simp [hop, hab, GateOp.eval, pairOp, isAnd]

lemma related_extend (xs old : List Bool) (gs : List Gate) (m : List (Option ℕ))
    (o : Option ℕ) (v : Bool) (hl : m.length = old.length)
    (hprior : ∀ i, optionalValue (vals gs xs) (m.getD i none) = old.getD i false)
    (hlast : optionalValue (vals gs xs) o = v) :
    Related xs (old ++ [v]) (gs, m ++ [o]) := by
  refine ⟨by simp [hl], ?_⟩
  intro i
  change optionalValue (vals gs xs) ((m ++ [o]).getD i none) = (old ++ [v]).getD i false
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi, getD_append_lt old [v] i false (by omega)]
    exact hprior i
  · subst i
    rw [getD_append_last, hl, getD_append_last]
    exact hlast
  · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by simp; omega)]
    rfl

lemma compileStep_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    Related xs (forceStep n q old g) (compileStep n q s g) := by
  by_cases hkill : s.2.length = n + q
  · have hold : old.length = n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    exact related_extend xs old s.1 s.2 none false hr.1 hr.2 rfl
  · have hold : old.length ≠ n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    apply related_extend xs old _ s.2 _ _ hr.1
    · intro i
      rw [emitPair_optional_prefix n s.1 (isAnd g.op) _ _ _ xs hx (bounded_getD n s hs.2 i)]
      exact hr.2 i
    · rw [emitPair_semantics n s.1 (isAnd g.op) _ _ xs hx, hr.2, hr.2]
      exact (form_eval g hop hlen old).symm

lemma initial_valid (n : ℕ) : Valid n (initial n) := by
  refine ⟨?_, ?_⟩
  · simp [initial, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack]
  · intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
    have hin := List.mem_range.mp hi
    simpa [Bounded, initial] using hin

lemma initial_related (n : ℕ) (xs : List Bool) (hx : xs.length = n) : Related xs xs (initial n) := by
  refine ⟨by simp [initial, hx], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, vals, List.getD_eq_getElem?_getD, hi, optionalValue]
  · have hn : n ≤ i := by omega
    simp [initial, vals, List.getD_eq_getElem?_getD, hi, hx, optionalValue]

lemma fold_valid_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (gs : List Gate) (hform : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s) :
    Valid n (gs.foldl (compileStep n q) s) ∧
      Related xs (gs.foldl (forceStep n q) old) (gs.foldl (compileStep n q) s) := by
  induction gs generalizing s old with
  | nil => exact ⟨hs, hr⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hform g (by simp)
    exact ih (forceStep n q old g) (fun h hh => hform h (by simp [hh])) (compileStep n q s g)
      (compileStep_valid n q s g hs) (compileStep_related n q xs old hx s hs hr g hop hlen)

lemma compiled_valid_related (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n) :
    Valid n (compiled n q C.gates) ∧ Related xs (forcedValues n q C xs) (compiled n q C.gates) := by
  exact fold_valid_related n q xs xs hx C.gates
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (initial n) (initial_valid n) (initial_related n xs hx)

lemma optionalValue_lookup (n : ℕ) (gs : List Gate) (xs : List Bool) (hx : xs.length = n)
    (o : Option ℕ) :
    (vals gs xs).getD (o.getD (n + gs.length)) false = optionalValue (vals gs xs) o := by
  cases o with
  | none =>
    change (vals gs xs).getD (n + gs.length) false = false
    exact getD_ge _ _ _ (by rw [vals_length, hx])
  | some i => rfl

lemma pruned_eval (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (xs : List Bool) (hx : xs.length = n) :
    (pruned n q C).eval xs = (forcedValues n q C xs).getD C.output false := by
  have h := (compiled_valid_related n q C hAO xs hx).2.2 C.output
  change (vals (compiled n q C.gates).1 xs).getD
    (((compiled n q C.gates).2.getD C.output none).getD (n + (compiled n q C.gates).1.length)) false = _
  rw [optionalValue_lookup n _ xs hx]
  exact h

lemma pruned_ao (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (pruned n q C) := by
  have h := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1.1
  exact h

lemma compileStep_map_prior (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (i : ℕ) (hi : i < s.2.length) :
    (compileStep n q s g).2.getD i none = s.2.getD i none := by
  unfold compileStep
  split_ifs <;> exact getD_append_lt _ _ _ _ hi

lemma fold_map_length (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).2.length = s.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, compileStep_map_length]
    simp [List.length_cons]
    omega

lemma fold_size_le (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).1.length ≤ s.1.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hh := ih (compileStep n q s g)
    have hs := compileStep_size n q s g
    simp only [List.length_cons]
    omega

lemma fold_map_prior (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (i : ℕ) (hi : i < s.2.length) :
    (gs.foldl (compileStep n q) s).2.getD i none = s.2.getD i none := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (compileStep n q s g) (by rw [compileStep_map_length]; omega)]
    exact compileStep_map_prior n q s g i hi

lemma compiled_map_length (n q : ℕ) (gs : List Gate) :
    (compiled n q gs).2.length = n + gs.length := by
  rw [compiled, fold_map_length]
  simp [initial]

lemma compiled_size_le (n q : ℕ) (gs : List Gate) : (compiled n q gs).1.length ≤ gs.length := by
  simpa [compiled, initial] using fold_size_le n q gs (initial n)

lemma compiled_split (n q : ℕ) (gs : List Gate) (k : ℕ) :
    compiled n q gs = (gs.drop k).foldl (compileStep n q) (compiled n q (gs.take k)) := by
  unfold compiled
  rw [← List.foldl_append, List.take_append_drop]

lemma compiled_take_succ (n q : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    compiled n q (gs.take (j + 1)) = compileStep n q (compiled n q (gs.take j)) gs[j] := by
  unfold compiled
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

lemma forced_step (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    compiled n q (gs.take (q + 1)) =
      ((compiled n q (gs.take q)).1, (compiled n q (gs.take q)).2 ++ [none]) := by
  rw [compiled_take_succ n q gs q hq]
  have hl : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simp [compileStep, hl]

lemma killed_alias (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    (compiled n q gs).2.getD (n + q) none = none := by
  rw [compiled_split n q gs (q + 1)]
  have hl : n + q < (compiled n q (gs.take (q + 1))).2.length := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
    omega
  rw [fold_map_prior n q (gs.drop (q + 1)) _ (n + q) hl, forced_step n q gs hq]
  have hlq : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  change ((compiled n q (gs.take q)).2 ++ [none]).getD (n + q) none = none
  rw [← hlq, getD_append_last]

lemma emitPair_drop (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (h : x = none ∨ y = none) : (emitPair n gs a x y).1 = gs := by
  rcases h with rfl | rfl
  · cases y <;> rfl
  · cases x <;> rfl

lemma compileStep_drop_missing (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (w : ℕ) (hw : w ∈ g.inputs) (hlen : g.inputs.length = 2) (hnone : s.2.getD w none = none) :
    (compileStep n q s g).1 = s.1 := by
  unfold compileStep
  split_ifs
  · rfl
  · apply emitPair_drop
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by simpa [hab] using hnone)
    · exact Or.inr (by simpa [hab] using hnone)

lemma reader_step_drop (n q r : ℕ) (gs : List Gate) (hqr : q < r) (hr : r < gs.length)
    (hread : n + q ∈ gs[r].inputs) (hlen : gs[r].inputs.length = 2) :
    (compiled n q (gs.take (r + 1))).1 = (compiled n q (gs.take r)).1 := by
  rw [compiled_take_succ n q gs r hr]
  apply compileStep_drop_missing n q _ gs[r] (n + q) hread hlen
  exact killed_alias n q (gs.take r) (by simp [List.length_take]; omega)

lemma count_two_skips (f : ℕ → ℕ) (N q r : ℕ) (hqr : q < r) (hr : r < N)
    (hzero : f 0 = 0) (hstep : ∀ j < N, f (j + 1) ≤ f j + 1)
    (hqdrop : f (q + 1) = f q) (hrdrop : f (r + 1) = f r) : f N + 2 ≤ N := by
  have hinterval : ∀ a d, a + d ≤ N → f (a + d) ≤ f a + d := by
    intro a d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs := hstep (a + d) (by omega)
      have he : a + (d + 1) = (a + d) + 1 := by omega
      rw [he]
      omega
  have h0q := hinterval 0 q (by omega)
  have hqr' := hinterval (q + 1) (r - (q + 1)) (by omega)
  have hrN := hinterval (r + 1) (N - (r + 1)) (by omega)
  have heq : q + 1 + (r - (q + 1)) = r := by omega
  have her : r + 1 + (N - (r + 1)) = N := by omega
  rw [heq, hqdrop] at hqr'
  rw [her, hrdrop] at hrN
  simp only [zero_add, hzero] at h0q
  omega

lemma pruned_size_two (n q r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs) :
    (pruned n q C).size + 2 ≤ C.size := by
  have hlen := hAO.2.2 C.gates[r] (List.getElem_mem hr)
  have h := count_two_skips (fun j => (compiled n q (C.gates.take j)).1.length)
    C.gates.length q r hqr hr (by simp [compiled, initial]) ?_ ?_ ?_
  · simpa [pruned, Circuit.size] using h
  · intro j hj
    rw [compiled_take_succ n q C.gates j hj]
    exact compileStep_size n q _ C.gates[j]
  · rw [forced_step n q C.gates (by omega)]
  · rw [reader_step_drop n q r C.gates hqr hr hread hlen]

end PEqualNP.Outside.L_meta_4675.Pruning


namespace PEqualNP.Outside.L_meta_4675.OrReachAPI

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (hi | ⟨k, _, hr, _, _⟩)
    · exact Fin.ext hi
    · have := hr.1
      omega
  · intro hi
    exact Or.inl (congrArg Fin.val hi)

lemma orIn_non_or (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op ≠ GateOp.or) : orIn n C (n + k) = ∅ := by
  ext i
  simp only [Finset.notMem_empty, iff_false]
  intro hi
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨j, _, hr, hjop, _⟩
  · have := i.isLt
    omega
  · obtain ⟨_, hr⟩ := (orReaches_iff n C k j).mp hr
    rcases hr with rfl | ⟨hkop, _⟩
    · exact hop hjop
    · exact hop hkop

lemma mem_orIn_or_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or)
    (hback : ∀ w ∈ (gateAt C k).inputs, w < n + k) (i : Fin n) :
    i ∈ orIn n C (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, i ∈ orIn n C w := by
  constructor
  · intro hi
    rw [mem_orIn] at hi
    rcases hi with hi | ⟨j, hj, hr, hjop, hij⟩
    · have := i.isLt
      omega
    · obtain ⟨_, hr⟩ := (orReaches_iff n C k j).mp hr
      rcases hr with rfl | ⟨_, w, hw, _, hrw⟩
      · exact ⟨i.val, hij, orIn_self n C i⟩
      · exact ⟨w, hw, (mem_orIn n C w i).mpr (Or.inr ⟨j, hj, hrw, hjop, hij⟩)⟩
  · rintro ⟨w, hw, hi⟩
    exact orIn_up n C k w i hk hop hw (hback w hw) hi

lemma orIn_or_pair (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hinputs : (gateAt C k).inputs = [a, b])
    (hback : ReadsBack n C) :
    orIn n C (n + k) = orIn n C a ∪ orIn n C b := by
  ext i
  rw [mem_orIn_or_iff n C k hk hop (hback k hk)]
  simp [hinputs]

lemma orSets_fold_prefix (n : ℕ) (hs : List Gate) (cs : List (List ℕ))
    (j : ℕ) (hj : j < cs.length) :
    (hs.foldl (orStep n) cs).getD j [] = cs.getD j [] := by
  induction hs generalizing cs with
  | nil => rfl
  | cons h hs ih =>
    rw [List.foldl_cons, ih]
    · simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hj]
    · simp only [orStep, List.length_append, List.length_singleton]
      omega

lemma gateAt_append_old (gs hs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt (⟨gs ++ hs, 0⟩ : Circuit) j = gateAt ⟨gs, 0⟩ j := by
  simp only [gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

lemma orReaches_append_prefix (n : ℕ) (gs hs : List Gate) (w j : ℕ)
    (hw : w < n + gs.length) :
    OrReaches n (⟨gs ++ hs, 0⟩ : Circuit) w j ↔ OrReaches n ⟨gs, 0⟩ w j := by
  by_cases hn : n ≤ w
  · unfold OrReaches orSets
    rw [List.foldl_append, orSets_fold_prefix n hs _ (w - n)]
    rw [orSets_len]
    simp only [List.length_nil, zero_add]
    omega
  · simp only [OrReaches, hn, false_and]

lemma orIn_append_prefix (n : ℕ) (gs hs : List Gate) (w : ℕ) (hw : w < n + gs.length) :
    orIn n (⟨gs ++ hs, 0⟩ : Circuit) w = orIn n ⟨gs, 0⟩ w := by
  ext i
  rw [mem_orIn, mem_orIn]
  constructor
  · rintro (hi | ⟨j, hj, hr, hop, hin⟩)
    · exact Or.inl hi
    · have hr' := (orReaches_append_prefix n gs hs w j hw).mp hr
      have hj' : j < gs.length := by
        have hb := (orReaches_bound n (⟨gs, 0⟩ : Circuit) j w hr').1
        omega
      rw [gateAt_append_old gs hs j hj'] at hop hin
      exact Or.inr ⟨j, hj', hr', hop, hin⟩
  · rintro (hi | ⟨j, hj, hr, hop, hin⟩)
    · exact Or.inl hi
    · rw [← gateAt_append_old gs hs j hj] at hop hin
      exact Or.inr ⟨j, by
        change j < (gs ++ hs).length
        simp only [List.length_append]
        change j < gs.length at hj
        omega,
        (orReaches_append_prefix n gs hs w j hw).mpr hr, hop, hin⟩

end PEqualNP.Outside.L_meta_4675.OrReachAPI

namespace PEqualNP.Outside.L_meta_4675.StarAppend

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.OrReachAPI

def appendStar (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [C.output, n + C.gates.length]⟩],
    n + C.gates.length + 1⟩

lemma appendStar_size (n : ℕ) (C : Circuit) (a b : ℕ) :
    (appendStar n C a b).size = C.size + 2 := by simp [appendStar, Circuit.size]

lemma gateAt_old (n : ℕ) (C : Circuit) (a b j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendStar n C a b) j = gateAt C j := by
  exact gateAt_append_old C.gates _ j hj

lemma gateAt_and (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendStar n C a b) C.gates.length = ⟨GateOp.and, [a, b]⟩ := by
  simp [appendStar, gateAt, List.getD_eq_getElem?_getD]

lemma gateAt_output (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendStar n C a b) (C.gates.length + 1) =
      ⟨GateOp.or, [C.output, n + C.gates.length]⟩ := by
  simp [appendStar, gateAt, List.getD_eq_getElem?_getD]

lemma appendStar_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) : IsAO2 n (appendStar n C a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendStar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.1 g hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj w hw
    have hj' : j < C.gates.length + 2 := by simpa [appendStar] using hj
    by_cases hjold : j < C.gates.length
    · rw [gateAt_old n C a b j hjold] at hw
      exact hAO.2.1 j hjold w hw
    · by_cases hjand : j = C.gates.length
      · subst j
        rw [gateAt_and] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption
      · have hjo : j = C.gates.length + 1 := by omega
        subst j
        rw [gateAt_output] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
  · intro g hg
    simp only [appendStar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.2.2 g hg
    · rfl
    · rfl

lemma orIn_old (n : ℕ) (C : Circuit) (a b w : ℕ) (hw : w < n + C.gates.length) :
    orIn n (appendStar n C a b) w = orIn n C w :=
  orIn_append_prefix n C.gates _ w hw

lemma orIn_and (n : ℕ) (C : Circuit) (a b : ℕ) :
    orIn n (appendStar n C a b) (n + C.gates.length) = ∅ := by
  apply orIn_non_or n _ C.gates.length
  · simp [appendStar]
  · rw [gateAt_and]
    simp

lemma orIn_output (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) :
    orIn n (appendStar n C a b) (n + C.gates.length + 1) = orIn n C C.output := by
  have hA := appendStar_ao n C a b hAO ha hb ho
  have he : n + C.gates.length + 1 = n + (C.gates.length + 1) := by omega
  rw [he, orIn_or_pair n _ (C.gates.length + 1) C.output (n + C.gates.length)]
  · rw [orIn_old n C a b C.output ho, orIn_and, Finset.union_empty]
  · simp [appendStar]
  · rw [gateAt_output]
  · rw [gateAt_output]
  · exact hA.2.1

lemma appendStar_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool)
    (hAO : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) (he : orIn n C C.output = ∅) :
    tCount n (appendStar n C a b) colour = tCount n C colour := by
  have hs : twoColour n (appendStar n C a b) colour = twoColour n C colour := by
    ext j
    simp only [twoColour, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hjc⟩
      have hj' : j < C.gates.length + 2 := by simpa [appendStar] using hj
      by_cases hjo : j < C.gates.length
      · refine ⟨hjo, ?_⟩
        rcases hjc with ⟨_, hop, hp, hl⟩
        rw [gateAt_old n C a b j hjo] at hop
        rw [orIn_old n C a b (n + j) (by omega)] at hp hl
        exact ⟨hjo, hop, hp, hl⟩
      · by_cases hja : j = C.gates.length
        · subst j
          have hh := hjc.2.1
          rw [gateAt_and] at hh
          cases hh
        · have hje : j = C.gates.length + 1 := by omega
          subst j
          have hh := hjc.2.2.1
          have hro := orIn_output n C a b hAO ha hb ho
          have heq : n + (C.gates.length + 1) = n + C.gates.length + 1 := by omega
          rw [heq, hro, he] at hh
          simp at hh
    · rintro ⟨hj, _, hop, hp, hl⟩
      refine ⟨by simp [appendStar]; omega, by simp [appendStar]; omega, ?_, ?_, ?_⟩
      · rw [gateAt_old n C a b j hj]
        exact hop
      · rw [orIn_old n C a b (n + j) (by omega)]
        exact hp
      · rw [orIn_old n C a b (n + j) (by omega)]
        exact hl
  unfold tCount
  rw [hs]

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length := by
  have h : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).length =
        ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      simp
      omega
  exact h C.gates xs

lemma appendStar_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool)
    (hx : xs.length = n) (ho : C.output < n + C.gates.length) :
    (appendStar n C a b).eval xs =
      (C.eval xs || ((C.wires xs).getD a false && (C.wires xs).getD b false)) := by
  let ws := C.wires xs
  let v := ws.getD a false && ws.getD b false
  have hw : ws.length = n + C.gates.length := by exact (wires_length C xs).trans (by rw [hx])
  have hp : (ws ++ [v]).getD C.output false = ws.getD C.output false := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  have hv : (ws ++ [v]).getD (n + C.gates.length) false = v := by
    rw [← hw]
    simp [List.getD_eq_getElem?_getD]
  have hl : (ws ++ [v]).length = n + C.gates.length + 1 := by simp [hw]
  have hout : ∀ t : Bool, ((ws ++ [v]) ++ [t]).getD (n + C.gates.length + 1) false = t := by
    intro t
    rw [← hl]
    simp [List.getD_eq_getElem?_getD]
  simp only [appendStar, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
  change ((ws ++ [v]) ++ [(ws ++ [v]).getD C.output false ||
    (ws ++ [v]).getD (n + C.gates.length) false]).getD (n + C.gates.length + 1) false =
    (ws.getD C.output false || v)
  rw [hout, hp, hv]

end PEqualNP.Outside.L_meta_4675.StarAppend

namespace PEqualNP.Outside.L_meta_4675.StarAppendOptional

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.OrReachAPI
open PEqualNP.Outside.L_meta_4675.StarAppend

def appendAnd (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.gates.length⟩

def restoreStar (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  if C.output < n + C.gates.length then appendStar n C a b else appendAnd n C a b

lemma appendAnd_gate (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendAnd n C a b) C.gates.length = ⟨GateOp.and, [a, b]⟩ := by
  simp [appendAnd, gateAt, List.getD_eq_getElem?_getD]

lemma appendAnd_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (appendAnd n C a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · exact Or.inl rfl
  · intro j hj w hw
    have hj' : j < C.gates.length + 1 := by simpa [appendAnd] using hj
    by_cases hjo : j < C.gates.length
    · have he : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hjo
      rw [he] at hw
      exact hAO.2.1 j hjo w hw
    · have he : j = C.gates.length := by omega
      subst j
      rw [appendAnd_gate] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl

lemma appendAnd_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool) :
    tCount n (appendAnd n C a b) colour = tCount n C colour := by
  have hs : twoColour n (appendAnd n C a b) colour = twoColour n C colour := by
    ext j
    simp only [twoColour, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hjc⟩
      have hj' : j < C.gates.length + 1 := by simpa [appendAnd] using hj
      have hjo : j < C.gates.length := by
        by_contra hno
        have he : j = C.gates.length := by omega
        subst j
        have hop := hjc.2.1
        rw [appendAnd_gate] at hop
        cases hop
      have hg : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hjo
      have hr : orIn n (appendAnd n C a b) (n+j) = orIn n C (n+j) :=
        orIn_append_prefix n C.gates _ (n+j) (by omega)
      rcases hjc with ⟨_, hop, hp, hl⟩
      rw [hg] at hop
      rw [hr] at hp hl
      exact ⟨hjo, hjo, hop, hp, hl⟩
    · rintro ⟨hj, _, hop, hp, hl⟩
      have hg : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hj
      have hr : orIn n (appendAnd n C a b) (n+j) = orIn n C (n+j) :=
        orIn_append_prefix n C.gates _ (n+j) (by omega)
      refine ⟨by simp [appendAnd]; omega, by simp [appendAnd]; omega, ?_, ?_, ?_⟩
      · rw [hg]; exact hop
      · rw [hr]; exact hp
      · rw [hr]; exact hl
  unfold tCount
  rw [hs]

lemma appendAnd_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (appendAnd n C a b).eval xs =
      ((C.wires xs).getD a false && (C.wires xs).getD b false) := by
  have hl : (C.wires xs).length = n + C.gates.length := by rw [wires_length, hx]
  simp only [appendAnd, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    Bool.and_true]
  change (C.wires xs ++ [(C.wires xs).getD a false && (C.wires xs).getD b false]).getD
    (n + C.gates.length) false =
      ((C.wires xs).getD a false && (C.wires xs).getD b false)
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

lemma restoreStar_size (n : ℕ) (C : Circuit) (a b : ℕ) :
    (restoreStar n C a b).size ≤ C.size + 2 := by
  unfold restoreStar
  split_ifs
  · rw [appendStar_size]
  · simp [appendAnd, Circuit.size]

lemma restoreStar_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (restoreStar n C a b) := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_ao n C a b hAO ha hb ho
  · exact appendAnd_ao n C a b hAO ha hb

lemma restoreStar_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool)
    (hAO : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (he : orIn n C C.output = ∅) :
    tCount n (restoreStar n C a b) colour = tCount n C colour := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_tCount n C a b colour hAO ha hb ho he
  · exact appendAnd_tCount n C a b colour

lemma restoreStar_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (restoreStar n C a b).eval xs =
      (C.eval xs || ((C.wires xs).getD a false && (C.wires xs).getD b false)) := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_eval n C a b xs hx ho
  · have hz : C.eval xs = false := by
      unfold Circuit.eval
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by rw [wires_length, hx]; omega)]
      rfl
    rw [hz, Bool.false_or]
    exact appendAnd_eval n C a b xs hx

end PEqualNP.Outside.L_meta_4675.StarAppendOptional


namespace PEqualNP.Outside.L_meta_4675.PruningTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.OrReachAPI

def AliasReach (n : ℕ) (C : Circuit) (gs : List Gate) (o : Option ℕ) (i : ℕ) : Prop :=
  ∀ w, o = some w → orIn n ⟨gs, 0⟩ w ⊆ orIn n C i

def ReachValid (n : ℕ) (C : Circuit) (s : List Gate × List (Option ℕ)) : Prop :=
  ∀ i, AliasReach n C s.1 (s.2.getD i none) i

def OrTrace (n : ℕ) (C : Circuit) (gs : List Gate) : Prop :=
  ∀ g < gs.length, (gateAt ⟨gs, 0⟩ g).op = GateOp.or →
    ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧
      orIn n ⟨gs, 0⟩ (n + g) ⊆ orIn n C (n + h)

lemma emitPair_reach_prior (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (w : ℕ) (hw : w < n + gs.length) :
    orIn n ⟨(emitPair n gs a x y).1, 0⟩ w = orIn n ⟨gs, 0⟩ w := by
  cases x <;> cases y <;> simp only [emitPair]
  exact orIn_append_prefix n gs [_] w hw

lemma emitPair_alias_prior (n : ℕ) (C : Circuit) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (i : ℕ) (ho : Bounded n gs o) (ha : AliasReach n C gs o i) :
    AliasReach n C (emitPair n gs a x y).1 o i := by
  intro w hw
  rw [emitPair_reach_prior n gs a x y w (ho w hw)]
  exact ha w hw

lemma emitPair_output_reach (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C k = if a then ∅ else orIn n C i ∪ orIn n C j) :
    AliasReach n C (emitPair n gs a x y).1 (emitPair n gs a x y).2 k := by
  cases x with
  | none =>
    cases y with
    | none => simp [AliasReach, emitPair]
    | some v =>
      cases a
      · intro w hw
        have he : v = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hyj v rfl).trans Finset.subset_union_right
      · simp [AliasReach, emitPair]
  | some u =>
    cases y with
    | none =>
      cases a
      · intro w hw
        have he : u = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hxi u rfl).trans Finset.subset_union_left
      · simp [AliasReach, emitPair]
    | some v =>
      intro w hw
      have he : n + gs.length = w := by simpa [emitPair] using hw
      subst w
      have hu : u < n + gs.length := hx u rfl
      have hv : v < n + gs.length := hy v rfl
      have hao := append_pair_ao n gs hAO a u v hu hv
      change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + gs.length) ⊆ _
      cases a with
      | false =>
        rw [orIn_or_pair n _ gs.length u v (by simp) (by rw [gateAt_snoc_last]; rfl)
          (by rw [gateAt_snoc_last]; rfl) hao.2.1]
        rw [orIn_append_prefix n gs [_] u hu, orIn_append_prefix n gs [_] v hv, hr]
        exact Finset.union_subset_union (hxi u rfl) (hyj v rfl)
      | true =>
        rw [orIn_non_or n _ gs.length (by simp) (by rw [gateAt_snoc_last]; simp [pairGate])]
        exact Finset.empty_subset _

lemma emitPair_trace (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (ht : OrTrace n C gs) (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = if a then GateOp.and else GateOp.or)
    (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C (n + k) = if a then ∅ else orIn n C i ∪ orIn n C j) :
    OrTrace n C (emitPair n gs a x y).1 := by
  cases x with
  | none => cases y <;> exact ht
  | some u =>
    cases y with
    | none => exact ht
    | some v =>
      intro g hg hgo
      change g < (gs ++ [pairGate a u v]).length at hg
      change (gateAt ⟨gs ++ [pairGate a u v], 0⟩ g).op = GateOp.or at hgo
      by_cases hgold : g < gs.length
      · rw [gateAt_snoc_old gs _ g hgold] at hgo
        obtain ⟨h, hh, hho, hsub⟩ := ht g hgold hgo
        refine ⟨h, hh, hho, ?_⟩
        change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + g) ⊆ _
        rw [orIn_append_prefix n gs [_] (n + g) (by omega)]
        exact hsub
      · have hge : g = gs.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hg; omega
        subst g
        rw [gateAt_snoc_last] at hgo
        have ha : a = false := by cases a <;> simp_all [pairGate]
        refine ⟨k, hk, by simpa [ha] using hop, ?_⟩
        exact emitPair_output_reach n C gs hAO a (some u) (some v) hx hy i j (n + k) hxi hyj hr
          (n + gs.length) rfl

lemma alias_extend (n : ℕ) (C : Circuit) (gs : List Gate) (m : List (Option ℕ)) (o : Option ℕ)
    (hprior : ∀ i, AliasReach n C gs (m.getD i none) i)
    (hlast : AliasReach n C gs o m.length) : ReachValid n C (gs, m ++ [o]) := by
  intro i w hw
  change (m ++ [o]).getD i none = some w at hw
  change orIn n ⟨gs, 0⟩ w ⊆ orIn n C i
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi] at hw
    exact hprior i w hw
  · subst i
    rw [getD_append_last] at hw
    exact hlast w hw
  · rw [getD_ge _ _ _ (by simp; omega)] at hw
    cases hw

lemma gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma original_pair_reach (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    orIn n C (n + k) = if isAnd (gateAt C k).op then ∅ else
      orIn n C ((gateAt C k).inputs.getD 0 0) ∪ orIn n C ((gateAt C k).inputs.getD 1 0) := by
  have hm := gateAt_mem C k hk
  have hlen := hAO.2.2 (gateAt C k) hm
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
  rcases hAO.1 (gateAt C k) hm with hop | hop
  · simp only [hop, isAnd, ↓reduceIte]
    exact orIn_non_or n C k hk (by rw [hop]; intro he; cases he)
  · simp only [hop, isAnd, hij, List.getD_cons_zero, List.getD_cons_succ]
    exact orIn_or_pair n C k i j hk hop hij hAO.2.1

lemma original_gate_kind (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).op = if isAnd (gateAt C k).op then GateOp.and else GateOp.or := by
  rcases hAO.1 (gateAt C k) (gateAt_mem C k hk) with hop | hop <;> simp [hop, isAnd]

lemma compileStep_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : ReachValid n C s)
    (ht : OrTrace n C s.1) (hl : s.2.length = n + j) :
    ReachValid n C (compileStep n q s (gateAt C j)) ∧
      OrTrace n C (compileStep n q s (gateAt C j)).1 := by
  have hx := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 0 0)
  have hy := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 1 0)
  have hpair := original_pair_reach n C hAO j hj
  unfold compileStep
  split_ifs <;> dsimp only
  · refine ⟨alias_extend n C s.1 s.2 none hr ?_, ht⟩
    simp [AliasReach]
  · constructor
    · apply alias_extend
      · intro i
        exact emitPair_alias_prior n C s.1 _ _ _ (s.2.getD i none) i
          (bounded_getD n s hs.2 i) (hr i)
      · rw [hl]
        exact emitPair_output_reach n C s.1 hs.1 _ _ _ hx hy _ _ (n + j) (hr _) (hr _) hpair
    · exact emitPair_trace n C s.1 hs.1 ht _ _ _ hx hy _ _ j hj
        (original_gate_kind n C hAO j hj) (hr _) (hr _) hpair

lemma initial_reaches (n : ℕ) (C : Circuit) : ReachValid n C (initial n) ∧ OrTrace n C (initial n).1 := by
  constructor
  · intro i w hw
    by_cases hi : i < n
    · have hget : (initial n).2.getD i none = some i := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      have he : i = w := Option.some.inj hw
      subst w
      change orIn n ⟨[], 0⟩ i ⊆ orIn n C i
      rw [orIn_input n _ i hi, orIn_input n C i hi]
    · have hget : (initial n).2.getD i none = none := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      cases hw
  · intro g hg
    simp [initial] at hg

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma compiled_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ReachValid n C (compiled n q C.gates) ∧ OrTrace n C (compiled n q C.gates).1 := by
  have h : ∀ j, j ≤ C.gates.length →
      Valid n (compiled n q (C.gates.take j)) ∧
      ReachValid n C (compiled n q (C.gates.take j)) ∧
      OrTrace n C (compiled n q (C.gates.take j)).1 := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [compiled] using (show Valid n (initial n) ∧ ReachValid n C (initial n) ∧
        OrTrace n C (initial n).1 from ⟨initial_valid n, initial_reaches n C⟩)
    | succ j ih =>
      intro hj
      obtain ⟨hv, hr, ht⟩ := ih (by omega)
      have hlt : j < C.gates.length := by omega
      rw [compiled_take_succ n q C.gates j hlt, ← gateAt_eq_getElem C j hlt]
      refine ⟨compileStep_valid n q _ (gateAt C j) hv, ?_⟩
      apply compileStep_reaches n q C hAO j hlt _ hv hr ht
      rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simpa using (h C.gates.length le_rfl).2

lemma trace_count_zero (n : ℕ) (C : Circuit) (gs : List Gate) (s : ℕ → Bool)
    (ht : OrTrace n C gs) (hz : tCount n C s = 0) : tCount n ⟨gs, 0⟩ s = 0 := by
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have htwo : IsTwoColour n ⟨gs, 0⟩ s g := (Finset.mem_filter.mp hg).2
  obtain ⟨h, hh, hop, hsub⟩ := ht g htwo.1 htwo.2.1
  have hold : IsTwoColour n C s h := by
    refine ⟨hh, hop, ?_, ?_⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.1
      exact ⟨i, hsub hi, hsi⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.2
      exact ⟨i, hsub hi, hsi⟩
  have hm : h ∈ twoColour n C s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hold⟩
  rw [he] at hm
  simp at hm

lemma pruned_count_zero (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (s : ℕ → Bool)
    (hz : tCount n C s = 0) : tCount n (pruned n q C) s = 0 := by
  exact trace_count_zero n C (compiled n q C.gates).1 s (compiled_reaches n q C hAO).2 hz

end PEqualNP.Outside.L_meta_4675.PruningTrace

namespace PEqualNP.Outside.L_meta_4675.PruningPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.Pruning

lemma range_some_getD (N w : ℕ) (hw : w < N) :
    ((List.range N).map some).getD w none = some w := by
  simp [List.getD_eq_getElem?_getD, hw]

lemma pairGate_form (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (hab : g.inputs = [a, b]) : pairGate (isAnd g.op) a b = g := by
  rcases hop with hop | hop <;> cases g <;> simp_all [pairGate, isAnd]

lemma compileStep_identity (n q : ℕ) (gs : List Gate) (g : Gate) (hq : gs.length < q)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hback : ∀ w ∈ g.inputs, w < n + gs.length) :
    compileStep n q (gs, (List.range (n + gs.length)).map some) g =
      (gs ++ [g], (List.range (n + (gs ++ [g]).length)).map some) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha := hback a (by simp [hab])
  have hb := hback b (by simp [hab])
  have hkill : n + gs.length ≠ n + q := by omega
  simp only [compileStep, List.length_map, List.length_range, hkill, ↓reduceIte]
  simp only [hab, List.getD_cons_zero, List.getD_cons_succ]
  rw [range_some_getD _ _ ha, range_some_getD _ _ hb]
  simp only [emitPair, pairGate_form g hop a b hab, List.length_append, List.length_singleton]
  rw [show n + (gs.length + 1) = (n + gs.length) + 1 by omega, List.range_succ, List.map_append]
  rfl

lemma compiled_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hkq : k ≤ q) (hkC : k ≤ C.gates.length) :
    compiled n q (C.gates.take k) = (C.gates.take k, (List.range (n + k)).map some) := by
  induction k with
  | zero => simp [compiled, initial]
  | succ k ih =>
    have hk : k < C.gates.length := by omega
    have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    have htake : (C.gates.take k).length = k := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    rw [compiled_take_succ n q C.gates k hk, ih (by omega) (by omega)]
    have hg : gateAt C k = C.gates[k] := by
      simp [gateAt, List.getD_eq_getElem?_getD, hk]
    have hback : ∀ w ∈ C.gates[k].inputs, w < n + (C.gates.take k).length := by
      intro w hw
      rw [htake]
      exact hAO.2.1 k hk w (by simpa [hg] using hw)
    have he := compileStep_identity n q (C.gates.take k) C.gates[k]
      (by omega) (hAO.1 _ hmem) (hAO.2.2 _ hmem) hback
    rw [htake, ← List.take_succ_eq_append_getElem hk] at he
    simpa [List.length_take, Nat.min_eq_left hkC] using he

lemma alias_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (w : ℕ) (hw : w < n + q) :
    (compiled n q C.gates).2.getD w none = some w := by
  rw [compiled_split n q C.gates q]
  have hlen : w < (compiled n q (C.gates.take q)).2.length := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left hq]
    exact hw
  rw [fold_map_prior n q (C.gates.drop q) _ w hlen, compiled_before n q C hAO q le_rfl hq]
  exact range_some_getD (n + q) w hw

lemma force_fold_before (n q : ℕ) (gs : List Gate) (xs : List Bool) (hx : xs.length = n)
    (hlen : gs.length ≤ q) : gs.foldl (forceStep n q) xs = vals gs xs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have hlen' : gs.length ≤ q := by simp only [List.length_append, List.length_singleton] at hlen; omega
    have hlt : gs.length < q := by simp only [List.length_append, List.length_singleton] at hlen; omega
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih hlen', vals_snoc]
    unfold forceStep step
    have hne : n + gs.length ≠ n + q := by omega
    simp only [vals_length, hx, hne, ↓reduceIte]

lemma force_fold_prefix (n q : ℕ) (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (gs.foldl (forceStep n q) xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (forceStep n q xs g) (by simp [forceStep]; omega)]
    exact getD_append_lt xs _ w false hw

lemma vals_prefix (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (vals gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (vals gs (step xs g)).getD w false = xs.getD w false
    rw [ih (step xs g) (by simp [step]; omega)]
    exact getD_append_lt xs _ w false hw

lemma forced_wire_before (n q : ℕ) (C : Circuit) (hq : q ≤ C.gates.length)
    (xs : List Bool) (hx : xs.length = n) (w : ℕ) (hw : w < n + q) :
    (forcedValues n q C xs).getD w false = (C.wires xs).getD w false := by
  have hlen : (C.gates.take q).length = q := by
    rw [List.length_take, Nat.min_eq_left hq]
  have hval : w < (vals (C.gates.take q) xs).length := by
    rw [vals_length, hx, hlen]
    exact hw
  have hplain : (C.wires xs).getD w false = (vals (C.gates.take q) xs).getD w false := by
    change (vals C.gates xs).getD w false = _
    calc
      _ = (vals (C.gates.drop q) (vals (C.gates.take q) xs)).getD w false := by
        rw [← vals_append, List.take_append_drop]
      _ = _ := vals_prefix _ _ w hval
  rw [hplain]
  calc
    _ = ((C.gates.drop q).foldl (forceStep n q)
        ((C.gates.take q).foldl (forceStep n q) xs)).getD w false := by
      unfold forcedValues
      rw [← List.foldl_append, List.take_append_drop]
    _ = _ := by
      rw [force_fold_before n q (C.gates.take q) xs hx (by omega)]
      exact force_fold_prefix n q (C.gates.drop q) _ w hval

lemma pruned_wire_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (xs : List Bool) (hx : xs.length = n)
    (w : ℕ) (hw : w < n + q) :
    ((pruned n q C).wires xs).getD w false = (C.wires xs).getD w false := by
  have h := (compiled_valid_related n q C hAO xs hx).2.2 w
  rw [alias_before n q C hAO hq w hw] at h
  exact h.trans (forced_wire_before n q C hq xs hx w hw)

end PEqualNP.Outside.L_meta_4675.PruningPrefix

namespace PEqualNP.Outside.L_meta_4675.PruneRestore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.PruningPrefix
open PEqualNP.Outside.L_meta_4675.PruningTrace
open PEqualNP.Outside.L_meta_4675.StarAppendOptional

lemma prior_wire_valid (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (w : ℕ) (hw : w < n + q) :
    w < n + (pruned n q C).gates.length := by
  have hv := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1
  have hb := bounded_getD n (compiled n q C.gates) hv.2 w
  exact hb w (alias_before n q C hAO hq w hw)

lemma prune_then_restore (n q r a b : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (colour : ℕ → Bool) (hAO : IsAO2 n C) (hz : tCount n C colour = 0)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs)
    (ha : a < n + q) (hb : b < n + q)
    (hreach : orIn n (pruned n q C) (pruned n q C).output = ∅)
    (hsemantic : ∀ x : Fin n → Bool,
      f x = ((forcedValues n q C (List.ofFn x)).getD C.output false ||
        ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false))) :
    ∃ D : Circuit, IsAO2 n D ∧ tCount n D colour = 0 ∧ D.size ≤ C.size ∧ circuitFun n D = f := by
  have hq : q ≤ C.gates.length := by omega
  have hAP := pruned_ao n q C hAO
  have hap := prior_wire_valid n q C hAO hq a ha
  have hbp := prior_wire_valid n q C hAO hq b hb
  let D := restoreStar n (pruned n q C) a b
  refine ⟨D, restoreStar_ao n _ a b hAP hap hbp, ?_, ?_, ?_⟩
  · change tCount n (restoreStar n (pruned n q C) a b) colour = 0
    rw [restoreStar_tCount n _ a b colour hAP hap hbp hreach]
    exact pruned_count_zero n q C hAO colour hz
  · exact (restoreStar_size n (pruned n q C) a b).trans
      (pruned_size_two n q r C hAO hqr hr hread)
  · funext x
    change (restoreStar n (pruned n q C) a b).eval (List.ofFn x) = f x
    rw [restoreStar_eval n _ a b (List.ofFn x) (by simp),
      pruned_eval n q C hAO (List.ofFn x) (by simp),
      pruned_wire_before n q C hAO hq (List.ofFn x) (by simp) a ha,
      pruned_wire_before n q C hAO hq (List.ofFn x) (by simp) b hb]
    exact (hsemantic x).symm

end PEqualNP.Outside.L_meta_4675.PruneRestore
