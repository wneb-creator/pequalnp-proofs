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

end PEqualNP.Outside.L_meta_4675.Pruning

namespace PEqualNP.Outside.L_meta_4675.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.CleanedNonEdge

def SemLE (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

lemma semLE_append (xs ys : List Bool) (a b : Bool) (h : SemLE xs ys)
    (hab : a = true → b = true) : SemLE (xs ++ [a]) (ys ++ [b]) := by
  have hlen := h.1
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hil : i < xs.length
  · rw [getD_append_lt xs [a] i false hil] at hi
    rw [getD_append_lt ys [b] i false (by omega)]
    exact h.2 i hi
  · by_cases hie : i = xs.length
    · subst i
      rw [getD_append_last] at hi
      rw [h.1, getD_append_last]
      exact hab hi
    · rw [getD_ge (xs ++ [a]) i false (by simp; omega)] at hi
      cases hi

lemma sem_gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (h : ∀ i, xs.getD i false = true → ys.getD i false = true) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true]
    intro hxs i hi
    exact h i (hxs i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i hx⟩

lemma sem_forceStep_mono (n q : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (h : SemLE xs ys) :
    SemLE (forceStep n q xs g) (forceStep n q ys g) := by
  unfold forceStep
  apply semLE_append xs ys _ _ h
  rw [h.1]
  split_ifs
  · simp
  · exact sem_gate_mono g hg xs ys h.2

lemma sem_forceStep_below (n q : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (h : SemLE xs ys) :
    SemLE (forceStep n q xs g) (step ys g) := by
  unfold forceStep step
  apply semLE_append xs ys _ _ h
  split_ifs
  · simp
  · exact sem_gate_mono g hg xs ys h.2

lemma sem_force_fold_mono (n q : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (h : SemLE xs ys) :
    SemLE (gs.foldl (forceStep n q) xs) (gs.foldl (forceStep n q) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun a ha => hg a (by simp [ha])) _ _
      (sem_forceStep_mono n q g (hg g (by simp)) xs ys h)

lemma sem_force_fold_below (n q : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (h : SemLE xs ys) :
    SemLE (gs.foldl (forceStep n q) xs) (vals gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun a ha => hg a (by simp [ha])) _ _
      (sem_forceStep_below n q g (hg g (by simp)) xs ys h)

lemma forcedValues_mono (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs ys : List Bool) (h : SemLE xs ys) :
    SemLE (forcedValues n q C xs) (forcedValues n q C ys) :=
  sem_force_fold_mono n q C.gates hAO.1 xs ys h

lemma forcedValues_below (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (w : ℕ) :
    (forcedValues n q C xs).getD w false = true → (C.wires xs).getD w false = true := by
  exact (sem_force_fold_below n q C.gates hAO.1 xs xs ⟨rfl, fun _ h => h⟩).2 w

lemma semLE_ofFn (n : ℕ) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : SemLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · have hxi : x ⟨i, hin⟩ = true := by
      simpa [List.getD_eq_getElem?_getD, hin] using hi
    simpa [List.getD_eq_getElem?_getD, hin] using h ⟨i, hin⟩ hxi
  · rw [getD_ge _ _ _ (by simp; omega)] at hi
    cases hi

lemma forcedValues_mono_input (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) (w : ℕ) :
    (forcedValues n q C (List.ofFn x)).getD w false = true →
      (forcedValues n q C (List.ofFn y)).getD w false = true :=
  (forcedValues_mono n q C hAO _ _ (semLE_ofFn n x y h)).2 w

lemma sem_force_fold_agrees (n q : ℕ) (gs : List Gate) (xs : List Bool)
    (hfalse : (vals gs xs).getD (n + q) false = false) :
    gs.foldl (forceStep n q) xs = vals gs xs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [vals_snoc] at hfalse ⊢
    have hprefix : (vals gs xs).getD (n + q) false = false := by
      by_cases hi : n + q < (vals gs xs).length
      · exact (getD_append_lt _ _ _ _ hi).symm.trans hfalse
      · exact getD_ge _ _ _ (by omega)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih hprefix]
    unfold forceStep step at *
    split_ifs with he
    · congr 1
      have h := hfalse
      rw [← he, getD_append_last] at h
      exact congrArg (fun b : Bool => [b]) h.symm
    · rfl

lemma forcedValues_agrees (n q : ℕ) (C : Circuit) (xs : List Bool)
    (hfalse : (C.wires xs).getD (n + q) false = false) :
    forcedValues n q C xs = C.wires xs :=
  sem_force_fold_agrees n q C.gates xs hfalse

lemma pruned_eval_below (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n) :
    (pruned n q C).eval xs = true → C.eval xs = true := by
  rw [pruned_eval n q C hAO xs hx]
  exact forcedValues_below n q C hAO xs C.output

lemma pruned_eval_agrees (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n)
    (hfalse : (C.wires xs).getD (n + q) false = false) :
    (pruned n q C).eval xs = C.eval xs := by
  rw [pruned_eval n q C hAO xs hx, forcedValues_agrees n q C xs hfalse]
  rfl

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

lemma sem_force_length (n q : ℕ) (gs : List Gate) (xs : List Bool) :
    (gs.foldl (forceStep n q) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [forceStep]
    omega

lemma sem_force_prefix (n q : ℕ) (gs : List Gate) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length) :
    (gs.foldl (forceStep n q) xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (forceStep n q xs g) (by simp [forceStep]; omega)]
    exact getD_append_lt _ _ _ _ hw

lemma forced_input (n q : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n)
    (w : ℕ) (hw : w < n) :
    (forcedValues n q C xs).getD w false = xs.getD w false :=
  sem_force_prefix n q C.gates xs w (by omega)

lemma sem_gateAt_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma forced_gate (n q : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n)
    (k : ℕ) (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    (forcedValues n q C xs).getD (n + k) false =
      if k = q then false else
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u =>
        (forcedValues n q C xs).getD u false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl (forceStep n q) xs with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, sem_force_length, hx, List.length_take]
    omega
  have hpref : ∀ u < n + k,
      (forcedValues n q C xs).getD u false = acc.getD u false := by
    intro u hu
    unfold forcedValues
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact sem_force_prefix n q (C.gates.drop k) acc u (by omega)
  have hlast : (forcedValues n q C xs).getD (n + k) false =
      (forceStep n q acc C.gates[k]).getD (n + k) false := by
    unfold forcedValues
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    apply sem_force_prefix
    simp [forceStep, hacc_len]
  rw [hlast]
  unfold forceStep
  rw [← hacc_len, getD_append_last]
  rw [hacc_len]
  simp only [Nat.add_left_cancel_iff]
  rw [sem_gateAt_getElem C k hk]
  congr 2
  apply List.map_congr_left
  intro u hu
  rw [← sem_gateAt_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma forced_orReaches_true (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqand : (gateAt C q).op = GateOp.and) (xs : List Bool) (hx : xs.length = n)
    (k : ℕ) (hv : (forcedValues n q C xs).getD (n + k) false = true) :
    ∀ w, OrReaches n C w k → (forcedValues n q C xs).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨a, rfl⟩ : ∃ a, w = n + a := ⟨w - n, by omega⟩
    obtain ⟨ha, he | ⟨hop, u, hu, hul, hur⟩⟩ := (orReaches_iff n C a k).mp hr
    · rw [← he]
      exact hv
    · have haq : a ≠ q := by
        intro heq
        subst a
        rw [hqand] at hop
        cases hop
      rw [forced_gate n q C xs hx a ha hAO.2.1, if_neg haq, hop]
      have hval := ih u hul hur
      simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
        (forcedValues n q C xs).getD v false = true from ⟨u, hu, hval⟩)

lemma sem_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p)
    (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma forced_orIn_true (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqand : (gateAt C q).op = GateOp.and) (x : Fin n → Bool)
    (w : ℕ) (i : Fin n) (hi : i ∈ orIn n C w) (hxi : x i = true) :
    (forcedValues n q C (List.ofFn x)).getD w false = true := by
  classical
  have hxi' : (forcedValues n q C (List.ofFn x)).getD i false = true := by
    rw [forced_input n q C _ (by simp) i i.isLt]
    simpa [List.getD_eq_getElem?_getD, i.isLt] using hxi
  have hi' : (i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs := by
    unfold orIn at hi
    exact ((sem_mem_filter _ _ _ _).1 hi).2
  rcases hi' with he | ⟨a, ha, hr, hop, hin⟩
  · rw [← he]
    exact hxi'
  · apply forced_orReaches_true n q C hAO hqand _ (by simp) a _ w hr
    have haq : a ≠ q := by
      intro heq
      subst a
      rw [hqand] at hop
      cases hop
    rw [forced_gate n q C _ (by simp) a ha hAO.2.1, if_neg haq, hop]
    simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
      (forcedValues n q C (List.ofFn x)).getD v false = true from ⟨i, hin, hxi'⟩)

lemma forced_reader_true (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqand : (gateAt C q).op = GateOp.and) (j : ℕ) (hj : j < C.gates.length)
    (hjq : j ≠ q) (hjand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) (i v : Fin n)
    (hi : i ∈ orIn n C (opnd C j 0)) (hv : v ∈ orIn n C (opnd C j 1))
    (hxi : x i = true) (hxv : x v = true) :
    (forcedValues n q C (List.ofFn x)).getD (n + j) false = true := by
  have hi' := forced_orIn_true n q C hAO hqand x (opnd C j 0) i hi hxi
  have hv' := forced_orIn_true n q C hAO hqand x (opnd C j 1) v hv hxv
  have hm : gateAt C j ∈ C.gates := by
    rw [sem_gateAt_getElem C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : (forcedValues n q C (List.ofFn x)).getD a false = true := by
    simpa [opnd, hab] using hi'
  have hb : (forcedValues n q C (List.ofFn x)).getD b false = true := by
    simpa [opnd, hab] using hv'
  rw [forced_gate n q C _ (by simp) j hj hAO.2.1]
  simpa [hjq, hjand, hab, GateOp.eval, List.getD_eq_getElem?_getD] using And.intro ha hb

lemma forced_output_of_reader_pair (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqand : (gateAt C q).op = GateOp.and) (j : ℕ) (hj : j < C.gates.length)
    (hjq : j ≠ q) (hjand : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C C.output j) (x : Fin n → Bool) (i v : Fin n)
    (hi : i ∈ orIn n C (opnd C j 0)) (hv : v ∈ orIn n C (opnd C j 1))
    (hxi : x i = true) (hxv : x v = true) :
    (forcedValues n q C (List.ofFn x)).getD C.output false = true :=
  forced_orReaches_true n q C hAO hqand _ (by simp) j
    (forced_reader_true n q C hAO hqand j hj hjq hjand x i v hi hv hxi hxv) C.output hr

lemma pruned_output_of_reader_pair (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqand : (gateAt C q).op = GateOp.and) (j : ℕ) (hj : j < C.gates.length)
    (hjq : j ≠ q) (hjand : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C C.output j) (x : Fin n → Bool) (i v : Fin n)
    (hi : i ∈ orIn n C (opnd C j 0)) (hv : v ∈ orIn n C (opnd C j 1))
    (hxi : x i = true) (hxv : x v = true) :
    circuitFun n (pruned n q C) x = true := by
  change (pruned n q C).eval (List.ofFn x) = true
  rw [pruned_eval n q C hAO _ (by simp)]
  exact forced_output_of_reader_pair n q C hAO hqand j hj hjq hjand hr x i v hi hv hxi hxv

lemma productive_lift_semantics (n q : ℕ) (C : Circuit) (xs : List Bool)
    (hprod : (C.wires xs).getD (n + q) false = true → C.eval xs = true) :
    C.eval xs = ((forcedValues n q C xs).getD C.output false ||
      (C.wires xs).getD (n + q) false) := by
  cases hq : (C.wires xs).getD (n + q) false with
  | false =>
    rw [forcedValues_agrees n q C xs hq]
    simp only [Bool.or_false]
    rfl
  | true =>
    rw [hprod hq]
    simp

lemma productive_pruned_semantics (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n)
    (hprod : (C.wires xs).getD (n + q) false = true → C.eval xs = true) :
    C.eval xs = ((pruned n q C).eval xs || (C.wires xs).getD (n + q) false) := by
  rw [pruned_eval n q C hAO xs hx]
  exact productive_lift_semantics n q C xs hprod

lemma productive_lift_input (n q : ℕ) (C : Circuit)
    (hprod : PEqualNP.CircuitMoves.WireBelowOutput n C (n + q)) (x : Fin n → Bool) :
    circuitFun n C x = ((forcedValues n q C (List.ofFn x)).getD C.output false ||
      PEqualNP.BlindGate.wireValue C n x (n + q)) := by
  exact productive_lift_semantics n q C (List.ofFn x) (hprod x)

end PEqualNP.Outside.L_meta_4675.Pruning
