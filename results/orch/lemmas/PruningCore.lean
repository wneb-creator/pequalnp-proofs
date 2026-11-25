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
