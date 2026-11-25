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

namespace PEqualNP.Outside.L_meta_4675.ContextualOr

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4675.Pruning

def emitContexts (n : ℕ) (gs : List Gate) (needZero needCarry : Bool)
    (freeZero z₀ z₁ c₀ c₁ : Option ℕ) : List Gate × (Option ℕ × Option ℕ) :=
  if needCarry then
    let r := emitPair n gs false c₀ c₁
    (r.1, (if needZero then freeZero else none, r.2))
  else if needZero then
    let r := emitPair n gs false z₀ z₁
    (r.1, (r.2, none))
  else (gs, (none, none))

lemma emitContexts_size (n : ℕ) (gs : List Gate) (z c : Bool)
    (f z₀ z₁ c₀ c₁ : Option ℕ) :
    (emitContexts n gs z c f z₀ z₁ c₀ c₁).1.length ≤ gs.length + 1 := by
  cases z <;> cases c <;> simp only [emitContexts, Bool.false_eq_true,
    ↓reduceIte]
  · omega
  all_goals exact emitPair_length_le _ _ _ _ _

lemma emitContexts_ao (n : ℕ) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (z c : Bool) (f z₀ z₁ c₀ c₁ : Option ℕ)
    (hz₀ : Bounded n gs z₀) (hz₁ : Bounded n gs z₁)
    (hc₀ : Bounded n gs c₀) (hc₁ : Bounded n gs c₁) :
    IsAO2 n ⟨(emitContexts n gs z c f z₀ z₁ c₀ c₁).1, 0⟩ := by
  cases z <;> cases c <;> simp only [emitContexts, Bool.false_eq_true,
    ↓reduceIte]
  · exact hAO
  · exact emitPair_ao n gs hAO false c₀ c₁ hc₀ hc₁
  · exact emitPair_ao n gs hAO false z₀ z₁ hz₀ hz₁
  · exact emitPair_ao n gs hAO false c₀ c₁ hc₀ hc₁

lemma emitContexts_prefix (n : ℕ) (gs : List Gate) (z c : Bool)
    (f z₀ z₁ c₀ c₁ o : Option ℕ) (ho : Bounded n gs o)
    (xs : List Bool) (hx : xs.length = n) :
    optionalValue (vals (emitContexts n gs z c f z₀ z₁ c₀ c₁).1 xs) o =
      optionalValue (vals gs xs) o := by
  cases z <;> cases c <;> simp only [emitContexts, Bool.false_eq_true,
    ↓reduceIte]
  all_goals exact emitPair_optional_prefix n gs false _ _ o xs hx ho

lemma emitContexts_bounded (n : ℕ) (gs : List Gate) (z c : Bool)
    (f z₀ z₁ c₀ c₁ : Option ℕ) (hf : Bounded n gs f)
    (hz₀ : Bounded n gs z₀) (hz₁ : Bounded n gs z₁)
    (hc₀ : Bounded n gs c₀) (hc₁ : Bounded n gs c₁) :
    Bounded n (emitContexts n gs z c f z₀ z₁ c₀ c₁).1
      (emitContexts n gs z c f z₀ z₁ c₀ c₁).2.1 ∧
    Bounded n (emitContexts n gs z c f z₀ z₁ c₀ c₁).1
      (emitContexts n gs z c f z₀ z₁ c₀ c₁).2.2 := by
  have hf' : Bounded n (emitPair n gs false c₀ c₁).1 f := by
    intro i hi
    have h := hf i hi
    have hl := emitPair_length_ge n gs false c₀ c₁
    omega
  cases z <;> cases c <;> simp only [emitContexts, Bool.false_eq_true,
    ↓reduceIte]
  · simp [Bounded]
  · exact ⟨by simp [Bounded], emitPair_bounded n gs false c₀ c₁ hc₀ hc₁⟩
  · exact ⟨emitPair_bounded n gs false z₀ z₁ hz₀ hz₁, by simp [Bounded]⟩
  · exact ⟨hf', emitPair_bounded n gs false c₀ c₁ hc₀ hc₁⟩

lemma emitContexts_semantics (n : ℕ) (gs : List Gate) (z c : Bool)
    (f z₀ z₁ c₀ c₁ : Option ℕ) (hf : Bounded n gs f)
    (xs : List Bool) (hx : xs.length = n)
    (hfree : z = true → c = true → optionalValue (vals gs xs) f =
      (optionalValue (vals gs xs) z₀ || optionalValue (vals gs xs) z₁)) :
    optionalValue (vals (emitContexts n gs z c f z₀ z₁ c₀ c₁).1 xs)
      (emitContexts n gs z c f z₀ z₁ c₀ c₁).2.1 =
        (if z then optionalValue (vals gs xs) z₀ || optionalValue (vals gs xs) z₁ else false) ∧
    optionalValue (vals (emitContexts n gs z c f z₀ z₁ c₀ c₁).1 xs)
      (emitContexts n gs z c f z₀ z₁ c₀ c₁).2.2 =
        (if c then optionalValue (vals gs xs) c₀ || optionalValue (vals gs xs) c₁ else false) := by
  have hz := emitPair_semantics n gs false z₀ z₁ xs hx
  have hc := emitPair_semantics n gs false c₀ c₁ xs hx
  simp only [pairOp, Bool.false_eq_true, ↓reduceIte] at hz hc
  cases z <;> cases c <;> simp only [emitContexts, Bool.false_eq_true,
    ↓reduceIte, optionalValue, Option.elim_none]
  · exact ⟨True.intro, True.intro⟩
  · exact ⟨True.intro, hc⟩
  · exact ⟨hz, True.intro⟩
  · refine ⟨?_, hc⟩
    change optionalValue (vals (emitPair n gs false c₀ c₁).1 xs) f = _
    rw [emitPair_optional_prefix n gs false c₀ c₁ f xs hx hf]
    exact hfree rfl rfl

structure Node (n : ℕ) where
  lhs : ℕ
  rhs : ℕ
  needZero : Bool
  needCarry : Bool
  freeZero : Option (Fin n)

def State := List Gate × List (Option ℕ × Option ℕ)

def ValidState (n : ℕ) (s : State) : Prop :=
  IsAO2 n ⟨s.1, 0⟩ ∧ ∀ v ∈ s.2, Bounded n s.1 v.1 ∧ Bounded n s.1 v.2

def compileNode (n : ℕ) (s : State) (g : Node n) : State :=
  let a := s.2.getD g.lhs (none, none)
  let b := s.2.getD g.rhs (none, none)
  let r := emitContexts n s.1 g.needZero g.needCarry (g.freeZero.map Fin.val) a.1 b.1 a.2 b.2
  (r.1, s.2 ++ [r.2])

lemma freeZero_bounded (n : ℕ) (gs : List Gate) (o : Option (Fin n)) :
    Bounded n gs (o.map Fin.val) := by
  cases o with
  | none => simp [Bounded]
  | some i =>
    intro j hj
    have he : i.val = j := by simpa using hj
    have hi := i.isLt
    omega

lemma map_get_bounded (n : ℕ) (s : State) (hs : ValidState n s) (i : ℕ) :
    Bounded n s.1 (s.2.getD i (none, none)).1 ∧
      Bounded n s.1 (s.2.getD i (none, none)).2 := by
  by_cases hi : i < s.2.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hs.2 s.2[i] (List.getElem_mem hi)
  · rw [getD_ge _ _ _ (by omega)]
    simp [Bounded]

lemma compileNode_size (n : ℕ) (s : State) (g : Node n) :
    (compileNode n s g).1.length ≤ s.1.length + 1 :=
  emitContexts_size _ _ _ _ _ _ _ _ _

lemma compileNode_valid (n : ℕ) (s : State) (g : Node n) (hs : ValidState n s) :
    ValidState n (compileNode n s g) := by
  have ha := map_get_bounded n s hs g.lhs
  have hb := map_get_bounded n s hs g.rhs
  have hf := freeZero_bounded n s.1 g.freeZero
  have hnew := emitContexts_bounded n s.1 g.needZero g.needCarry _ _ _ _ _
    hf ha.1 hb.1 ha.2 hb.2
  have hlen : s.1.length ≤ (compileNode n s g).1.length := by
    cases hz : g.needZero <;> cases hc : g.needCarry <;>
      simp only [compileNode, emitContexts, hz, hc, Bool.false_eq_true, ↓reduceIte]
    · exact Nat.le_refl s.1.length
    all_goals exact emitPair_length_ge _ _ _ _ _
  refine ⟨emitContexts_ao n s.1 hs.1 _ _ _ _ _ _ _ ha.1 hb.1 ha.2 hb.2, ?_⟩
  intro v hv
  change v ∈ s.2 ++ [_] at hv
  rcases List.mem_append.mp hv with hold | hlast
  · have hh := hs.2 v hold
    constructor <;> intro i hi
    · have hi' := hh.1 i hi
      omega
    · have hi' := hh.2 i hi
      omega
  · have he := List.mem_singleton.mp hlast
    subst v
    exact hnew

lemma compile_size (n : ℕ) (gs : List (Node n)) (s : State) :
    (gs.foldl (compileNode n) s).1.length ≤ s.1.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    have h := ih (compileNode n s g)
    have hh := compileNode_size n s g
    simp only [List.foldl_cons, List.length_cons]
    omega

lemma compile_valid (n : ℕ) (gs : List (Node n)) (s : State) (hs : ValidState n s) :
    ValidState n (gs.foldl (compileNode n) s) := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih => exact ih (compileNode n s g) (compileNode_valid n s g hs)

end PEqualNP.Outside.L_meta_4675.ContextualOr
