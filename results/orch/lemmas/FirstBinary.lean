import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.FirstBinary

open PEqualNP.CircuitLowerBounds

def originStep (origins : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  origins ++ [match g.op, g.inputs with
    | .not, i :: _ => origins.getD i none
    | _, _ => none]

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def SignedState (n : ℕ) (origins : List (Option ℕ))
    (values : (Fin n → Bool) → List Bool) : Prop :=
  (∀ x, (values x).length = origins.length) ∧
    ∀ j, j < origins.length → ∃ v : Fin n, ∃ sign : Bool,
      origins.getD j none = some v.val ∧
      ∀ x, (values x).getD j false = if sign then !(x v) else x v

lemma signed_initial (n : ℕ) :
    SignedState n (List.ofFn (fun i : Fin n => some i.val)) (fun x => List.ofFn x) := by
  refine ⟨by intro x; simp, ?_⟩
  intro j hj
  have before : j < n := by simpa using hj
  refine ⟨⟨j, before⟩, false, ?_, ?_⟩
  · simp [before]
  · intro x
    simp [before]

lemma signed_not_step {n : ℕ} {origins : List (Option ℕ)}
    {values : (Fin n → Bool) → List Bool} (state : SignedState n origins values)
    (j : ℕ) (before : j < origins.length) :
    SignedState n (origins ++ [origins.getD j none])
      (fun x => values x ++ [!(values x).getD j false]) := by
  refine ⟨by intro x; simp [state.1 x], ?_⟩
  intro i hi
  by_cases old : i < origins.length
  · obtain ⟨v, sign, mark, evaluates⟩ := state.2 i old
    refine ⟨v, sign, ?_, ?_⟩
    · simpa only [List.getD_append _ _ _ _ old] using mark
    · intro x
      have inValues : i < (values x).length := by rw [state.1 x]; exact old
      simpa only [List.getD_append _ _ _ _ inValues] using evaluates x
  · have atLast : i = origins.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    obtain ⟨v, sign, mark, evaluates⟩ := state.2 j before
    refine ⟨v, !sign, ?_, ?_⟩
    · simpa using mark
    · intro x
      have lengths := state.1 x
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have sub : origins.length - (values x).length = 0 := by omega
      simp only [sub, List.getD_cons_zero, evaluates x]
      cases sign <;> simp

lemma signed_not_fold {n : ℕ} (gs : List Gate) (origins : List (Option ℕ))
    (values : (Fin n → Bool) → List Bool) (state : SignedState n origins values)
    (notOnly : ∀ p g, gs[p]? = some g →
      g.op = GateOp.not ∧ ∃ j, j < origins.length + p ∧ g.inputs = [j]) :
    SignedState n (gs.foldl originStep origins)
      (fun x => gs.foldl gateStep (values x)) := by
  induction gs generalizing origins values with
  | nil => exact state
  | cons g gs ih =>
    obtain ⟨op, j, before, inputs⟩ := notOnly 0 g (by rfl)
    have step : SignedState n (originStep origins g) (fun x => gateStep (values x) g) := by
      simpa [originStep, gateStep, op, inputs, GateOp.eval] using
        signed_not_step state j (by simpa using before)
    apply ih _ _ step
    intro p a ha
    obtain ⟨ao, i, ibefore, ai⟩ := notOnly (p + 1) a (by simpa using ha)
    exact ⟨ao, i, by simp only [originStep, List.length_append, List.length_singleton]; omega, ai⟩

lemma not_prefix_literals (n : ℕ) (gs : List Gate)
    (notOnly : ∀ p g, gs[p]? = some g →
      g.op = GateOp.not ∧ ∃ j, j < n + p ∧ g.inputs = [j]) :
    SignedState n (gs.foldl originStep (List.ofFn (fun i : Fin n => some i.val)))
      (fun x => gs.foldl gateStep (List.ofFn x)) := by
  apply signed_not_fold gs _ _ (signed_initial n)
  simpa using notOnly

lemma signed_pair_collapse (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b : Bool) :
    (∀ x : Bool, op.eval [if a then !x else x, if b then !x else x] =
      if a then !x else x) ∨
    ∃ c : Bool, ∀ x : Bool, op.eval [if a then !x else x, if b then !x else x] = c := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> decide

lemma binary_distinct_origins {n : ℕ} (origins : List (Option ℕ))
    (values : (Fin n → Bool) → List Bool) (state : SignedState n origins values)
    (g : Gate) (a b : ℕ) (ha : a < origins.length) (hb : b < origins.length)
    (hop : g.op = .and ∨ g.op = .or) (inputs : g.inputs = [a, b])
    (noAlias : ¬ ∀ x, g.op.eval (g.inputs.map fun i => (values x).getD i false) =
      (values x).getD a false)
    (noConstant : ∀ c : Bool,
      ¬ ∀ x, g.op.eval (g.inputs.map fun i => (values x).getD i false) = c) :
    ∃ u v : Fin n, u ≠ v ∧ origins.getD a none = some u.val ∧
      origins.getD b none = some v.val ∧
      ∃ sa sb : Bool, (∀ x, (values x).getD a false = if sa then !(x u) else x u) ∧
        (∀ x, (values x).getD b false = if sb then !(x v) else x v) := by
  obtain ⟨u, sa, ua, va⟩ := state.2 a ha
  obtain ⟨v, sb, ub, vb⟩ := state.2 b hb
  refine ⟨u, v, ?_, ua, ub, sa, sb, va, vb⟩
  intro same
  subst v
  rcases signed_pair_collapse g.op hop sa sb with aliases | ⟨c, constant⟩
  · apply noAlias
    intro x
    simp only [inputs, List.map_cons, List.map_nil]
    rw [va x, vb x]
    exact aliases (x u)
  · apply noConstant c
    intro x
    simp only [inputs, List.map_cons, List.map_nil]
    rw [va x, vb x]
    exact constant (x u)

end PEqualNP.Outside.L_meta_2592_aux.FirstBinary
