import Mathlib.Tactic
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_7493

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

open PEqualNP.Outside.L_meta_7493
open CircuitProof CircuitProof.Readers

lemma least_no_constant {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (p : ℕ) (hp : p < gs.length) (c : Bool) :
    ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = c := by
  intro constant
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], by simp [hp]⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  obtain ⟨gs', o', hcl, shorter, cost, evaluates⟩ :=
    drop_core n pre g post L.hcl o (Sum.inl c)
      (fun x => ⟨trivial, (constant x).symm⟩) (L.ncv hnc)
  have budget : nonNotCount gs' ≤ nonNotCount (pre ++ g :: post) := by
    simp only [nonNotCount, List.countP_append, List.countP_cons] at cost ⊢
    omega
  have minimal := L.hmin gs' o' hcl (fun x => (evaluates x).trans (L.hev x)) budget
  omega


lemma clean_not_shape {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (onlyNot : ∀ g ∈ gs, g.op = .not) :
    ∀ p g, gs[p]? = some g → g.op = .not ∧ ∃ j, j < n + p ∧ g.inputs = [j] := by
  intro p g hp
  rcases clean p g hp with shape | ⟨op, shape⟩
  · exact shape
  · have hn := onlyNot g (List.mem_iff_getElem?.mpr ⟨p, hp⟩)
    rcases op with op | op <;> rw [hn] at op <;> cases op

lemma least_has_nonNot {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (noUnary : ∀ v : Fin n, ∀ sign : Bool,
      ¬ ∀ x : Fin n → Bool, f x = if sign then !(x v) else x v) :
    ∃ g ∈ gs, g.op ≠ .not := by
  by_contra! onlyNot
  have state := not_prefix_literals n gs (clean_not_shape L.hcl onlyNot)
  have length : (gs.foldl originStep (List.ofFn (fun i : Fin n => some i.val))).length = n + gs.length := by
    have h := state.1 (fun _ => false)
    change (wiresFrom gs (List.ofFn (fun _ : Fin n => false))).length = _ at h
    simpa only [length_wiresFrom, List.length_ofFn] using h.symm
  have valid : o < n + gs.length := by
    by_contra outside
    have zero (x : Fin n → Bool) : vl gs x o = false := vl_beyond gs x o (by omega)
    obtain ⟨x, y, different⟩ := hnc
    apply different
    rw [← L.hev x, ← L.hev y, zero x, zero y]
  obtain ⟨v, sign, _, evaluates⟩ := state.2 o (by rw [length]; exact valid)
  apply noUnary v sign
  intro x
  have h := evaluates x
  change vl gs x o = _ at h
  exact (L.hev x).symm.trans h

lemma first_nonNot_split (gs : List Gate) (has : ∃ g ∈ gs, g.op ≠ .not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ (∀ a ∈ pre, a.op = .not) ∧ g.op ≠ .not := by
  induction gs with
  | nil => simp at has
  | cons g gs ih =>
    by_cases op : g.op = .not
    · have tail : ∃ a ∈ gs, a.op ≠ .not := by
        obtain ⟨a, ha, notOp⟩ := has
        rcases List.mem_cons.mp ha with rfl | ha
        · exact (notOp op).elim
        · exact ⟨a, ha, notOp⟩
      obtain ⟨pre, a, post, split, onlyNot, notOp⟩ := ih tail
      refine ⟨g :: pre, a, post, by rw [split]; rfl, ?_, notOp⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact op
      · exact onlyNot b hb
    · exact ⟨[], g, gs, rfl, by simp, op⟩

lemma prefix_value {n : ℕ} (pre post : List Gate) (x : Fin n → Bool)
    (j : ℕ) (before : j < n + pre.length) :
    vl (pre ++ post) x j = (pre.foldl gateStep (List.ofFn x)).getD j false := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ j (by simpa only [length_wiresFrom, List.length_ofFn] using before)]
  rfl

def readsOrigin (origins : List (Option ℕ)) (v : ℕ) (g : Gate) : Bool :=
  g.inputs.any (fun i => decide (origins.getD i none = some v))

lemma least_first_binary {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (noUnary : ∀ v : Fin n, ∀ sign : Bool,
      ¬ ∀ x : Fin n → Bool, f x = if sign then !(x v) else x v) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate) (u v : Fin n)
      (code : Bool → Bool → Bool),
      gs = pre ++ g :: post ∧ (∀ a ∈ pre, a.op = .not) ∧
      (g.op = .and ∨ g.op = .or) ∧ u ≠ v ∧
      readsOrigin (pre.foldl originStep (List.ofFn (fun i : Fin n => some i.val))) u.val g = true ∧
      readsOrigin (pre.foldl originStep (List.ofFn (fun i : Fin n => some i.val))) v.val g = true ∧
      ∀ x : Fin n → Bool,
        g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) =
          code (x u) (x v) := by
  obtain ⟨pre, g, post, split, onlyNot, notOp⟩ := first_nonNot_split gs (least_has_nonNot L hnc noUnary)
  have atGate : gs[pre.length]? = some g := by simp [split]
  have gateClean := L.hcl pre.length g atGate
  have cleanPre : CleanL n pre := by
    intro p a ha
    have before : p < pre.length := (List.getElem?_eq_some_iff.mp ha).1
    apply L.hcl p a
    rw [split, List.getElem?_append_left before]
    exact ha
  rcases gateClean with ⟨op, _⟩ | ⟨op, a, b, ha, hb, inputs⟩
  · exact (notOp op).elim
  have state := not_prefix_literals n pre (clean_not_shape cleanPre onlyNot)
  have length : (pre.foldl originStep (List.ofFn (fun i : Fin n => some i.val))).length = n + pre.length := by
    have h := state.1 (fun _ => false)
    change (wiresFrom pre (List.ofFn (fun _ : Fin n => false))).length = _ at h
    simpa only [length_wiresFrom, List.length_ofFn] using h.symm
  have gateValue (x : Fin n → Bool) : vl gs x (n + pre.length) =
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) := by
    rw [vl_gate gs L.hcl x pre.length g atGate]
    congr 1
    apply List.map_congr_left
    intro j hj
    have before : j < n + pre.length := (L.hcl pre.length g atGate).lt j hj
    rw [split]
    exact prefix_value pre (g :: post) x j before
  have atGateLt : pre.length < gs.length := (List.getElem?_eq_some_iff.mp atGate).1
  have noAlias : ¬ ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) =
        (pre.foldl gateStep (List.ofFn x)).getD a false := by
    intro aliases
    apply L.no_alias hnc pre.length atGateLt a ha
    intro x
    have old : vl gs x a = (pre.foldl gateStep (List.ofFn x)).getD a false := by
      rw [split]
      exact prefix_value pre (g :: post) x a ha
    exact (gateValue x).trans ((aliases x).trans old.symm)
  have noConstant : ∀ c : Bool, ¬ ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) = c := by
    intro c constant
    exact least_no_constant L hnc pre.length atGateLt c (fun x => (gateValue x).trans (constant x))
  obtain ⟨u, v, different, originU, originV, sa, sb, valueA, valueB⟩ :=
    binary_distinct_origins _ _ state g a b (by rw [length]; exact ha)
      (by rw [length]; exact hb) op inputs noAlias noConstant
  refine ⟨pre, g, post, u, v,
    (fun x y => g.op.eval [if sa then !x else x, if sb then !y else y]),
    split, onlyNot, op, different, ?_, ?_, ?_⟩
  · exact List.any_eq_true.mpr ⟨a, by simp [inputs], decide_eq_true originU⟩
  · exact List.any_eq_true.mpr ⟨b, by simp [inputs], decide_eq_true originV⟩
  · intro x
    simp only [inputs, List.map_cons, List.map_nil]
    rw [valueA x, valueB x]

end PEqualNP.Outside.L_meta_2592_aux.FirstBinary
