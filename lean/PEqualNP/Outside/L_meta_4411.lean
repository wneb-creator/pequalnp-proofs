import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4411

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi


def fn (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def X0 (u t : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t)

def X1 (u t v : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t) || decide (i = v)

theorem key : ∀ v t : Fin 9, v ≠ t → ∃ u : Fin 9, u ≠ v ∧ fn (X0 u t) = false ∧
    fn (X1 u t v) = true := by
  decide +kernel

theorem single : ∀ v : Fin 9, fn (X0 v v) = false := by
  decide +kernel

theorem getU (x : Fin 9 → Bool) (p q : Bool) (i : ℕ) :
    (List.ofFn x ++ [p, q]).getD i false =
      if h : i < 9 then x ⟨i, h⟩ else if i = 9 then p else if i = 10 then q else false := by
  by_cases h : i < 9
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
      List.getElem?_eq_getElem (by simpa using h), List.getElem_ofFn]
    rfl
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    obtain ⟨k, rfl⟩ : ∃ k, i = 9 + k := ⟨i - 9, by omega⟩
    rcases k with _ | _ | k
    · simp
    · simp
    · simp
      omega

end PEqualNP.Outside.L_meta_4411

open PEqualNP.Outside.L_meta_4411 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4411 : ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x10 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)), x10 x1 || x10 x2]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)))) → ∀ (x11 : Fin (9 : ℕ)), ∃ x12 ∈ x3.gates, ↑x11 ∈ if x12.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x12.inputs else x12.inputs := by
  intro a b C ha0 ha4 hb0 hb4 hab hC hf v
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => by simpa using (hC g hg).1
  have hf' : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = fn x := hf
  by_contra hcon
  push Not at hcon
  have hno : ∀ g ∈ C.gates, v.val ∉ rds g := by
    intro g hg
    have h := hcon g hg
    rcases hops g hg with ho | ho | ho
    · rw [ho] at h; simpa [rds, ho, GateOp.eval] using h
    · rw [ho] at h; simpa [rds, ho, GateOp.eval] using h
    · rw [ho] at h; simpa [rds, ho, GateOp.eval] using h
  have hout : C.output ≠ v := by
    intro h
    have h1 := hf' (X0 v v)
    rw [single v] at h1
    have h2 : C.eval (List.ofFn (X0 v v) ++ [X0 v v 0 || X0 v v 4, X0 v v a || X0 v v b]) =
        true := by
      change (run C.gates _).getD C.output false = true
      rw [h, run_input _ _ _ (by simp; omega), getU, dif_pos v.isLt]
      simp [X0]
    rw [h1] at h2
    exact Bool.false_ne_true h2
  obtain ⟨t, hvt, c0, c4, ca, cb⟩ : ∃ t : Fin 9, v ≠ t ∧ (v = 0 → t = 4) ∧ (v = 4 → t = 0) ∧
      (v = a → t = b) ∧ (v = b → t = a) := by
    by_cases h0 : v = 0
    · exact ⟨4, by rw [h0]; decide, fun _ => rfl, fun h => by rw [h0] at h; exact absurd h (by decide),
        fun h => absurd (h.symm.trans h0) ha0, fun h => absurd (h.symm.trans h0) hb0⟩
    · by_cases h4 : v = 4
      · exact ⟨0, by rw [h4]; decide, fun h => absurd h h0, fun _ => rfl,
          fun h => absurd (h.symm.trans h4) ha4, fun h => absurd (h.symm.trans h4) hb4⟩
      · by_cases hA : v = a
        · exact ⟨b, by rw [hA]; exact hab, fun h => absurd h h0, fun h => absurd h h4, fun _ => rfl,
            fun h => absurd (hA.symm.trans h) hab⟩
        · by_cases hB : v = b
          · exact ⟨a, by rw [hB]; exact hab.symm, fun h => absurd h h0, fun h => absurd h h4,
              fun h => absurd h hA, fun _ => rfl⟩
          · exact ⟨0, h0, fun h => absurd h h0, fun h => absurd h h4, fun h => absurd h hA,
              fun h => absurd h hB⟩
  obtain ⟨u, huv, k0, k1⟩ := key v t hvt
  have hor : ∀ p q : Fin 9, (v = p → t = q) → (v = q → t = p) →
      (X0 u t p || X0 u t q) = (X1 u t v p || X1 u t v q) := by
    intro p q h1 h2
    by_cases hp : v = p
    · have := h1 hp
      subst this
      simp [X0, X1]
    · by_cases hq : v = q
      · have := h2 hq
        subst this
        simp [X0, X1]
      · simp [X0, X1, Ne.symm hp, Ne.symm hq]
  have e := indep v.val C.gates hops hno
    (List.ofFn (X0 u t) ++ [X0 u t 0 || X0 u t 4, X0 u t a || X0 u t b])
    (List.ofFn (X1 u t v) ++ [X1 u t v 0 || X1 u t v 4, X1 u t v a || X1 u t v b]) (by simp)
    (fun i hi => by
      rw [getU, getU, hor 0 4 c0 c4, hor a b ca cb]
      by_cases h : i < 9
      · have hne : (⟨i, h⟩ : Fin 9) ≠ v := fun e => hi (by rw [← e])
        rw [dif_pos h, dif_pos h]
        simp [X0, X1, hne]
      · rw [dif_neg h, dif_neg h]) C.output hout
  have e1 := hf' (X0 u t)
  have e2 := hf' (X1 u t v)
  rw [k0] at e1
  rw [k1] at e2
  have e' : C.eval (List.ofFn (X0 u t) ++ [X0 u t 0 || X0 u t 4, X0 u t a || X0 u t b]) =
    C.eval (List.ofFn (X1 u t v) ++ [X1 u t v 0 || X1 u t v 4, X1 u t v a || X1 u t v b]) := e
  rw [e1, e2] at e'
  exact Bool.false_ne_true e'
