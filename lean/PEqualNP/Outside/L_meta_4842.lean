import Mathlib
import PEqualNP.Defs

-- Only gate x4 reads wire 6. Gates before it never read wire 6, so on two inputs that differ
-- only at wire 6 they agree everywhere except wire 6. If the OR gate x4 were true on the first
-- input it would be true on the second (wire 6 is true there), and every later gate ignores
-- wire 6, so the outputs would agree: a contradiction.

namespace PEqualNP.Outside.L_meta_4842_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def reads6 (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
    fun i => decide (i = 6)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Agree (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ 6 < w.length ∧ w'.getD 6 false = true ∧
    ∀ i, i ≠ 6 → w.getD i false = w'.getD i false

theorem agree_append (w w' : List Bool) (a b : Bool) (h : Agree w w') (hab : a = b) :
    Agree (w ++ [a]) (w' ++ [b]) := by
  obtain ⟨hl, h6, hw6, hs⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact hw6
  · intro i hi
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact hs i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        hl, hab]

theorem gate_eq (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hr : reads6 g = false) (w w' : List Bool) (h : Agree w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨_, _, _, hs⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · have hall : ∀ i ∈ g.inputs, i ≠ 6 := by
      intro i hi h6
      simp [reads6, hop, GateOp.eval] at hr
      exact hr i hi h6
    rw [List.map_congr_left (fun i hi => hs i (hall i hi))]
  · have hall : ∀ i ∈ g.inputs, i ≠ 6 := by
      intro i hi h6
      simp [reads6, hop, GateOp.eval] at hr
      exact hr i hi h6
    rw [List.map_congr_left (fun i hi => hs i (hall i hi))]
  · rw [hop]
    cases hin : g.inputs with
    | nil => rfl
    | cons j rest =>
      have hj : j ≠ 6 := by
        simp [reads6, hop, GateOp.eval, hin] at hr
        exact hr
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [hs j hj]

theorem fold_agree : ∀ (gs : List Gate) (w w' : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ reads6 g = false) →
    Agree w w' → Agree (gs.foldl stepW w) (gs.foldl stepW w') := by
  intro gs
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' hg h
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · obtain ⟨hop, hr⟩ := hg g (by simp)
      exact agree_append _ _ _ _ h (gate_eq g hop hr w w' h)

theorem key (x2 x3 : List Gate) (x4 : Gate) (x5 : ℕ) (x6 x7 : List Bool)
    (hF : FanInTwo ⟨x2 ++ x4 :: x3, x5⟩) (hr : ∀ g ∈ x2 ++ x3, reads6 g = false)
    (hor : x4.op = GateOp.or) (hlen : x6.length = x7.length) (h6 : 6 < x7.length)
    (h76 : x7.getD 6 false = true) (hsame : ∀ i, i ≠ 6 → x6.getD i false = x7.getD i false)
    (h5 : x5 ≠ 6) (he6 : Circuit.eval ⟨x2 ++ x4 :: x3, x5⟩ x6 = false)
    (he7 : Circuit.eval ⟨x2 ++ x4 :: x3, x5⟩ x7 = true) :
    x4.op.eval (List.map (fun i => (Circuit.wires ⟨x2, 0⟩ x6).getD i false) x4.inputs) = false := by
  have hops : ∀ g ∈ x2 ++ x4 :: x3,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := fun g hg => (hF g hg).1
  have hA0 : Agree x6 x7 := ⟨hlen, by omega, h76, hsame⟩
  have hA : Agree (x2.foldl stepW x6) (x2.foldl stepW x7) :=
    fold_agree x2 x6 x7 (fun g hg => ⟨hops g (by simp [hg]), hr g (by simp [hg])⟩) hA0
  show x4.op.eval (List.map (fun i => (x2.foldl stepW x6).getD i false) x4.inputs) = false
  by_contra hv0
  have hv : x4.op.eval (List.map (fun i => (x2.foldl stepW x6).getD i false) x4.inputs) = true := by
    simpa using hv0
  have hv' : x4.op.eval (List.map (fun i => (x2.foldl stepW x7).getD i false) x4.inputs) = true := by
    have hv1 := hv
    rw [hor] at hv1 ⊢
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv1 ⊢
    obtain ⟨i, hi, hti⟩ := hv1
    refine ⟨i, hi, ?_⟩
    by_cases hi6 : i = 6
    · subst hi6
      exact hA.2.2.1
    · rw [← hA.2.2.2 i hi6]
      exact hti
  have hfold : ∀ x : List Bool, Circuit.wires ⟨x2 ++ x4 :: x3, x5⟩ x =
      x3.foldl stepW (stepW (x2.foldl stepW x) x4) := by
    intro x
    show (x2 ++ x4 :: x3).foldl stepW x = _
    rw [List.foldl_append, List.foldl_cons]
  have hs6 : stepW (x2.foldl stepW x6) x4 = x2.foldl stepW x6 ++ [true] := by
    simp only [stepW, hv]
  have hs7 : stepW (x2.foldl stepW x7) x4 = x2.foldl stepW x7 ++ [true] := by
    simp only [stepW, hv']
  have hAfin := fold_agree x3 _ _
    (fun g hg => ⟨hops g (by simp [hg]), hr g (by simp [hg])⟩)
    (agree_append _ _ _ _ hA (rfl : true = true))
  have e6 : Circuit.eval ⟨x2 ++ x4 :: x3, x5⟩ x6 =
      (x3.foldl stepW (x2.foldl stepW x6 ++ [true])).getD x5 false := by
    unfold Circuit.eval
    rw [hfold, hs6]
  have e7 : Circuit.eval ⟨x2 ++ x4 :: x3, x5⟩ x7 =
      (x3.foldl stepW (x2.foldl stepW x7 ++ [true])).getD x5 false := by
    unfold Circuit.eval
    rw [hfold, hs7]
  rw [e6] at he6
  rw [e7] at he7
  have := hAfin.2.2.2 x5 h5
  rw [he6, he7] at this
  exact Bool.false_ne_true this

end PEqualNP.Outside.L_meta_4842_aux

theorem PEqualNP.Outside.L_meta_4842 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 x7 : List Bool),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 → (∀ x10 ∈ x2 ++ x3, x1 x10 = Bool.false) → x1 x4 = Bool.true → x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6.length = x7.length → (6 : ℕ) < x7.length → x7.getD (6 : ℕ) Bool.false = Bool.true → (∀ (x16 : ℕ), x16 ≠ (6 : ℕ) → x6.getD x16 Bool.false = x7.getD x16 Bool.false) → x5 ≠ (6 : ℕ) → x8.eval x6 = Bool.false → x8.eval x7 = Bool.true → x4.op.eval (List.map (fun (x20 : ℕ) => ({ gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x6).getD x20 Bool.false) x4.inputs) = Bool.false := by
  dsimp only
  intro x2 x3 x4 x5 x6 x7 hF hr _ hor hlen h6 h76 hsame h5 he6 he7
  exact PEqualNP.Outside.L_meta_4842_aux.key x2 x3 x4 x5 x6 x7 hF hr hor hlen h6 h76 hsame h5
    he6 he7
