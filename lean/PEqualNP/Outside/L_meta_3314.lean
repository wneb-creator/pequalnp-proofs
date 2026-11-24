import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3314

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_big (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

lemma ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

lemma mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  apply mono C.gates (List.ofFn x) (List.ofFn y) (by simp)
  · intro g hg
    simpa using (hmono g hg).1
  · intro i hi
    by_cases h : i < n
    · rw [getD_ofFn x i h] at hi
      rw [getD_ofFn y i h]
      exact hxy ⟨i, h⟩ hi
    · rw [getD_big _ _ (by simpa using Nat.le_of_not_lt h)] at hi
      contradiction

end PEqualNP.Outside.L_meta_3314

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_3314 : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  intro h
  obtain ⟨C, op, a, b, p, hC, hsize, ha, hab, hb, hop, hrest⟩ := h (fun _ => False)
  rcases hop with ⟨rfl, hp⟩
  dsimp only at hrest
  obtain ⟨hne, heq, heq', hmin, hmax⟩ := hrest
  have ht : Maximal (fun _ : Fin 14 → Bool => ¬ False) (fun _ => true) := by
    refine ⟨by simp, ?_⟩
    intro x hx hle i
    change x i ≤ true
    cases x i <;> decide
  have hz := hmax (fun _ => true) ht
  rcases hz with ⟨hbad, _⟩ | hz
  · cases hbad
  · simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false] at hz
    have hz' := Bool.or_eq_false_iff.mp hz
    have hma := PEqualNP.Outside.L_meta_3314.wires_mono C hC
      (fun i : Fin 14 => p.1.testBit i.val) (fun _ => true) (fun _ _ => rfl) a
    have hmb := PEqualNP.Outside.L_meta_3314.wires_mono C hC
      (fun i : Fin 14 => p.1.testBit i.val) (fun _ => true) (fun _ _ => rfl) b
    cases hwa : (C.wires (List.ofFn (fun i : Fin 14 => p.1.testBit i.val))).getD a false <;>
      cases hwb : (C.wires (List.ofFn (fun i : Fin 14 => p.1.testBit i.val))).getD b false <;>
      simp_all
