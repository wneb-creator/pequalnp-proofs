import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18344_aux

open PEqualNP.CircuitLowerBounds

private def Joined (a b c : List Bool) : Prop :=
  b.length = a.length ∧ c.length = a.length ∧
    ∀ i, c.getD i false = (a.getD i false || b.getD i false)

private theorem joinedInputs {n : ℕ} (a b : Fin n → Bool) :
    Joined (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem anyJoined {a b c : List Bool} (h : Joined a b c) (inputs : List ℕ) :
    (inputs.map (fun i => c.getD i false)).any id =
    ((inputs.map (fun i => a.getD i false)).any id ||
     (inputs.map (fun i => b.getD i false)).any id) := by
  induction inputs with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [h.2.2 i, ih]
    ac_rfl

private theorem joinedAppend {a b c : List Bool} (h : Joined a b c) (x y : Bool) :
    Joined (a ++ [x]) (b ++ [y]) (c ++ [x || y]) := by
  rcases h with ⟨hb, hc, hw⟩
  refine ⟨by simp [hb], by simp [hc], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ (by simpa [hc] using hi),
        List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by simpa [hb] using hi)]
    exact hw i
  · have hn := Nat.le_of_not_lt hi
    rw [List.getD_append_right _ _ _ _ (by simpa [hc] using hn),
        List.getD_append_right _ _ _ _ hn,
        List.getD_append_right _ _ _ _ (by simpa [hb] using hn), hc, hb]
    cases i - a.length <;> simp

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldJoined (gates : List Gate) (hor : ∀ g ∈ gates, g.op = .or)
    {a b c : List Bool} (h : Joined a b c) :
    Joined (gates.foldl step a) (gates.foldl step b) (gates.foldl step c) := by
  induction gates generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hor q (List.mem_cons_of_mem g hq))
    simp only [step, hor g (List.mem_cons_self), GateOp.eval, anyJoined h]
    exact joinedAppend h _ _

private theorem outputJoined {n : ℕ} (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = .or)
    (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) =
      (C.eval (List.ofFn a) || C.eval (List.ofFn b)) :=
  (foldJoined C.gates hor (joinedInputs a b)).2.2 C.output

end PEqualNP.Outside.L_meta_18344_aux

open PEqualNP.Outside.L_meta_18344_aux in
theorem PEqualNP.Outside.L_meta_18344 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (10 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (10 : ℕ) (x6 % (10 : ℕ))) := by
  intro C hC _ hAnd
  have hOr : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    have h := (hC g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      exact False.elim (hAnd ⟨i, (congrArg (fun q => q.op) hi).trans h⟩)
    · exact h
  by_contra! correct
  let a : Fin 10 → Bool := fun i => decide (i = 0)
  let b : Fin 10 → Bool := fun i => decide (i = 1)
  have ha : C.eval (List.ofFn a) = false := (correct a).trans (by decide +kernel)
  have hb : C.eval (List.ofFn b) = false := (correct b).trans (by decide +kernel)
  have hab : C.eval (List.ofFn fun i => a i || b i) = true :=
    (correct (fun i => a i || b i)).trans (by decide +kernel)
  have h := outputJoined C hOr a b
  rw [ha, hb, hab] at h
  contradiction
