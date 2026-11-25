import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases lt_trichotomy w W.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _), if_pos rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (le_of_lt h), if_neg (Nat.ne_of_gt h)]
    have h1 : 1 ≤ w - W.length := by omega
    rw [List.getD_eq_default _ _ (by simpa using h1),
      List.getD_eq_default _ _ (le_of_lt h)]

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (h : ∀ i ∈ g.inputs, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with h1 | h1
  · rw [h1]
    simp only [GateOp.eval]
    intro hall
    rw [List.all_eq_true] at hall ⊢
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact h i hi (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [h1]
    simp only [GateOp.eval]
    intro hany
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨y, hy, hyt⟩ := hany
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact ⟨b i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hi hyt⟩

lemma fold_mono_except (G : List Gate) (v : ℕ)
    (basis : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ G, v ∉ g.inputs)
    (a b : List Bool) (same : a.length = b.length) (early : v < a.length)
    (ordered : ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true) :
    ∀ i, i ≠ v → (G.foldl step a).getD i false = true →
      (G.foldl step b).getD i false = true := by
  induction G generalizing a b with
  | nil => simpa using ordered
  | cons g G ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · exact fun h hm => basis h (List.mem_cons_of_mem g hm)
    · exact fun h hm => ignore h (List.mem_cons_of_mem g hm)
    · simp only [step, List.length_append, List.length_singleton, same]
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · intro i hiv
      simp only [step, getD_snoc, same]
      by_cases hi : i = b.length
      · simp only [hi, if_pos]
        apply gate_mono g (basis g (List.mem_cons_self ..))
        intro j hj
        apply ordered j
        intro he
        exact ignore g (List.mem_cons_self ..) (he ▸ hj)
      · simp only [hi, if_false]
        exact ordered i hiv

lemma eval_mono_except (C : Circuit) (mono : Monotone2 C) (v : ℕ)
    (ignore : ∀ g ∈ C.gates, v ∉ g.inputs) (out : C.output ≠ v)
    (a b : List Bool) (same : a.length = b.length) (early : v < a.length)
    (ordered : ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true) :
    C.eval a = true → C.eval b = true := by
  apply fold_mono_except C.gates v ?_ ignore a b same early ordered C.output out
  intro g hg
  simpa using (mono g hg).1

def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def leftInput : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
def rightInput : Fin 10 → Bool := fun i => decide (i = 1)

lemma first_not_needs_positive_input (C : Circuit) (mono : Monotone2 C)
    (ignore : ∀ g ∈ C.gates, 0 ∉ g.inputs) (out : C.output ≠ 0) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = edge x := by
  intro correct
  have left : C.eval (List.ofFn leftInput ++ [!leftInput 0]) = true := by
    rw [correct]
    decide
  have right : C.eval (List.ofFn rightInput ++ [!rightInput 0]) = false := by
    rw [correct]
    decide
  have ordered : ∀ i : ℕ, i ≠ 0 →
      (List.ofFn leftInput ++ [!leftInput 0]).getD i false = true →
      (List.ofFn rightInput ++ [!rightInput 0]).getD i false = true := by
    intro i hi ht
    by_cases bound : i < 11
    · interval_cases i <;> simp_all [leftInput, rightInput, List.ofFn_succ]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound)] at ht
      cases ht
  have h := eval_mono_except C mono 0 ignore out
    (List.ofFn leftInput ++ [!leftInput 0]) (List.ofFn rightInput ++ [!rightInput 0])
    (by simp) (by simp) ordered left
  rw [right] at h
  cases h

end PEqualNP.Outside.L_meta_2592.Restriction

namespace PEqualNP.Outside.L_meta_2592.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma fold_input (G : List Gate) (a : List Bool) (i : ℕ) (early : i < a.length) :
    (G.foldl step a).getD i false = a.getD i false := by
  induction G generalizing a with
  | nil => rfl
  | cons g G ih =>
    have earlyNext : i < (step a g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (step a g) earlyNext]
    exact List.getD_append _ _ _ _ early

def spikeInput : Fin 10 → Bool := fun i => decide (i = 0)

lemma positive_input_required (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = edge x) :
    ∃ g ∈ C.gates, 0 ∈ g.inputs := by
  by_contra! ignore
  have out : C.output ≠ 0 := by
    intro hout
    have h := correct spikeInput
    simp only [Circuit.eval, Circuit.wires, hout] at h
    change (C.gates.foldl step (List.ofFn spikeInput ++ [!spikeInput 0])).getD 0 false =
      edge spikeInput at h
    rw [fold_input _ _ _ (by simp)] at h
    have input : (List.ofFn spikeInput ++ [!spikeInput 0]).getD 0 false = true := by decide
    have output : edge spikeInput = false := by decide
    rw [input, output] at h
    cases h
  exact first_not_needs_positive_input C mono ignore out correct

end PEqualNP.Outside.L_meta_2592.Restriction
