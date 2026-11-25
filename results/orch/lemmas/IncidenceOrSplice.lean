import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.OrSplice

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

lemma fold_length (G : List Gate) (x : List Bool) :
    (G.foldl step x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma sole_or_transfer (pre post : List Gate) (v a out : ℕ)
    (basis : ∀ g ∈ pre ++ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ignore : ∀ g ∈ pre ++ post, v ∉ g.inputs)
    (hout : out ≠ v) (x y : List Bool) (same : x.length = y.length)
    (early : v < x.length)
    (ordered : ∀ i, i ≠ v → x.getD i false = true → y.getD i false = true)
    (other : (pre.foldl step y).getD a false = true) :
    (Circuit.mk (pre ++ ⟨GateOp.or, [v, a]⟩ :: post) out).eval x = true →
      (Circuit.mk (pre ++ ⟨GateOp.or, [v, a]⟩ :: post) out).eval y = true := by
  have preBasis : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => basis g (List.mem_append_left _ hg)
  have postBasis : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => basis g (List.mem_append_right _ hg)
  have preIgnore : ∀ g ∈ pre, v ∉ g.inputs :=
    fun g hg => ignore g (List.mem_append_left _ hg)
  have postIgnore : ∀ g ∈ post, v ∉ g.inputs :=
    fun g hg => ignore g (List.mem_append_right _ hg)
  have before := fold_mono_except pre v preBasis preIgnore x y same early ordered
  have len : (pre.foldl step x).length = (pre.foldl step y).length := by
    simp only [fold_length, same]
  have trueGate : GateOp.or.eval ([v, a].map fun i =>
      (pre.foldl step y).getD i false) = true := by
    change ((pre.foldl step y).getD v false ||
      ((pre.foldl step y).getD a false || false)) = true
    rw [other]
    simp
  have after : ∀ i, i ≠ v →
      (step (pre.foldl step x) ⟨GateOp.or, [v, a]⟩).getD i false = true →
      (step (pre.foldl step y) ⟨GateOp.or, [v, a]⟩).getD i false = true := by
    intro i hi
    simp only [step, getD_snoc, len, trueGate]
    by_cases he : i = (pre.foldl step y).length
    · simp [he]
    · simp only [he, if_false]
      exact before i hi
  change ((pre ++ ⟨GateOp.or, [v, a]⟩ :: post).foldl step x).getD out false = true →
    ((pre ++ ⟨GateOp.or, [v, a]⟩ :: post).foldl step y).getD out false = true
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply fold_mono_except post v postBasis postIgnore _ _ ?_ ?_ after out hout
  · simp only [step, List.length_append, List.length_singleton, len]
  · simp only [step, List.length_append, List.length_singleton, fold_length]
    omega

end PEqualNP.Outside.L_meta_2583_aux.OrSplice
