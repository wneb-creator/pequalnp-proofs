import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux

def graphValue (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))

def pairAt (i j : Fin 10) (k : Fin 10) : Bool := decide (k = i ∨ k = j)

lemma pairAt_count : ∀ i j : Fin 10, (List.ofFn (pairAt i j)).count true ≤ 2 := by
  decide

lemma graphValue_mono {x y : Fin 10 → Bool}
    (h : ∀ i, x i = true → y i = true) (hx : graphValue x = true) :
    graphValue y = true := by
  simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  obtain ⟨i, hi, hxy⟩ := hx
  refine ⟨i, hi, ?_⟩
  rcases hxy with (hxy | hxy) | hxy
  · exact Or.inl (Or.inl ⟨h _ hxy.1, h _ hxy.2⟩)
  · exact Or.inl (Or.inr ⟨h _ hxy.1, h _ hxy.2⟩)
  · exact Or.inr ⟨h _ hxy.1, h _ hxy.2⟩

lemma graphValue_pair_witness {x : Fin 10 → Bool} (hx : graphValue x = true) :
    ∃ i j : Fin 10, graphValue (pairAt i j) = true ∧
      ∀ k, pairAt i j k = true → x k = true := by
  simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hx
  obtain ⟨i, hi, hxy⟩ := hx
  have pair_below (a b : Fin 10) (ha : x a = true) (hb : x b = true) :
      ∀ k, pairAt a b k = true → x k = true := by
    intro k hk
    simp only [pairAt, decide_eq_true_eq] at hk
    rcases hk with rfl | rfl <;> assumption
  rcases hxy with (hxy | hxy) | hxy
  · refine ⟨Fin.castAdd 5 i, Fin.castAdd 5 (i + 1), ?_, pair_below _ _ hxy.1 hxy.2⟩
    simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
    exact ⟨i, hi, Or.inl (Or.inl ⟨by simp [pairAt], by simp [pairAt]⟩)⟩
  · refine ⟨Fin.castAdd 5 i, Fin.natAdd 5 i, ?_, pair_below _ _ hxy.1 hxy.2⟩
    simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
    exact ⟨i, hi, Or.inl (Or.inr ⟨by simp [pairAt], by simp [pairAt]⟩)⟩
  · refine ⟨Fin.natAdd 5 i, Fin.natAdd 5 (i + 2), ?_, pair_below _ _ hxy.1 hxy.2⟩
    simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
    exact ⟨i, hi, Or.inr ⟨by simp [pairAt], by simp [pairAt]⟩⟩

lemma monotone_promise_full (u : (Fin 10 → Bool) → Bool)
    (hm : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (hp : ∀ x, graphValue x = false ∨ (List.ofFn x).count true ≤ 2 →
      u x = graphValue x) :
    ∀ x, u x = graphValue x := by
  intro x
  cases hx : graphValue x with
  | false => exact (hp x (Or.inl hx)).trans hx
  | true =>
    obtain ⟨i, j, hij, below⟩ := graphValue_pair_witness hx
    exact hm (pairAt i j) x below ((hp _ (Or.inr (pairAt_count i j))).trans hij)

open PEqualNP.CircuitLowerBounds

lemma append_mono (p q : List Bool) (a b : Bool) (hlen : p.length = q.length)
    (hpq : ∀ i, p.getD i false = true → q.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (p ++ [a]).getD i false = true → (q ++ [b]).getD i false = true := by
  intro i hi
  by_cases before : i < p.length
  · rw [List.getD_append _ _ _ _ before] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hpq i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    cases h : i - p.length with
    | zero => simpa [h] using hab (by simpa [h] using hi)
    | succ j => simp [h] at hi

lemma gate_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (p q : List Bool) (hpq : ∀ i, p.getD i false = true → q.getD i false = true) :
    g.op.eval (g.inputs.map fun i => p.getD i false) = true →
      g.op.eval (g.inputs.map fun i => q.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro h i hi
    exact hpq i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, h⟩
    exact ⟨i, hi, hpq i h⟩

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (p q : List Bool) (hlen : p.length = q.length)
    (hpq : ∀ i, p.getD i false = true → q.getD i false = true) :
    ∀ i,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) p).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) q).getD i false = true := by
  induction gs generalizing p q with
  | nil => exact hpq
  | cons g gs ih =>
    apply ih (fun g h => hg g (List.mem_cons_of_mem _ h))
    · simpa using hlen
    · exact append_mono p q _ _ hlen hpq (gate_mono g (hg _ List.mem_cons_self) p q hpq)

lemma ofFn_mono {n : Nat} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases bound : i < n
  · have get (f : Fin n → Bool) : (List.ofFn f).getD i false = f ⟨i, bound⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using bound)]
      simp
    rw [get] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound)] at hi
    contradiction

lemma positive_wires_mono {n : Nat} (c : Circuit)
    (hc : ∀ g ∈ c.gates, g.op = .and ∨ g.op = .or)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ i, (c.wires (List.ofFn x)).getD i false = true →
      (c.wires (List.ofFn y)).getD i false = true := by
  exact fold_mono c.gates hc (List.ofFn x) (List.ofFn y) (by simp) (ofFn_mono x y h)

lemma positive_two_wire_promise_full (c : Circuit) (a b : Nat)
    (hc : ∀ g ∈ c.gates, g.op = .and ∨ g.op = .or)
    (hp : ∀ x : Fin 10 → Bool, graphValue x = false ∨ (List.ofFn x).count true ≤ 2 →
      ((c.wires (List.ofFn x)).getD a false || (c.wires (List.ofFn x)).getD b false) = graphValue x) :
    ∀ x : Fin 10 → Bool,
      ((c.wires (List.ofFn x)).getD a false || (c.wires (List.ofFn x)).getD b false) = graphValue x := by
  apply monotone_promise_full _ _ hp
  intro x y hxy h
  simp only [Bool.or_eq_true] at h ⊢
  exact h.imp (positive_wires_mono c hc x y hxy a) (positive_wires_mono c hc x y hxy b)

end PEqualNP.Outside.L_meta_3821_aux
