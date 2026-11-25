import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def rowCounterCirc : Circuit :=
  ⟨[
    ⟨.or, [3, 6]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [10, 0]⟩,
    ⟨.or, [11, 1]⟩,
    ⟨.or, [10, 2]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.and, [9, 15]⟩,
    ⟨.or, [16, 17]⟩
  ], 18⟩

def rowCounterMatrix : Fin 6 → Fin 3 → Bool :=
  fun a b => ([1, 2, 4, 6, 5, 3].getD a.val (0 : Nat)).testBit b.val

lemma rowCounter_mono : Monotone2 rowCounterCirc := by
  simp [Monotone2, rowCounterCirc]

set_option maxRecDepth 100000 in
lemma rowCounter_rep : Represents rowCounterMatrix rowCounterCirc := by
  decide +kernel

lemma rowCounter_size : rowCounterCirc.size = 10 := by decide

lemma rowCounter_rows_nonempty : ∀ a : Fin 6, ∃ b : Fin 3, rowCounterMatrix a b = true := by
  decide +kernel

lemma rowCounter_rows_nonfull : ∀ a : Fin 6, ∃ b : Fin 3, rowCounterMatrix a b = false := by
  decide +kernel

lemma rowCounter_cols_nonempty : ∀ b : Fin 3, ∃ a : Fin 6, rowCounterMatrix a b = true := by
  decide +kernel

lemma rowCounter_cols_nonfull : ∀ b : Fin 3, ∃ a : Fin 6, rowCounterMatrix a b = false := by
  decide +kernel

lemma rowCounter_rows_distinct : ∀ a a' : Fin 6, (∀ b : Fin 3, rowCounterMatrix a b = rowCounterMatrix a' b) → a = a' := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma rowCounter_singletons_false : ∀ i : Fin 9,
    rowCounterCirc.eval (List.ofFn (fun j : Fin 9 => decide (j = i))) = false := by
  decide +kernel

lemma rowCounter_upper : RepSizeAtMost rowCounterMatrix 10 :=
  ⟨rowCounterCirc, rowCounter_mono, by decide, rowCounter_rep⟩

end PEqualNP.Outside.L_meta_9502
