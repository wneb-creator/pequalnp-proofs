import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds

def path4Adj (a b : Fin 4) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

def path4Fun (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path4Block (op : Bool) (a b : Fin 6) : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩,
    ⟨if op then .and else .or, [a.val, b.val]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def path4Short : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

lemma path4_exchange_identity : ∀ a b c d : Bool,
    (((a || c) && (b || d)) && (b || c)) =
      ((b && (a || c)) || (c && d)) := by
  decide

lemma path4_block_mono (op : Bool) (a b : Fin 6) :
    PEqualNP.MetaComplexity.Monotone2 (path4Block op a b) := by
  cases op <;> simp [PEqualNP.MetaComplexity.Monotone2, path4Block]

lemma path4_short_mono : PEqualNP.MetaComplexity.Monotone2 path4Short := by
  simp [PEqualNP.MetaComplexity.Monotone2, path4Short]

lemma path4_no_triangle : ∀ a b c : Fin 4,
    path4Adj a b → path4Adj b c → ¬ path4Adj c a := by
  unfold path4Adj
  decide

lemma path4_no_four_cycle : ∀ a b c d : Fin 4,
    path4Adj a b → path4Adj b c → path4Adj c d → path4Adj d a →
      a = c ∨ b = d := by
  unfold path4Adj
  decide

lemma path4_edge_function : ∀ x : Fin 4 → Bool,
    path4Fun x = decide (∃ a b : Fin 4,
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) ∧ x a = true ∧ x b = true) := by
  decide

lemma path4_block_computes : ∀ x : Fin 4 → Bool,
    (path4Block true 4 5).eval (List.ofFn x) = path4Fun x := by
  decide

lemma path4_block_dirty :
    let x : Fin 4 → Bool := fun i => decide (i = 0 ∨ i = 3)
    ((path4Block true 4 5).wires (List.ofFn x)).getD 6 false = true ∧
      path4Fun x = false := by
  decide

set_option maxHeartbeats 2000000 in
lemma path4_one_gate_obstruction : ∀ (op : Bool) (a b : Fin 6),
    (∀ x : Fin 4 → Bool, (path4Block op a b).eval (List.ofFn x) = path4Fun x) →
    ∃ x : Fin 4 → Bool,
      ((path4Block op a b).wires (List.ofFn x)).getD 6 false = true ∧
        path4Fun x = false := by
  decide

lemma path4_shorter_safe : path4Short.size < (path4Block true 4 5).size ∧
    ∀ x : Fin 4 → Bool, path4Short.eval (List.ofFn x) = path4Fun x ∧
      (((path4Short.wires (List.ofFn x)).getD 5 false = true → path4Fun x = true) ∧
       ((path4Short.wires (List.ofFn x)).getD 6 false = true → path4Fun x = true)) := by
  decide

end PEqualNP.Outside.L_meta_1904
