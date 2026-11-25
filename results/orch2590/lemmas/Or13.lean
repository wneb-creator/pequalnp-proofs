import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.Or13

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def witness : Circuit :=
  ⟨[⟨.or, [7, 6]⟩,
    ⟨.and, [4, 0]⟩,
    ⟨.or, [7, 1]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.or, [12, 3]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.and, [15, 8]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [15, 10]⟩,
    ⟨.and, [18, 12]⟩,
    ⟨.and, [14, 2]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [13, 9]⟩,
    ⟨.or, [19, 0]⟩,
    ⟨.and, [23, 1]⟩,
    ⟨.and, [17, 14]⟩,
    ⟨.and, [25, 3]⟩,
    ⟨.and, [23, 21]⟩,
    ⟨.or, [27, 16]⟩,
    ⟨.or, [24, 20]⟩,
    ⟨.or, [29, 28]⟩,
    ⟨.or, [26, 22]⟩,
    ⟨.or, [30, 31]⟩], 32⟩

def orCount (C : Circuit) : ℕ := C.gates.countP fun g =>
  match g.op with
  | .or => true
  | _ => false

def andCount (C : Circuit) : ℕ := C.gates.countP fun g =>
  match g.op with
  | .and => true
  | _ => false

lemma witness_ao2 : IsAO2 10 witness := by decide

lemma witness_monotone : Monotone2 witness := by decide

lemma witness_size : witness.size = 23 := by rfl

lemma witness_or_count : orCount witness = 13 := by decide

lemma witness_and_count : andCount witness = 10 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma witness_correct : ∀ x : Fin 10 → Bool,
    witness.eval (List.ofFn x) = target x := by decide +kernel

lemma thirteen_or_gates_suffice : ∃ C : Circuit,
    IsAO2 10 C ∧ Monotone2 C ∧ C.size = 23 ∧ orCount C = 13 ∧ andCount C = 10 ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = target x := by
  exact ⟨witness, witness_ao2, witness_monotone, witness_size, witness_or_count,
    witness_and_count, witness_correct⟩

end PEqualNP.Outside.L_meta_2590.Or13
