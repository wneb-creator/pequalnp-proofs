import Mathlib

namespace StackSummary

def relation (readPrefix writePrefix input output : List Bool) : Prop :=
  ∃ tail, input = readPrefix ++ tail ∧ output = writePrefix ++ tail

lemma compose_consumes_written (read₁ write₁ read₂ write₂ extra input output : List Bool)
    (h : write₁ = read₂ ++ extra) :
    (∃ middle, relation read₁ write₁ input middle ∧
      relation read₂ write₂ middle output) ↔
      relation read₁ (write₂ ++ extra) input output := by
  constructor
  · rintro ⟨middle, ⟨tail₁, hi, hm₁⟩, ⟨tail₂, hm₂, ho⟩⟩
    have he : extra ++ tail₁ = tail₂ := by
      simpa [h, List.append_assoc] using hm₁.symm.trans hm₂
    refine ⟨tail₁, hi, ?_⟩
    simpa [← he, List.append_assoc] using ho
  · rintro ⟨tail, hi, ho⟩
    refine ⟨write₁ ++ tail, ⟨tail, hi, rfl⟩, extra ++ tail, ?_, ?_⟩
    · simp [h, List.append_assoc]
    · simpa [List.append_assoc] using ho

lemma compose_reads_beyond_written (read₁ write₁ read₂ write₂ extra input output : List Bool)
    (h : read₂ = write₁ ++ extra) :
    (∃ middle, relation read₁ write₁ input middle ∧
      relation read₂ write₂ middle output) ↔
      relation (read₁ ++ extra) write₂ input output := by
  constructor
  · rintro ⟨middle, ⟨tail₁, hi, hm₁⟩, ⟨tail₂, hm₂, ho⟩⟩
    have he : tail₁ = extra ++ tail₂ := by
      simpa [h, List.append_assoc] using hm₁.symm.trans hm₂
    refine ⟨tail₂, ?_, ho⟩
    simpa [he, List.append_assoc] using hi
  · rintro ⟨tail, hi, ho⟩
    refine ⟨read₂ ++ tail, ⟨extra ++ tail, ?_, ?_⟩, tail, rfl, ho⟩
    · simpa [List.append_assoc] using hi
    · simp [h, List.append_assoc]

lemma push (b : Bool) (input output : List Bool) :
    relation [] [b] input output ↔ output = b :: input := by
  simp [relation]

lemma pop (b : Bool) (input output : List Bool) :
    relation [b] [] input output ↔ input = b :: output := by
  simp [relation]

def coarse (depth : ℕ) (stack : List Bool) : ℕ × List Bool :=
  (stack.length, stack.take depth)

def observe (depth : ℕ) (stack : List Bool) : Option Bool :=
  (stack.drop depth).head?

lemma bounded_view_collision (depth : ℕ) :
    coarse depth (List.replicate depth false ++ [false]) =
      coarse depth (List.replicate depth false ++ [true]) ∧
    observe depth (List.replicate depth false ++ [false]) ≠
      observe depth (List.replicate depth false ++ [true]) := by
  constructor
  · simp [coarse]
  · simp [observe]

lemma heights_only_unsound :
    (∃ middle, relation [false] [true] [false] middle ∧
      relation [true] [] middle []) ∧
    ¬ (∃ middle, relation [false] [false] [false] middle ∧
      relation [true] [] middle []) := by
  simp [relation]

lemma empty_result_test (readPrefix input : List Bool) :
    relation readPrefix [] input [] ↔ input = readPrefix := by
  simp [relation]

lemma exact_summary_injective {Summary : Type} (summarize : List Bool → Summary)
    (h : ∀ x y, summarize x = summarize y → ∀ readPrefix,
      relation readPrefix [] x [] ↔ relation readPrefix [] y []) :
    Function.Injective summarize := by
  intro x y he
  have hy := (h x y he x).mp ((empty_result_test x x).mpr rfl)
  exact ((empty_result_test x y).mp hy).symm

lemma exact_summary_card {Summary : Type} [Fintype Summary]
    (depth : ℕ) (summarize : List Bool → Summary)
    (h : ∀ x y, x.length = depth → y.length = depth →
      summarize x = summarize y → ∀ readPrefix,
      relation readPrefix [] x [] ↔ relation readPrefix [] y []) :
    2 ^ depth ≤ Fintype.card Summary := by
  have hi : Function.Injective (fun f : Fin depth → Bool => summarize (List.ofFn f)) := by
    intro f g hfg
    have hg := (h _ _ (by simp) (by simp) hfg (List.ofFn f)).mp
      ((empty_result_test _ _).mpr rfl)
    exact List.ofFn_injective ((empty_result_test _ _).mp hg).symm
  simpa using Fintype.card_le_of_injective _ hi

end StackSummary
