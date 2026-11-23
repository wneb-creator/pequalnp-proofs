import Mathlib

namespace PriorRoutes

def stackSummary {Symbol State : Type} (step : State → Symbol → State)
    (word : List Symbol) : State → State :=
  word.foldl (fun f a => f ∘ fun state => step state a) id

lemma stackSummary_general {Symbol State : Type} (step : State → Symbol → State)
    (word : List Symbol) (f : State → State) (state : State) :
    (word.foldl (fun f a => f ∘ fun state => step state a) f) state =
      f (word.reverse.foldl step state) := by
  induction word generalizing f state with
  | nil => rfl
  | cons a word ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    exact ih (f ∘ fun state => step state a) state

lemma stackSummary_correct {Symbol State : Type} (step : State → Symbol → State)
    (word : List Symbol) (state : State) :
    stackSummary step word state = word.reverse.foldl step state := by
  exact stackSummary_general step word id state

lemma stackSummary_append_one {Symbol State : Type} (step : State → Symbol → State)
    (word : List Symbol) (a : Symbol) :
    stackSummary step (word ++ [a]) = stackSummary step word ∘ fun state => step state a := by
  simp [stackSummary, List.foldl_append]

lemma stackSummary_finite_control {State : Type} [Fintype State] :
    Finite (State → State) := inferInstance

lemma paired_stackSummary_correct {Left Right State : Type}
    (step : State → Left × Right → State) (left : List Left) (right : List Right)
    (equal_length : left.length = right.length) (state : State) :
    stackSummary step (List.zipWith Prod.mk left right) state =
      (List.zipWith Prod.mk left.reverse right.reverse).foldl step state := by
  rw [stackSummary_correct, List.reverse_zipWith equal_length]

lemma paired_stackSummary_append_one {Left Right State : Type}
    (step : State → Left × Right → State) (left : List Left) (right : List Right)
    (equal_length : left.length = right.length) (a : Left) (b : Right) :
    stackSummary step (List.zipWith Prod.mk (left ++ [a]) (right ++ [b])) =
      stackSummary step (List.zipWith Prod.mk left right) ∘
        fun state => step state (a, b) := by
  rw [List.zipWith_append equal_length]
  exact stackSummary_append_one step (List.zipWith Prod.mk left right) (a, b)

end PriorRoutes
