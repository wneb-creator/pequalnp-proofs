import Mathlib

namespace PEqualNP.Outside.L_meta_1031.ExchangeBoundary

abbrev Signal := BitVec 16

def target : Signal := 63688

def boundary : List Signal :=
  [0, 65535, 43690, 52428, 61680, 65280, 64250, 65484, 64764]

def next (xs : List Signal) : List Signal :=
  (xs.flatMap fun a => xs.flatMap fun b =>
    (a ||| b) :: if (a &&& b) &&& ~~~target = 0 then [a &&& b] else []).dedup

lemma not_initial : target ∉ boundary := by decide +kernel

lemma not_one : target ∉ next boundary := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma not_two : ∀ x ∈ next boundary, target ∉ next (x :: boundary) := by
  have h : (next boundary).all (fun x => ! (next (x :: boundary)).contains target) = true := by
    decide +kernel
  intro x hx
  have hh := List.all_eq_true.mp h x hx
  simpa using hh

end PEqualNP.Outside.L_meta_1031.ExchangeBoundary
