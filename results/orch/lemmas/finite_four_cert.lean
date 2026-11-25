import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451.Four

abbrev Mask := BitVec 16

def inputs : List Mask := [43690, 52428, 61680, 65280]

def choices (xs : List Mask) : List Mask :=
  (0 :: 65535 :: xs ++ xs.flatMap (fun a => xs.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

def possible : ℕ → List Mask → Mask → Bool
  | 0, xs, t => t == 0 || xs.contains t
  | k + 1, xs, t => (t == 0 || xs.contains t) ||
    (choices xs).any (fun a => possible k (xs ++ [a]) t)

def target (r : Fin 16) : Mask :=
  ([0, 41120, 43520, 43680, 49344, 57568, 60096, 60128,
    52224, 60576, 60928, 61088, 52416, 60640, 61120, 61152] : List Mask).getD r.val 0

def bound (r : Fin 16) : ℕ :=
  [0, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4, 2, 4, 4, 3].getD r.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certificate : ∀ r : Fin 16, 0 < bound r →
    possible (bound r - 1) inputs (target r) = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_3451.Four
