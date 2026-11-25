import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890.Finite

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def assignment (r : Nat) (i : Fin 10) : Bool := r.testBit i.val

def lowerRow (a b : Fin 10) : Nat :=
  if a = 0 then
    [0, 2, 0, 10, 16, 32, 80, 130, 258, 514].getD b.val 0
  else
    [0, 2, 0, 8, 18, 34, 72, 128, 258, 514].getD b.val 0

def afterOr (a b : Fin 10) (x : Fin 10 → Bool) : List Bool :=
  List.ofFn (fun i => if i = a then false else x i) ++
    [x 0 && x 2, x a || x b]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma firstOrWitness : ∀ (a b : Fin 10), (a = 0 ∨ a = 2) → b ≠ 0 → b ≠ 2 →
    afterOr a b (assignment (lowerRow a b)) =
      afterOr a b (assignment (lowerRow a b + 2 ^ a.val)) ∧
    pet (assignment (lowerRow a b)) = false ∧
    pet (assignment (lowerRow a b + 2 ^ a.val)) = true := by
  decide +kernel

lemma cannotRecoverEndpoint (a b : Fin 10) (ha : a = 0 ∨ a = 2)
    (hb0 : b ≠ 0) (hb2 : b ≠ 2) (f : List Bool → Bool) :
    ¬ ∀ x : Fin 10 → Bool, f (afterOr a b x) = pet x := by
  intro h
  obtain ⟨he, hl, hh⟩ := firstOrWitness a b ha hb0 hb2
  have lo := (h (assignment (lowerRow a b))).trans hl
  have hi := (h (assignment (lowerRow a b + 2 ^ a.val))).trans hh
  rw [he] at lo
  exact Bool.false_ne_true (lo.symm.trans hi)

end PEqualNP.Outside.L_meta_1890.Finite
