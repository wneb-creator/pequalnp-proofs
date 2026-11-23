import Mathlib

namespace PEqualNP.Outside.L_meta_984.Forcing

def forceNat {α : Sort _} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)

theorem forceNat_eq {α : Sort _} (x : Nat) (f : Nat → α) : forceNat x f = f x := by
  cases x <;> rfl

def forceMap {α : Type} {β : Sort _} : List α → (α → Nat) → (List Nat → β) → β
  | [], _, k => k []
  | x :: xs, g, k => forceNat (g x) (fun v => forceMap xs g (fun vs => k (v :: vs)))

theorem forceMap_eq {α : Type} {β : Sort _} (xs : List α) (g : α → Nat)
    (k : List Nat → β) : forceMap xs g k = k (xs.map g) := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [forceMap,forceNat_eq,ih,List.map_cons]

end PEqualNP.Outside.L_meta_984.Forcing
