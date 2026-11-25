namespace PEqualNP.Outside.L_meta_2592_aux.PetersenTwinsFast

def adjacentMask (v : Fin 10) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

def bits (mask : Nat) : Nat :=
  ((List.range 10).filter (fun v => mask.testBit v)).length

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem neighborhood_difference : ∀ u v : Fin 10, u ≠ v →
    4 ≤ bits (Nat.xor (adjacentMask u) (adjacentMask v)) := by
  decide

theorem filter_length_mono {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have bound := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases hp : p a with
    | false =>
      cases hq : q a with
      | false => simpa [hp, hq] using bound
      | true => simpa [hp, hq] using Nat.le_trans bound (Nat.le_succ _)
    | true =>
      have hq := h a List.mem_cons_self hp
      simpa [hp, hq] using Nat.succ_le_succ bound

def residual (deleted : Nat) (v : Fin 10) : Nat :=
  Nat.land (adjacentMask v) (Nat.xor 1023 deleted)

theorem full_mask_bits : ∀ i : Fin 10, Nat.testBit 1023 i.val = true := by decide

theorem no_twins_after_three (deleted : Nat) (small : bits deleted ≤ 3)
    (u v : Fin 10) (different : u ≠ v) : residual deleted u ≠ residual deleted v := by
  intro same
  have removed : ∀ i ∈ List.range 10,
      (Nat.xor (adjacentMask u) (adjacentMask v)).testBit i = true →
      deleted.testBit i = true := by
    intro i hi hd
    have full := full_mask_bits ⟨i, List.mem_range.mp hi⟩
    have eqBit := congrArg (fun mask : Nat => mask.testBit i) same
    change ((adjacentMask u &&& (1023 ^^^ deleted)).testBit i) =
      ((adjacentMask v &&& (1023 ^^^ deleted)).testBit i) at eqBit
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, full] at eqBit
    change (adjacentMask u ^^^ adjacentMask v).testBit i = true at hd
    rw [Nat.testBit_xor] at hd
    cases hu : (adjacentMask u).testBit i <;>
      cases hv : (adjacentMask v).testBit i <;>
      cases ht : deleted.testBit i <;> simp_all
  have bound := filter_length_mono
    (fun i => (Nat.xor (adjacentMask u) (adjacentMask v)).testBit i)
    (fun i => deleted.testBit i) (List.range 10) removed
  have floor := neighborhood_difference u v different
  exact Nat.not_succ_le_self 3 (Nat.le_trans floor (Nat.le_trans bound small))

end PEqualNP.Outside.L_meta_2592_aux.PetersenTwinsFast
