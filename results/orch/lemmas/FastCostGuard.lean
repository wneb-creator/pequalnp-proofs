import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux.FastCostGuard

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))

lemma two_loss_le (ka kb ax ay : Bool) :
    (cond ka 0 (cond ax 0 1)) + (cond kb 0 (cond ay 0 1)) ≤ 2 := by
  cases ka <;> cases kb <;> cases ax <;> cases ay <;> decide

noncomputable def guardedFastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  if s.2.2.2.2.1 ≤ 2 then fastCost s i j op ka kb else false

lemma guardedFastCost_eq (s : QS) (i j op : Nat) (ka kb : Bool) :
    guardedFastCost s i j op ka kb = fastCost s i j op ka kb := by
  by_cases h : s.2.2.2.2.1 ≤ 2
  · simp only [guardedFastCost,h,ite_true]
  · simp only [guardedFastCost,h,ite_false,fastCost,force_eq]
    have neq : s.2.2.2.2.1 ≠
        (cond ka 0 (cond (navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 (s.2.2.2.2.2.1.getD i 0)) 0 1)) +
        (cond kb 0 (cond (navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 (s.2.2.2.2.2.1.getD j 0)) 0 1)) := by
      have hb := two_loss_le ka kb
        (navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 (s.2.2.2.2.2.1.getD i 0))
        (navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 (s.2.2.2.2.2.1.getD j 0))
      omega
    have heq : Nat.beq _ _ = false := Bool.eq_false_iff.mpr (fun he => neq (Nat.eq_of_beq_eq_true he))
    simp only [Nat.add_eq]
    rw [heq]
    rfl

end PEqualNP.Outside.L_meta_670_aux.FastCostGuard
