import Lean

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl

noncomputable def forcePackedList {β : Type} (xs : List PackedSig)
    (f : List PackedSig → β) : β :=
  List.rec (fun f => f []) (fun a _ ih f =>
    force a.1 fun x => force a.2 fun y => ih fun ys => f ((x,y)::ys)) xs f

theorem forcePackedList_eq {β : Type} (xs : List PackedSig) (f : List PackedSig → β) :
    forcePackedList xs f = f xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    change force x.1 (fun a => force x.2 fun b => forcePackedList xs fun ys => f ((a,b)::ys)) = _
    rw [force_eq,force_eq,ih]

noncomputable def forceBatch {β : Type} (b : Batch) (f : Batch → β) : β :=
  force b.2.2.1 fun r =>
  forcePackedList b.2.2.2.1 fun ws =>
  force b.2.2.2.2.1 fun a =>
  force b.2.2.2.2.2.1 fun c =>
  force b.2.2.2.2.2.2 fun d =>
  f (b.1,b.2.1,r,ws,(a,c,d))

theorem forceBatch_eq {β : Type} (b : Batch) (f : Batch → β) :
    forceBatch b f = f b := by
  rcases b with ⟨k,n,r,ws,a,c,d⟩
  simp only [forceBatch,force_eq,forcePackedList_eq]

