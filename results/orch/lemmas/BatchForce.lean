namespace PEqualNP.Outside.L_meta_670_aux.BatchForce

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n

theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by
  cases n <;> rfl

noncomputable def forcePacked {β : Type} (p : PackedSig) (f : PackedSig → β) : β :=
  force p.1 fun a => force p.2 fun b => f (a,b)

theorem forcePacked_eq {β : Type} (p : PackedSig) (f : PackedSig → β) :
    forcePacked p f = f p := by
  simp only [forcePacked,force_eq]

noncomputable def forcePackedList {β : Type} (ps : List PackedSig) :
    (List PackedSig → β) → β :=
  List.rec (fun f => f [])
    (fun p _ ih f => forcePacked p fun q => ih fun qs => f (q::qs)) ps

theorem forcePackedList_eq {β : Type} (ps : List PackedSig) (f : List PackedSig → β) :
    forcePackedList ps f = f ps := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePacked p (fun q => forcePackedList ps fun qs => f (q::qs)) = _
    rw [forcePacked_eq,ih]

noncomputable def forceBatch {β : Type} (b : Batch) (f : Batch → β) : β :=
  force b.1 fun k => force b.2.1 fun n => force b.2.2.1 fun u =>
    forcePackedList b.2.2.2.1 fun ws =>
      force b.2.2.2.2.1 fun c0 => force b.2.2.2.2.2.1 fun c1 =>
        force b.2.2.2.2.2.2 fun c2 => f (k,n,u,ws,c0,c1,c2)

theorem forceBatch_eq {β : Type} (b : Batch) (f : Batch → β) :
    forceBatch b f = f b := by
  simp only [forceBatch,force_eq,forcePackedList_eq]

end PEqualNP.Outside.L_meta_670_aux.BatchForce
