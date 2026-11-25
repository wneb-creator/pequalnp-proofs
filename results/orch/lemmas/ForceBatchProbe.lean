import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_670.ForceBatchProbe
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forcePacked {β : Type} (xs : List PackedSig) : (List PackedSig → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f =>
    force p.1 fun a => force p.2 fun b => ih fun ys => f ((a,b)::ys)) xs

theorem forcePacked_eq {β : Type} (xs : List PackedSig) (f : List PackedSig → β) :
    forcePacked xs f = f xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons p xs ih =>
    change force p.1 (fun a => force p.2 (fun b => forcePacked xs (fun ys => f ((a,b)::ys)))) = _
    rw [force_eq,force_eq,ih]

noncomputable def forceBatch {β : Type} (b : Batch) (f : Batch → β) : β :=
  force b.1 fun k => force b.2.1 fun n => force b.2.2.1 fun r =>
  forcePacked b.2.2.2.1 fun ws =>
  force b.2.2.2.2.1 fun c0 => force b.2.2.2.2.2.1 fun c1 => force b.2.2.2.2.2.2 fun c2 =>
  f (k,n,r,ws,c0,c1,c2)

theorem forceBatch_eq {β : Type} (b : Batch) (f : Batch → β) : forceBatch b f = f b := by
  simp only [forceBatch,force_eq,forcePacked_eq]

end PEqualNP.Outside.L_meta_670.ForceBatchProbe
