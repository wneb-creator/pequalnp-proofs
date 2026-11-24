namespace PEqualNP.Outside.L_meta_670_aux.DynamicRawTransient

open LiveCheck DynamicLeaf DynamicRaw

def check {n : Nat} (oracles : Fin n → Oracle)
    (k t : Nat) (v : List Sig) (ctx : Context n) : Bool :=
  !(MemoLocalBoolFast.solve (RawContext n) (cut oracles) (next oracles)
    (fun _ _ _ => false) k t v ctx .empty).1

lemma check_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    {k t : Nat} {v : List Sig} {ctx : Context n}
    (hctx : Valid oracles v ctx)
    (hc : check oracles k t v ctx = true) : Impossible k t v := by
  have hs := MemoInvariant.solve_sound (RawContext n) (Valid oracles) (cut oracles)
    (next oracles) (fun _ _ _ => false) (cut_sound oracles hsound htarget)
    (next_valid oracles) k t v ctx .empty hctx
    (show MemoBoolFast.Sound .empty from trivial)
  apply hs.2
  simpa only [check,Bool.not_eq_true'] using hc

end PEqualNP.Outside.L_meta_670_aux.DynamicRawTransient
