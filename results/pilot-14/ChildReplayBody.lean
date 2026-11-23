namespace PEqualNP.Outside.L_meta_670_aux.ChildReplay

open LiveCheck

structure Child where
  nots : Nat
  wires : List Sig

def fill (k : Nat) : List Child → MemoBoolFast.Memo → MemoBoolFast.Memo
  | [],m => m
  | p :: ps,m => fill k ps (MemoBoolFast.save (fun _ _ _ => true) k p.nots p.wires m)

lemma fill_sound {k : Nat} (ps : List Child) {m : MemoBoolFast.Memo}
    (hm : MemoBoolFast.Sound m)
    (children : ∀ p ∈ ps, Impossible k p.nots p.wires) : MemoBoolFast.Sound (fill k ps m) := by
  induction ps generalizing m with
  | nil => exact hm
  | cons p ps ih =>
    exact ih (MemoBoolFast.save_sound _ hm (children p List.mem_cons_self))
      (fun q hq => children q (List.mem_cons_of_mem p hq))

def check (k t : Nat) (v : List Sig) (children : List Child) : Bool :=
  let memo := fill k children .empty
  BoolNodup.check v && !(stepTest k t v
    (fun w => MemoBoolFast.answer k (t-1) w memo)
    (fun w => MemoBoolFast.answer k t w memo))

lemma check_sound {k t : Nat} {v : List Sig} (ps : List Child)
    (children : ∀ p ∈ ps, Impossible k p.nots p.wires)
    (h : check k t v ps = true) : Impossible (k+1) t v := by
  have hm := fill_sound ps (show MemoBoolFast.Sound .empty from trivial) children
  simp only [check,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply exclude_step (BoolNodup.sound h.1) _ _ h.2
  · intro w hw
    exact MemoBoolFast.answer_false hm hw
  · intro w hw
    exact MemoBoolFast.answer_false hm hw

lemma check_fin_sound {k t : Nat} {v : List Sig} (ps : List Child)
    (children : ∀ i : Fin ps.length, Impossible k ps[i.val].nots ps[i.val].wires)
    (h : check k t v ps = true) : Impossible (k+1) t v := by
  apply check_sound ps ?_ h
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  simpa only [he] using children ⟨i,hi⟩

end PEqualNP.Outside.L_meta_670_aux.ChildReplay
