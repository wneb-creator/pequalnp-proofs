import Lean

abbrev Sig := BitVec 512
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl

theorem sigs (ws : List Sig) : (ws.map BitVec.toNat).map (BitVec.ofNat 512) = ws := by
  simp only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id']

noncomputable def forced {β : Type} (ws : List Sig) (f : List Sig → β) :=
  forceMap BitVec.toNat ws fun ns => f (ns.map (BitVec.ofNat 512))
theorem forced_eq {β : Type} (ws : List Sig) (f : List Sig → β) : forced ws f = f ws := by
  rw [forced,forceMap_eq,sigs]

noncomputable def panelShape (ws : List Sig) (f : List Sig → Bool) :=
  forceMap BitVec.toNat ws fun ns =>
  let ws := ns.map (BitVec.ofNat 512)
  f ws
theorem panelShape_sound {ws f} (ok : panelShape ws f=true) : f ws=true := by
  have e : (ws.map BitVec.toNat).map (BitVec.ofNat 512)=ws := by
    simp only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id']
  unfold panelShape at ok
  rw [forceMap_eq,e] at ok
  exact ok
