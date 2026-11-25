import PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760
noncomputable section lookCutCore
def lookCut (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat)
    (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv F l m g k t z v y))
    true (Nat.ble v.length 1)

def look1Cut (F G : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat)
    (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv F l m g k t z v y) true
        (node (G (Nat.sub k 1) t) (pos t) l m g
          (Nat.sub (Nat.sub k t) y) v.length z v pairsS)))
    true (Nat.ble v.length 1)
end lookCutCore

lemma lookCut_eq (l m g fuel k t z : Nat) (v : List W) :
    lookCut (look l m g fuel) l m g k t z v =
      look l m g (fuel + 1) k t z v := by rfl

lemma look1Cut_eq (l m g K fuel k t z : Nat) (v : List W) :
    look1Cut (look l m g K) (look1 l m g K fuel) l m g k t z v =
      look1 l m g K (fuel + 1) k t z v := by rfl

noncomputable def strictSt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
lemma strictSt_eq (n : Nat) (f : Nat → Bool) : strictSt n f = f n := by
  cases n <;> rfl
noncomputable def frcAll (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
    (fun w _ ih h => strictSt w.s fun s => strictSt w.a fun a => strictSt w.b fun b =>
      strictSt w.c fun c => strictSt w.r fun tag => ih fun r => h (⟨s,a,b,c,tag⟩ :: r)) v
lemma frcAll_eq (v : List W) : ∀ h, frcAll v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change strictSt w.s (fun s => strictSt w.a fun a => strictSt w.b fun b =>
      strictSt w.c fun c => strictSt w.r fun tag => frcAll v fun r => h (⟨s,a,b,c,tag⟩ :: r)) = _
    simp only [strictSt_eq]
    rw [ih]

noncomputable def normLookStep (F : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) : Bool :=
  strictSt k (fun k => strictSt t (fun t => strictSt z (fun z =>
    frcAll v (fun v => lookCut F l m g k t z v))))

lemma normLookStep_eq (F : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) :
    normLookStep F l m g k t z v = lookCut F l m g k t z v := by
  simp only [normLookStep, strictSt_eq, frcAll_eq]

noncomputable def normLook (l m g : Nat) : Nat → Nat → Nat → Nat → List W → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, k, t, z, v => normLookStep (normLook l m g fuel) l m g k t z v

lemma normLook_eq (l m g fuel : Nat) : normLook l m g fuel = look l m g fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext k t z v
    change normLookStep (normLook l m g fuel) l m g k t z v = look l m g (fuel + 1) k t z v
    rw [normLookStep_eq, ih]
    exact lookCut_eq l m g fuel k t z v

noncomputable def normLook1Step (F G : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) : Bool :=
  strictSt k (fun k => strictSt t (fun t => strictSt z (fun z =>
    frcAll v (fun v => look1Cut F G l m g k t z v))))

lemma normLook1Step_eq (F G : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) :
    normLook1Step F G l m g k t z v = look1Cut F G l m g k t z v := by
  simp only [normLook1Step, strictSt_eq, frcAll_eq]

noncomputable def normLook1 (l m g K : Nat) : Nat → Nat → Nat → Nat → List W → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, k, t, z, v =>
      normLook1Step (normLook l m g K) (normLook1 l m g K fuel) l m g k t z v

lemma normLook1_eq (l m g K fuel : Nat) : normLook1 l m g K fuel = look1 l m g K fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext k t z v
    change normLook1Step (normLook l m g K) (normLook1 l m g K fuel)
      l m g k t z v = look1 l m g K (fuel + 1) k t z v
    rw [normLook1Step_eq, normLook_eq, ih]
    exact look1Cut_eq l m g K fuel k t z v

end PEqualNP.Outside.L_meta_10760
