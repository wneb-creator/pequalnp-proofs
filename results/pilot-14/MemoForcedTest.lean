import DynamicBase
namespace PEqualNP.Outside.L_meta_670_aux.MemoForced

open LiveCheck

structure Entry where
  budget : Nat
  nots : Nat
  wires : List Sig

inductive Memo where
  | empty
  | node (entries : List Entry) (left right : Memo)

def Sound : Memo → Prop
  | .empty => True
  | .node es l r =>
    (∀ e ∈ es, Impossible e.budget e.nots e.wires) ∧ Sound l ∧ Sound r

def entries : Memo → List Entry
  | .empty => []
  | .node es _ _ => es

def left : Memo → Memo
  | .empty => .empty
  | .node _ l _ => l

def right : Memo → Memo
  | .empty => .empty
  | .node _ _ r => r

lemma entries_sound {m : Memo} (h : Sound m) :
    ∀ e ∈ entries m, Impossible e.budget e.nots e.wires := by
  cases m with
  | empty => simp [entries]
  | node es l r => exact h.1

lemma left_sound {m : Memo} (h : Sound m) : Sound (left m) := by
  cases m with
  | empty => trivial
  | node es l r => exact h.2.1

lemma right_sound {m : Memo} (h : Sound m) : Sound (right m) := by
  cases m with
  | empty => trivial
  | node es l r => exact h.2.2

def bucket : Nat → Nat → Memo → List Entry
  | 0, _, m => entries m
  | d+1, key, m => bucket d (key/2) (if key%2 = 0 then left m else right m)

def insert : Nat → Nat → Entry → Memo → Memo
  | 0, _, e, .empty => .node [e] .empty .empty
  | 0, _, e, .node es l r => .node (e :: es) l r
  | d+1, key, e, .empty =>
    if key%2 = 0 then .node [] (insert d (key/2) e .empty) .empty
    else .node [] .empty (insert d (key/2) e .empty)
  | d+1, key, e, .node es l r =>
    if key%2 = 0 then .node es (insert d (key/2) e l) r
    else .node es l (insert d (key/2) e r)

lemma insert_zero (key : Nat) (e : Entry) (m : Memo) :
    insert 0 key e m = .node (e :: entries m) (left m) (right m) := by
  cases m <;> rfl

lemma insert_succ (d key : Nat) (e : Entry) (m : Memo) :
    insert (d+1) key e m =
      if key%2 = 0 then .node (entries m) (insert d (key/2) e (left m)) (right m)
      else .node (entries m) (left m) (insert d (key/2) e (right m)) := by
  cases m <;> rfl

lemma bucket_sound {m : Memo} (h : Sound m) (d key : Nat) :
    ∀ e ∈ bucket d key m, Impossible e.budget e.nots e.wires := by
  induction d generalizing key m with
  | zero => exact entries_sound h
  | succ d ih =>
    simp only [bucket]
    split
    · exact ih (left_sound h) _
    · exact ih (right_sound h) _

lemma insert_sound {m : Memo} (h : Sound m) (d key : Nat) (e : Entry)
    (he : Impossible e.budget e.nots e.wires) : Sound (insert d key e m) := by
  induction d generalizing key m with
  | zero =>
    rw [insert_zero]
    refine ⟨?_,left_sound h,right_sound h⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact entries_sound h a ha
  | succ d ih =>
    rw [insert_succ]
    split
    · exact ⟨entries_sound h,ih (left_sound h) _,right_sound h⟩
    · exact ⟨entries_sound h,left_sound h,ih (right_sound h) _⟩

def hash (t : Nat) (v : List Sig) : Nat :=
  (v.foldl (fun h a => h + 31*(a.1.toNat%65521) + a.2.toNat%65521) t)%65521

def hit (k t : Nat) (v : List Sig) (m : Memo) : Bool :=
  (bucket 12 (hash t v) m).any fun e =>
    decide (k ≤ e.budget) && e.nots == t && decide (v.Perm e.wires)

lemma hit_sound {k t : Nat} {v : List Sig} {m : Memo}
    (hm : Sound m) (hh : hit k t v m = true) : Impossible k t v := by
  obtain ⟨e,he,hgood⟩ := List.any_eq_true.mp hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hgood
  obtain ⟨⟨hk,ht⟩,hp⟩ := hgood
  intro n hn hl
  apply bucket_sound hm 12 (hash t v) e he n (by omega)
  have heq : v.toFinset = e.wires.toFinset := by
    ext a
    simpa only [List.mem_toFinset] using hp.mem_iff
  rw [ht,← heq]
  exact hl

def answer (k t : Nat) (v : List Sig) (m : Memo) : Bool := !(hit k t v m)

lemma answer_false {k t : Nat} {v : List Sig} {m : Memo}
    (hm : Sound m) (ha : answer k t v m = false) : Impossible k t v := by
  apply hit_sound hm
  unfold answer at ha
  cases hh : hit k t v m <;> simp_all

def forceNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | m+1 => f (m+1)

lemma forceNat_eq {α : Type} (n : Nat) (f : Nat → α) : forceNat n f = f n := by
  cases n <;> rfl

def forceSig {α : Type} (a : Sig) (f : Sig → α) : α :=
  forceNat a.1.toNat fun p =>
    forceNat a.2.toNat fun n => f (BitVec.ofNat 414 p,BitVec.ofNat 414 n)

lemma forceSig_eq {α : Type} (a : Sig) (f : Sig → α) : forceSig a f = f a := by
  simp only [forceSig,forceNat_eq,BitVec.ofNat_toNat,BitVec.setWidth_eq]

def forceWires {α : Type} : List Sig → (List Sig → α) → α
  | [], f => f []
  | a :: xs, f => forceSig a fun b => forceWires xs fun ys => f (b :: ys)

lemma forceWires_eq {α : Type} (v : List Sig) (f : List Sig → α) :
    forceWires v f = f v := by
  induction v generalizing f with
  | nil => rfl
  | cons a v ih => simp only [forceWires,forceSig_eq,ih]

def save (retain : Nat → Nat → List Sig → Bool)
    (k t : Nat) (v : List Sig) (m : Memo) : Memo :=
  if retain k t v then
    forceNat k fun k' => forceNat t fun t' => forceWires v fun xs =>
      forceNat (hash t' xs) fun key => insert 12 key ⟨k',t',xs⟩ m
  else m

lemma save_sound (retain : Nat → Nat → List Sig → Bool)
    {k t : Nat} {v : List Sig} {m : Memo} (hm : Sound m) (hv : Impossible k t v) :
    Sound (save retain k t v m) := by
  unfold save
  split
  · simpa only [forceNat_eq,forceWires_eq] using insert_sound hm 12 (hash t v) ⟨k,t,v⟩ hv
  · exact hm

def ResultSound (k t : Nat) (v : List Sig) (r : Bool × Memo) : Prop :=
  Sound r.2 ∧ (r.1 = false → Impossible k t v)

def finish (retain : Nat → Nat → List Sig → Bool)
    (k t : Nat) (v : List Sig) (b : Bool) (m : Memo) : Bool × Memo :=
  if b then (true,m) else (false,save retain k t v m)

lemma finish_sound (retain : Nat → Nat → List Sig → Bool)
    {k t : Nat} {v : List Sig} {b : Bool} {m : Memo}
    (hm : Sound m) (hb : b = false → Impossible k t v) :
    ResultSound k t v (finish retain k t v b m) := by
  cases b
  · exact ⟨save_sound retain hm (hb rfl),fun _ => hb rfl⟩
  · exact ⟨hm,by simp [finish]⟩

lemma fold_sound {α : Type} (f : Memo → α → Memo)
    (hf : ∀ m a, Sound m → Sound (f m a)) (xs : List α) {m : Memo} (hm : Sound m) :
    Sound (xs.foldl f m) := by
  induction xs generalizing m with
  | nil => exact hm
  | cons a xs ih => exact ih (hf m a hm)

variable (Context : List Sig → Type)

structure Child where
  nots : Nat
  wires : List Sig
  context : Unit → Context wires

variable (cut : (k t : Nat) → (v : List Sig) → Context v → Bool)
variable (next : (k t : Nat) → (v : List Sig) → Context v → List (Child Context))
variable (retain : Nat → Nat → List Sig → Bool)

def guarded (k t : Nat) (v : List Sig) (c : Context v)
    (m : Memo) (evaluate : Memo → Bool × Memo) : Bool × Memo :=
  if hit k t v m then (false,m)
  else if decide v.Nodup then
    if cut k t v c then finish retain k t v false m else evaluate m
  else (true,m)

lemma guarded_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    {k t : Nat} {v : List Sig} {c : Context v} {m : Memo}
    {evaluate : Memo → Bool × Memo} (hm : Sound m)
    (he : v.Nodup → ResultSound k t v (evaluate m)) :
    ResultSound k t v (guarded Context cut retain k t v c m evaluate) := by
  unfold guarded
  split
  · rename_i hh
    exact ⟨hm,fun _ => hit_sound hm hh⟩
  · split
    · rename_i hv
      have hn : v.Nodup := of_decide_eq_true hv
      split
      · rename_i hc
        exact finish_sound retain hm (fun _ => cutSound k t v c hn hc)
      · exact he hn
    · exact ⟨hm,by simp⟩

def solve : (k t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo
  | 0,t,v,c,m => guarded Context cut retain 0 t v c m fun m' =>
      finish retain 0 t v (search 0 t v) m'
  | k+1,t,v,c,m => guarded Context cut retain (k+1) t v c m fun m' =>
      let filled := (next (k+1) t v c).foldl (fun current child =>
        if hit k child.nots child.wires current then current else
          (solve k child.nots child.wires (child.context ()) current).2) m'
      finish retain (k+1) t v
        (stepTest k t v (fun w => answer k (t-1) w filled)
          (fun w => answer k t w filled)) filled

lemma solve_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (v : List Sig) (c : Context v) (m : Memo) (hm : Sound m) :
    ResultSound k t v (solve Context cut next retain k t v c m) := by
  induction k generalizing t v c m with
  | zero =>
    rw [solve]
    apply guarded_sound Context cut retain cutSound hm
    intro hv
    exact finish_sound retain hm (exclude_search hv)
  | succ k ih =>
    rw [solve]
    apply guarded_sound Context cut retain cutSound hm
    intro hv
    let filled := (next (k+1) t v c).foldl (fun current child =>
      if hit k child.nots child.wires current then current else
        (solve Context cut next retain k child.nots child.wires (child.context ()) current).2) m
    have hs : Sound filled := fold_sound _ (fun current child hc => by
      split
      · exact hc
      · exact (ih child.nots child.wires (child.context ()) current hc).1) _ hm
    apply finish_sound retain hs
    apply exclude_step hv
    · intro w hw
      exact answer_false hs hw
    · intro w hw
      exact answer_false hs hw

end PEqualNP.Outside.L_meta_670_aux.MemoForced
namespace PEqualNP.Outside.L_meta_670_aux.MemoForced

open LiveCheck

def UnitContext (_ : List Sig) := Unit

def noCut (_ _ : Nat) (v : List Sig) (_ : UnitContext v) : Bool := false

def tinyChildren (k : Nat) (_ : Nat) (v : List Sig) (_ : UnitContext v) :
    List (Child UnitContext) :=
  if k = 2 then [⟨0,[],fun _ => ()⟩,⟨0,[],fun _ => ()⟩] else []

def retainAll (_ _ : Nat) (_ : List Sig) : Bool := true

def trial := solve UnitContext noCut tinyChildren retainAll 2 0 [] () .empty

def entryCount : Memo → Nat
  | .empty => 0
  | .node es l r => es.length + entryCount l + entryCount r

lemma trial_false : trial.1 = false := by decide +kernel

lemma trial_entries : entryCount trial.2 = 2 := by decide +kernel

lemma trial_hit : hit 1 0 [] trial.2 = true := by decide +kernel

lemma trial_sound : ResultSound 2 0 [] trial := by
  apply solve_sound
  · intro k t v c hv hc
    simp [noCut] at hc
  · trivial

lemma target_open :
    (solve UnitContext noCut tinyChildren retainAll 0 0 [target] () .empty).1 = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_670_aux.MemoForced
