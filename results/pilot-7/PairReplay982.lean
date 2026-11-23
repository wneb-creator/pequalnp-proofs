import BinaryHint982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.PairReplay
open PEqualNP.Outside.L_meta_982_aux.Finite.Live
open PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

def Rel (f : Nat → Nat) (xs : List (Nat × Nat)) : Prop := ∀ a ∈ xs, a.2 = f a.1

theorem rel_cons {f : Nat → Nat} {a xs} (ha : a.2 = f a.1) (h : Rel f xs) : Rel f (a::xs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact h b hb

theorem rel_tail {f : Nat → Nat} {a xs} (h : Rel f (a::xs)) : Rel f xs :=
  fun b hb => h b (List.mem_cons_of_mem a hb)

theorem rel_getD {f : Nat → Nat} {xs} (h0 : f 0 = 0) (h : Rel f xs) (i : Nat) :
    (xs.getD i (0,0)).2 = f (xs.getD i (0,0)).1 := by
  induction xs generalizing i with
  | nil => exact h0.symm
  | cons a xs ih =>
    cases i with
    | zero => exact h a List.mem_cons_self
    | succ i => exact ih (rel_tail h) i

def without (a b : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | _,[] => []
  | i,x::xs => if i = a ∨ i = b then without a b (i+1) xs
      else x :: without a b (i+1) xs

theorem rel_without {f : Nat → Nat} {xs} (h : Rel f xs) (a b i : Nat) : Rel f (without a b i xs) := by
  induction xs generalizing i with
  | nil => simp [without,Rel]
  | cons x xs ih =>
    simp only [without]
    split
    · exact ih (rel_tail h) _
    · exact rel_cons (h x List.mem_cons_self) (ih (rel_tail h) _)

def inv (m : Nat) (a : Nat × Nat) : Nat × Nat := (a.1 ^^^ m,a.2 ^^^ m)
def bin (c : Bool) (a b : Nat × Nat) : Nat × Nat :=
  if c then (a.1 &&& b.1,a.2 &&& b.2) else (a.1 ||| b.1,a.2 ||| b.2)

theorem rel_inv {f : Nat → Nat} {m a} (hn : ∀ x, f (x ^^^ m) = f x ^^^ m) (ha : a.2 = f a.1) :
    (inv m a).2 = f (inv m a).1 := by simp [inv,hn,ha]

theorem rel_bin {f : Nat → Nat} {a b} (hm : ∀ x y, f (x &&& y) = f x &&& f y)
    (hj : ∀ x y, f (x ||| y) = f x ||| f y) (ha : a.2 = f a.1) (hb : b.2 = f b.1)
    (c : Bool) : (bin c a b).2 = f (bin c a b).1 := by cases c <;> simp [bin,hm,hj,ha,hb]

theorem rel_kept {f : Nat → Nat} {a xs} (h : Rel f xs) (ha : a.2 = f a.1) (b : Bool) :
    Rel f (kept b a xs) := by
  cases b
  · exact h
  · exact rel_cons ha h

def move (m : Nat) (ws : List (Nat × Nat)) (tag : Nat) : List (Nat × Nat) :=
  if tag < 48 then
    let i := tag/4
    let a := ws.getD i (0,0)
    inv m a :: kept (tag%4 == 3) a (without i i 0 ws)
  else
    let q := (tag-48)/8
    let j := (List.range 16).foldl (fun old i => if i*(i+1)/2 ≤ q then i else old) 0
    let i := q-j*(j+1)/2
    let a := ws.getD i (0,0)
    let b := ws.getD j (0,0)
    bin ((tag-48)/4%2 == 1) a b ::
      kept ((tag-48)/2%2 == 1) a (kept ((tag-48)%2 == 1) b (without i j 0 ws))

theorem rel_move {f : Nat → Nat} {m ws} (h0 : f 0 = 0) (hn : ∀ x, f (x ^^^ m) = f x ^^^ m)
    (hm : ∀ x y, f (x &&& y) = f x &&& f y)
    (hj : ∀ x y, f (x ||| y) = f x ||| f y) (h : Rel f ws) (tag : Nat) :
    Rel f (move m ws tag) := by
  unfold move
  split
  · exact rel_cons (rel_inv hn (rel_getD h0 h _))
      (rel_kept (rel_without h _ _ _) (rel_getD h0 h _) _)
  · exact rel_cons (rel_bin hm hj (rel_getD h0 h _) (rel_getD h0 h _) _)
      (rel_kept (rel_kept (rel_without h _ _ _) (rel_getD h0 h _) _) (rel_getD h0 h _) _)

def insert (a : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [a]
  | b::bs => if a.1 ≤ b.1 then a::b::bs else b::insert a bs

theorem rel_insert {f : Nat → Nat} {a xs} (h : Rel f xs) (ha : a.2 = f a.1) : Rel f (insert a xs) := by
  induction xs with
  | nil => exact rel_cons ha (by simp [Rel])
  | cons b bs ih =>
    simp only [insert]
    split
    · exact rel_cons ha h
    · exact rel_cons (h b List.mem_cons_self) (ih (rel_tail h))

def sort (xs : List (Nat × Nat)) : List (Nat × Nat) := xs.foldr insert []

theorem rel_sort {f : Nat → Nat} {xs} (h : Rel f xs) : Rel f (sort xs) := by
  induction xs with
  | nil => simp [sort,Rel]
  | cons a xs ih => exact rel_insert (ih (rel_tail h)) (h a List.mem_cons_self)

def fromRoot (cap m : Nat) (root : List (Nat × Nat)) (records : Nat → Nat → Nat × Nat) :
    Nat → Nat → List (Nat × Nat)
  | 0,i => if i = 0 then root else []
  | d+1,i =>
    let r := records (cap-(d+1)) i
    sort (move m (fromRoot cap m root records d r.1) r.2)

theorem rel_fromRoot {f : Nat → Nat} {cap m root records} (h0 : f 0 = 0)
    (hn : ∀ x, f (x ^^^ m) = f x ^^^ m)
    (hm : ∀ x y, f (x &&& y) = f x &&& f y)
    (hj : ∀ x y, f (x ||| y) = f x ||| f y)
    (hroot : Rel f root) (d i : Nat) : Rel f (fromRoot cap m root records d i) := by
  induction d generalizing i with
  | zero => simp only [fromRoot]; split; exact hroot; simp [Rel]
  | succ d ih => exact rel_sort (rel_move h0 hn hm hj (ih _) _)

def state (cap m : Nat) (root : List (Nat × Nat)) (records : Nat → Nat → Nat × Nat)
    (s i : Nat) : List (Nat × Nat) :=
  if s ≤ cap then fromRoot cap m root records (cap-s) i else []

theorem rel_state {f : Nat → Nat} {cap m root records} (h0 : f 0 = 0)
    (hn : ∀ x, f (x ^^^ m) = f x ^^^ m)
    (hm : ∀ x y, f (x &&& y) = f x &&& f y)
    (hj : ∀ x y, f (x ||| y) = f x ||| f y)
    (hroot : Rel f root) (s i : Nat) : Rel f (state cap m root records s i) := by
  unfold state
  split
  · exact rel_fromRoot h0 hn hm hj hroot _ _
  · simp [Rel]

def guarded (child : List (Nat × Nat)) (ys : List Nat) : List Nat :=
  if ys.isPerm (child.map Prod.fst) then child.map Prod.snd else ys

theorem guarded_run {forbidden m y} {f : Nat → Nat} {child} (hc : Rel f child)
    (hf : ∀ {t ws}, RNatRun forbidden m y t ws → RNatRun forbidden m y t (ws.map f))
    {t ys} (h : RNatRun forbidden m y t ys) : RNatRun forbidden m y t (guarded child ys) := by
  unfold guarded
  split
  · rename_i hp
    have p := List.isPerm_iff.1 hp
    have he : (child.map Prod.fst).map f = child.map Prod.snd := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact (hc a ha).symm
    exact RRun.perm (by simpa only [he] using p.map f) (hf h)
  · exact h

def child (cap m : Nat) (root : List (Nat × Nat)) (records : Nat → Nat → Nat × Nat)
    (s i tag : Nat) : List (Nat × Nat) := move m (state cap m root records s i) tag

theorem child_rel {f : Nat → Nat} {cap m root records} (h0 : f 0 = 0)
    (hn : ∀ x, f (x ^^^ m) = f x ^^^ m)
    (hm : ∀ x y, f (x &&& y) = f x &&& f y)
    (hj : ∀ x y, f (x ||| y) = f x ||| f y)
    (hroot : Rel f root) (s i tag : Nat) : Rel f (child cap m root records s i tag) :=
  rel_move h0 hn hm hj (rel_state h0 hn hm hj hroot s i) tag

end PEqualNP.Outside.L_meta_982_aux.Finite.PairReplay
