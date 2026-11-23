import DynamicClosedTest
namespace PEqualNP.Outside.L_meta_670_aux.MemoProtocol

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
  | 0, _, e, m => .node (e :: entries m) (left m) (right m)
  | d+1, key, e, m =>
    if key%2 = 0 then .node (entries m) (insert d (key/2) e (left m)) (right m)
    else .node (entries m) (left m) (insert d (key/2) e (right m))

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
    refine ⟨?_,left_sound h,right_sound h⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact entries_sound h a ha
  | succ d ih =>
    simp only [insert]
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

def save (retain : Nat → Nat → List Sig → Bool)
    (k t : Nat) (v : List Sig) (m : Memo) : Memo :=
  if retain k t v then insert 12 (hash t v) ⟨k,t,v⟩ m else m

lemma save_sound (retain : Nat → Nat → List Sig → Bool)
    {k t : Nat} {v : List Sig} {m : Memo} (hm : Sound m) (hv : Impossible k t v) :
    Sound (save retain k t v m) := by
  unfold save
  split
  · exact insert_sound hm _ _ _ hv
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

end PEqualNP.Outside.L_meta_670_aux.MemoProtocol
namespace PEqualNP.Outside.L_meta_670_aux.MemoChildren

open LiveCheck

inductive Move where
  | unary (a : Sig)
  | binary (isOr : Bool) (a b : Sig)

def Move.value : Move → Sig
  | .unary a => neg a
  | .binary d a b => bin d a b

structure Proposal where
  nots : Nat
  wires : List Sig
  move : Move

def gateLists (k t : Nat) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : List (List Sig) :=
  if !(gateAvailable v g) then [] else
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    if base == top then [g::rest] else []
  else keep.filterMap fun h =>
    if decide (n+h.length+1 ≤ k-t+1) && (base ||| unionSep d h == top)
    then some (g::(h++rest)) else none

def unaryAt (k t : Nat) (v : List Sig) (c : Cov) (a : Sig) : List Proposal :=
  (gateLists k t v (dropped [a] v) (v.length-1)
    (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]).map
    (fun w => ⟨t,w,.unary a⟩)

def unaryMoves (k t : Nat) (v : List Sig) : List Proposal :=
  let c := coverage (decide (0<t)) v
  v.flatMap (unaryAt k t v c)

def fastBinary (t : Nat) (v : List Sig) (a b : Sig) (ua ub : B) : List Proposal :=
  let rest := dropped [a,b] v
  let use : Bool → List Proposal := fun d =>
    let g := bin d a b
    if gateAvailable v g then [⟨t,g::rest,Move.binary d a b⟩] else []
  (if (ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 then use false else []) ++
    (if (ua &&& b.2) == 0 && (ub &&& a.2) == 0 then use true else [])

def slowBinary (k t : Nat) (v : List Sig) (c : Cov) (a b : Sig) : List Proposal :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  (gateLists k t v rest (v.length-2) mask (bin false a b) (allowedKeeps a b)).map
      (fun w => ⟨t,w,.binary false a b⟩) ++
    (gateLists k t v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)).map
      (fun w => ⟨t,w,.binary true a b⟩)

def pairs {α β : Type} (f : α → α → List β) : List α → List β
  | [] => []
  | a :: xs => xs.flatMap (f a) ++ pairs f xs

def binaryMoves (k t : Nat) (v : List Sig) : List Proposal :=
  let c := coverage (decide (0<t)) v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a,c.2.1 &&& sep false a))
    pairs (fun a b => fastBinary t v a.1 b.1 a.2 b.2) acts
  else pairs (slowBinary k t v c) v

def proposals : Nat → Nat → List Sig → List Proposal
  | 0,_,_ => []
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then [] else
    if v == [target] then [] else
    (if 0<t then unaryMoves k (t-1) v else []) ++ binaryMoves k t v

end PEqualNP.Outside.L_meta_670_aux.MemoChildren
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open LiveCheck

def updateWithRecipe {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  fun i => updateOne (oracles i) v w (ctx i) r

lemma updateWithRecipe_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updateWithRecipe oracles v w ctx r) := by
  intro i
  simp only [updateWithRecipe, updateOne, compact]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
namespace PEqualNP.Outside.L_meta_670_aux.DynamicMemo

open LiveCheck DynamicLeaf

abbrev CheckedContext {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) :=
  {ctx : Context n // Valid oracles v ctx}

def cut {n : Nat} (oracles : Fin n → Oracle) (k _t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : Bool := pruned oracles k c.val

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) (hv : v.Nodup) (hc : cut oracles k t v c = true) :
    Impossible k t v := pruned_sound hsound hv c.property hc

def recipe : MemoChildren.Move → Recipe
  | .unary a => .unary a
  | .binary d a b => .binary d a b

def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : List (MemoProtocol.Child (CheckedContext oracles)) :=
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        (⟨updateWithRecipe oracles v p.wires c.val (some (recipe p.move)),
          @updateWithRecipe_valid n oracles v c.val c.property p.wires
            (some (recipe p.move))⟩ : CheckedContext oracles p.wires) })
    (MemoChildren.proposals k t v)

def initial {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    CheckedContext oracles v :=
  ⟨DynamicLeaf.initial oracles v programs,DynamicLeaf.initial_valid oracles v programs⟩

def run {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoProtocol.Memo :=
  MemoProtocol.solve (CheckedContext oracles) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (initial oracles v programs) .empty

def leafCheck {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(run oracles k t v programs).1

lemma leafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound) {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : leafCheck oracles k t v programs = true) : Impossible k t v := by
  have hs := MemoProtocol.solve_sound (CheckedContext oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound)
    k t v (initial oracles v programs) .empty (show MemoProtocol.Sound .empty from trivial)
  apply hs.2
  change (run oracles k t v programs).1 = false
  unfold leafCheck at hc
  cases h : (run oracles k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicMemo
