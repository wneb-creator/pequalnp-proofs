import Smoke
import Batteries.Tactic.OpenPrivate
export private
  PEqualNP.Outside.L_meta_670_aux.Base1007.sep_unary
  PEqualNP.Outside.L_meta_670_aux.Base1007.sep_binary
  PEqualNP.Outside.L_meta_670_aux.Base1007.sep_weaken
  PEqualNP.Outside.L_meta_670_aux.Base1007.mem_unionSep
  from SlimCompact1007

-- lower-bound/ProjectedCoverageBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.ProjectedCoverage

variable {p : LiveCheck.Sig → Base1007.Sig}
variable (pt : p LiveCheck.target = Base1007.target)
variable (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
variable (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))

include pt pn pb

lemma projected_sep {k t : Nat} {S : Finset LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (i : Nat) (hi : i < 252) :
    ∃ a ∈ S, (Base1007.sep (decide (0 < t)) (p a)).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨LiveCheck.target,by simp,?_⟩
    rw [pt]
    change (BitVec.allOnes 252 &&& ~~~(0 : Base1007.B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 252)] <;>
      simp [hi]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨x,hx,hs⟩ := ih
    simp only [Nat.zero_lt_succ,decide_true]
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      refine ⟨a,Finset.mem_insert_self _ _,?_⟩
      apply Base1007.sep_unary t (p a) i
      simpa only [pn] using hs
    · exact ⟨x,Finset.mem_insert_of_mem hx,Base1007.sep_weaken t (p x) i hi hs⟩
  | @binary k t U a b d ha hb hab hf tail ih =>
    obtain ⟨x,hx,hs⟩ := ih
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      have hs' : (Base1007.sep (decide (0 < t)) (Base1007.bin d (p a) (p b))).getLsbD i = true := by
        simpa only [pb] using hs
      rcases Base1007.sep_binary (decide (0 < t)) d (p a) (p b) i hs' with h | h
      · exact ⟨a,Finset.mem_insert_self _ _,h⟩
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),hs⟩

lemma projected_cover {k t : Nat} {S : Finset LiveCheck.Sig} {v : List LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (he : v.toFinset = S) :
    Base1007.unionSep (decide (0 < t)) (v.map p) = Base1007.top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,ha,hs⟩ := projected_sep pt pn pb h i hi
  have hm : p a ∈ v.map p := List.mem_map.mpr ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),rfl⟩
  simpa only [Base1007.top,BitVec.getLsbD_allOnes,hi,decide_true] using
    (Base1007.mem_unionSep _ _ _).2 ⟨p a,hm,hs⟩

lemma projected_xor_cover {k t : Nat} {S : Finset LiveCheck.Sig} {v : List LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (he : v.toFinset = S) :
    Base1007.unionSep true (v.map p) = Base1007.top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,ha,hs⟩ := projected_sep pt pn pb h i hi
  have hm : p a ∈ v.map p := List.mem_map.mpr ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),rfl⟩
  simpa only [Base1007.top,BitVec.getLsbD_allOnes,hi,decide_true] using
    (Base1007.mem_unionSep _ _ _).2 ⟨p a,hm,Base1007.sep_weaken t (p a) i hi hs⟩

lemma directed_failure {k t : Nat} {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hf : Base1007.unionSep (decide (0 < t)) ps ≠ Base1007.top) :
    LiveCheck.Impossible k t v := by
  intro m hm h
  apply hf
  rw [hp]
  exact projected_cover pt pn pb h rfl

lemma xor_failure {k t : Nat} {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hf : Base1007.unionSep true ps ≠ Base1007.top) :
    LiveCheck.Impossible k t v := by
  intro m hm h
  apply hf
  rw [hp]
  exact projected_xor_cover pt pn pb h rfl

end PEqualNP.Outside.L_meta_670_aux.ProjectedCoverage

-- toolchain/BoolNodupBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.BoolNodup

open LiveCheck

def check : List Sig → Bool
  | [] => true
  | a :: v => !(v.contains a) && check v

lemma check_eq_true (v : List Sig) : check v = true ↔ v.Nodup := by
  induction v with
  | nil => simp [check]
  | cons a v ih => simp [check,ih,List.nodup_cons]

lemma sound {v : List Sig} (h : check v = true) : v.Nodup :=
  (check_eq_true v).mp h

end PEqualNP.Outside.L_meta_670_aux.BoolNodup

-- lower-bound/MemoBoolFastBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.MemoBoolFast

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
  | d+1, key, m => bucket d (key/2) (if key % 2 = 0 then left m else right m)

def insert : Nat → Nat → Entry → Memo → Memo
  | 0, _, e, .empty => .node [e] .empty .empty
  | 0, _, e, .node es l r => .node (e :: es) l r
  | d+1, key, e, .empty =>
    if key % 2 = 0 then .node [] (insert d (key/2) e .empty) .empty
    else .node [] .empty (insert d (key/2) e .empty)
  | d+1, key, e, .node es l r =>
    if key % 2 = 0 then .node es (insert d (key/2) e l) r
    else .node es l (insert d (key/2) e r)

lemma insert_zero (key : Nat) (e : Entry) (m : Memo) :
    insert 0 key e m = .node (e :: entries m) (left m) (right m) := by
  cases m <;> rfl

lemma insert_succ (d key : Nat) (e : Entry) (m : Memo) :
    insert (d+1) key e m =
      if key % 2 = 0 then .node (entries m) (insert d (key/2) e (left m)) (right m)
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
    decide (k ≤ e.budget) && e.nots == t && v.isPerm e.wires

lemma hit_sound {k t : Nat} {v : List Sig} {m : Memo}
    (hm : Sound m) (hh : hit k t v m = true) : Impossible k t v := by
  obtain ⟨e,he,hgood⟩ := List.any_eq_true.mp hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.isPerm_iff] at hgood
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

end PEqualNP.Outside.L_meta_670_aux.MemoBoolFast

-- sat-proof/DynamicCoveredBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.DynamicCovered

open LiveCheck DynamicLeaf

abbrev CheckedContext {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) :=
  {ctx : Context n // Valid oracles v ctx}

def cut {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : Bool :=
  ((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (c.val i).vals == Base1007.top)) ||
      pruned oracles k c.val

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (k t : Nat) (v : List Sig) (c : CheckedContext oracles v)
    (hv : v.Nodup) (hc : cut oracles k t v c = true) : Impossible k t v := by
  rcases Bool.or_eq_true_iff.mp hc with hcover | hprefix
  · obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hcover
    have hf : Base1007.unionSep (decide (0<t)) (c.val i).vals ≠ Base1007.top := by
      intro he
      simp only [he,beq_self_eq_true,Bool.not_true,Bool.false_eq_true] at hbad
    exact ProjectedCoverage.directed_failure (htarget i) (oracles i).mapNeg
      (oracles i).mapBin (c.property i) hf
  · exact pruned_sound hsound hv c.property hprefix

def recipe : MemoChildren.Move → Recipe
  | .unary a => .unary a
  | .binary d a b => .binary d a b

end PEqualNP.Outside.L_meta_670_aux.DynamicCovered

-- toolchain/StrictPrefixBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.StrictPrefix

open LiveCheck DynamicLeaf PEqualNP.CircuitLowerBounds

def rootOf (v : List Sig) (roots : List Nat) (a : Sig) : Nat :=
  roots.getD (v.idxOf a) 8

def recipeGate (v : List Sig) (roots : List Nat) : Recipe → Gate
  | .unary a => ⟨.not,[rootOf v roots a]⟩
  | .binary d a b => ⟨if d then .or else .and,[rootOf v roots a,rootOf v roots b]⟩

def traceWire (gs : List Gate) : Nat → Nat → List Nat → List Gate →
    Nat × List Nat × List Gate
  | 0, _, seen, out => (8,seen,out)
  | fuel+1, j, seen, out =>
      MemoBoolFast.forceNat j fun j =>
        if j < 10 then (j,seen,out)
        else if seen.contains j then
          MemoBoolFast.forceNat (10+seen.idxOf j) fun index => (index,seen,out)
        else
          match gs.getD (j-10) ⟨.or,[]⟩ with
          | ⟨op,inputs⟩ =>
              match inputs.foldl (fun (s : List Nat × List Nat × List Gate) a =>
                  match s with
                  | (roots,seen,out) =>
                      match traceWire gs fuel a seen out with
                      | (index,seen,out) =>
                          MemoBoolFast.forceNat index fun index =>
                            (roots ++ [index],seen,out)) ([],seen,out) with
              | (roots,seen,out) =>
                  MemoBoolFast.forceNat (10+out.length) fun index =>
                    (index,seen ++ [j],out ++ [⟨op,roots⟩])

def compactParts (gates : List Gate) (roots : List Nat) : List Gate × List Nat :=
  match roots.foldl (fun (s : List Nat × List Nat × List Gate) j =>
      match s with
      | (roots,seen,out) =>
          match traceWire gates (gates.length+1) j seen out with
          | (index,seen,out) =>
              MemoBoolFast.forceNat index fun index =>
                (roots ++ [index],seen,out)) ([],[],[]) with
  | (roots,_,out) => (out,roots)

def compact : PrefixCtx → PrefixCtx
  | ⟨gates,roots,vals⟩ =>
      let parts := compactParts gates roots
      ⟨parts.1,parts.2,vals⟩

lemma compact_vals (c : PrefixCtx) : (compact c).vals = c.vals := by
  cases c
  rfl

def updateOne (o : Oracle) (v w : List Sig) : PrefixCtx → Option Recipe → PrefixCtx
  | ⟨gates,roots,vals⟩, r =>
      let z := w.headD zero
      let q := proposedValue o v vals z r
      let old := vals.idxOf q
      let cached := vals.contains q
      let free := o.inputs.contains q
      let fresh := !(free || cached)
      let g := match r with
        | some a => recipeGate v roots a
        | none => ⟨.or,[]⟩
      let out := if free then o.inputs.idxOf q
        else if cached then roots.getD old 8 else 10+gates.length
      compact ⟨if fresh then gates ++ [g] else gates,
        w.map (fun a => if a == z then out else rootOf v roots a),
        w.map (fun a => if a == z then q else retrieve o.project v vals a)⟩

lemma updateOne_vals (o : Oracle) (v w : List Sig) (c : PrefixCtx) (r : Option Recipe) :
    (updateOne o v w c r).vals =
      w.map (fun a => if a == w.headD zero then
        proposedValue o v c.vals (w.headD zero) r else retrieve o.project v c.vals a) := by
  cases c
  rfl

def updateWithRecipe {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  fun i => updateOne (oracles i) v w (ctx i) r

lemma updateWithRecipe_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updateWithRecipe oracles v w ctx r) := by
  intro i
  simp only [updateWithRecipe,updateOne_vals]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

end PEqualNP.Outside.L_meta_670_aux.StrictPrefix

-- replay/MetadataReplayBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.MetadataReplay

open LiveCheck

structure Edge where
  nots : Nat
  wires : List Sig
  hint : Sig → Nat
  cut : Bool

structure Config where
  limit : Nat
  count : Nat → Nat → Nat
  state : Nat → Nat → Nat → List Sig
  enabled : Nat → Nat → Nat → Bool
  transport : (Sig → Nat) → Fin 12 → List Sig → List Sig
  lookup : (Sig → Nat) → Nat → Nat → List Sig → Nat × Fin 12
  terminal : Nat → Nat → Nat → List Sig → Bool
  edges : Nat → Nat → Nat → List Edge

structure Valid (c : Config) : Prop where
  transport : ∀ hint g k t w z, (c.transport hint g w).Perm z →
    Impossible k t z → Impossible k t w
  terminal : ∀ k t j v, c.terminal k t j v = true → Impossible k t v
  cuts : ∀ k t j e, e ∈ c.edges (k+1) t j →
    e.cut = true → Impossible k e.nots e.wires

def linkCheck (c : Config) (hint : Sig → Nat) (k t : Nat) (w : List Sig) : Bool :=
  let found := c.lookup hint k t w
  decide (found.1 < c.count k t) && c.enabled k t found.1 &&
    (c.transport hint found.2 w).isPerm (c.state k t found.1)

lemma linkCheck_sound (c : Config) (hc : Valid c)
    {hint : Sig → Nat} {k t : Nat} {w : List Sig}
    (known : ∀ j < c.count k t, c.enabled k t j = true → Impossible k t (c.state k t j))
    (h : linkCheck c hint k t w = true) : Impossible k t w := by
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at h
  exact hc.transport hint (c.lookup hint k t w).2 k t w _ h.2
    (known _ h.1.1 h.1.2)

def edgeCheck (c : Config) (k : Nat) (e : Edge) : Bool :=
  e.cut || (decide (e.nots ≤ c.limit) && linkCheck c e.hint k e.nots e.wires)

lemma edgeCheck_sound (c : Config) (hc : Valid c) {k : Nat} {e : Edge}
    (known : ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j))
    (cutSound : e.cut = true → Impossible k e.nots e.wires)
    (h : edgeCheck c k e = true) : Impossible k e.nots e.wires := by
  simp only [edgeCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨ht,hl⟩
  · exact cutSound h
  · exact linkCheck_sound c hc (known e.nots ht) hl

def fill (c : Config) (k : Nat) : List Edge → MemoBoolFast.Memo → MemoBoolFast.Memo
  | [], m => m
  | e :: es, m => fill c k es
      (if edgeCheck c k e then MemoBoolFast.save (fun _ _ _ => true) k e.nots e.wires m else m)

lemma fill_sound (c : Config) (hc : Valid c) {k : Nat}
    (known : ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j))
    (es : List Edge)
    (cutSound : ∀ e ∈ es, e.cut = true → Impossible k e.nots e.wires)
    {m : MemoBoolFast.Memo} (hm : MemoBoolFast.Sound m) :
    MemoBoolFast.Sound (fill c k es m) := by
  induction es generalizing m with
  | nil => exact hm
  | cons e es ih =>
    apply ih (fun a ha => cutSound a (List.mem_cons_of_mem e ha))
    split
    · rename_i he
      exact MemoBoolFast.save_sound _ hm
        (edgeCheck_sound c hc known (cutSound e (List.mem_cons_self)) he)
    · exact hm

def nodeCheck (c : Config) (k t j : Nat) : Bool :=
  let v := c.state k t j
  !(c.enabled k t j) || c.terminal k t j v || (BoolNodup.check v &&
    match k with
    | 0 => !(search 0 t v)
    | k+1 =>
      let m := fill c k (c.edges (k+1) t j) .empty
      !(stepTest k t v (fun w => MemoBoolFast.answer k (t-1) w m)
        (fun w => MemoBoolFast.answer k t w m)))

lemma nodeCheck_zero_sound (c : Config) (hc : Valid c) {t j : Nat}
    (he : c.enabled 0 t j = true) (h : nodeCheck c 0 t j = true) :
    Impossible 0 t (c.state 0 t j) := by
  simp only [nodeCheck,he,Bool.not_true,Bool.false_or,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true'] at h
  rcases h with ht | ⟨hn,hs⟩
  · exact hc.terminal 0 t j _ ht
  · exact exclude_search (BoolNodup.sound hn) hs

lemma nodeCheck_succ_sound (c : Config) (hc : Valid c) {k t j : Nat}
    (known : ∀ u ≤ c.limit, ∀ i < c.count k u,
      c.enabled k u i = true → Impossible k u (c.state k u i))
    (he : c.enabled (k+1) t j = true) (h : nodeCheck c (k+1) t j = true) :
    Impossible (k+1) t (c.state (k+1) t j) := by
  simp only [nodeCheck,he,Bool.not_true,Bool.false_or,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true'] at h
  rcases h with ht | ⟨hn,hs⟩
  · exact hc.terminal (k+1) t j _ ht
  · have hm : MemoBoolFast.Sound (fill c k (c.edges (k+1) t j) .empty) :=
      fill_sound c hc known _ (hc.cuts k t j) trivial
    apply exclude_step (BoolNodup.sound hn) _ _ hs
    · intro w hw
      exact MemoBoolFast.answer_false hm hw
    · intro w hw
      exact MemoBoolFast.answer_false hm hw

lemma levels_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      nodeCheck c k t j = true) :
    ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j) := by
  intro k
  induction k with
  | zero =>
    intro hk t ht j hj he
    exact nodeCheck_zero_sound c hc he (checks 0 hk t ht j hj)
  | succ k ih =>
    intro hk t ht j hj he
    exact nodeCheck_succ_sound c hc (ih (by omega)) he (checks (k+1) hk t ht j hj)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, start => f start && span f n (start+1)

lemma span_point {f : Nat → Bool} {n start j : Nat}
    (h : span f n start = true) (hs : start ≤ j) (hj : j < start+n) : f j = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h
    by_cases he : j = start
    · simpa only [he] using h.1
    · exact ih h.2 (by omega) (by omega)

lemma span_join {f : Nat → Bool} {a b start : Nat}
    (h₁ : span f a start = true) (h₂ : span f b (start+a) = true) :
    span f (a+b) start = true := by
  induction a generalizing start with
  | zero => simpa only [Nat.zero_add,Nat.add_zero] using h₂
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at h₁
    rw [Nat.succ_add,span,Bool.and_eq_true]
    refine ⟨h₁.1,ih h₁.2 ?_⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₂

lemma span_of_points {f : Nat → Bool} {n start : Nat}
    (h : ∀ j, start ≤ j → j < start+n → f j = true) : span f n start = true := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [span,Bool.and_eq_true]
    exact ⟨h start (by omega) (by omega),ih (fun j hj hjn => h j (by omega) (by omega))⟩

lemma span_of_fin {f : Nat → Bool} {n start : Nat}
    (h : ∀ i : Fin n, f (start+i.val) = true) : span f n start = true := by
  apply span_of_points
  intro j hj hjn
  have hi : j-start < n := by omega
  have he : start+(j-start) = j := by omega
  simpa only [he] using h ⟨j-start,hi⟩

def levelCheck (c : Config) (k t : Nat) : Bool :=
  span (nodeCheck c k t) (c.count k t) 0

def enabledNodes (c : Config) (k t : Nat) : List Nat :=
  (List.range (c.count k t)).filter (c.enabled k t)

lemma levelCheck_of_enabled (c : Config) {k t : Nat}
    (checks : ∀ j ∈ enabledNodes c k t, nodeCheck c k t j = true) :
    levelCheck c k t = true := by
  apply span_of_points
  intro j hj hjn
  by_cases he : c.enabled k t j = true
  · apply checks
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),he⟩
  · have hf : c.enabled k t j = false := by cases h : c.enabled k t j <;> simp_all
    simp only [nodeCheck,hf,Bool.not_false,Bool.true_or]

lemma levelCheck_of_list (c : Config) {k t : Nat} (nodes : List Nat)
    (enumeration : enabledNodes c k t = nodes)
    (checks : ∀ i : Fin nodes.length, nodeCheck c k t nodes[i.val] = true) :
    levelCheck c k t = true := by
  apply levelCheck_of_enabled
  intro j hj
  rw [enumeration] at hj
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hj
  simpa only [he] using checks ⟨i,hi⟩

lemma checked_levels_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, levelCheck c k t = true) :
    ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j) := by
  apply levels_sound c hc budget
  intro k hk t ht j hj
  exact span_point (checks k hk t ht) (Nat.zero_le j) (by omega)

lemma checked_link_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, levelCheck c k t = true)
    {hint : Sig → Nat} {k t : Nat} {w : List Sig} (hk : k ≤ budget) (ht : t ≤ c.limit)
    (h : linkCheck c hint k t w = true) : Impossible k t w := by
  exact linkCheck_sound c hc (checked_levels_sound c hc budget checks k hk t ht) h

end PEqualNP.Outside.L_meta_670_aux.MetadataReplay

-- replay/MetadataStrictEdgesBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.MetadataStrictEdges

open LiveCheck DynamicLeaf

def codeLength : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, code => if code = 0 then 0 else 1+codeLength fuel (code >>> 4)

def appendCode (a b : Nat) : Nat := a + (b <<< (4*codeLength 31 a))

def moveCode (hint : Sig → Nat) : MemoChildren.Move → Nat
  | .unary a => appendCode (hint a) 10
  | .binary d a b => appendCode (appendCode (hint a) (hint b)) (if d then 12 else 11)

def childHint (hint : Sig → Nat) (p : MemoChildren.Proposal) (a : Sig) : Nat :=
  if a == p.move.value then moveCode hint p.move else hint a

def listHint (v : List Sig) (codes : List Nat) (a : Sig) : Nat :=
  codes.getD (v.idxOf a) 0

def childContext {n : Nat} (oracles : Fin n → Oracle) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal) :
    DynamicCovered.CheckedContext oracles p.wires :=
  ⟨StrictPrefix.updateWithRecipe oracles v p.wires c.val (some (DynamicCovered.recipe p.move)),
    @StrictPrefix.updateWithRecipe_valid n oracles v c.val c.property p.wires
      (some (DynamicCovered.recipe p.move))⟩

def edge {n : Nat} (oracles : Fin n → Oracle) (hint : Sig → Nat) (k : Nat)
    {v : List Sig} (c : DynamicCovered.CheckedContext oracles v)
    (p : MemoChildren.Proposal) : MetadataReplay.Edge :=
  ⟨p.nots,p.wires,childHint hint p,
    BoolNodup.check p.wires && DynamicCovered.cut oracles k p.nots p.wires
      (childContext oracles c p)⟩

lemma edge_cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (hint : Sig → Nat) (k : Nat) {v : List Sig}
    (c : DynamicCovered.CheckedContext oracles v) (p : MemoChildren.Proposal)
    (h : (edge oracles hint k c p).cut = true) : Impossible k p.nots p.wires := by
  simp only [edge,Bool.and_eq_true] at h
  exact DynamicCovered.cut_sound oracles hsound htarget k p.nots p.wires
    (childContext oracles c p) (BoolNodup.sound h.1) h.2

def edges {n : Nat} (oracles : Fin n → Oracle)
    (state : Nat → Nat → Nat → List Sig)
    (initial : (k t j : Nat) → DynamicCovered.CheckedContext oracles (state k t j))
    (hint : Nat → Nat → Nat → Sig → Nat) : Nat → Nat → Nat → List MetadataReplay.Edge
  | 0,_,_ => []
  | k+1,t,j =>
    (MemoChildren.proposals (k+1) t (state (k+1) t j)).map
      (edge oracles (hint (k+1) t j) k (initial (k+1) t j))

lemma edges_cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (state : Nat → Nat → Nat → List Sig)
    (initial : (k t j : Nat) → DynamicCovered.CheckedContext oracles (state k t j))
    (hint : Nat → Nat → Nat → Sig → Nat)
    (k t j : Nat) (e : MetadataReplay.Edge)
    (he : e ∈ edges oracles state initial hint (k+1) t j)
    (h : e.cut = true) : Impossible k e.nots e.wires := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  exact edge_cut_sound oracles hsound htarget _ _ _ p h

end PEqualNP.Outside.L_meta_670_aux.MetadataStrictEdges

-- status-review/Cut12CodecBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.Cut12Data

def wireCount : Nat := 555
def rowCount : Nat := 4734
def groupCount : Nat := 98

def recipeBits : Nat := 0xcc97c21cc97b31cc95c31cc95c21cc94c21cc94b21cc93c71cc93c21cc93b21cc92b41cc92b31cc91c43cc87c91cc87c61cc87c51cc87c41cc87c31cc87c21cc87b41cc85c31cc85c21cc84c21cc84b21cc83b21cc82b41cc81c43cc81c32cc76c21cc75c91cc75c61cc75c41cc75c31cc75c21cc74c61cc74c21cc74b31cc73c61cc73c21cc73b41cc72b41cc72b31cc71c96cc71c94cc71c43cc65c21cc64c21cc64b31cc64b21cc63b21cc62b41cc54c21cc53c61cc53c21cc51c43cc43c61cc43c21cc43b21cc42b31cc32c61cbc7169cbc7165cbc7164cbc7163cbc7162cbc7149cbc7148cbc7146cbc7143cbc7142cbc7139cbc7136cbc7135cbc7134cbc7132cbc4129cbc4128cbc4126cbc4125cbc4123cbc3195cbc3194cbc3192cbc3149cbc3148cbc3147cbc3146cbc3142cbc3129cbc3127cbc3125cbc3124cbc2149cbc2148cbc2147cbc2146cbc2143cbc2139cbc2137cbc2136cbc2135cbc2134cb94b21cb93c21cb93b21cb92c31cb92b41cb92b31cb64b31cb63c21cb63b21cb43b21cb42b31cb41c32cb31c94bcc9716bcc9714bcc9713bcc9314bcc9312bcc7184bcc6174bcc6173bcc5176bcc5173bcc5139bcc5136bcc5132bcc4319bcc4316bcc4315bcc4312bcc4176bcc4175bcc4173bcc4152bcc3176bcc3174bcc3172bcc2184bcc2176bcc2174bcc2173bcc2159bcc2156bcc2153bcc2149bcc2146bcc2145bcc2143bcc2139bcc2136bcc2134bcb4173bcb4172bcb4129bcb4126bcb4123bcb3194bcb3192bcb3174bcb3149bcb3146bcb3142bcb3129bcb3124bcb2184bcb2183bcb2149bcb2146bcb2143bcb2139bcb2136bcb2134bc95c71bc95c31bc94c21bc93c21bc92c41bc92c31bc84c71bc84c31bc84c21bc82c71bc82c41bc74c31bc74c21bc73c21bc64c31bc63c21bc53c71bc53c21bc52c71bc52c41bc52c31bc43c21bc42c310cba1470cba1430cba1420cba1390cba1370cba1360cba1350cba1340cba1320cba1290cba1280cba1260cba1240cba1230cac7190cac7180cac7160cac7150cac7140cac7130cac7120cac4170cac4150cac4120cac3190cac3170cac3150cac3140cac3120cac2180cac2150cac2140cac2130bac7160bac7140bac7130bac4120bac3190bac3140bac3120bac2140bac2130ba9c310ba6c710ba5c410ba4c710ba4c310ba4c210ba3c710ba3c210ba2c410ba2c310acc9710acc9310acc7580acc7180acc6170acc5170acc5130acc4310acc4170acc4150acc3170acc2180acc2170acc2150acc2140acc2130acb4170acb4120acb3190acb3170acb3140acb3120acb2180acb2140acb21300cc98500cc97500cc97300cc97100cc96500cc96300cc96100cc94800cc94700cc94600cc94500cc94300cc94200cc94100cc93500cc93100cc92800cc92700cc92500cc91800cc86400cc86200cc84700cc83900cc83700cc83500cc83100cc82500cc75800cc73500cc72800cc72600cc72500cc72400cc71800cc65700cc64700cc64200cc63800cc63700cc63500cc62500cc61800cc61700cc61400cc61300cc61200cc54800cc54700cc54600cc54200cc51800cc51700cc51300cc43800cc43700cc43600cc43500cc43200cc43100cc42800cc41800cc41700cc41500cc32900cc32800cc32700cc32500cc31700cc21900cc21800cc21700cc21500cc21400cc21300cb94100cb93600cb93500cb93400cb93200cb93100cb92800cb92500cb92400cb92300cb92100cb64700cb64200cb63500cb63400cb63100cb62100cb61700cb43700cb43600cb43200cb43100cb42600cb42100cb41900cb41800cb41700cb41600cb41300cb41200cb32100cb31900cb31700cb31600cb31400cb31200cb21900cb21800cb21700cb21600cb21500cb21400cb21300bc95600bc95200bc94300bc93600bc93400bc92700bc92400bc92300bc91600bc91400bc91300bc91200bc84900bc84200bc82900bc82400bc81900bc81400bc81200bc76100bc74600bc74300bc74100bc73600bc73400bc71600bc71400bc71300bc64900bc64200bc63800bc63400bc61300bc61200bc53900bc53600bc52900bc52600bc52300bc43900bc43600bc42900bc42600bc41900bc41600bc41500bc41300bc41200bc31900bc31600bc31400bc31200bc21900bc21600bc21400bc213000ba94000ba92000ba64000ba63000ba49000ba46000ba43000ba42000ba41000ba39000ba36000ba34000ba32000ba31000ba29000ba26000ba24000ba23000ba21000ba14000ba13000ba12000ac95000ac94000ac93000ac92000ac91000ac84000ac82000ac81000ac76000ac74000ac73000ac71000ac64000ac63000ac53000ac52000ac43000ac42000ac41000ac31000ac210000c980000c970000c960000c950000c940000c930000c920000c910000c870000c860000c850000c840000c830000c820000c810000c760000c750000c740000c730000c720000c710000c650000c640000c630000c620000c610000c540000c530000c520000c510000c430000c420000c410000c320000c310000c210000b960000b940000b930000b920000b640000b630000b430000b420000b410000b310000b2100000a900000a800000a700000a600000a500000a400000a300000a200000a1000000900000080000007000000600000050000004000000300000020000001
def groupBits : Nat := 0xad60a7ff8b3f5dff863aabff853aa1ff7b3187fe792f9dfe782f93fe742baffd722a9dfd702977fc6f295dfc6b25dffb69247dfb68246bfb662317fa6522f5fa6422d7f96322bff85f1ec7f75d1d25f75c1d13f75b1c37f65a1c1df6591bf7f5581bdff4571bbff3561badf3551ba7f2511847ef4f16bdef4e169bef4d165fee4c164dee4b1627ed4a161fec491607eb4815fdeb4715f7ea4615d7e74515cde74415c7e6411377df4012e5df3f1297de3e1277dd3d1247db3c123ddb3b1227d73a121dd739120fcf381205cf340e27bf320c85bf310c73bf300be7be2f0bddbe2e0b9fbd2d0b95bd2c0b6fbb2b0b65bb2a0b57ba290b2fb7280b1fb6270ad7af260acdaf250ac7ae240abf9f2107ef7f1f06b57f1e06a37f1d063f7e1c061f7d1b060f7c1a05e77b1905d57b1805b7771705a5771605876f15057d6f1405775f1305473f12053d3f1105373e10052f2f0d0236ff0c015cff0b0106fe0a00c6fd090096fb08008cfb07007efa060056f705004cf7040036ef03002cef020026df01000ebf0000067f
def offsetBits : Nat := 0xd847d789d53ad300d0aece5acc06c9c8c785c59bc3b1c212c028be42bc60baa5b8d4b713b556b3c3b222b069af19ad88ac41ab04a9d8a843a669a4b4a2f1a16f9ffe9e929d079b869a65995c98369727962e953a941c9302920d911c8ffc8efd8e0d8d068be68ae689f689948856872085e284ae8367820b80b57f867e487d097be27aa07989787177577660755a747e73ca7307724471b370886f8c6e906d876c886bb46b046a4c698868cf682467f3679a674c66f466666660660a63d561f45fdf5e135cc15b8d5a625933581856bc556e555f531d51274fd14e8d4e6d4cd74c694ab34a864944472145c9448243c74254423d41593fae3f6e3f2b3ef73c9e3ad7398f3853372835d435bd33e333b63357332232df32bf32a131952f632d962c452b4e29fa29d22949292128be28a028682851283327f027d927bb26ea24e12382228b21ec21a9214d213620fe20e720bc20a51ea71c6b1b1519b8188e1755173e161d16061594157d152c151514eb149a147013d613bf13a11383118f10120ec70e510cd20cbb0bf90bb60b8c0b3c0b1a0ad60ab40a710a5a0a3c09e009c909ab098d073b05a9045c02ef024401cc016b0154012a00db00c4008d00760058001e0000
def chunkBits : Nat := 0x1f2493749e468058107a12a76b2c00088ff2005f4320efea18b62f8f0006812999a28000008eca002f02100eff9426bd49d1ea213deb08300ebcb101009c3b18710005947e96e1c8ea4008b98fd312c99bddee4e80c06402b60c0950000485b06f9402880fe7a1fea3fa0bd3831d713472eea957eebacd63ac98e5c3ef82813c430000580683ce1380e80c4e000d4e87253171f2a01ac96c236a0e4101f401c005839400cd1f51a60b946a01c85f7f2a2eee12e0034093c098800012650073e20fe9b4d1961db8a3465b826a000b04ca000d4e221e457d022e0008095f66fe1cb8030c00092e49ff31d9bd71f0603167cbcb0492ad000327bf141431abccab109f7690b3a00010031000004b02000b095a9f4a3e164c23bfb4252cd3ab8a6ac68cb9f1ad048af25ac908ad7f2b484abdaaac24acbeaa59ed060382d33258b87be002d27bdcb7e717ad800d08a67e0f037f22defeb7a82dd6c3728edc3db00046c4ac00133d2bc0011923300005fecd735b00000c636aff1850c56e312d2c3fab0cb4c2e1379eeb784109301d8ffa43f9cdf8d8fb297d13be169ecd4f65379983ce9de2a2f0247754a0d521aff64e9afdad6a16aab35031a586d332681a33bb99bc8cc65659132781913ec7985e5293d8c4e261d2b00f9825cbff460392f6f97898bb165d0d2e2b4071a56ff6dce63ea6bd295baaa5bb545ea93e80016a24052250003541909ecf4ee82728800049b89000005ba5fc0654502ee87b901e228001412d50603ef90c026b04ba721a07f01f97200f1400001e808004400040004000003800100008c578034b1c78028a027a06ded1767ec000000a21f5e00400000091d0de26579321e026002839c0035e00a0e0d6946d9ac4b80910000107039802203cc0630001d4e703284da0700972b4560fa800074ffe0004b2fe003742ff32000e48fe6be56f5e0043adea732886278f642d6400800f747fcb44f2010b001f4eff9230a6c48b9c2e0930004336000597d70990000d7e380340000029ac970040004005b26ae00003b0004000169170053382e0055badc1c0cf80a181a2b7de9a256b670709a128d65e06c30856003913ff05a0a7b8020072b77f8f800dffffc0405801c5e3fc020036d9ff02014cf81495bfbee607b59975001761ff4887e9bf8be1de01610006020020006c867f080012468a001ad6ff8a7045000d32dfc5000d1b1fc2800d1d5ff53a800cfb9fc0800ca13fc00001609fce1e82779ac4bad86f87e7206bc453c0ac150440010004000040000234741f66bf592c7301102205703180027e2004345fe4e587d07406b2c3abab207801b01b012802c02b3f9b276fc52060070014813204604f80e009a02e0150059ed2f8068000502fc0002bcffe25f0f90252171fa6b181b0711e4361fc72051b40a81270011d30e9e4b2338b89bb9201480fe07283c809006507d811800e002001a5c5f00a142a79df0040000078c0cd1c85af80167bff94e194002cc1ff002caa7f00043d7f0001f57f1dc006c0bfeb7778003923fdceaa14d82bd71a6b24d43994320a0023060f5e809996801501838101800a8d3fc0228401000085dfc001187fc006d9bfc00231dfeca3401b834012db889cdc60094e70bc637a5d19a4a87c7f390336c27429e1000160381040000c600000a00001c0041bc0c60000221b4ecd7fec53b80bc1b61cc31c585b8e185a05800a8d7fc10010160029977f0028f97f001be0b802d726240057c1fcfe70bebd7ff13fc0d2542f1ec0d0740d118280349a242a919400c238141cbd953b16c00003e2fe57e0038d8fe27000714ff6a13d02afa993a39133e3fb71d49429edd6c63140038d8ff517f080c4603ec0b0700d13c25090461885906c7c0a8245d0c6314002bdffe7f1f9f97cc461be5252145e24cd81e938e0e540d38c388047810035b86c6b72a30fc57001c9dff0006777f21f8967d41de418281a4c1be0841410262f800e4eff80031ebfe6f4f81ac1174256a932b1684952034244f8e0b8c4c13beac016104c2c10a104001b8e7f83f6bf43f00068c7fc36688077024c57af40739602900a13751a06bc08c08d5e01783c7b416cb4f6414ec8e10401b557fe015b03fe018b2ffe013466fe007644fe018903fe0281dffe404907ceb5bd1278c6c029736c028b68f8052775805a5fdc63300041bb7a76fa0c0000146816ca2c00801655e6a46c0008a8c0340003da6d26f004300bfcd00248e5e014004327fe014301ec281f9c81af12e10040010000100002b072073080a03b8000038008549d7897100180100700096051895e3a402965ce014d0661e1ea2d0e05872002a7f400522687ba76d91d402919cc1e20142b8164a3fa06300008f476081103cc0c60003006983ac73e210443cc320ab7d2cb88060020046e83324879741587d33a0d83082b02000492a2c78d62f01b04a02c0aca016e950003923fdceaf9ef5c11feb880bf0c382060007837f35e2b92eb7ac6fe561ee104bf890007a07fa892ebf300a817be150c380038a7fe04d78cb0cd2e2a161d6000ceefee9e02e31690cb1988f1812c040a04040006cd7fd83809a9706449304128d64f8384c0940100200a6c27f06a2afacdf050ccf80409000207c002dbe0d0000a6a5e080080b4e9e90068008007dde020000121d580ab31200880040020000700100003d814ed9029762702454f7002ca1ae9029a10db0ee5001ee11139b8c004835f40aae556fa9c4a904478b6612b0307040147762c012ab2a524e1c00de83206627c386c6b72a2c0850012fca945505fca00f05402c8840201db00d8c006809027c44005412fab2505232d002d7b8006c5c05542c00a8409192fc0a66288ca83938016f66f4af59a56c048899027af86edd5497b1f141d3945c494a9618d519166df460028bf80e74d6a927732a44ac013528522f1b6189014890aef0b4ee612df328012d818c22aa798426a48b3dd9ab5808b0802f9504b01ae1a94316b6011280118f8cff7457ec024c228040200000663ff6036b829b6580290001217f02b58101b7ca003cf75c0b3142cb00540000f7ff012200295810bc70c31ebe024007829d0870181003000d88c2d453e5e4480a4638c632fcbe544c45ac104d48be26a1328a991e140061ae47588b6824888b552028b4e6c18467480b7867e2c05b00889a304a002bc97cea56b000a8e1008c08000110ff70b81665850b00a92bf801baca538a16cd88cc00233a55e3832a4128160150e142010d63380fbc386cbab6e0151812048bca18003bfcb3d8de8bc2250bb094443ac0e04e8cfd01b0c88742380402024f9400333c33575953f65f1616015031c0de8e188ccd6cb806200a921e3c6d65cb56300049d5758ac68066f8e08183041410266f8471e10248080001fdfe01110715222cc254300023eaa1c8584ccc07040c1820a08122688804a9c604042ada08f10a84815830001348088cc35bfaed43096b0c505385d6f0adc483c13c82004467d740280000000213a5264f3533af2a9e3ac70426fa005db2b5ba13400d8008be8217ec42e0dc003c77f0a2270c666c95101672c7be1a18787e6eebc56bb023a955560869022404fcc1b78ab847b7fa0af2ca2dab09fa74825304f1200549e052978c007132041818e593244383203f14408e026c605f149f8520478031bf2e09edc1005b4fe77b0252a4105f472cf02f67c5fd33b8ae2000ad06044cf639201294002801238ade7166ec016a77505400c080204ba80225bc85b59e478de2785e077dde775dc76dda765d875de2755d474dd274dd050d2bef39cd731cb729c9641e338ce2386e1382e037edf37ade2ecdc56d38d5f6201004fde212f4ad2b46d112ab7766d3766094df22c8320c7234e311474688b8561185609826097f5f97e5f17d3e1bc2eebbaeaba3b44a1b85859e727499d52665519b566218d965465d51866264965905664555905862d658b5461873dbc83a930ec0c1adb0abeecb0404f77f9d2f674b99d2d674b19d2b674a99d306888da222688899ccde33ed18f3463ad18e34638d18d34632d18c3461cdd372dfb70db36adab66eab46f03de35cceb3961029dab669c96b6395b94a47a8e1d48aa178cb916ca72e92846b41aa35f6337397a099c726e2c000a6998659966519465591655c731cd904040482812380001e8e868000429fe2825f8f7219c834a5905fc851014ea02d2208007060401252e5b270448060e0bc70001757f10038730f161338ad9ee0ab1cc60004140830495cb02c5c100c9ee72c00ea7f057394484090a30ddef20f87418000c04004119c52fa297d148afa5c4828124001e8e87182dab10b6298e322389e098504608104371f81e7e075ff5fadf800352843b0bad867421c8145e0b6d0968208102811608207040c8b9aebb94f9f8800d20025a8c028728da1a615ac80e50114104af16bb3cc7184016d6f83d10ac2a019eff223c041458b3fa11812898900803c000187f807e4c048054103140b990005fdb50a00008840204004c0023c00a402f822008275809480008212a027f4d4a02008620845108427f0c4a1104d25828234e09b24005dff500055fcaa6d4226290601000b0477628dd828a355fb1d66bc451d2c188b856ad91454d87c73dd30a3c8c131c398230e85e56de615319e11014410011dfea042214054779041603da5b0e41433c4041080e1c10358882820810182314500442b008860c386bc6221c1927982f6d28050c38428410ae30052c618908101bc3fc0ebd0debd01fa01c7ffb5f0fca0b7e89c006a36a43b51a2636c008e375237c8d01f07fb567e54d212407102e9409d804b7c28d8fd400080ff0052febbd3320832411f4c7e96fc8c0777da0011ff8005dfe63e320dc84fca611041564308064c3ac885046034127c00167f9f0013ffdf80067fcf840504a1314808c10c9627e818e8149554f40960740b788029002e7802c755d08a0183106483be9ad25fb706fd947c28600a0352d04fb6e826448570ea19cc52da416027900c0000243980f880ff27d56057fc000f7f80005a80001dfc0000027f81334044840001ffc0cfef80ee03029013f8820b0167fc803f0e203006200000013242ebfff9280aab7240158009bac93ce887e00ac038934fe0384004d3d85fe6db0013665661fb0236002b61cf018061167bdf6b8b8046c005636aef03d800920056002655e6807d023654633c2e73ae1ec04900a1349f00cd1a7f09a023004c28002b009ba05e300ce97870860004ecee78b630e9e300b73788500c802c01400b009d346f0e10aa1813726602602602e7f7ff00ffa47f028acbff8c6f7b6f0076acff026f56e04dcb1c098036a11ffb53a8afe266124050dc1a3602b01351360aca21a6201320d68d80fcb0159d2a38660075198002714966a0013086fe000e7902200c0046a2811006001001372ffaeb7b227e124050fbc8d80ac04d1b860009d08c550b0033c699b9b32b09b31e01ca7c2544acf2f009387dd512b13831f6292140b04da2c00a8800a984e9214200080a825fa8d5ae3ea35660f2680d58989aeb8a6758efd992282cf0a6254820010020203e3a1c00569f2858ac0c1c100531f5670fab5b4416bab13137b792564eaef2450a97d403e78383638006c7d680150c000400801aa18047dab63756265eeac9df1ab3272af35ab326acad804369c70004dd564d43861c10322e00054e30202216d443026ab1f110c0400043bfe02d0e0000c000000adab4acab0ab958d5153549515414f0b681fc2c58bfd1304353fad5dcc6130994e6b82821214314bb244b73af79873978604ffd34982e614d2208140784404130a03428ba6c67d09bd892140b04c26ba00800800000000000346877abfead07046aae3f92a79d9ce4fdb28b6e2d4bd7e0edd302200055454e766c5401804eedc37750531c0077000f8385304f1800130963dfc1e08ed6b07efc1f40440a3126015e4cfebf4d1fb0aa4f196aae5e4803bfd7f82380a8134009619011c18ac5d0522e3c08e0c5002822ff9b6bb33059d0a443486013ae2cb0048000c00253c2526812c271358ba3b1598fc02261c70089bfdc3355a3b142ec0226b17ca896dc9488164def82a200034c80c0137bd2389f02899e51f4a9f488820dcff5215c26a108821f6a10c0e00ee64888202218200000f9b33288d29482c5cff2a3c1079b4e1534002b9285c0d217c32b4e70617281794c14851845016055a1fdaa070fa086847054268049400171d268130b85f30bc3b4d4804f0d60123b4fe6dbf74c017839fcc644efcc84d37fc32846c34ae6b91695b1442a58589020d21f22f80d8100580301780004a1c9000a000000515b18900000b0c660b10fc6445fb6516dc5a17afd0edd10220002aa67ff0197881d0e141f0133b827a824140b3801f33cec9180bfde6fe021c97fffbf7cb401fa18ff639009dbf1dcb308b37c10c04c9864048821a0430132636832804c9a4a00720affff6345e060050e026424034009e7c14c33a2657cf8acc71358bed3f946c5e655085001c35476285d946c5f2a09acd06b904c24e19dca0003a578a0f468c22a09acc0c4f7c9532e9702899e51f4a9f48d81d6244d70afa2206113d8f64440c40000167dfc8da2f630099f85d41747cf184add900dd58081a2f0e00f0bfd65e22e41c632013c8fff48dbeead9406000280014060300004050100400099fbf8db1e79106b0c99200026d5313737b6bef4f53a98e14e85e160c82a3f029081385c718204da9480269d000aa96fe6d08c79d6fc003b41ff7e5e321ecdc2f9b29b905699d0ad45262208348008f707a03813016008004160bd076870500000025fbf5a4368b00007687cf122aa000053e2a65e80000005a1cac678146518fe953cfc119ce5fed945ec7f5de1797afc131cc50adc9261d8c78a9a03009f77267713d4074961269001f130680026070d3f7f1fab0faa040fd8af38a8082982800acea34278016403f826240042867600098900108a9d94132d41ca4004b71bf800e753fc2ee9eca43d4da842e4997d2291e1013762b69600a001c219ebaf84d326570c9916a1aa3b758044db8f89985a404d2081619dca38a94805468c22a09acc8000ccf347f81bcccba5f1efe5328f0010d4b035c4ce1e2ad88841b161f0c94bee4c7da44202064700002c8d098e6b1547c95e4c385e01770051c25c096bdb0243301003684a709805530650190344dbfc08a82d5ffd22a18814216038af000a00140c0e040a0402003284cfdff1bb700761fc6be42620881c0027d531380379ecfe10b62dffff2401f959fc51afadb44307c2087c528a049f83661b086c90a640bd0cc47091974139014404a00d00fa02f40bd11d4d000000dddc1090000c1587cf6809ea12e4e00003e21d4cb48000007b436cd07cb00002cb2cc175100000ac4fb1100002cb0b758000211d2a97ff2c597e4a9e17ae043d99239910dc654c43b9c72fe963f6fbc1a6f1c0f2c3f6b1252f405547fe5e80180c00fbbb33b817c92c26007c98340026070d3f7f7e0008f0cd408d068aa023ec407700178036c03980638b2d4f01842b7623f1abc0370f7ffb9d4855998c2e5152cb02890d614e00000cc0025ac26411600547fd03b8e485ce0e0174037414401316782d838e6000bcbddd8eff3b015cba209b89b61b32a49b0c82aa98ec0da6be458740804f57fecb50d5b0c0e05856200008f9050f7c553c9f8112c714aa72547fe41b473303413583281ee0340314c130cc90001153f940470ff801400a0c18002001010100061bbfe08807787f8dc67e1b803b0feebeed44c600309526d86601006154bfc267b12e83ae61ee40028000009945978000c031b73fe723b80b70500014e400000049c88375600047c005fb000000029c8fbca5e9400047d005fb20000003e67e2fe3222fcc2301e0a6dc5a17afd0edd102203e2a6905521d3d41f96af03e6173c1c747dffd0101081fff0277fe3bcbc94fb7170402e41dfd12df1804eb82650caa8c0ca087030001304c8bb013212d086811c18a298300054f7b8fa5b7209a4102c30d9e283d7c1504d6a0000029fff899e51f4a908e64caa42b84d70f98bdc4a70400004384fd2fe16d1b4f048c676776019c1790030088038018a004d33f3ee616012c6dac01e699febd56865c1d87b982e05e9400047eda1f3c48aa800016110b5c119da1b83ea80000c000ba922f3972580002140179fce756000cb7005fb6969afd96b5c6a89fbeda6e0400129b3c09226e004cf0bf5f519004c2fa42d798cfa680a52004c000b000c95b19347e801300094001a004876a18009900a2d9e27ec932d4007c4c1a0009b6451e2f56cf8dde001200003373b83e30fcc07d00004c0025287834fc7097927a0508ef082d0d0700ccc0f6b00050320013ae0483004d00025000241593487850001d9ffcc097936d6bde4dfdf0cf153128b3c74547225e4d8184010011657807a025f79c0047507e030080022616168c602000411ffa4713e05133ca3e9502dbc3fd485709ae1b15e80114dbd72009000001585963f257c7dca5312fc61c48d7ffc1670fa3b203c47ca0011a1831818adf02a58004c0e3d8290803abcc61102c8d0acdc28008838182814ff09f4000129dc093f4c4a2cf1ca869124638001f6a62ac00ce57fc090adfffba600febefebe0135a0af80981b7fb38c82062d05e86b4012800002a00003ee457c43dfe786e04621614000088007191722be21efdb3540004850071934f6900000af9cfcf54bd7f65000022b1054000017016dda7f0d8fd6696ab493b7237017a5800121c0000980000034000130582e3033fc5ef3dbbbbb716baf5f876e98110202aaeffd7b79c9ea04cb5001f130b80e3a3efef4d2000a5a85a804e4fc765b727fd802ca000000029000351b0200202c001134ff80439a642e6996f962bc0e180202c29600579003b882846000d4706800b43e2a04c374e44800873449c33b9476283d1a308a826ac41bf326b7899e51f4a80ec596244d5c096b17a307b164a7120800001188253bc7312bc2f4251bfbce68ebc60819ff6d30affc76301ef487e06014132cdfa3bd800050000a0180600002028001c14d0267efe1b63ca45942649000af24c500037cf7ffbaec571a2c3ae2caf3c2f730578bd0caa8000047b43e78915500002ecf6d2000023442f686d9a0f9600006b85a90ba9a2f317a83e580001b1c5a02f413c1f6d4bd2800091a00bf7400019abaf8853fcf122a469400003200719c00000190000006c1e1e60fe44900f4808ce72fe03b651ffb8b5fdebf1dba782207c54dc0c0363333d4132d400f93068004c0e1a7efe7efc7d0040fdf009c521041f0ab144bc849f0029046280290f012012800e753ff9a8146ed0292bba04351932fa4523d6518d80026e74098994ca2184c92d21a11c62a9802677192c390132800437502c30d99526812055f054135200400297b23f133ca3e950058e214ab84d70d300578fa70111100000723857bfe987eb1de36917164a18c18aac4c918140520a305083b00280000880398f04d33f3cf19f40c005216001aedac01e6b7feae5776549e77b982a45e857540000380bed96ff6859e0dc2460161600009507a6e2ffb436cd07cb000039002ea796b480000e45e7cbd7f608ca000039802f429ecf672c000aa400bf7800019b2172f9725800026800019b4

def wireRecipe (i : Nat) : Nat := (recipeBits >>> (28*i)) % 268435456

def groupHeader (g : Nat) : Nat := (groupBits >>> (32*g)) % 4294967296

def groupStart (g : Nat) : Nat := (groupHeader g >>> 11) % 8192

def locateGroup : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel+1, i, lo, hi =>
    if hi ≤ lo+1 then lo else
    let mid := (lo+hi)/2
    if groupStart mid ≤ i then locateGroup fuel i mid hi
    else locateGroup fuel i lo mid

def rankWidth : Nat → Nat
  | 1 => 10
  | 2 => 18
  | 3 => 25
  | _ => 1

def chunkOffset (i : Nat) : Nat := (offsetBits >>> (16*i)) % 65536

def chunkCode (i : Nat) : Nat :=
  let start := chunkOffset i
  (chunkBits >>> start) % ((1 : Nat) <<< (chunkOffset (i+1)-start))

def readDelta : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, w, c, _ => (c % ((1 : Nat) <<< w), c >>> w)
  | fuel+1, k, w, c, q =>
    if c % 2 = 0 then
      ((q <<< k) + ((c >>> 1) % ((1 : Nat) <<< k)), c >>> (k+1))
    else readDelta fuel k w (c >>> 1) (q+1)

def advanceRank : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, r => r
  | count+1, k, w, c, r =>
    let z := readDelta 7 k w c 0
    advanceRank count k w z.2 (r+z.1+1)

def rankAt (chunk i n : Nat) : Nat :=
  let w := rankWidth n
  let c := chunkCode chunk
  let first := c % ((1 : Nat) <<< w)
  let k := (c >>> w) % 32
  advanceRank i k w (c >>> (w+5)) first

def smallChoose (x : Nat) : Nat → Nat
  | 1 => x
  | 2 => x*(x-1)/2
  | 3 => x*(x-1)*(x-2)/6
  | _ => 1

def locateIndex : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, lo, _ => lo
  | fuel+1, n, r, lo, hi =>
    if hi ≤ lo+1 then lo else
    let mid := (lo+hi)/2
    if smallChoose mid n ≤ r then locateIndex fuel n r mid hi
    else locateIndex fuel n r lo mid

def unrank : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n+1, r, hi =>
    let x := locateIndex 10 (n+1) r 0 hi
    unrank n (r-smallChoose x (n+1)) x ++ [x+9]

def row (i : Nat) : Nat × List Nat :=
  if i < rowCount then
    let g := locateGroup 7 i 0 groupCount
    let h := groupHeader g
    let mask := h % 512
    let n := (h >>> 9) % 4
    let localIndex := i-groupStart g
    let chunk := (h >>> 24) % 256 + localIndex/32
    (mask, unrank n (rankAt chunk (localIndex%32) n) 546)
  else (0,[])

def wireIds (i : Nat) : List Nat :=
  let r := row i
  (List.range 9).filter (fun j => (r.1 >>> j) % 2 == 1) ++ r.2

end PEqualNP.Outside.L_meta_670_aux.Cut12Data

-- status-review/Cut12LookupBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.Cut12Data

def tableSize : Nat := 4739
def tableBuckets : Nat := 1174
def tableMultiplier : Nat := 17021
def tableBits : Nat := 0xc92e5facae9a481fa49660d87d3d6369b2ca22d7594dbe18174e3725a40742ec2e7998fba3eaba8e729c20a5a4eb778db6b8ddac04ab20e2bfaf45c01ece3118a845d2c315a73645496e8396aa514b972f6e6e666f04cce782057ac2216acfe494ef1acf697641e8d7f394414809cda94b4e0a4bd30799707a8610353390a3097d950e07b305dd2a96243c510244c45057dda45ebd2ccc14abbaa9244a007eee289124aa7252dc39af3950d4790eaa43a059c788111750950fe4b64e0af476fcc80409f88d2b959574f901ee53ad7020c4aac7b364abbb09874c0dab76ac4ed0aef68d7a91830020d5d50a2d286e48b86a6552c2473e000db494230cbd1914746d6530dcabd03a223702da3a2d7f82280330126db012459b55487b6e9968981555d756ba83698c3e5151847c14e3cfbda67907794674bf6360e54e3c3326a11e4d34015310c16980cfe50a2362b80d36ba08d5dac9e9b88ed89da5df9b4f8f079dfb52dabdd919ad77e0ca3872b522c102d609e3a2f3ae76408c40d7c52c29f5162da7b8a74121b481ec80f0c08f68a37fc400003a3499801ac23a4cb6168a2d3999a8f078658e2f31f392707503318b0414738d99c42597582114eb83558665b831aaa6ce637999b4374f8a47ef2c6a968547dea2cea93dc4b809bc2c83b76fcc364f1600f4787c2e646d72cc7c50bc62e4d2a9186c1db09eceb881b17970428a39b984d4d12e9c5a65dd219d402dca03f8adbbb7178b349893b12185a71fec071a99b2c863d1206e169d34482c601b88618d18539116b286a686a03930ac8257c96b2a9a3e7eb0dc1fc60a56ae97fb9ab466840c52213c40358d474c4867d06c8bb4645c684d7c33b3c9696bc898db40fa7d29ddd50000a63973d6c0321c0e0798565ac219d8dd5bebbd85275bd6b490e017f54335c42853c8dc8598af6f0f6244307a09504bb9b37a0ff3325bad95bd4f2c9816199b465ad7b070b044278538d0380712e649f39543c43c266ebc76c4667bf20000bc823b745cba9b69a3f39ff2127ddd1b5c0e75c3d951a2019c4c32707d05d783955688bc987dbf9d788d3937bfa957028fd4bf3bda12af53c9409bdd54c25f5137bcdd48ab9c45a15cac13c594233f4fd6ab02fe0d04713dd9df2b653c6f2c2dd94740d114a271728b402433a0dbae7d3a8e2ba26f47c9f472b1651615070000678c00d520331a500d7650f06de2b8bf438114f62681462800001d36160e28f868427ba086faa96250b7633b9728dc4686b8b13f0a0a8d399749a6eac905218b216db8a360583c899a28658cbda37a2f3e12ceff548a944f7089546b6731a77f2fc652d3d9ec6d0563b1140d7a7714514f4700006a722c4ac7455141811752a48f2037393f9c7a5e4d3955ab8ba897f593e5d576dac2bea0d309715e51e4c6d58c41484fd5acac28b1339eaa35c2cc71abdea226acaa1003a131c82c03a193516c1956931a07000083b66f513e7e5e743be3b3a600639fc90858726a65010000cd6f8a06d939afde24cc375d792f95e5b3211197179100002d2c6a0a134101444fb111073dd5337c57f117c3ad242cf4888d657a0bf733f0267c368b40635eb09baf341d00c232c6769c8bb862020000000037a090b358b6989baa1102246399c048937cce4f875aac16271bc95604847e873dc230f600002adb991abf0816470fabdbed2429000064816aed000095f484f751c5ab543bb56e287a4b2b3100000000bc1ec3d318013f6259270000c5fb1ce50f1f80339b0da5a55df9037ac381957ad0c2cd451bfa0000a81f80c78f29d81f435564d47aadc45829770000ba23a001086444fa60b923bcad3698ee9e4c6aba2f75b7639457446d1c3bb84694717c25b99b2fe8250a1d5ba7bacff331992d0e72204a6700005192b6695fe04536c9994783a8b4a96a69ad61896c0f4710762f8e47199f5bb87c3f09fe5b3b9fe42ed84e6821e72bd123a370df0bc9a39e0ac01fcca505d464d6f591b9645fbba0bd739661d982d1450b7b6f1bbb712db0b8d104c24da84dd15cda4aba0f2c9f68b21c7c754aeca02fb7fba810587e5ee27477d53975443d09265dc704ac0d27be5c42cf32b3ff36082ed01f3a4a08b7dc5fadaf70cd1c05d3196142c397db0000c27d912d253cd88917a057a631bad20ea9457ea6be65cdd690544c090f5dbf7f918f157a94a3b0ba0b2d163bcf4739f571aed649a6de7cbf187dd9baade92ffb3f0d28372bc622b732f08901000005677f2c831001d0317a374fd0b4ae221f9f0df4000078719f061e9fc1fa0f8700002bb9076ba5ecda0b0000d37d7a1e0000ac99397a0c56a8e31f03ac5da958b09f00002e6d4658d02cb5e2c31c61a5d22812a415e13bcc99f36c6b03e6c1d67d1962090fa1c4380633d675b4c7d47f8673190280532deb23124f77c6a57549cb7f3eb7a80cc68d2a79634abec8aa8d108fc0d50000556489a6bdcb6d3429f1b7cb3cfa106d01a0256d4b0e4368c81a088e6a330d3c8fd053dbb4602b15c0a95a2100001edf49ae3edb709b34cab86b9ad205a0b9569394d05c233d00001c9871101f765883b2b300002a054ae881b94fefa6c59f3e0d541d1803fd5b496f9a9798b03b58ed042740c4c9cad4c5671dc41f7b10801809157f76bd16472b2607a3a833198caf58121fbb00003ef51e9c7f14382f83d922099dc14eaad25b80a50da4bbba11cb6b62bd56b7318ed983e008a5c899353c5408db514c970d98903f75e9187036982cd29c8ddaf06c2d8dba4e517b2d2f4311375b69b5c1d034d7d1751fd51e139e000037c777e9727f49275b6582baaed24cd8c4a0c5676a9e971dd7a80000aa07a2799d990eaf808a7958bf2f725666a630316531c2a216dc31adc7f845d1a044b7bd1b389eeb2ee1c33307f9859ad03f69c18df201a9785c8a6a0ea7be3bb247d6d3c680d507c64c6428cf83c8285d333b244267644310998574018d228d3b9099b775a41dc07af7ac8e2a7506bb617048afd278d5489734743cb59cc53c43b8965dab1baa0068072966a0d1a01251b9023d4a870c8f7b5cc8511bd168c8517ed2e666cd000001c61e1ec6307a1cd4f739df3906252ccf5f6633a3d25b156c7d0ca1060d8aa400282d00b683020cccb64fc5c87779a6a37b43e766b0ae5fb2d7d3d18d5a0000ca4c4866c83ac6472a29dc60d20a27911bbbdba9abe68a5456a20a44be76576ad883da5c4bc226959cc73fb0bbaf7e0fd74ed2391f6078de1588b4da8a717422d3fa7d4534a78e6b72cc7a0daf7d451828c45c1eac2d41a025683e0e2e896a1a1818a5b45deea14111e2264c9ce5425b49309e357d7e8882bbeab72bd856caf67c118329b3db6db30e366c535b8f06c99b800f0076ed8b957125832096b6ba285326b55c79e4bffd850c506d759a7ef3dcfec2d724f50d211c5b9aac09a506ef7f95619bc0bf208217d9a78e0b1c274f77c73c981a363e2e895e54921ecc96030c026cf34f0bc719231fa0a20000c1ed95d607bda665563871caa530a55750052a4118a21224d3bdb1540db83ae783cdd6098f985db52a4cc2b932dd9463845f000099a2c1420000bf445b78807c530c1714ae2cc88287852bfca41f0e227f18a4d22cbb349972e067f95ff1d78cd95e94e719ca16593da500008ce6b87b41b00b10a3608faf8c7ca7d7927b9f514610d6bf2d49b915d012c6713c232d77adb396516bf5baac8bc9b39987382dfc8e5400005caf3bf367f2306f5f9104f6a1e147d521f7000069b7c40c23ec9287748d67e8b4b0079a30a25412b3cc3594bf4ea89c281fd168b0798b589806ccc212f52240a8f9dba6c6b0488222018796104fd0de5d494d19c5d042cd5ef146c0ab8d73c53a3cb8d5993437dd3848352c5d7933d07c993a203bd1599587e822872534893cb5144b398cf2ca44d0751b82af088e9e48e34a1fd479503a8c8461e161946524cf07beb5728515769db0d3b72f63aec8d76e9ead58b0ce39814432527ff96686d827154bb0a95d0c13913df8be5a6e4eda6bb230acdcc24e939fafbf653e9df6da713ff4ced10b5a5f67baa053663296657ecb5245c8770509253ff0dcc2c632a63453147b52d430dcd5853821cdd35f2122bc613e71be97641e192e1c7762d5864476964545c561524f6dee3620a27106f990145b5cd35912147cff699d8099b634d86cb20f0472201b2cc67e32431b7114c8c1c8eb25bf94882ba7504108cacac901211c5f7e5c1598a1768e022829a23dc08151d0385b9678a0bc07a5718b9fa7135938256051ce75a3721dfb52409b3aab5815102768ca1b47a2c7296b70a402c91b2253928d820a08db79850294700e07b8be05c8c99a056da6494465c71c1f073426544ad706e2cf682231661d0e975d6b212ed4bc9e65cd5b74044227d816cb4b95f61b4a6ce05ac50000d1f589ea25efb38ed329afed8ccdd7b2a3293c0fbdb5182f096ab1cf40397ee3468401ba7add59f0c5146ae362e904bb29da344d313b20ad0114c4dba0273d3280da27d543d9b16728a4000083b96555ab094c3490095af86b9d083324d54b8022ead5e7af2c25a32613dc061e25ca2c76e11a48c5582bdb7e939d4e36b8034bb9479952280767c525d8a56863568c6050e76e9428665f9721487d6d83f729ab77b72e4e84a999d8b1b062bf96d19cf19e2e9f3805270cd04f98416443f018e8258baa6c5d2d1af11cf3a66b065d516915558299cb8c28a6c2b0193b4b306bbf6b1356327cee4db48af19cbf4a61c50f56ffa4454ec757c0ce9b675458342a99471c3510cf12d68f90b697a85ebd7996aef039b036b16f817d890ee5c3fe24eb9211823e1eaaba3c050f5507beab67ae683059f5ce9257540c66173ca1b8142975acbb19b1c91055010449d2c8e41f9809c802a88779615a114cbc586c5da2669959c479c7a3d55d9c2432bb3aaf2e51db614e896aaf5aab416663f53d7b935578bda0e8ccb3293cd40ecb2c7d280269ad5626238e7b3de41dce1ef10ab854bab9c38f6f9b1fa24baedd659654df72ce44f4d23fa1822af034bb6ccb16632d631e40cd287ec35d962463421b9d0aa4ccbc45804c7f31a7e3c02e291b4e5a4438d0e8209c0e68525a1c308349b826455fbcd2a3463b5919c5738c8702375417470764248c271631d5868230b96ac6bac76f8a18951449612633663428bb316ccd5374906e96b0c0a1a3dc1cbc74c4590209767db8734fbae598e74776c060aa6015fa5458872c235fb0dd3af5c3153bc045fc8f8f22adb9ef2b3d1e5c45ee20fadb413d3b2e3912dda454283abcb53b7d0669c9b4befb4c28065464de2280a707acfa1704d49ea6981166a3c023de09e6398e112e6ce691e105df40a872a09056c7b00ef2a64902f1777eb6977dccb6fd483b6d9a29e08083d62f436baf1651055fbbb10b80bc69edb972be4ac1a513ecc2c6ac75c6b7ad072500467f0b4e662e29b47e25767b0f61db603564371eaa3f5158b15b44ad688a5d3f16d1284517e848e96305addad96a46666af9afb21b9489217852672825cd49b570efdde73fc828105d1a02ae2b461dd68183461e883d0842d71e9dda8ee121a8198c120642b4696c45fe2a3361d846a0ce0bc14c05a3bfb9cee4a6f4c99f975d49ea5558118cb188449ca2a02c0e305155bb3c2ab1a333ffd389535e9915d27f7b7e247c46f9210e268b886c2fd34f6bdbde5e46371171519e8dbae1648e184aad47dc25aab8cd88abaf88f098664ffcc131d58ec4c163f087af720c31c3b001446316a138e043ca90f2d100cb6bca573ec5a156629831262a69d9c1a4a18520c59456c55cfdba0eb8011172b0f952fcb58cd2bd89551041a20e9e646c462d9e3d173f2159064a49625d5de034f7d6e012b916f33779125882d007e033bb18cdd41f340c5b0478e63c40238eb621592dbb04298172362b11854cd4115f3770e27ff4bb4b9b96d13b3cb151aea0ab9175614d04361f71da5887f97dfc9c01a90870c103d59841a6c95b355871009fa616d19a15beaa1ec6e914c9789ccb0f05516ca2a08d3dcb67a03fd196e417e915c22e3851f75c1b9c3a39d061c46881a23935172f88b23dc80a896718f70c7c6acb347059483f071691ce0215d03866adab19f91d8993f3a5126b8490cd50a8263153bec6985c37782b9abe5b11727532d53eddd3983786649e4fd3c487aa751da6dd0d03223cdf5854bdf3c1751c016fd8b32abe2e85e94cf07bc0372e2057322e90ecd3364ccd89a0c8a9cdc71496a07446a7d583c1c5134d0a88327f9c846659d458595ddd9c4badac40c25900827d7c639f34d55aeb4aa78ff430580545db24b40e600804d71461bfd9afab952267ddbcccb5a9351ec7c336e7ab3d43446d1d033990258df04cb12be127396374bbd917af74d08b809f7018dc1c72607881317059bd053f6051f0c3a40bb15779942d1fc5a25da7eb41c1ae174990758d2ec875d4ad8027ec41ebc115a7409e52775d2c580d68884fa7fb4c893d6ca3009db20ec99b91a07d224852e96e64c75a87b78ad022255d87153370971f31848d9d6e8006806c4902d7bed3ef107e623d1946528189cb428a74f120096104c5acd29f91edbb3b1ff3233132fd744721bd6938a53fb0efbe6a5c3404d0a3360647c3eea42a64b2915fc20e4e9a644b316c3da01e8d26fd4dba44ba1fffb312205fc22910b022f589d11b0982fbbc0087c37aa918457b1942702e0db8fb47983cf00f15c97dcb275e5e4bf5c228ae4d797e861c42478b6ed5f302de215393e335665b9e910b5f21d295cdf8773b4646440e83ef730f3cb76b455c7e448948f35e0f61f1cebdc3f1c05065e1b4200bf44d4a14be8431908495653b0dcfc20dfd8314b271045da99ecab24433ddd088a35f5a16236d3c5114c0fe86f064382d5bcbea96f55778d12d2959d7057d59196e40700c9ab649d9270b8442fdb224053248007bab9d6766049564457110d78cc1c9d3b5f878f63d233b5381c1b759414991fe4eba4b68a5f5a6bc589a7ccbb6919c75ca809a6eb4e7d43c79d1b4f487d52069d9ce2f1f9c57ae8f6e713e63712b8f37c57e5fd1a2d9a390d0f2772b36d8396c86df221eac5123af234b931965a8913937cfc3b01ab5578a025c588f1c9e40f2842265d16d837c877beed5b6a1a58653a87c1548263e50fe43490eda9705ddbea0455935bdd8d9fe9dd3b65da70273e37cecd18a0805db929b2a7c6909ac98aa2f8f168b4859b021c54603900cc010881729566bab819d897ecf318e532d04411b6a33a591be719c4f3c4e8462a346436f78bd61b2c13e39575a5723b63d6dfa8a16dab4191e9a688106243d93d3552ca1cb4a1466c27dacd16320f178d67d534fe2979a6bdc12406b79c0f2af0d6d2c0aa5130976b1b20337e18e42a51b8f41462f5f7d18852fabc6e1c2484323246e49df240d19937f742f50a9cb366c30935f06b6c793ca3ba58fe22ef9bcdd3d0258d409035c975965b266327aaa30b90bb81d4e1979c421c3ccd40acad7c99bbfd7313e6c5d5cd65b41f6ba4b6fca4e714bde7798b6ed72e82f30630f0e3235fc85210e7edb0edbb742b88e2aa386ca81d9ac513801d72b07db739d18c16414949b17388e302e6615217b5e384f2aa84b62f5bcfdcffe77c45210d90180b16c37761e47be53e638d9c9156a543e576e3b4c6d550eaa9dd0a108ee3110695536c9069fc3be3afc8631cd635a56306b77a48196985288762aaa0004ad7ccb39ad8c88dcdc52c34f27abbaf545e123d2541f6289a4ded1085ce9a71d81d8c09a2d4401e7b51d391528556b0abee22a1e51a28934622db53cd06f5a45236f0540c66a912aa6b0898ca8d887188daea48b93715bc18c70cf8d029dc94c1d4e6409bf163e89600f151d16ab87de8b0f4503dadb1e654af82e232a867af16c0b2c90249f568774e6be0a897360614a7b0b4c35557835ace7b991a7651a33277a03e0d36b0fcb9a313d5b941d44d0522972268b018c9d95178d88b28c983fdc79d63d3ebdb00bc1b61cce93aecc08c5732a5a0e58c0ed8c550a9748d47dd5a69d68c026f1c0033294c9360e42384074855618006f117e85c4b28fd59d569daf38c6f389e3963955fc290f3adf8e823a9c35e5c196d342401f5b856a7f666a3e253858ac6aca028a598de3441860a679b24fa328df5a18a1031f0c413909315e39844a494d2b98a1d49c4802768aded490cb9ba56e3a7f9236a98bc1e4567156d3bde997ba39601af894960416a859cbb06879c3720316702e06d28b478a45998e96c4480f9fae16e4d2cf7ad2564dd0484a8c97819d7e04e5d6216e2bca9bd8ac89b0a772447c525d31ea8f7362ced3e60705911b9f99ad6ec388776e3e03363c1e524375505536f1409b13fa81e1ae0630060c3094120c4592a386d36cb5aaee936503b34211a71aab0f1607d34cdb80d8ba400a88ca5d0f1b781a65732111251833b5601c89b44549844d5020cac96e8d00cbc60811b02aa8a496e77e6b128bc7e0a57a9480241b9404361127f6cab0254e11a2ac022db597575ff7a5924cc41164bcf073537cde315071f2c6ca9ca5985cc068544b42fc2b6b8390b813ae35c4fb737b9bda55cc82e261647e3e2f988c1cbd3fc5e3b08054d14bd323c8a19f5c73c1559e089710391b17857ca75a0cda9bc3c268ea2520bff435cab40a357e57f0491c8bf7a9aaaf9f0fe68ca300d977d9533eccdc9b783b13868f22690dd31101215f41d9d66434521a976a4d3f3e04fabb2ad093bf79dd354b721e0a8ef02dcf38c3c367920f75df9de9be29a33a8efd95088477320a67b9cc9f6f9e6cb390fe8824da9222d35a85067bafe2d7375c4d1909cfcf99d9881ec73f698d11e9257825a7b93a28e285f1ca1160c7a996030c1b19208db9cb802752744047d71a19f04d87dbd5ba5e68b725ea8c2e18c7b27a98b9b3b2b8bc3307ba8115b37fdcaea77c2fc46b3f3b3a007495cef3c0777f5d7212a93457b08bd64a9853a8ab33d1e026a7a8300cb276464ca8c5bd9a0d9331b8402454cc926a02a5ce6ed78a949ebb4acdaf675dc8cd962fad7ddf86633b44444e9744412f857b7684203b73692b219e7581869997d4e1273f36dda7295b258d91c010c5b150801bc138a230ffba937a8c55e133faa467cc6050185e1c29c3833752bc2e051b1595390b6a0be6427d7f5b53f64df66f57856662775397a01c4b57bf947a672b84cdc9094739c3817358eca975025135ebd7713cce746d1334cc2512b195cadb8ad183033ed44a7915323e3475502497c70f45b1e5451f14872601b09468210032b0c65eb34d9ac1a4060070b370a57fb64e2b757281a44ed994b36818ae3e497983a363e4a47e9cd91d0479f42c5f35478d733c0b4fdf7344cfb18ff58371b45042a328756d1029cd3f7b27da8c074d107bc35edd5aded2529edf756865b60f72558957d5602d767145611f1751722d1ba5c6cc8674d14742b12ba2b50147731e08987dc402865efa9e950998822d0ba066f659ab6b275c890f02d1c847633d5d876dcbbd4c63cada34fa6709bc947005a9e1bb5e7a9f047c930e9f7b6adf301339e9055bc4e16fe2b1bcca6092cd4faf969473af6a89143d42490ba83fa6814bbab8d6155dcfce6ddaf52f381be710e222fb322614dcacc885433fe276c13678074d7fadd875b2f63b33c26f0a65d061bdaa6d5411b1b9d7586775351f4a76540c73716ac9df098069505448202449530698459038b6058a07cb08b91ebc46b87e6e7611294982df049fbc198b216701c01a55776f34507aad2b6ec975f3b5b51f82b38538ef6219083aaadaa9100de7d0154a332ef4dc90018a91c92073073f05cc88056faa7c927417aa8610bcb54bb9a4458195a92d9746da924e3ffe362763c952196dc00ddd8e13797331c925b30aeaa1399a997f9aa1f37b63b7af94b0b33dd8e57a555983410e84401a1f50ca26be195c685518c01cbd1680512f5f75b85a78057ec030b173cb011e678ec84ac121d11c41278059a2919cfd46e4405871c37e03c1cdc111389782f526c95a49db048e6575813a0d8d63bd929d9826e1c8af166ad2dc1d82d92d6d7a55bf9ca9ba677ac5a58b8c1f061c82ad4f58a5fdd69b5741acbb932b081fbb8c560ab1f724b7bed09bf93439a194a75d891ad22180fb0e71008aa10cb4bb91af11d1b70c9e264b40b3c39149bca5a7ac5ed15237c528579336790f9c12d44e0f1ca83d870587102a8eb8885260e368e30e8ab36c7c55bbf5bd34bc3047533dba4194a44088c3ba766141adfdc9850392a9c4daaa18b173f8d5c3d7f7a4ba8bec068db52692fe3ea0692363b666983d494c5290a7a476342fbc9a4f0459b786c6cf6e58166a4170230161b6df0a6a2b80b4a6b9694394c6114b8bb7a3803e08f8772405b0cc4a20c30a57dc09840687434de2bd7b645c71aa5800b78d5bd901696be8b60b0177b73f7f87cb74ce7f647b1300827f44d24a3859c628d4b25bbf25ad5b76d54ee69adca418836042356c9a439a8f138ac9b6bbd67375bc0ce233de15296ba92b58394c3f768ecbbbc39093925a14b16f63640882c087657929b96002c44a545e083aca53f38c02aae56286049801fbb2fe1a621ee631534dc5916d5da128b503ba39b79905613895bbd8d6444194fcb4cf6dcc7186502f141186bacc45db3c90c74c00294d735f0b267306750e476fc9b98a1a17a369257cb43b3c96803c5bade702c5d31b608181b2897e78c7321a2c3e7bcf8558359f608d299a6ddb0af9dc332fbdcd2d75550609c780402a5f342fee4df2ad1b92316bb115eaa4ae9f8f3a6f1d1d1d33b56b529816c635ac136592e60ebd4b0874ad9306452eb3489a1ecafb5cc6bed545ae7714bc6f60f23ccb8cd7301b11bb2bf61819cf53a657d4eb0367d9928ec01cdf1e13ab2e471e3132d28f663f8d20c79679dea535365dbe837fe2d806cdba81207847dacc78158b63a622929d3047337813f1dbfb7e1965f99af6d8326fb927077b4269d5686254a0d84d9c154693da4906aa44a233cbcbf6c327dbc95bfb710313c9a7ce2d8531fa1b3f3ac1af4d674f2ad3b48cd7e07c624cf91de5ca96ce1b74a4b42ca8bddd59ab6755399ef5774eb8ee5059dae61e32dc9b705038f72042c88c334c407cb7819e1a603d20da691362519a8700b30a9947cb84a8070dccf81e7b3ab93c7b8ae984f00f5037fc777957175386095c9625ba009d571b2665655a749a50a5b659da0a78c5d56ef79b5f547734e984980448dcf5141dc1694c1846ca3e48330d829543a792bb5a9154ef0519364fa9d9131c7e4f1fa71a136ec3919dcf9911ff59c18383982f2c1e08b67077871961179f2752afdb2dd54b26d26760b92d5119276e7b3147b1bc059afc71fc5bf5dd6e5847af95abc85f180c0e6d98c61d5e8d763d5e26d1ab5d706e7f90396e453ea2c4f0101faead2aa71b9e8219226060354551a2e584d1ce2459898f8119e10bc4d591b9b7626ed98037b0dd7eb5989646a1f75ab507570784cb1734c598cd5bd3420a345dbef46fe5bf6860961ad4a05dbfe8c8d33c3ac28dafd3490f0bd3c4cf5e8197eb09884f2d4117621e13a52c71a0c12ce1dce792e960b436a165c10d717f3e9613b791740d1261a2abb6a466dd1927197da3b69a9307ed97d48160982388a664e2ab6f79601aa2d8c203c67fcada31dd79d89630cf255b1d9861755fc63fbd4ba78ba07334654cb176ddb2d76055f733575ea32cb065e940e246ef05778bc53774894a558ea8695a7d8dc500e50dc641784898cd7b0e118fc4bfc51d6c272949a3a68abb5ccf2cc23d13b3b47f0e593246b11769f35f49b7cdd39bd56166706b3d1b908289172638833b9b41a3c2750c234ea848a842944ca023f893882e962ab8125079073344a1151b5b19b9a60d99e6977380e732a36f2f7deba870952f1f564d6eccfe9a7abb7c1e6fb868861e035c394368d16d462d3210601baf5536b9e11c245348ac4d170fb74cb5cd77fa9f155187924c35d82e1dc75ed5130cf2677e8e952ca3c7e771d5b2aa689ad6e8957fd14dd0ca664a1a78646f8e1eb194c656bbd2415589fc49679ba7b35494c06948559c8506d84343fb1d0c686b32b35623adc52401a290185d7606132426b12a185a28cde948710d8b0092d4a859e42c17b4ff89bb0cca333aa757dc701d47279dd7465438315f4ef4066d0ada7e8329293c68da8678ae10c9c3e0b3e7ce4784dcb053a9ee00b5583b81f817c8d178caecd46a95b5638e7c207b96744d0d186eaa6b892dd981628f5985d14e036836af87745c2acc7f4c022a3f88cd3ea795d6874c4166e8c8698ab487a4c2963c9fb0b40919b6d4a91d123c357c27cb0876b46f64f835b49bea572db57c4d246a9210f3a16ba31993bd100e6ff576cfa54b0a1eb3ea9a5a298a8b8696a788e99e7d6eef4d6212c1633ed1bab925b8e2c5f2632d37f3794d73bb5c5d9067901923817625d917c59bcbe5acd241800f8424e35aa40b8b8a7ed90a9925146c993fd0b0239ab8acd99b348ec3442375c8fcdd8fcd9b9fe730ead7971f2acc1e0051b060ba3d8248bcc207e15e7d1fdb1294045344deab9e977a7be27f020c39c394cd0e122bc2f8d1ed59750374880a934430ccae614312cba7cfa8b2e42afc705e0869508db7f0ca6985ff48c2d1d24c7da886cf230d49958a3ef249c19bcfda26abfc5ce5a0f07b8bd7010cee2492922133988835b29c655a58be82600131690c66bc6bf484258129bb92c3605a38cb643a58d3dc4be9638272f6a1635e564488564b2f1769944f60b35940b1a219c7d109d53f2a0d0fc182175954fbce2b1386245885dcbad44ceb29257a355ba89c259fba3bf5005563d261098b1b91db591264bedcaa6c73706b92d6c2ed8eaf56ef9c9c8c93dd4f13dc43bd7660a089d52e21922f070f3861ba488f7a00ceb38d9dcbd871e79fd3573b54af08e46a2ca35a826b52073a67ab0044233b6a308969de8fa28252527e2d05739a3d93484547944d8d2102863fd604235152ee11530fbf6772987192ae7820a2c46319a4f5a8387244399fcea6bc354091d9f24ab81772858d714978a13a875482396e9edcdcd29d28c3079f195519a1c4aabd56e78d4a1df37c0568f61c4b156b534da9bb9ccf02196e071d77d4aeaac570cb17679c652ea99f55004291590625556958d742dcb71c673e1a8c3814d8f2acf2d3a6b0dc84c04e3e2eb6542e28fb348c9ae405f275256b580fd3c0c5650c74314b1a61d12299072b94cbc0dd0886b1dc5dab05c1d26341ce890a288894e0a8c9379821e319d938711be2aeb9dcbb
def displacementBits : Nat := 0x10b0037079000801000318c00601f8001106805402039f9291390d8c04f63080080080020120494000334090004869e3340b912506900100f2813ce840e742e802d1f802e01180242905f301b80e876e08a437804c04e3562018ae80da02f00b000439600140210142e600102a14a41866201a8802c01a15c24d13300000fd3f5000421204c0a200e0a784b20320dc071206d41880bc0822cb0001c9c0740cf02484d0df8030009800807e01200080b00221d100000100be00700109181321b400e228802a020007875409a625121800401814003880003000010c3000420e0170020ff85340000078fe403630700000ac11c004001009401209200201a003cd3800e80fc02800002105cc3540000f78241ed21c4000810424a0be0038c240063ce0d1805c00003f002817801601f3cb89800040b9012808403a35000185a810c14c0bb005400064404a196801e0000008d54000385050800437a01b02db0cc01806b1a6002c03801e035024800820d025017c02023702600300162c202a811c0700045e3944d1602a602903aa0be00000901313a40c100216a8006065002000c00807918780440140eb048801c5282d10118020002307046800400e003005087c03a070002806800400101f000021600033204c009e004006805800400501c806c1ac12d0368510034003010001802a01523a800407810d02180b404e00b149082811413d074801007002500300801a80d121581242ae2a006800c436801c006800400004d00d000002e11f027005c03212900500001b800a17744d09220010000001d4801a0240c98b2c03c0068f0809601112f011400206f00d005c2d00c72c3805405600302900d00e40000039510aa801007c800c00246d02181c00040010c2147800411c00d817002400800002400b21ae00001a40045ad13702304e400d0f1031493000802e887c00405d00c804c10002206d001c00800000b0048ac2033007800634e07b159000c0ea2d900182400340b806200f8016ff304c82c80d023400c040863601300300d0000002007828c08c08c17500a00a603400a048800200000281a80760422ac0b280fe06800180d0018560000800403808e007000000009934000e018000000803e404c0221af810400c02d09681bd006003021000c0001b70108000a8607600200320f4019010014052600000e82294100040020de800c27e005829801212902805200b202d069043002017b00002180c600006480040f601a002000009a0030070024060d7c001b55003601501a80484c039900580440000af000058c00002602f812c00203f00100b0344002759060409e4b005f800800200001a00f9d8032b1bd226000208d0de000c11a06103d80f808c0c4028818d40008d003001c26200600400c80260040f3017000400f044811800001a007000801c2290be008c00b1b900182547e601100f80240aa01c070014c01000500e800805800001e01e805600101e024001a00c057035c052015001084c15a02f00e80600020378b202440fa0070a3006400800202280300d6001028000403200900ac3bc0ae038003008400002409080440001f70018000000003005929c00a009000002c31a00600000140c6001006803804000c000801400400a45a0c1c04a00500a8098002017014800407e008007023c012012000820818601b000800042603001d8008008001604800051e0070040004046049000005c00200f7940000004030007800595a000016801800805102403c00aa1d9003805c0d000704706c80040010008134062d3701501b411200111f859800a001005804400e00200102d400a08a009806c058007001004000000c00000bc00a000007031c18e1280030010092001019801c05402d000001c08b039024806c0040ab72f800401005000000ec0000465d300040020591dd803c0de0b800400cc010085000805c00c0020020000000071001003000e0100008028000017000000004a00100080400020f500000b403e01b00a805801813d004043402801900602cc01600200001281b200c014805406200400408fc00400e007800409e1300a5246408a00300000200220200a3000400211904a800400000000c819809804c004000800001b00015e805a056084000003212d0ca801803a000019801c0120000070270000052009802805e0000f8183c08c16d000809008000100007f80900b6032004c000112002809825e0688a8002401c08b007803c37a0010b7c510000000005802801c091003801c17c04c0390020000c560460040014001002817802a0a001086a40aef71000002800e001000002c00200000600e40c484300f809401c018000807c372069005801c000004000001400a01d01e804c004016003801801202e01e8048078003000003404e05c05e802400000b0148014004037050003401800544200440ba01700da77803a006008004000800050e800c00000004100ec20c01d007003008e03402b81140f20050038174016058009a07c0020075a4804808a009008003000e0e3011814401e00120880740020440160018126007075001800200300080500c8000015af2800a00a00182dc000006002000000a002002002803000600c806c00800158a800c016002004802400e02d0020038050005
def activePatterns : Nat := 0xff000000007e0000003f000000003f0000003e0000001f0f00001f0000001e0000000f0700000f000000001f0000001e0000000f0000000e000000080000000700000006000000030000000200000001
def activeIndices : Nat := 0xc2c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c18b162c58b161458b162c583162c58b162c58b162858b162c58b162c58b160c58b162c5870e2c28b162c58b082c58b162c58b162c58b101440b122c580122c58b162c584122c58b162c5840a2c58b160058b162c588162c58b162c58b082c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c18b162050b161458b161058b122c58b162c58b162c587162c58b162c58b0e2c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c5a64c7d3264c993014c993264c993014c993024a993264c993264c993263e7d3264c993264c993264c993264c993264c993264c7cb95489931748092814c993264c993264c993264c993264c993264c993264c993294c993264ca13264c993264c953264c98d174c993294c993264c893264e993574c993584c99326b0a53584c9931bb0993264c993264cb13264d613264c994a64c993265c993264d6d4263c792a64c913204c993194c993264c993264c993264c9935952b162c4eb13a64c993264d613264c9932654993265a993264c996d8b56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab56ad5ab546850a142850a142850a142850a142850a142850a142850a143365cf972e7d7b36a23c98b264c98ba62c98b263a98f253a98a222e5d3164c5060c4278f224c9532244513174c98b162c993264c9932142890a64c986a62c993173c99097183060c62c58b68335b50bcc58b1c592fab183060c1a3061c183060c183130c183060c183060c183060c183243262c65367d72fb462c58be82c58b1d03c61c183060c183060c189860c383460c1830613183060c193a83e62c58d0a141bdf8ec58b194c66377cc58d4775070c1a3060c183060c183060c183080c183068c183080c383060c183285094c58b183328506f76fbc62c58ca6ec7435a8ceaa6225d114204c6254c5c60d3c9862228411111a75097183283284fa7d0a14284563834b865198b3755060c183060c183060c183060c183060c60c65d0b8c58b162c59d33a64f124c9530d429930d2e58621223529c42993264c4460c1830650a0fdbcfa1326505f8f0df792a0b162d58b9a4ea940655918c1830b0c4c5c60c4c99311183060c183060c91421319f268506f7754f64c58c462eaa3166c4c10183060c1830626203060c183060c183060c1831eb162ca7b7bad18b162c58d4670e1b1
def activeBlocks : Nat := 0x8c6338c6317463163110625103190f6b5ce735ad6b5ad6b58d298cd6b1ac6b58c6358c6318c3b18c3198c318cc2108b5294a5108a2108a2100a319e83210831908418c8318c851ce739ce731ce719ce7398e7318e7398c7318c7018c718c6762206321e639da6321063190639ce631ce6418e6398e6318e618ce6440c67bcc6420c6320c691cc639cc631cc6798c6618c6418c6398c6318c618cc618ca65916421164211446488422c8422884590845108421084190840108430c8420c8418c8420084180842106420c6418c642280451004210044210321083190830108320c8318c8300c83210631906378c6340c6320c6318c63108420884200842104421004200042108221080210841210802106010840

def primaryStamp (h : Nat) : Nat :=
  let d := (displacementBits >>> (13*(h % tableBuckets))) % 8192
  let slot := ((h*tableMultiplier % 2147483647)+d) % tableSize
  (tableBits >>> (16*slot)) % 65536

def enabled (k t j : Nat) : Bool :=
  if 12 ≤ k && k ≤ 15 && t < 8 && j < 4734 then
    let block := (activeIndices >>> (7*(j/4))) % 128
    let pattern := (activeBlocks >>> (20*block+5*(j%4))) % 32
    ((activePatterns >>> (32*pattern+8*(k-12)+t)) % 2) == 1
  else false

def aliasBits : Nat := 0xd2f210f2cc6210eed1b410cdc76e108fc7311080c709107fd08c105fcec91041c2e61028c4921012cabe0fedb6780f09b5320effb5ff0ed2b5d50eae90860c0a8f530bf08dd20bd08d070bbf8ab70b8e8a870b8a86080b2a85b10b2385810b1f84c30b0f84680b07840f0b007c4e0a4579430a017b0909c1774a09b46edd092b6eb809226e9c09111ae202391a8402331376019d136e019b0b3600eb

def aliasEntry (i : Nat) : Nat := (aliasBits >>> (32*i)) % 4294967296

def findAlias : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel+1, j, lo, hi =>
    if hi ≤ lo+1 then lo else
      let mid := (lo+hi)/2
      if aliasEntry mid % 65536 ≤ j then findAlias fuel j mid hi
      else findAlias fuel j lo mid

def lookupStamp (k t h : Nat) : Nat :=
  let stamp := primaryStamp h
  let j := (stamp-1)/12
  if enabled k t j then stamp else
    let entry := aliasEntry (findAlias 6 j 0 39)
    if entry % 65536 = j then entry >>> 16 else stamp

end PEqualNP.Outside.L_meta_670_aux.Cut12Data

-- replay/Cut12RuntimeStrictBody.lean
namespace PEqualNP.Outside.L_meta_670_aux.Cut12StrictReplay

open LiveCheck

def signal (i : Nat) : Sig := recipeValue sourceSignals (Cut12Data.wireRecipe i)

def state (_ _ j : Nat) : List Sig := (Cut12Data.wireIds j).map signal

def hint (_ _ j : Nat) : Sig → Nat :=
  MetadataStrictEdges.listHint (state 0 0 j) ((Cut12Data.wireIds j).map Cut12Data.wireRecipe)

def count (k t : Nat) : Nat :=
  if 12 ≤ k ∧ k ≤ 15 ∧ t ≤ k-8 then Cut12Data.rowCount else 0

def rawHashes : Nat := 0x4fc52ac86957602c663ac11e237e558d86e5ba381c99b6113a9819b1e7939325c78120

def word (data bits i : Nat) : Nat := (data >>> (bits*i)) &&& (2^bits-1)

def hashSig (a : Sig) : Nat :=
  (((a.1.toNat % 2147483647)*65537+a.2.toNat % 2147483647+317) % 2147483647)^3 % 2147483647

def hashCodes (g : Fin 12) (codes : List Nat) : Nat :=
  (codes.foldl (fun s code => s +
    if code ≤ 9 then word rawHashes 31 (rawSym g (Fin.ofNat 9 (code-1))).val
    else hashSig (recipeValue (rawImage g) code)) 0) % 2147483647

def canonical (h : Sig → Nat) (v : List Sig) : Nat × Fin 12 :=
  let codes := v.map h
  (List.finRange 12).foldl (fun best g =>
    let value := hashCodes g codes
    if value < best.1 then (value,g) else best) (hashCodes 0 codes,0)

def compositionData : Nat := 0x5127390a864b4036281b975a680a4b271539791b5a36042832450189ba6723541098ab76046382b179a5157293a068b486a0b472519397b1a5634082ab8967452301ba9876543210

def lookup (h : Sig → Nat) (k t : Nat) (v : List Sig) : Nat × Fin 12 :=
  let canon := canonical h v
  let stamp := Cut12Data.lookupStamp k t canon.1
  ((stamp-1)/12,
    Fin.ofNat 12 (word compositionData 4 (12*canon.2.val+(stamp-1) % 12)))

lemma rhoCorrect (q : Fin 12) : CachedProjection.cachedRaw q =
    (ClosedDomains12.oracles q).project ∘ FastRecipe.source := by
  funext i
  exact ClosedDomains12.cachedRaw_correct q i

def programs (h : Sig → Nat) (v : List Sig) (q : Fin 12) :
    List PEqualNP.CircuitLowerBounds.Gate × List Nat :=
  AutoContext.programs (ClosedDomains12.oracles q).inputs (CachedProjection.wireMap q) h v
    (FastRecipe.values (ClosedDomains12.oracles q).project (CachedProjection.cachedRaw q) h v)

def initial (k t j : Nat) : DynamicCovered.CheckedContext ClosedDomains12.oracles (state k t j) :=
  ⟨FastRecipe.initial ClosedDomains12.oracles CachedProjection.cachedRaw (hint k t j)
      (state k t j) (programs (hint k t j) (state k t j)),
    FastRecipe.initial_valid ClosedDomains12.oracles CachedProjection.cachedRaw (hint k t j)
      rhoCorrect (state k t j) (programs (hint k t j) (state k t j))⟩

def config (terminal : Nat → Nat → Nat → List Sig → Bool) : MetadataReplay.Config where
  limit := 7
  count := count
  state := state
  enabled := Cut12Data.enabled
  transport := fun h g v => v.map (recipeAction h g)
  lookup := lookup
  terminal := terminal
  edges := MetadataStrictEdges.edges ClosedDomains12.oracles state initial hint

lemma config_valid
    (hsound : ∀ q, (ClosedDomains12.oracles q).Sound)
    (terminal : Nat → Nat → Nat → List Sig → Bool)
    (hterminal : ∀ k t j v, terminal k t j v = true → Impossible k t v) :
    MetadataReplay.Valid (config terminal) := by
  constructor
  · intro h g k t w z hp hz
    exact rotate_recipe_impossible h g hp hz
  · exact hterminal
  · exact MetadataStrictEdges.edges_cut_sound ClosedDomains12.oracles hsound
      (fun q => ProjectionDomains.project_target q) state initial hint

end PEqualNP.Outside.L_meta_670_aux.Cut12StrictReplay
