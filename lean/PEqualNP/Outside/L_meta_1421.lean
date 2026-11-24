import Mathlib
import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- The truth-table samples and witnesses below are for this shard. Apache-2.0.
namespace PEqualNP.Outside.L_meta_1421_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hu,hT⟩
    cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def evalT (T : ℕ) (x : Fin 5 → Bool) := Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

theorem cost (T : ℕ) (raw : List Sig) (s : ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (nd : raw.Nodup) (len : raw.length = 5)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test : ∀ t : Fin 2, search s t.val raw = false)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : s < C.gates.length := by
  by_contra! small
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have oneNot := notCount C.gates single
  have eq := necessary raw essential live sub
  have size := live_size live
  rw [←eq,List.toFinset_card_of_nodup nd,len] at size
  have good := search_complete live s (by omega) raw nd eq
  exact Bool.false_ne_true ((test ⟨t,by omega⟩).symm.trans good)


open PEqualNP.CircuitLowerBounds

def raw0 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa010950084a8042540212a010950084a8042540212a010950084a8042540212a),
   (0xfffffffffffc00001fffff000007ffffc00001ffffffffff800003ffffffffff, 0xcaa526552932a949954a4caa526552932a949954a4caa526552932a949954a4c),
   (0xfffffffffffffffe00000000007fffffffffe00000ffffffffffc00001fffff, 0xcc6386631c3318e198c70cc6386631c3318e198c70cc6386631c3318e198c70),
   (0xf000007ffffffffffffffffffff8000000000000000fffffffffffffffe00000, 0xf07c0783e03c1f01e0f80f07c0783e03c1f01e0f80f07c0783e03c1f01e0f80),
   (0x7ffffffffffffffffffffffffffffffffffff000000000000000000000, 0xff8007fc003fe001ff000ff8007fc003fe001ff000ff8007fc003fe001ff000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut0Zero : search 7 0 raw0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut0One : search 7 1 raw0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2863179904 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2863179904 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2863179904 raw0 7 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut0Zero
      · exact ruledOut0One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 11]⟩], 12, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw1 : List Sig := [(0xfffffffffffc00001fffffffffffffffffffffffffffffffffffffffffffffff, 0x2248491242489212449092248491242489212449092248491242489212449092),
   (0xffffffffffffffffe00000fffffffffffffffffffff000007fffffffffffffff, 0x44929224949124a48925244929224949124a48925244929224949124a4892524),
   (0xf000007fffffffffffffff000007ffffc00001ffffffffff800003ffffe00000, 0x88e31c4718e238c711c6388e31c4718e238c711c6388e31c4718e238c711c638),
   (0x7ffffffffffffffffffff80000000001fffffffffffffffc0000000000, 0xf03e0781f03c0f81e07c0f03e0781f03c0f81e07c0f03e0781f03c0f81e07c0),
   (0x7ffffffffffffffffffffffffffffffe00000000000000000000000000, 0xffc007fe003ff001ff800ffc007fe003ff001ff800ffc007fe003ff001ff800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut1Zero : search 5 0 raw1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut1One : search 5 1 raw1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3901270152 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3901270152 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3901270152 raw1 5 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut1Zero
      · exact ruledOut1One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩], 10, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw2 : List Sig := [(0xfffffffffffc00001ffffffffffffffffffffffffff000007fffffffffffffff, 0xa248951244a8922544912a248951244a8922544912a248951244a8922544912a),
   (0xffffffffffffffffe00000ffffffffffffffffffffffffff800003ffffffffff, 0xc49126248931244989224c49126248931244989224c49126248931244989224c),
   (0xfffffffffffffffffffff000007ffffc00001fffffffffffffffc00001fffff, 0x8e2384711c2388e11c4708e2384711c2388e11c4708e2384711c2388e11c470),
   (0xf000007ffffffffffffffffffff80000000001ffffffffffffffffffffe00000, 0xf03c0781e03c0f01e0780f03c0781e03c0f01e0780f03c0781e03c0f01e0780),
   (0x7ffffffffffffffffffffffffffffffe00000000000000000000000000, 0xffc007fe003ff001ff800ffc007fe003ff001ff800ffc007fe003ff001ff800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut2Zero : search 7 0 raw2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut2One : search 7 1 raw2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3901286528 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3901286528 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3901286528 raw2 7 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut2Zero
      · exact ruledOut2One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [8, 11]⟩], 12, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw3 : List Sig := [(0xfffffffffffc00001fffffffffffffffffffffffffffffffffffffffffffffff, 0xa210951084a8842544212a210951084a8842544212a210951084a8842544212a),
   (0xffffffffffffffffe00000ffffffffffc00001ffffffffff800003ffffffffff, 0xc4a5262529312949894a4c4a5262529312949894a4c4a5262529312949894a4c),
   (0xfffffffffffffffffffff000007fffffffffe00000ffffffffffc00001fffff, 0x8c6384631c2318e118c708c6384631c2318e118c708c6384631c2318e118c70),
   (0xf000007ffffffffffffffffffff8000000000000000fffffffffffffffe00000, 0xf07c0783e03c1f01e0f80f07c0783e03c1f01e0f80f07c0783e03c1f01e0f80),
   (0x7ffffffffffffffffffffffffffffffffffff000000000000000000000, 0xff8007fc003fe001ff000ff8007fc003fe001ff000ff8007fc003fe001ff000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero01 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[0]! raw3[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero02 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[0]! raw3[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero03 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[0]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero04 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[0]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero12 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[1]! raw3[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero13 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[1]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero14 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[1]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero23 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[2]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero24 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[2]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Zero34 :
    slowBinary 7 0 (search 7 0) raw3 (coverage false raw3) raw3[3]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut3Zero : search 8 0 raw3 = false := by
  have bin : binaryMoves 7 0 (search 7 0) raw3 = false := by
    change scanPairs (slowBinary 7 0 (search 7 0) raw3 (coverage false raw3)) [raw3[0]!, raw3[1]!, raw3[2]!, raw3[3]!, raw3[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case3Zero01, case3Zero02, case3Zero03, case3Zero04, case3Zero12, case3Zero13, case3Zero14, case3Zero23, case3Zero24, case3Zero34, Bool.false_or]

  change stepTest 7 0 raw3 (search 7 0) (search 7 0) = false
  unfold stepTest
  rw [bin]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One01 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[0]! raw3[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One02 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[0]! raw3[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One03 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[0]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One04 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[0]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One12 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[1]! raw3[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One13 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[1]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One14 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[1]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One23 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[2]! raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One24 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[2]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3One34 :
    slowBinary 7 1 (search 7 1) raw3 (coverage true raw3) raw3[3]! raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Unary0 :
    unaryAt 7 0 (search 7 0) raw3 (coverage false raw3) raw3[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Unary1 :
    unaryAt 7 0 (search 7 0) raw3 (coverage false raw3) raw3[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Unary2 :
    unaryAt 7 0 (search 7 0) raw3 (coverage false raw3) raw3[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Unary3 :
    unaryAt 7 0 (search 7 0) raw3 (coverage false raw3) raw3[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case3Unary4 :
    unaryAt 7 0 (search 7 0) raw3 (coverage false raw3) raw3[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut3One : search 8 1 raw3 = false := by
  have bin : binaryMoves 7 1 (search 7 1) raw3 = false := by
    change scanPairs (slowBinary 7 1 (search 7 1) raw3 (coverage true raw3)) [raw3[0]!, raw3[1]!, raw3[2]!, raw3[3]!, raw3[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case3One01, case3One02, case3One03, case3One04, case3One12, case3One13, case3One14, case3One23, case3One24, case3One34, Bool.false_or]

  have un : unaryMoves 7 0 (search 7 0) raw3 = false := by
    change [raw3[0]!, raw3[1]!, raw3[2]!, raw3[3]!, raw3[4]!].any (unaryAt 7 0 (search 7 0) raw3 (coverage false raw3)) = false
    simp only [List.any_cons, List.any_nil, case3Unary0, case3Unary1, case3Unary2, case3Unary3, case3Unary4, Bool.false_or]

  change stepTest 7 1 raw3 (search 7 0) (search 7 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903367296 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3903367296 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3903367296 raw3 8 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut3Zero
      · exact ruledOut3One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 12]⟩], 13, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw4 : List Sig := [(0xfffffffffffc00001fffffffffffffffffffffffffffffff800003ffffffffff, 0xa2149510a4a8852544292a2149510a4a8852544292a2149510a4a8852544292a),
   (0xffffffffffffffffe00000ffffffffffc00001ffffffffffffffffffffffffff, 0xc4a126250931284989424c4a126250931284989424c4a126250931284989424c),
   (0xfffffffffffffffffffff000007fffffffffe00000ffffffffffc00001fffff, 0x8c6384631c2318e118c708c6384631c2318e118c708c6384631c2318e118c70),
   (0xf000007ffffffffffffffffffff8000000000000000fffffffffffffffe00000, 0xf07c0783e03c1f01e0f80f07c0783e03c1f01e0f80f07c0783e03c1f01e0f80),
   (0x7ffffffffffffffffffffffffffffffffffff000000000000000000000, 0xff8007fc003fe001ff000ff8007fc003fe001ff000ff8007fc003fe001ff000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut4Zero : search 7 0 raw4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut4One : search 7 1 raw4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903375488 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3903375488 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3903375488 raw4 7 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut4Zero
      · exact ruledOut4One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [6, 11]⟩], 12, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw5 : List Sig := [(0xfffffffffffc00001fffffffffffffffffffffffffffffff800003ffffffffff, 0xa21155108aa884554422aa21155108aa884554422aa21155108aa884554422aa),
   (0xfffffffffffffffe00000ffffffffffc00001fffffffffffffffc00001fffff, 0xc4a26625133128998944cc4a26625133128998944cc4a26625133128998944cc),
   (0xf000007fffffffffffffff000007fffffffffe00000fffffffffffffffe00000, 0x8c4784623c2311e1188f08c4784623c2311e1188f08c4784623c2311e1188f0),
   (0xfffffffffffffffffffffffffff8000000000000000fffffffffffffffffffff, 0xf0780783c03c1e01e0f00f0780783c03c1e01e0f00f0780783c03c1e01e0f00),
   (0x7ffffffffffffffffffffffffffffffffffff000000000000000000000, 0xff8007fc003fe001ff000ff8007fc003fe001ff000ff8007fc003fe001ff000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut5Zero : search 6 0 raw5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut5One : search 6 1 raw5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903383552 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3903383552 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3903383552 raw5 6 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut5Zero
      · exact ruledOut5One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [6, 10]⟩], 11, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw6 : List Sig := [(0xffffffffffc00001ffffffffffffffffffffffffffffffffffffc00001fffff, 0xa02a950154a80aa540552a02a950154a80aa540552a02a950154a80aa540552a),
   (0xffffffffffffffffe00000fffff800003ffffe00000fffffffffffffffffffff, 0xc543262a193150c98a864c543262a193150c98a864c543262a193150c98a864c),
   (0xffffffffffffffffffffff00000000003ffffffffff000007fffffffffffffff, 0x98c384c61c2630e13187098c384c61c2630e13187098c384c61c2630e131870),
   (0xf000007fffffffffffffffffffffffffc0000000000000007fffffffffe00000, 0xe0fc0707e0383f01c1f80e0fc0707e0383f01c1f80e0fc0707e0383f01c1f80),
   (0x7fffffffffffffffffffffffffffffffffffffffff8000000000000000, 0xff0007f8003fc001fe000ff0007f8003fc001fe000ff0007f8003fc001fe000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut6Zero : search 6 0 raw6 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut6One : search 6 1 raw6 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3936927872 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3936927872 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3936927872 raw6 6 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut6Zero
      · exact ruledOut6One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [8, 10]⟩], 11, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw7 : List Sig := [(0xf000007ffffc00001fffffffffffffffffffffffffffffffffffffffffe00000, 0xa0155500aaa80555402aaa0155500aaa80555402aaa0155500aaa80555402aaa),
   (0xffffffffffffffffe00000fffff800003ffffe00000fffff800003ffffffffff, 0xc546662a333151998a8ccc546662a333151998a8ccc546662a333151998a8ccc),
   (0xffffffffffffffffffffff00000000003ffffffffff00000000003ffffffffff, 0x998784cc3c2661e1330f0998784cc3c2661e1330f0998784cc3c2661e1330f0),
   (0xffffffffffffffffffffffffffffffffc000000000000000000003ffffffffff, 0xe1f8070fc0387e01c3f00e1f8070fc0387e01c3f00e1f8070fc0387e01c3f00),
   (0x7ffffffffffffffffffffffffffffffffffffffffffffffc0000000000, 0xfe0007f0003f8001fc000fe0007f0003f8001fc000fe0007f0003f8001fc000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut7Zero : search 3 0 raw7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut7One : search 3 1 raw7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937058816 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3937058816 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3937058816 raw7 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut7Zero
      · exact ruledOut7One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [5, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw8 : List Sig := [(0xffffffffffc00001ffffffffffffffffffffe00000ffffffffffc00001fffff, 0xa12555092aa84955424aaa12555092aa84955424aaa12555092aa84955424aaa),
   (0xf000007fffffffffe00000fffff800003fffffffffffffffffffffffffe00000, 0xc446662233311199888ccc446662233311199888ccc446662233311199888ccc),
   (0xffffffffffffffffffffff00000000003ffffffffff000007fffffffffffffff, 0x988784c43c2621e1310f0988784c43c2621e1310f0988784c43c2621e1310f0),
   (0xffffffffffffffffffffffffffffffffc0000000000000007fffffffffffffff, 0xe0f80707c0383e01c1f00e0f80707c0383e01c1f00e0f80707c0383e01c1f00),
   (0x7fffffffffffffffffffffffffffffffffffffffff8000000000000000, 0xff0007f8003fc001fe000ff0007f8003fc001fe000ff0007f8003fc001fe000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut8Zero : search 6 0 raw8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut8One : search 6 1 raw8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3939033088 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3939033088 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 3939033088 raw8 6 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut8Zero
      · exact ruledOut8One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [8, 10]⟩], 11, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw9 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1092010920109201092010920109201092010920109201092010920109201092),
   (0xfffffffff00000fffff00000fffff00000ffffffffff00000fffffffffffffff, 0xa524aa524aa524aa524aa524aa524aa524aa524aa524aa524aa524aa524aa524),
   (0xffffffffff0000000000ffffffffff00000ffffffffff00000fffff00000, 0xc638cc638cc638cc638cc638cc638cc638cc638cc638cc638cc638cc638cc638),
   (0xffffffffffffffffffff000000000000000fffffffffffffff0000000000, 0x7c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0),
   (0xfffffffffffffffffffffffffffffffffff0000000000000000000000000, 0xf800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut9Zero : search 5 0 raw9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut9One : search 5 1 raw9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2863179912 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2863179912 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2863179912 raw9 5 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut9Zero
      · exact ruledOut9One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [2, 4]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 9]⟩], 10, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

end PEqualNP.Outside.L_meta_1421_aux

open PEqualNP.Outside.L_meta_1421_aux in
theorem PEqualNP.Outside.L_meta_1421 :
    ∀ T ∈ ({0xaaa8a880, 0xe888a888, 0xe888e880, 0xe8a8a880, 0xe8a8c880, 0xe8a8e800, 0xeaa8c080, 0xeaaac000, 0xeac8e000, 0xaaa8a888} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gs o legal single correct
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact table0 gs o legal single correct
  · exact table1 gs o legal single correct
  · exact table2 gs o legal single correct
  · exact table3 gs o legal single correct
  · exact table4 gs o legal single correct
  · exact table5 gs o legal single correct
  · exact table6 gs o legal single correct
  · exact table7 gs o legal single correct
  · exact table8 gs o legal single correct
  · exact table9 gs o legal single correct
