import Mathlib.Tactic.FinCases
import PEqualNP.Defs
-- The live-wire semantics and search are adapted from L-meta-1007, Apache-2.0.
namespace PEqualNP.Outside.L_meta_1431_aux

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


def Impossible (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Live m t v.toFinset

lemma exclude_search {k t : Nat} {v : List Sig} (hv : v.Nodup) (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hv rfl))

lemma exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible k (t-1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Live j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Live j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

def index (key : Nat) (j : Fin 256) : Fin 256 := Fin.ofNat 256 ((key >>> (8 * j.val)) &&& 255)

def reindex (f : Fin 256 → Fin 256) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 256 → Fin 256) (a : B) (j : Nat) (hj : j < 256) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 256 → Fin 256) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 256 → Fin 256) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 256 → Fin 256) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 256 → Fin 256) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 256 → Fin 256) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

lemma reindex_injective {s inv : Fin 256 → Fin 256} (h : Function.LeftInverse inv s) :
    Function.Injective (reindex s) := by
  have hs := Finite.surjective_of_injective h.injective
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨x,hx⟩ := hs ⟨j,hj⟩
  have c := congrArg (fun a : B => a.getLsbD x.val) eq
  simpa only [reindex_bit _ _ _ x.isLt, Fin.eta, hx] using c

def action (g : Fin 256 ≃ Fin 256) (a : Sig) : Sig :=
  (reindex g a.1, reindex g a.2)

lemma action_neg (g : Fin 256 ≃ Fin 256) (a : Sig) : action g (neg a) = neg (action g a) := by
  simp [action, neg, reindex_not]

lemma action_bin (g : Fin 256 ≃ Fin 256) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := by
  cases d <;> simp [action, bin, reindex_and, reindex_or]

lemma action_zero (g : Fin 256 ≃ Fin 256) : action g zero = zero :=
  Prod.ext (reindex_zero _) (reindex_zero _)

lemma action_one (g : Fin 256 ≃ Fin 256) : action g one = one :=
  Prod.ext (reindex_top _) (reindex_top _)

lemma action_target (g : Fin 256 ≃ Fin 256) : action g target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma action_injective (g : Fin 256 ≃ Fin 256) : Function.Injective (action g) := by
  intro a b eq
  have hi := reindex_injective (inv := g.symm) g.left_inv
  have hf : reindex g a.1 = reindex g b.1 :=
    congrArg (fun x : Sig => x.1) eq
  have hs : reindex g a.2 = reindex g b.2 :=
    congrArg (fun x : Sig => x.2) eq
  exact Prod.ext (hi hf) (hi hs)

lemma action_proper (g : Fin 256 ≃ Fin 256) (a : Sig) (h : proper a) : proper (action g a) := by
  constructor
  · intro h0
    exact h.1 ((action_injective g) (h0.trans (action_zero g).symm))
  · intro h1
    exact h.2 ((action_injective g) (h1.trans (action_one g).symm))

lemma restricted_action {k t : Nat} {S : Finset Sig} (h : Live k t S) (g : Fin 256 ≃ Fin 256) :
    Live k t (S.image (action g)) := by
  induction h using liveInd with
  | stop => simpa [action_target] using Live.stop
  | @unary k t U a ha hf tail ih =>
    simp only [Finset.image_insert, action_neg] at ih ⊢
    have hne : neg (action g a) ∉ insert (action g a) (U.image (action g)) := by
      rw [← Finset.image_insert, ← action_neg]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Live.unary (action_proper _ _ ha) hne ih
  | @binary k t U a b d ha hb hab hf tail ih =>
    simp only [Finset.image_insert, action_bin] at ih ⊢
    have hne : bin d (action g a) (action g b) ∉ insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← Finset.image_insert, ← Finset.image_insert, ← action_bin]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Live.binary (action_proper _ _ ha) (action_proper _ _ hb) (fun e => hab ((action_injective g) e)) hne ih

lemma rotate_impossible {k t : Nat} {w z : List Sig} (g : Fin 256 ≃ Fin 256)
    (hp : (w.map (action g)).Perm z) (hn : Impossible k t z) : Impossible k t w := by
  intro m hm h
  apply hn m hm
  suffices hi : z.toFinset = w.toFinset.image (action g) by rw [hi]; exact restricted_action h g
  ext a
  simp only [List.mem_toFinset, hp.mem_iff.symm, List.mem_map, Finset.mem_image]

lemma impPerm {k t : Nat} {w z : List Sig} (p : w.Perm z) (h : Impossible k t z) : Impossible k t w := by
  have e : w.toFinset = z.toFinset := by ext x; simpa using (p.mem_iff (a := x))
  simpa only [Impossible,e] using h

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

def Clean (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private lemma findWire {v : Sig} {w : List Sig} (h : v ∈ w) : ∃ i : Nat, w.getD i zero = v := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  exact ⟨i,by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq⟩

private lemma replay {k t S} (h : Live k t S) : t = 0 → ∀ (w : List Sig),
    (∀ v ∈ S, v ∈ w) → ∃ gs : List Gate, Clean gs ∧ gs.length ≤ k ∧ target ∈ execute gs w := by
  induction h using liveInd with
  | stop =>
    intro _ w hw
    exact ⟨[],by simp [Clean],by simp,hw target (by simp)⟩
  | unary _ _ _ _ => intro ht; omega
  | @binary k t U a b d _ _ _ _ _ ih =>
    intro ht w hw
    obtain ⟨i,hi⟩ := findWire (hw a (by simp))
    obtain ⟨j,hj⟩ := findWire (hw b (by simp))
    let g : Gate := ⟨if d then .or else .and,[i,j]⟩
    have he : gv w g = bin d a b := by
      cases d
      · change bin false (w.getD i zero) (bin false (w.getD j zero) one) = _
        rw [hi,hj,(bin_laws b).1]
      · change bin true (w.getD i zero) (bin true (w.getD j zero) zero) = _
        rw [hi,hj,(bin_laws b).2.1]
    have hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by cases d <;> simp [g]
    obtain ⟨gs,hgs,len,out⟩ := ih ht (w++[gv w g]) (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp [he]
      · exact List.mem_append_left _ (hw _ (by simp [hv])))
    refine ⟨g::gs,?_,by simp; omega,out⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hh
    · exact hg
    · exact hgs _ hh

private lemma bit_target (b i) : bit b i target = b := by
  cases b
  · simp [bit,target]
  · exact bit_one true i

theorem from_target (T : Nat) (raw : List Sig)
    (rid : List.ofFn (fun i : Fin 5 => raw.getD i.val zero) = raw)
    (rows : ∀ b i, evalT T (sample raw b i) = b)
    (allRows : ∀ x : Fin 5 → Bool, ∃ b i, sample raw b i = x)
    (gs : List Gate) (clean : Clean gs) (hit : target ∈ execute gs raw) :
    ∃ o : Nat, ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT T x := by
  obtain ⟨o,ho⟩ := findWire hit
  refine ⟨o,?_⟩
  intro x
  obtain ⟨b,i,rfl⟩ := allRows x
  rw [rows,sample_list raw rid]
  have legal (g : Gate) (hg : g ∈ gs) : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    rcases (clean g hg).1 with a | a <;> simp [a]
  change (gs.foldl _ (raw.map (bit b i))).getD o false = b
  rw [←execute_bits gs b i raw legal,b_read,ho,bit_target]

theorem solve (T : Nat) (raw : List Sig) (cap : Nat)
    (rid : List.ofFn (fun i : Fin 5 => raw.getD i.val zero) = raw)
    (rows : ∀ b i, evalT T (sample raw b i) = b)
    (allRows : ∀ x : Fin 5 → Bool, ∃ b i, sample raw b i = x)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (noOne : Impossible cap 1 raw)
    (gs : List Gate) (o : Nat) (legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit))
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT T x)
    (upper : ∃ ds : List Gate, ∃ p : Nat, Clean ds ∧ ds.length = cap+1 ∧
      ∀ x, Circuit.eval ⟨ds,p⟩ (List.ofFn x) = evalT T x) :
    ∃ ds : List Gate, ∃ p : Nat, Clean ds ∧ ds.length ≤ gs.length ∧
      ∀ x, Circuit.eval ⟨ds,p⟩ (List.ofFn x) = evalT T x := by
  by_cases small : gs.length ≤ cap
  · obtain ⟨k,t,S,hk,ht,live,sub⟩ := extract gs raw legal (circuit_target T raw rid rows ⟨gs,o⟩ legal he)
    have h1 := notCount gs single
    by_cases z : t = 0
    · obtain ⟨ds,hds,n,hit⟩ := replay live z raw sub
      obtain ⟨p,hp⟩ := from_target T raw rid rows allRows ds hds hit
      exact ⟨ds,p,hds,by omega,hp⟩
    · have one : t = 1 := by omega
      subst t
      have eq := necessary raw essential live sub
      exact (noOne k (by omega) (eq ▸ live)).elim
  · obtain ⟨ds,p,hds,n,hp⟩ := upper
    exact ⟨ds,p,hds,by omega,hp⟩
open PEqualNP.CircuitLowerBounds
def r0 : List Sig := [(0xffffc0001ffffffffffffffffe0000ffffffffffffe0000fffffffffffffffff,0x20a81054082a0415020a81054082a0415020a81054082a0415020a81054082a),(0xffffffffe0000ffff80003ffffffff00007ffffffffffff00007fffc0001ffff,0x245312298914c48a6245312298914c48a6245312298914c48a6245312298914c),(0xfffffffffffff000000003ffffffffffff80003ffffffffffff800000001ffff,0x489c244e122709138489c244e122709138489c244e122709138489c244e12270),(0x7ffffffffffffffffffffc00000000000000003ffffffffffffffffffffe0000,0x70e038701c380e1c070e038701c380e1c070e038701c380e1c070e038701c380),(0x7fffffffffffffffffffffffffffffffffffffc0000000000000000000000000,0x7f003f801fc00fe007f003f801fc00fe007f003f801fc00fe007f003f801fc00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative0_1 : Impossible 7 1 r0 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132928 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132928 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132928 r0 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative0_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.and,[0,5]⟩,⟨.or,[6,3]⟩,⟨.or,[0,5]⟩,⟨.or,[1,2]⟩,⟨.and,[9,4]⟩,⟨.or,[10,7]⟩,⟨.and,[8,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r1 : List Sig := [(0xffffc0001ffffffffffffffffe0000fffffffffffffffff00007ffffffffffff,0x2a8015400aa0055002a8015400aa0055002a8015400aa0055002a8015400aa),(0x7fffffffe0000ffff80003ffffffff00007fffc0001ffffffff80003fffe0000,0x24b31259892cc496624b31259892cc496624b31259892cc496624b31259892cc),(0x7ffffffffffff000000003ffffffffffff800000001ffffffffffffc00000000,0x493c249e124f09278493c249e124f09278493c249e124f09278493c249e124f0),(0xfffffffffffffffffffffc000000000000000000001fffffffffffffffffffff,0x71c038e01c700e38071c038e01c700e38071c038e01c700e38071c038e01c700),(0x7fffffffffffffffffffffffffffffffffffffffffe000000000000000000000,0x7e003f001f800fc007e003f001f800fc007e003f001f800fc007e003f001f800)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative1_1 : Impossible 3 1 r1 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941263872 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941263872 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941263872 r1 3 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative1_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.or,[0,5]⟩,⟨.or,[3,4]⟩,⟨.and,[6,7]⟩],8,by simp [Clean],rfl,by decide +kernel⟩

def r2 : List Sig := [(0xffffc0001ffffffff80003ffffffff00007fffffffe0000fffffffffffffffff,0xa2285114288a14450a2285114288a14450a2285114288a14450a2285114288a),(0x7fffffffe0000ffffffffc0001ffffffff80003ffffffff00007fffffffe0000,0xc4b06258312c18960c4b06258312c18960c4b06258312c18960c4b06258312c),(0xfffffffffffff0000000000001fffffffffffffffffffffffff80003ffffffff,0x508c284614230a118508c284614230a118508c284614230a118508c284614230),(0x7ffffffffffffffffffffffffe0000000000003ffffffffffffffffc00000000,0x60f03078183c0c1e060f03078183c0c1e060f03078183c0c1e060f03078183c0),(0x7fffffffffffffffffffffffffffffffffffffc0000000000000000000000000,0x7f003f801fc00fe007f003f801fc00fe007f003f801fc00fe007f003f801fc00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative2_1 : Impossible 7 1 r2 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4007717024 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4007717024 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4007717024 r2 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative2_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[5,4]⟩,⟨.and,[3,6]⟩,⟨.or,[2,7]⟩,⟨.or,[3,6]⟩,⟨.and,[1,9]⟩,⟨.or,[0,10]⟩,⟨.and,[11,8]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_2 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefcfdfbfaf9f8f4f3f2f7f6f5f1f0efeeedebeceae9e8e7e3e2e1e6e5e4e0dfdedddcdadbd9d8d7d6d2d1d0d5d4d3cfcecdcc989697959493928e8d8c91908f8b8a8988878586848382817d7c7b807f7e7a797877767475737271706c6b6a6f6e6d69686766cbc9cac8c7c6c5c1c0bfc4c3c2bebdbcbbbab8b9b7b6b5b4b0afaeb3b2b1adacabaaa9a7a8a6a5a4a39f9e9da2a1a09c9b9a996563646261605f5b5a595e5d5c5857565554525351504f4e4a49484d4c4b47464544434142403f3e3d3938373c3b3a363534333230312f2e2d2c2827262b2a2925242322100e0f0d0c0b0a06050409080703020100211f201e1d1c1b1716151a191814131211,index 0xfffefcfdfbfaf9f8f4f3f2f7f6f5f1f0efeeedebeceae9e8e7e3e2e1e6e5e4e0dfdedddcdadbd9d8d7d6d2d1d0d5d4d3cfcecdcc989697959493928e8d8c91908f8b8a8988878586848382817d7c7b807f7e7a797877767475737271706c6b6a6f6e6d69686766cbc9cac8c7c6c5c1c0bfc4c3c2bebdbcbbbab8b9b7b6b5b4b0afaeb3b2b1adacabaaa9a7a8a6a5a4a39f9e9da2a1a09c9b9a996563646261605f5b5a595e5d5c5857565554525351504f4e4a49484d4c4b47464544434142403f3e3d3938373c3b3a363534333230312f2e2d2c2827262b2a2925242322100e0f0d0c0b0a06050409080703020100211f201e1d1c1b1716151a191814131211,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_3 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffef8fdf7f6f5fcf4f3f2fbfaf9f1f0efeeede7ece6e5e4ebe3e2e1eae9e8e0dfdedddcd6dbd5d4d3dad2d1d0d9d8d7cfcecdcc544e534d4c4b524a494851504f47464544433d423c3b3a41393837403f3e36353433322c312b2a29302827262f2e2d25242322cbc5cac4c3c2c9c1c0bfc8c7c6bebdbcbbbab4b9b3b2b1b8b0afaeb7b6b5adacabaaa9a3a8a2a1a0a79f9e9da6a5a49c9b9a99211b201a19181f1716151e1d1c1413121198929791908f968e8d8c9594938b8a8988878186807f7e857d7c7b8483827a7978777670756f6e6d746c6b6a73727169686766100a0f0908070e0605040d0c0b03020100655f645e5d5c635b5a5962616058575655,index 0xfffefcf8f4f3f2fdfbfaf9f7f6f5f1f0efeeedebe7e3e2e1eceae9e8e6e5e4e0dfdedddcdad6d2d1d0dbd9d8d7d5d4d3cfcecdcc9896928e8d8c9795949391908f8b8a89888785817d7c7b86848382807f7e7a7978777674706c6b6a757372716f6e6d6968676654524e4a49485351504f4d4c4b4746454443413d39383742403f3e3c3b3a3635343332302c282726312f2e2d2b2a2925242322100e0a0605040f0d0c0b09080703020100cbc9c5c1c0bfcac8c7c6c4c3c2bebdbcbbbab8b4b0afaeb9b7b6b5b3b2b1adacabaaa9a7a39f9e9da8a6a5a4a2a1a09c9b9a9965635f5b5a59646261605e5d5c58575655211f1b171615201e1d1c1a191814131211,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_6 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfafbf9f8f6f7f5f3f4f2f1eff0eedcdbdad8d9d7d6d4d5d3d1d2d0cfcdceccedecebe9eae8e7e5e6e4e2e3e1e0dedfddcbcac9c7c8c6c5c3c4c2c0c1bfbebcbdbba9a8a7a5a6a4a3a1a2a09e9f9d9c9a9b99bab9b8b6b7b5b4b2b3b1afb0aeadabacaa9897969495939290918f8d8e8c8b898a88767574727371706e6f6d6b6c6a69676866878685838482817f807e7c7d7b7a7879776564636162605f5d5e5c5a5b595856575554535250514f4e4c4d4b494a48474546443231302e2f2d2c2a2b29272826252324224342413f403e3d3b3c3a3839373634353321201f1d1e1c1b191a1816171514121311100f0e0c0d0b0a08090705060403010200,index 0xfffefdfcfafbf9f8f6f7f5f3f4f2f1eff0eedcdbdad8d9d7d6d4d5d3d1d2d0cfcdceccedecebe9eae8e7e5e6e4e2e3e1e0dedfddcbcac9c7c8c6c5c3c4c2c0c1bfbebcbdbba9a8a7a5a6a4a3a1a2a09e9f9d9c9a9b99bab9b8b6b7b5b4b2b3b1afb0aeadabacaa9897969495939290918f8d8e8c8b898a88767574727371706e6f6d6b6c6a69676866878685838482817f807e7c7d7b7a7879776564636162605f5d5e5c5a5b595856575554535250514f4e4c4d4b494a48474546443231302e2f2d2c2a2b29272826252324224342413f403e3d3b3c3a3839373634353321201f1d1e1c1b191a1816171514121311100f0e0c0d0b0a08090705060403010200,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_8 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefcfdfafbf9f8f3f4f2f6f7f5f1eff0eedcdadbd8d9d7d6d1d2d0d4d5d3cfcdceccedebece9eae8e7e2e3e1e5e6e4e0dedfdd989697949593928d8e8c90918f8b898a88767475727371706b6c6a6e6f6d69676866878586838482817c7d7b7f807e7a787977cbc9cac7c8c6c5c0c1bfc3c4c2bebcbdbba9a7a8a5a6a4a39e9f9da1a2a09c9a9b99bab8b9b6b7b5b4afb0aeb2b3b1adabacaa6563646162605f5a5b595d5e5c5856575554525350514f4e494a484c4d4b474546443230312e2f2d2c2728262a2b29252324224341423f403e3d3839373b3c3a36343533100e0f0c0d0b0a05060408090703010200211f201d1e1c1b161715191a1814121311,index 0xfffefcfdfafbf9f8f3f4f2f6f7f5f1eff0eedcdadbd8d9d7d6d1d2d0d4d5d3cfcdceccedebece9eae8e7e2e3e1e5e6e4e0dedfdd989697949593928d8e8c90918f8b898a88767475727371706b6c6a6e6f6d69676866878586838482817c7d7b7f807e7a787977cbc9cac7c8c6c5c0c1bfc3c4c2bebcbdbba9a7a8a5a6a4a39e9f9da1a2a09c9a9b99bab8b9b6b7b5b4afb0aeb2b3b1adabacaa6563646162605f5a5b595d5e5c5856575554525350514f4e494a484c4d4b474546443230312e2f2d2c2728262a2b29252324224341423f403e3d3839373b3c3a36343533100e0f0c0d0b0a05060408090703010200211f201d1e1c1b161715191a1814121311,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_9 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffef8fdf6f7f5fcf3f4f2fafbf9f1eff0eedcd6dbd4d5d3dad1d2d0d8d9d7cfcdceccede7ece5e6e4ebe2e3e1e9eae8e0dedfdd544e534c4d4b52494a4850514f47454644322c312a2b29302728262e2f2d25232422433d423b3c3a413839373f403e36343533cbc5cac3c4c2c9c0c1bfc7c8c6bebcbdbba9a3a8a1a2a0a79e9f9da5a6a49c9a9b99bab4b9b2b3b1b8afb0aeb6b7b5adabacaa211b20191a181f1617151d1e1c1412131198929790918f968d8e8c9495938b898a887670756e6f6d746b6c6a727371696768668781867f807e857c7d7b8384827a787977100a0f0809070e0506040c0d0b03010200655f645d5e5c635a5b5961626058565755,index 0xfffefcf8f3f4f2fdfafbf9f6f7f5f1eff0eedcdad6d1d2d0dbd8d9d7d4d5d3cfcdceccedebe7e2e3e1ece9eae8e5e6e4e0dedfdd9896928d8e8c9794959390918f8b898a887674706b6c6a757273716e6f6d696768668785817c7d7b868384827f807e7a78797754524e494a485350514f4c4d4b4745464432302c272826312e2f2d2a2b292523242243413d383937423f403e3b3c3a36343533100e0a0506040f0c0d0b08090703010200cbc9c5c0c1bfcac7c8c6c3c4c2bebcbdbba9a7a39e9f9da8a5a6a4a1a2a09c9a9b99bab8b4afb0aeb9b6b7b5b2b3b1adabacaa65635f5a5b59646162605d5e5c58565755211f1b161715201d1e1c191a1814121311,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_1 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdf8f7f6f5fcfbfaf9f4f3f2f1f0efeeedece7e6e5e4ebeae9e8e3e2e1e0dfdedddcdbd6d5d4d3dad9d8d7d2d1d0cfcecdcccbcac5c4c3c2c9c8c7c6c1c0bfbebdbcbbbab9b4b3b2b1b8b7b6b5b0afaeadacabaaa9a8a3a2a1a0a7a6a5a49f9e9d9c9b9a9954534e4d4c4b5251504f4a49484746454443423d3c3b3a41403f3e3938373635343332312c2b2a29302f2e2d2827262524232221201b1a19181f1e1d1c1716151413121198979291908f969594938e8d8c8b8a8988878681807f7e858483827d7c7b7a7978777675706f6e6d747372716c6b6a6968676665645f5e5d5c636261605b5a5958575655100f0a0908070e0d0c0b06050403020100,index 0xfffefdf8f7f6f5fcfbfaf9f4f3f2f1f0efeeedece7e6e5e4ebeae9e8e3e2e1e0dfdedddcdbd6d5d4d3dad9d8d7d2d1d0cfcecdcccbcac5c4c3c2c9c8c7c6c1c0bfbebdbcbbbab9b4b3b2b1b8b7b6b5b0afaeadacabaaa9a8a3a2a1a0a7a6a5a49f9e9d9c9b9a9954534e4d4c4b5251504f4a49484746454443423d3c3b3a41403f3e3938373635343332312c2b2a29302f2e2d2827262524232221201b1a19181f1e1d1c1716151413121198979291908f969594938e8d8c8b8a8988878681807f7e858483827d7c7b7a7978777675706f6e6d747372716c6b6a6968676665645f5e5d5c636261605b5a5958575655100f0a0908070e0d0c0b06050403020100,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_4 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefcf8f4f3f2fdfbfaf9f7f6f5f1f0efeeedebe7e3e2e1eceae9e8e6e5e4e0dfdedddcdad6d2d1d0dbd9d8d7d5d4d3cfcecdcc9896928e8d8c9795949391908f8b8a89888785817d7c7b86848382807f7e7a7978777674706c6b6a757372716f6e6d6968676654524e4a49485351504f4d4c4b4746454443413d39383742403f3e3c3b3a3635343332302c282726312f2e2d2b2a2925242322100e0a0605040f0d0c0b09080703020100cbc9c5c1c0bfcac8c7c6c4c3c2bebdbcbbbab8b4b0afaeb9b7b6b5b3b2b1adacabaaa9a7a39f9e9da8a6a5a4a2a1a09c9b9a9965635f5b5a59646261605e5d5c58575655211f1b171615201e1d1c1a191814131211,index 0xfffef8fdf7f6f5fcf4f3f2fbfaf9f1f0efeeede7ece6e5e4ebe3e2e1eae9e8e0dfdedddcd6dbd5d4d3dad2d1d0d9d8d7cfcecdcc544e534d4c4b524a494851504f47464544433d423c3b3a41393837403f3e36353433322c312b2a29302827262f2e2d25242322cbc5cac4c3c2c9c1c0bfc8c7c6bebdbcbbbab4b9b3b2b1b8b0afaeb7b6b5adacabaaa9a3a8a2a1a0a79f9e9da6a5a49c9b9a99211b201a19181f1716151e1d1c1413121198929791908f968e8d8c9594938b8a8988878186807f7e857d7c7b8483827a7978777670756f6e6d746c6b6a73727169686766100a0f0908070e0605040d0c0b03020100655f645e5d5c635b5a5962616058575655,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym3_7 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdf8f6f7f5fcfafbf9f3f4f2f1eff0eedcdbd6d4d5d3dad8d9d7d1d2d0cfcdceccedece7e5e6e4ebe9eae8e2e3e1e0dedfddcbcac5c3c4c2c9c7c8c6c0c1bfbebcbdbba9a8a3a1a2a0a7a5a6a49e9f9d9c9a9b99bab9b4b2b3b1b8b6b7b5afb0aeadabacaa54534e4c4d4b5250514f494a484745464432312c2a2b29302e2f2d2728262523242243423d3b3c3a413f403e3839373634353321201b191a181f1d1e1c1617151412131198979290918f969495938d8e8c8b898a887675706e6f6d747273716b6c6a696768668786817f807e858384827c7d7b7a78797765645f5d5e5c636162605a5b5958565755100f0a0809070e0c0d0b05060403010200,index 0xfffefdf8f6f7f5fcfafbf9f3f4f2f1eff0eedcdbd6d4d5d3dad8d9d7d1d2d0cfcdceccedece7e5e6e4ebe9eae8e2e3e1e0dedfddcbcac5c3c4c2c9c7c8c6c0c1bfbebcbdbba9a8a3a1a2a0a7a5a6a49e9f9d9c9a9b99bab9b4b2b3b1b8b6b7b5afb0aeadabacaa54534e4c4d4b5250514f494a484745464432312c2a2b29302e2f2d2728262523242243423d3b3c3a413f403e3839373634353321201b191a181f1d1e1c1617151412131198979290918f969495938d8e8c8b898a887675706e6f6d747273716b6c6a696768668786817f807e858384827c7d7b7a78797765645f5d5e5c636162605a5b5958565755100f0a0809070e0c0d0b05060403010200,by decide +kernel,by decide +kernel⟩

def r3 : List Sig := [(0xffffc0001ffffffff80003ffffffff00007ffffffffffff00007ffffffffffff,0x44a82254112a0895044a82254112a0895044a82254112a0895044a82254112a),(0xffffffffe0000ffffffffc0001ffffffff80003ffffffffffff80003ffffffff,0x89304498224c1126089304498224c1126089304498224c1126089304498224c),(0xfffffffffffff0000000000001ffffffffffffc0001ffffffffffffc0001ffff,0x511c288e14470a238511c288e14470a238511c288e14470a238511c288e14470),(0xfffffffffffffffffffffffffe00000000000000001ffffffffffffffffe0000,0x61e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f018780),(0xffffffffffffffffffffffffffffffffffffffffffe000000000000000000000,0x7e003f001f800fc007e003f001f800fc007e003f001f800fc007e003f001f800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_1_0 : action sym3_1 (r3.getD 0 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_1_1 : action sym3_1 (r3.getD 1 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_1_2 : action sym3_1 (r3.getD 2 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_1_3 : action sym3_1 (r3.getD 3 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_1_4 : action sym3_1 (r3.getD 4 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_2_0 : action sym3_2 (r3.getD 0 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_2_1 : action sym3_2 (r3.getD 1 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_2_2 : action sym3_2 (r3.getD 2 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_2_3 : action sym3_2 (r3.getD 3 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_2_4 : action sym3_2 (r3.getD 4 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_3_0 : action sym3_3 (r3.getD 0 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_3_1 : action sym3_3 (r3.getD 1 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_3_2 : action sym3_3 (r3.getD 2 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_3_3 : action sym3_3 (r3.getD 3 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_3_4 : action sym3_3 (r3.getD 4 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_4_0 : action sym3_4 (r3.getD 0 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_4_1 : action sym3_4 (r3.getD 1 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_4_2 : action sym3_4 (r3.getD 2 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_4_3 : action sym3_4 (r3.getD 3 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_4_4 : action sym3_4 (r3.getD 4 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_6_0 : action sym3_6 (r3.getD 0 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_6_1 : action sym3_6 (r3.getD 1 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_6_2 : action sym3_6 (r3.getD 2 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_6_3 : action sym3_6 (r3.getD 3 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_6_4 : action sym3_6 (r3.getD 4 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_7_0 : action sym3_7 (r3.getD 0 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_7_1 : action sym3_7 (r3.getD 1 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_7_2 : action sym3_7 (r3.getD 2 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_7_3 : action sym3_7 (r3.getD 3 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_7_4 : action sym3_7 (r3.getD 4 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_8_0 : action sym3_8 (r3.getD 0 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_8_1 : action sym3_8 (r3.getD 1 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_8_2 : action sym3_8 (r3.getD 2 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_8_3 : action sym3_8 (r3.getD 3 zero) = r3.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_8_4 : action sym3_8 (r3.getD 4 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_9_0 : action sym3_9 (r3.getD 0 zero) = r3.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_9_1 : action sym3_9 (r3.getD 1 zero) = r3.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_9_2 : action sym3_9 (r3.getD 2 zero) = r3.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_9_3 : action sym3_9 (r3.getD 3 zero) = r3.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot3_9_4 : action sym3_9 (r3.getD 4 zero) = r3.getD 2 zero := by decide +kernel

def x3_0 : Sig := r3.getD 0 zero

def x3_1 : Sig := r3.getD 1 zero

def x3_2 : Sig := r3.getD 2 zero

def x3_3 : Sig := r3.getD 3 zero

def x3_4 : Sig := r3.getD 4 zero

def y3_5 : Sig := neg x3_0

def y3_6 : Sig := bin false y3_5 x3_1

def y3_7 : Sig := bin true y3_5 x3_1

def y3_8 : Sig := bin false y3_5 x3_2

def y3_9 : Sig := bin true y3_5 x3_2

def y3_10 : Sig := bin false y3_5 x3_3

def y3_11 : Sig := bin true y3_5 x3_3

def y3_12 : Sig := bin false y3_5 x3_4

def y3_13 : Sig := bin true y3_5 x3_4

def y3_14 : Sig := bin false x3_0 x3_1

def y3_15 : Sig := bin true x3_0 x3_1

def y3_16 : Sig := bin false x3_0 x3_2

def y3_17 : Sig := bin true x3_0 x3_2

def y3_18 : Sig := bin false x3_0 x3_3

def y3_19 : Sig := bin true x3_0 x3_3

def y3_20 : Sig := bin false x3_0 x3_4

def y3_21 : Sig := bin true x3_0 x3_4

def y3_22 : Sig := bin false x3_1 x3_2

def y3_23 : Sig := bin true x3_1 x3_2

def y3_24 : Sig := bin false x3_1 x3_3

def y3_25 : Sig := bin true x3_1 x3_3

def y3_26 : Sig := bin false x3_1 x3_4

def y3_27 : Sig := bin true x3_1 x3_4

def y3_28 : Sig := bin false x3_2 x3_3

def y3_29 : Sig := bin true x3_2 x3_3

def y3_30 : Sig := bin false x3_2 x3_4

def y3_31 : Sig := bin true x3_2 x3_4

def y3_32 : Sig := bin false x3_3 x3_4

def y3_33 : Sig := bin true x3_3 x3_4

def y3_34 : Sig := neg x3_2

def y3_35 : Sig := bin false y3_34 x3_0

def y3_36 : Sig := bin true y3_34 x3_0

def y3_37 : Sig := bin false y3_34 x3_1

def y3_38 : Sig := bin true y3_34 x3_1

def y3_39 : Sig := bin false y3_34 x3_3

def y3_40 : Sig := bin true y3_34 x3_3

def y3_41 : Sig := bin false y3_34 x3_4

def y3_42 : Sig := bin true y3_34 x3_4

def y3_43 : Sig := neg y3_14

def y3_44 : Sig := neg x3_1

def y3_45 : Sig := neg x3_3

def y3_46 : Sig := neg x3_4

def y3_47 : Sig := bin false y3_14 x3_2

def y3_48 : Sig := bin true y3_14 x3_2

def y3_49 : Sig := bin false y3_14 x3_3

def y3_50 : Sig := bin true y3_14 x3_3

def y3_51 : Sig := bin false y3_14 x3_4

def y3_52 : Sig := bin true y3_14 x3_4

def y3_53 : Sig := neg y3_15

def y3_54 : Sig := bin false y3_15 x3_2

def y3_55 : Sig := bin true y3_15 x3_2

def y3_56 : Sig := bin false y3_15 x3_3

def y3_57 : Sig := bin true y3_15 x3_3

def y3_58 : Sig := bin false y3_15 x3_4

def y3_59 : Sig := bin true y3_15 x3_4

def y3_60 : Sig := neg y3_16

def y3_61 : Sig := bin true y3_16 x3_1

def y3_62 : Sig := bin false y3_16 x3_3

def y3_63 : Sig := bin true y3_16 x3_3

def y3_64 : Sig := bin false y3_16 x3_4

def y3_65 : Sig := bin true y3_16 x3_4

def y3_66 : Sig := neg y3_17

def y3_67 : Sig := bin false y3_17 x3_1

def y3_68 : Sig := bin false y3_17 x3_3

def y3_69 : Sig := bin true y3_17 x3_3

def y3_70 : Sig := bin false y3_17 x3_4

def y3_71 : Sig := bin true y3_17 x3_4

def y3_72 : Sig := neg y3_28

def y3_73 : Sig := bin true y3_28 x3_0

def y3_74 : Sig := bin false y3_28 x3_1

def y3_75 : Sig := bin true y3_28 x3_1

def y3_76 : Sig := bin false y3_28 x3_4

def y3_77 : Sig := bin true y3_28 x3_4

def y3_78 : Sig := neg y3_29

def y3_79 : Sig := bin false y3_29 x3_0

def y3_80 : Sig := bin false y3_29 x3_1

def y3_81 : Sig := bin true y3_29 x3_1

def y3_82 : Sig := bin false y3_29 x3_4

def y3_83 : Sig := bin true y3_29 x3_4

def s3_1u0 : List Sig := [neg (r3.getD 0 zero),r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1u0u : List (List Sig) := []

lemma s3_1u0ux (v : List Sig) (h : (!s3_1u0u.contains v) = false) : Impossible 7 0 v := by
  simp [s3_1u0u] at h

def s3_1u0b0 : List Sig := [y3_6,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b0x : Impossible 7 0 s3_1u0b0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b1 : List Sig := [y3_6,y3_5,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b1x : Impossible 7 0 s3_1u0b1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b2 : List Sig := [y3_7,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b2x : Impossible 7 0 s3_1u0b2 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b3 : List Sig := [y3_7,y3_5,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b3x : Impossible 7 0 s3_1u0b3 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b4 : List Sig := [y3_8,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b4x : Impossible 7 0 s3_1u0b4 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b5 : List Sig := [y3_8,y3_5,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b5x : Impossible 7 0 s3_1u0b5 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b6 : List Sig := [y3_9,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b6x : Impossible 7 0 s3_1u0b6 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b7 : List Sig := [y3_9,y3_5,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b7x : Impossible 7 0 s3_1u0b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b8 : List Sig := [y3_10,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b8x : Impossible 7 0 s3_1u0b8 := rotate_impossible sym3_2 (z := s3_1u0b4) (by simp only [s3_1u0b8,x3_0,x3_1,x3_2,x3_3,x3_4,y3_10,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b4x

def s3_1u0b9 : List Sig := [y3_10,y3_5,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b9x : Impossible 7 0 s3_1u0b9 := rotate_impossible sym3_2 (z := s3_1u0b5) (by simp only [s3_1u0b9,x3_0,x3_1,x3_2,x3_3,x3_4,y3_10,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b5x

def s3_1u0b10 : List Sig := [y3_11,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b10x : Impossible 7 0 s3_1u0b10 := rotate_impossible sym3_2 (z := s3_1u0b6) (by simp only [s3_1u0b10,x3_0,x3_1,x3_2,x3_3,x3_4,y3_11,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b6x

def s3_1u0b11 : List Sig := [y3_11,y3_5,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b11x : Impossible 7 0 s3_1u0b11 := rotate_impossible sym3_2 (z := s3_1u0b7) (by simp only [s3_1u0b11,x3_0,x3_1,x3_2,x3_3,x3_4,y3_11,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b7x

def s3_1u0b12 : List Sig := [y3_12,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b12x : Impossible 7 0 s3_1u0b12 := rotate_impossible sym3_3 (z := s3_1u0b4) (by simp only [s3_1u0b12,x3_0,x3_1,x3_2,x3_3,x3_4,y3_12,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b4x

def s3_1u0b13 : List Sig := [y3_12,y3_5,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b13x : Impossible 7 0 s3_1u0b13 := rotate_impossible sym3_3 (z := s3_1u0b5) (by simp only [s3_1u0b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_12,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b5x

def s3_1u0b14 : List Sig := [y3_13,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b14x : Impossible 7 0 s3_1u0b14 := rotate_impossible sym3_3 (z := s3_1u0b6) (by simp only [s3_1u0b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_13,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b6x

def s3_1u0b15 : List Sig := [y3_13,y3_5,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b15x : Impossible 7 0 s3_1u0b15 := rotate_impossible sym3_3 (z := s3_1u0b7) (by simp only [s3_1u0b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_13,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b7x

def s3_1u0b16 : List Sig := [y3_14,x3_0,x3_1,y3_5,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b16x : Impossible 7 0 s3_1u0b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b17 : List Sig := [y3_15,x3_0,x3_1,y3_5,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b17x : Impossible 7 0 s3_1u0b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b18 : List Sig := [y3_16,x3_0,x3_2,y3_5,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b18x : Impossible 7 0 s3_1u0b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b19 : List Sig := [y3_17,x3_0,x3_2,y3_5,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b19x : Impossible 7 0 s3_1u0b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b20 : List Sig := [y3_18,x3_0,x3_3,y3_5,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b20x : Impossible 7 0 s3_1u0b20 := rotate_impossible sym3_2 (z := s3_1u0b18) (by simp only [s3_1u0b20,x3_0,x3_1,x3_2,x3_3,x3_4,y3_18,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b18x

def s3_1u0b21 : List Sig := [y3_19,x3_0,x3_3,y3_5,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b21x : Impossible 7 0 s3_1u0b21 := rotate_impossible sym3_2 (z := s3_1u0b19) (by simp only [s3_1u0b21,x3_0,x3_1,x3_2,x3_3,x3_4,y3_19,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b19x

def s3_1u0b22 : List Sig := [y3_20,x3_0,x3_4,y3_5,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b22x : Impossible 7 0 s3_1u0b22 := rotate_impossible sym3_3 (z := s3_1u0b18) (by simp only [s3_1u0b22,x3_0,x3_1,x3_2,x3_3,x3_4,y3_20,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b18x

def s3_1u0b23 : List Sig := [y3_21,x3_0,x3_4,y3_5,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b23x : Impossible 7 0 s3_1u0b23 := rotate_impossible sym3_3 (z := s3_1u0b19) (by simp only [s3_1u0b23,x3_0,x3_1,x3_2,x3_3,x3_4,y3_21,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b19x

def s3_1u0b24 : List Sig := [y3_22,x3_1,x3_2,y3_5,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b24x : Impossible 7 0 s3_1u0b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b25 : List Sig := [y3_23,x3_1,x3_2,y3_5,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b25x : Impossible 7 0 s3_1u0b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b26 : List Sig := [y3_24,x3_1,x3_3,y3_5,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b26x : Impossible 7 0 s3_1u0b26 := rotate_impossible sym3_2 (z := s3_1u0b24) (by simp only [s3_1u0b26,x3_0,x3_1,x3_2,x3_3,x3_4,y3_24,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b24x

def s3_1u0b27 : List Sig := [y3_25,x3_1,x3_3,y3_5,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b27x : Impossible 7 0 s3_1u0b27 := rotate_impossible sym3_2 (z := s3_1u0b25) (by simp only [s3_1u0b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_25,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u0b25x

def s3_1u0b28 : List Sig := [y3_26,x3_1,x3_4,y3_5,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b28x : Impossible 7 0 s3_1u0b28 := rotate_impossible sym3_3 (z := s3_1u0b24) (by simp only [s3_1u0b28,x3_0,x3_1,x3_2,x3_3,x3_4,y3_26,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b24x

def s3_1u0b29 : List Sig := [y3_27,x3_1,x3_4,y3_5,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b29x : Impossible 7 0 s3_1u0b29 := rotate_impossible sym3_3 (z := s3_1u0b25) (by simp only [s3_1u0b29,x3_0,x3_1,x3_2,x3_3,x3_4,y3_27,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u0b25x

def s3_1u0b30 : List Sig := [y3_28,x3_2,x3_3,y3_5,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b30x : Impossible 7 0 s3_1u0b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b31 : List Sig := [y3_29,x3_2,x3_3,y3_5,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b31x : Impossible 7 0 s3_1u0b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u0b32 : List Sig := [y3_30,x3_2,x3_4,y3_5,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b32x : Impossible 7 0 s3_1u0b32 := rotate_impossible sym3_1 (z := s3_1u0b30) (by simp only [s3_1u0b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_30,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u0b30x

def s3_1u0b33 : List Sig := [y3_31,x3_2,x3_4,y3_5,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b33x : Impossible 7 0 s3_1u0b33 := rotate_impossible sym3_1 (z := s3_1u0b31) (by simp only [s3_1u0b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_31,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u0b31x

def s3_1u0b34 : List Sig := [y3_32,x3_3,x3_4,y3_5,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b34x : Impossible 7 0 s3_1u0b34 := rotate_impossible sym3_4 (z := s3_1u0b30) (by simp only [s3_1u0b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_32,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1u0b30x

def s3_1u0b35 : List Sig := [y3_33,x3_3,x3_4,y3_5,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0b35x : Impossible 7 0 s3_1u0b35 := rotate_impossible sym3_4 (z := s3_1u0b31) (by simp only [s3_1u0b35,x3_0,x3_1,x3_2,x3_3,x3_4,y3_33,y3_5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1u0b31x

def s3_1u0b : List (List Sig) := [s3_1u0b0,s3_1u0b1,s3_1u0b2,s3_1u0b3,s3_1u0b4,s3_1u0b5,s3_1u0b6,s3_1u0b7,s3_1u0b8,s3_1u0b9,s3_1u0b10,s3_1u0b11,s3_1u0b12,s3_1u0b13,s3_1u0b14,s3_1u0b15,s3_1u0b16,s3_1u0b17,s3_1u0b18,s3_1u0b19,s3_1u0b20,s3_1u0b21,s3_1u0b22,s3_1u0b23,s3_1u0b24,s3_1u0b25,s3_1u0b26,s3_1u0b27,s3_1u0b28,s3_1u0b29,s3_1u0b30,s3_1u0b31,s3_1u0b32,s3_1u0b33,s3_1u0b34,s3_1u0b35]

lemma s3_1u0bx (v : List Sig) (h : (!s3_1u0b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1u0b := by simpa using h
  simp only [s3_1u0b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1u0b0x
  · exact s3_1u0b1x
  · exact s3_1u0b2x
  · exact s3_1u0b3x
  · exact s3_1u0b4x
  · exact s3_1u0b5x
  · exact s3_1u0b6x
  · exact s3_1u0b7x
  · exact s3_1u0b8x
  · exact s3_1u0b9x
  · exact s3_1u0b10x
  · exact s3_1u0b11x
  · exact s3_1u0b12x
  · exact s3_1u0b13x
  · exact s3_1u0b14x
  · exact s3_1u0b15x
  · exact s3_1u0b16x
  · exact s3_1u0b17x
  · exact s3_1u0b18x
  · exact s3_1u0b19x
  · exact s3_1u0b20x
  · exact s3_1u0b21x
  · exact s3_1u0b22x
  · exact s3_1u0b23x
  · exact s3_1u0b24x
  · exact s3_1u0b25x
  · exact s3_1u0b26x
  · exact s3_1u0b27x
  · exact s3_1u0b28x
  · exact s3_1u0b29x
  · exact s3_1u0b30x
  · exact s3_1u0b31x
  · exact s3_1u0b32x
  · exact s3_1u0b33x
  · exact s3_1u0b34x
  · exact s3_1u0b35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u0x : Impossible 8 0 s3_1u0 := exclude_step (u := fun v => !s3_1u0u.contains v) (b := fun v => !s3_1u0b.contains v) (by decide +kernel) s3_1u0ux s3_1u0bx (by decide +kernel)

def s3_1u1 : List Sig := [neg (r3.getD 1 zero),r3.getD 1 zero,r3.getD 0 zero,r3.getD 2 zero,r3.getD 3 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u1x : Impossible 8 0 s3_1u1 := rotate_impossible sym3_6 (z := s3_1u0) (by simp only [s3_1u1,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0x

def s3_1u2 : List Sig := [neg (r3.getD 2 zero),r3.getD 2 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1u2u : List (List Sig) := []

lemma s3_1u2ux (v : List Sig) (h : (!s3_1u2u.contains v) = false) : Impossible 7 0 v := by
  simp [s3_1u2u] at h

def s3_1u2b0 : List Sig := [y3_35,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b0x : Impossible 7 0 s3_1u2b0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b1 : List Sig := [y3_35,y3_34,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b1x : Impossible 7 0 s3_1u2b1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b2 : List Sig := [y3_36,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b2x : Impossible 7 0 s3_1u2b2 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b3 : List Sig := [y3_36,y3_34,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b3x : Impossible 7 0 s3_1u2b3 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b4 : List Sig := [y3_37,x3_1,x3_2,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b4x : Impossible 7 0 s3_1u2b4 := rotate_impossible sym3_6 (z := s3_1u2b0) (by simp only [s3_1u2b4,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_37,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b0x

def s3_1u2b5 : List Sig := [y3_37,y3_34,x3_1,x3_2,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b5x : Impossible 7 0 s3_1u2b5 := rotate_impossible sym3_6 (z := s3_1u2b1) (by simp only [s3_1u2b5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_37,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b1x

def s3_1u2b6 : List Sig := [y3_38,x3_1,x3_2,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b6x : Impossible 7 0 s3_1u2b6 := rotate_impossible sym3_6 (z := s3_1u2b2) (by simp only [s3_1u2b6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_38,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b2x

def s3_1u2b7 : List Sig := [y3_38,y3_34,x3_1,x3_2,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b7x : Impossible 7 0 s3_1u2b7 := rotate_impossible sym3_6 (z := s3_1u2b3) (by simp only [s3_1u2b7,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_38,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b3x

def s3_1u2b8 : List Sig := [y3_39,x3_3,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b8x : Impossible 7 0 s3_1u2b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b9 : List Sig := [y3_39,y3_34,x3_3,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b9x : Impossible 7 0 s3_1u2b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b10 : List Sig := [y3_40,x3_3,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b10x : Impossible 7 0 s3_1u2b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b11 : List Sig := [y3_40,y3_34,x3_3,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b11x : Impossible 7 0 s3_1u2b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b12 : List Sig := [y3_41,x3_4,x3_2,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b12x : Impossible 7 0 s3_1u2b12 := rotate_impossible sym3_1 (z := s3_1u2b8) (by simp only [s3_1u2b12,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_41,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b8x

def s3_1u2b13 : List Sig := [y3_41,y3_34,x3_4,x3_2,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b13x : Impossible 7 0 s3_1u2b13 := rotate_impossible sym3_1 (z := s3_1u2b9) (by simp only [s3_1u2b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_41,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b9x

def s3_1u2b14 : List Sig := [y3_42,x3_4,x3_2,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b14x : Impossible 7 0 s3_1u2b14 := rotate_impossible sym3_1 (z := s3_1u2b10) (by simp only [s3_1u2b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_42,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b10x

def s3_1u2b15 : List Sig := [y3_42,y3_34,x3_4,x3_2,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b15x : Impossible 7 0 s3_1u2b15 := rotate_impossible sym3_1 (z := s3_1u2b11) (by simp only [s3_1u2b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_34,y3_42,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b11x

def s3_1u2b16 : List Sig := [y3_16,x3_2,x3_0,y3_34,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b16x : Impossible 7 0 s3_1u2b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b17 : List Sig := [y3_17,x3_2,x3_0,y3_34,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b17x : Impossible 7 0 s3_1u2b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b18 : List Sig := [y3_22,x3_2,x3_1,y3_34,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b18x : Impossible 7 0 s3_1u2b18 := rotate_impossible sym3_6 (z := s3_1u2b16) (by simp only [s3_1u2b18,x3_0,x3_1,x3_2,x3_3,x3_4,y3_22,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b16x

def s3_1u2b19 : List Sig := [y3_23,x3_2,x3_1,y3_34,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b19x : Impossible 7 0 s3_1u2b19 := rotate_impossible sym3_6 (z := s3_1u2b17) (by simp only [s3_1u2b19,x3_0,x3_1,x3_2,x3_3,x3_4,y3_23,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b17x

def s3_1u2b20 : List Sig := [y3_28,x3_2,x3_3,y3_34,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b20x : Impossible 7 0 s3_1u2b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b21 : List Sig := [y3_29,x3_2,x3_3,y3_34,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b21x : Impossible 7 0 s3_1u2b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b22 : List Sig := [y3_30,x3_2,x3_4,y3_34,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b22x : Impossible 7 0 s3_1u2b22 := rotate_impossible sym3_1 (z := s3_1u2b20) (by simp only [s3_1u2b22,x3_0,x3_1,x3_2,x3_3,x3_4,y3_30,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b20x

def s3_1u2b23 : List Sig := [y3_31,x3_2,x3_4,y3_34,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b23x : Impossible 7 0 s3_1u2b23 := rotate_impossible sym3_1 (z := s3_1u2b21) (by simp only [s3_1u2b23,x3_0,x3_1,x3_2,x3_3,x3_4,y3_31,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b21x

def s3_1u2b24 : List Sig := [y3_14,x3_0,x3_1,y3_34,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b24x : Impossible 7 0 s3_1u2b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b25 : List Sig := [y3_15,x3_0,x3_1,y3_34,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b25x : Impossible 7 0 s3_1u2b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b26 : List Sig := [y3_18,x3_0,x3_3,y3_34,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b26x : Impossible 7 0 s3_1u2b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b27 : List Sig := [y3_19,x3_0,x3_3,y3_34,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b27x : Impossible 7 0 s3_1u2b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b28 : List Sig := [y3_20,x3_0,x3_4,y3_34,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b28x : Impossible 7 0 s3_1u2b28 := rotate_impossible sym3_1 (z := s3_1u2b26) (by simp only [s3_1u2b28,x3_0,x3_1,x3_2,x3_3,x3_4,y3_20,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b26x

def s3_1u2b29 : List Sig := [y3_21,x3_0,x3_4,y3_34,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b29x : Impossible 7 0 s3_1u2b29 := rotate_impossible sym3_1 (z := s3_1u2b27) (by simp only [s3_1u2b29,x3_0,x3_1,x3_2,x3_3,x3_4,y3_21,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1u2b27x

def s3_1u2b30 : List Sig := [y3_24,x3_1,x3_3,y3_34,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b30x : Impossible 7 0 s3_1u2b30 := rotate_impossible sym3_6 (z := s3_1u2b26) (by simp only [s3_1u2b30,x3_0,x3_1,x3_2,x3_3,x3_4,y3_24,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b26x

def s3_1u2b31 : List Sig := [y3_25,x3_1,x3_3,y3_34,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b31x : Impossible 7 0 s3_1u2b31 := rotate_impossible sym3_6 (z := s3_1u2b27) (by simp only [s3_1u2b31,x3_0,x3_1,x3_2,x3_3,x3_4,y3_25,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u2b27x

def s3_1u2b32 : List Sig := [y3_26,x3_1,x3_4,y3_34,x3_2,x3_0,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b32x : Impossible 7 0 s3_1u2b32 := rotate_impossible sym3_7 (z := s3_1u2b26) (by simp only [s3_1u2b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_26,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_7_0,rot3_7_1,rot3_7_2,rot3_7_3,rot3_7_4]; decide +kernel) s3_1u2b26x

def s3_1u2b33 : List Sig := [y3_27,x3_1,x3_4,y3_34,x3_2,x3_0,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b33x : Impossible 7 0 s3_1u2b33 := rotate_impossible sym3_7 (z := s3_1u2b27) (by simp only [s3_1u2b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_27,y3_34,List.map_cons,List.map_nil,action_bin,action_neg,rot3_7_0,rot3_7_1,rot3_7_2,rot3_7_3,rot3_7_4]; decide +kernel) s3_1u2b27x

def s3_1u2b34 : List Sig := [y3_32,x3_3,x3_4,y3_34,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b34x : Impossible 7 0 s3_1u2b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b35 : List Sig := [y3_33,x3_3,x3_4,y3_34,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2b35x : Impossible 7 0 s3_1u2b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1u2b : List (List Sig) := [s3_1u2b0,s3_1u2b1,s3_1u2b2,s3_1u2b3,s3_1u2b4,s3_1u2b5,s3_1u2b6,s3_1u2b7,s3_1u2b8,s3_1u2b9,s3_1u2b10,s3_1u2b11,s3_1u2b12,s3_1u2b13,s3_1u2b14,s3_1u2b15,s3_1u2b16,s3_1u2b17,s3_1u2b18,s3_1u2b19,s3_1u2b20,s3_1u2b21,s3_1u2b22,s3_1u2b23,s3_1u2b24,s3_1u2b25,s3_1u2b26,s3_1u2b27,s3_1u2b28,s3_1u2b29,s3_1u2b30,s3_1u2b31,s3_1u2b32,s3_1u2b33,s3_1u2b34,s3_1u2b35]

lemma s3_1u2bx (v : List Sig) (h : (!s3_1u2b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1u2b := by simpa using h
  simp only [s3_1u2b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1u2b0x
  · exact s3_1u2b1x
  · exact s3_1u2b2x
  · exact s3_1u2b3x
  · exact s3_1u2b4x
  · exact s3_1u2b5x
  · exact s3_1u2b6x
  · exact s3_1u2b7x
  · exact s3_1u2b8x
  · exact s3_1u2b9x
  · exact s3_1u2b10x
  · exact s3_1u2b11x
  · exact s3_1u2b12x
  · exact s3_1u2b13x
  · exact s3_1u2b14x
  · exact s3_1u2b15x
  · exact s3_1u2b16x
  · exact s3_1u2b17x
  · exact s3_1u2b18x
  · exact s3_1u2b19x
  · exact s3_1u2b20x
  · exact s3_1u2b21x
  · exact s3_1u2b22x
  · exact s3_1u2b23x
  · exact s3_1u2b24x
  · exact s3_1u2b25x
  · exact s3_1u2b26x
  · exact s3_1u2b27x
  · exact s3_1u2b28x
  · exact s3_1u2b29x
  · exact s3_1u2b30x
  · exact s3_1u2b31x
  · exact s3_1u2b32x
  · exact s3_1u2b33x
  · exact s3_1u2b34x
  · exact s3_1u2b35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u2x : Impossible 8 0 s3_1u2 := exclude_step (u := fun v => !s3_1u2u.contains v) (b := fun v => !s3_1u2b.contains v) (by decide +kernel) s3_1u2ux s3_1u2bx (by decide +kernel)

def s3_1u3 : List Sig := [neg (r3.getD 3 zero),r3.getD 3 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u3x : Impossible 8 0 s3_1u3 := rotate_impossible sym3_2 (z := s3_1u2) (by simp only [s3_1u3,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2x

def s3_1u4 : List Sig := [neg (r3.getD 4 zero),r3.getD 4 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1u4x : Impossible 8 0 s3_1u4 := rotate_impossible sym3_3 (z := s3_1u2) (by simp only [s3_1u4,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2x

def s3_1u : List (List Sig) := [s3_1u0,s3_1u1,s3_1u2,s3_1u3,s3_1u4]

lemma s3_1ux (v : List Sig) (h : (!s3_1u.contains v) = false) : Impossible 8 0 v := by
  have hm : v ∈ s3_1u := by simpa using h
  simp only [s3_1u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact s3_1u0x
  · exact s3_1u1x
  · exact s3_1u2x
  · exact s3_1u3x
  · exact s3_1u4x

def s3_1b0 : List Sig := [bin false (r3.getD 0 zero) (r3.getD 1 zero),r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1b0u0 : List Sig := [y3_43,x3_0,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u0x : Impossible 7 0 s3_1b0u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0u1 : List Sig := [y3_43,y3_14,x3_0,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u1x : Impossible 7 0 s3_1b0u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0u2 : List Sig := [y3_5,x3_0,y3_14,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u2x : Impossible 7 0 s3_1b0u2 := impPerm (z := s3_1u0b16) (by decide +kernel) s3_1u0b16x

def s3_1b0u3 : List Sig := [y3_44,x3_1,y3_14,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u3x : Impossible 7 0 s3_1b0u3 := rotate_impossible sym3_6 (z := s3_1u0b16) (by simp only [s3_1b0u3,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b16x

def s3_1b0u4 : List Sig := [y3_34,x3_2,y3_14,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u4x : Impossible 7 0 s3_1b0u4 := impPerm (z := s3_1u2b24) (by decide +kernel) s3_1u2b24x

def s3_1b0u5 : List Sig := [y3_45,x3_3,y3_14,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u5x : Impossible 7 0 s3_1b0u5 := rotate_impossible sym3_2 (z := s3_1u2b24) (by simp only [s3_1b0u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b24x

def s3_1b0u6 : List Sig := [y3_46,x3_4,y3_14,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0u6x : Impossible 7 0 s3_1b0u6 := rotate_impossible sym3_3 (z := s3_1u2b24) (by simp only [s3_1b0u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b24x

def s3_1b0u : List (List Sig) := [s3_1b0u0,s3_1b0u1,s3_1b0u2,s3_1b0u3,s3_1b0u4,s3_1b0u5,s3_1b0u6]

lemma s3_1b0ux (v : List Sig) (h : (!s3_1b0u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b0u := by simpa using h
  simp only [s3_1b0u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b0u0x
  · exact s3_1b0u1x
  · exact s3_1b0u2x
  · exact s3_1b0u3x
  · exact s3_1b0u4x
  · exact s3_1b0u5x
  · exact s3_1b0u6x

def s3_1b0b7 : List Sig := [y3_47,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b7x : Impossible 7 1 s3_1b0b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b8 : List Sig := [y3_47,y3_14,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b8x : Impossible 7 1 s3_1b0b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b9 : List Sig := [y3_48,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b9x : Impossible 7 1 s3_1b0b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b10 : List Sig := [y3_48,y3_14,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b10x : Impossible 7 1 s3_1b0b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b11 : List Sig := [y3_49,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b11x : Impossible 7 1 s3_1b0b11 := rotate_impossible sym3_2 (z := s3_1b0b7) (by simp only [s3_1b0b11,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_49,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b7x

def s3_1b0b12 : List Sig := [y3_49,y3_14,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b12x : Impossible 7 1 s3_1b0b12 := rotate_impossible sym3_2 (z := s3_1b0b8) (by simp only [s3_1b0b12,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_49,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b8x

def s3_1b0b13 : List Sig := [y3_50,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b13x : Impossible 7 1 s3_1b0b13 := rotate_impossible sym3_2 (z := s3_1b0b9) (by simp only [s3_1b0b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_50,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b9x

def s3_1b0b14 : List Sig := [y3_50,y3_14,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b14x : Impossible 7 1 s3_1b0b14 := rotate_impossible sym3_2 (z := s3_1b0b10) (by simp only [s3_1b0b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_50,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b10x

def s3_1b0b15 : List Sig := [y3_51,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b15x : Impossible 7 1 s3_1b0b15 := rotate_impossible sym3_3 (z := s3_1b0b7) (by simp only [s3_1b0b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_51,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b7x

def s3_1b0b16 : List Sig := [y3_51,y3_14,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b16x : Impossible 7 1 s3_1b0b16 := rotate_impossible sym3_3 (z := s3_1b0b8) (by simp only [s3_1b0b16,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_51,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b8x

def s3_1b0b17 : List Sig := [y3_52,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b17x : Impossible 7 1 s3_1b0b17 := rotate_impossible sym3_3 (z := s3_1b0b9) (by simp only [s3_1b0b17,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_52,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b9x

def s3_1b0b18 : List Sig := [y3_52,y3_14,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b18x : Impossible 7 1 s3_1b0b18 := rotate_impossible sym3_3 (z := s3_1b0b10) (by simp only [s3_1b0b18,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_52,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b10x

def s3_1b0b19 : List Sig := [y3_15,y3_14,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b19x : Impossible 7 1 s3_1b0b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b20 : List Sig := [y3_15,x3_0,y3_14,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b20x : Impossible 7 1 s3_1b0b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b21 : List Sig := [y3_15,x3_1,y3_14,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b21x : Impossible 7 1 s3_1b0b21 := rotate_impossible sym3_6 (z := s3_1b0b20) (by simp only [s3_1b0b21,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_15,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b0b20x

def s3_1b0b22 : List Sig := [y3_15,x3_0,x3_1,y3_14,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b22x : Impossible 7 1 s3_1b0b22 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b23 : List Sig := [y3_16,x3_0,x3_2,y3_14,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b23x : Impossible 7 1 s3_1b0b23 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b24 : List Sig := [y3_17,x3_0,x3_2,y3_14,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b24x : Impossible 7 1 s3_1b0b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b25 : List Sig := [y3_18,x3_0,x3_3,y3_14,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b25x : Impossible 7 1 s3_1b0b25 := rotate_impossible sym3_2 (z := s3_1b0b23) (by simp only [s3_1b0b25,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_18,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b23x

def s3_1b0b26 : List Sig := [y3_19,x3_0,x3_3,y3_14,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b26x : Impossible 7 1 s3_1b0b26 := rotate_impossible sym3_2 (z := s3_1b0b24) (by simp only [s3_1b0b26,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_19,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b0b24x

def s3_1b0b27 : List Sig := [y3_20,x3_0,x3_4,y3_14,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b27x : Impossible 7 1 s3_1b0b27 := rotate_impossible sym3_3 (z := s3_1b0b23) (by simp only [s3_1b0b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_20,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b23x

def s3_1b0b28 : List Sig := [y3_21,x3_0,x3_4,y3_14,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b28x : Impossible 7 1 s3_1b0b28 := rotate_impossible sym3_3 (z := s3_1b0b24) (by simp only [s3_1b0b28,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_21,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b0b24x

def s3_1b0b29 : List Sig := [y3_22,x3_1,x3_2,y3_14,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b29x : Impossible 7 1 s3_1b0b29 := rotate_impossible sym3_6 (z := s3_1b0b23) (by simp only [s3_1b0b29,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_22,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b0b23x

def s3_1b0b30 : List Sig := [y3_23,x3_1,x3_2,y3_14,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b30x : Impossible 7 1 s3_1b0b30 := rotate_impossible sym3_6 (z := s3_1b0b24) (by simp only [s3_1b0b30,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_23,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b0b24x

def s3_1b0b31 : List Sig := [y3_24,x3_1,x3_3,y3_14,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b31x : Impossible 7 1 s3_1b0b31 := rotate_impossible sym3_8 (z := s3_1b0b23) (by simp only [s3_1b0b31,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_24,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b0b23x

def s3_1b0b32 : List Sig := [y3_25,x3_1,x3_3,y3_14,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b32x : Impossible 7 1 s3_1b0b32 := rotate_impossible sym3_8 (z := s3_1b0b24) (by simp only [s3_1b0b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_25,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b0b24x

def s3_1b0b33 : List Sig := [y3_26,x3_1,x3_4,y3_14,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b33x : Impossible 7 1 s3_1b0b33 := rotate_impossible sym3_9 (z := s3_1b0b23) (by simp only [s3_1b0b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_26,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b0b23x

def s3_1b0b34 : List Sig := [y3_27,x3_1,x3_4,y3_14,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b34x : Impossible 7 1 s3_1b0b34 := rotate_impossible sym3_9 (z := s3_1b0b24) (by simp only [s3_1b0b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_27,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b0b24x

def s3_1b0b35 : List Sig := [y3_28,x3_2,x3_3,y3_14,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b35x : Impossible 7 1 s3_1b0b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b36 : List Sig := [y3_29,x3_2,x3_3,y3_14,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b36x : Impossible 7 1 s3_1b0b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b0b37 : List Sig := [y3_30,x3_2,x3_4,y3_14,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b37x : Impossible 7 1 s3_1b0b37 := rotate_impossible sym3_1 (z := s3_1b0b35) (by simp only [s3_1b0b37,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_30,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b0b35x

def s3_1b0b38 : List Sig := [y3_31,x3_2,x3_4,y3_14,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b38x : Impossible 7 1 s3_1b0b38 := rotate_impossible sym3_1 (z := s3_1b0b36) (by simp only [s3_1b0b38,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_31,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b0b36x

def s3_1b0b39 : List Sig := [y3_32,x3_3,x3_4,y3_14,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b39x : Impossible 7 1 s3_1b0b39 := rotate_impossible sym3_4 (z := s3_1b0b35) (by simp only [s3_1b0b39,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_32,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b0b35x

def s3_1b0b40 : List Sig := [y3_33,x3_3,x3_4,y3_14,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0b40x : Impossible 7 1 s3_1b0b40 := rotate_impossible sym3_4 (z := s3_1b0b36) (by simp only [s3_1b0b40,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_33,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b0b36x

def s3_1b0b : List (List Sig) := [s3_1b0b7,s3_1b0b8,s3_1b0b9,s3_1b0b10,s3_1b0b11,s3_1b0b12,s3_1b0b13,s3_1b0b14,s3_1b0b15,s3_1b0b16,s3_1b0b17,s3_1b0b18,s3_1b0b19,s3_1b0b20,s3_1b0b21,s3_1b0b22,s3_1b0b23,s3_1b0b24,s3_1b0b25,s3_1b0b26,s3_1b0b27,s3_1b0b28,s3_1b0b29,s3_1b0b30,s3_1b0b31,s3_1b0b32,s3_1b0b33,s3_1b0b34,s3_1b0b35,s3_1b0b36,s3_1b0b37,s3_1b0b38,s3_1b0b39,s3_1b0b40]

lemma s3_1b0bx (v : List Sig) (h : (!s3_1b0b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b0b := by simpa using h
  simp only [s3_1b0b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b0b7x
  · exact s3_1b0b8x
  · exact s3_1b0b9x
  · exact s3_1b0b10x
  · exact s3_1b0b11x
  · exact s3_1b0b12x
  · exact s3_1b0b13x
  · exact s3_1b0b14x
  · exact s3_1b0b15x
  · exact s3_1b0b16x
  · exact s3_1b0b17x
  · exact s3_1b0b18x
  · exact s3_1b0b19x
  · exact s3_1b0b20x
  · exact s3_1b0b21x
  · exact s3_1b0b22x
  · exact s3_1b0b23x
  · exact s3_1b0b24x
  · exact s3_1b0b25x
  · exact s3_1b0b26x
  · exact s3_1b0b27x
  · exact s3_1b0b28x
  · exact s3_1b0b29x
  · exact s3_1b0b30x
  · exact s3_1b0b31x
  · exact s3_1b0b32x
  · exact s3_1b0b33x
  · exact s3_1b0b34x
  · exact s3_1b0b35x
  · exact s3_1b0b36x
  · exact s3_1b0b37x
  · exact s3_1b0b38x
  · exact s3_1b0b39x
  · exact s3_1b0b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b0x : Impossible 8 1 s3_1b0 := exclude_step (u := fun v => !s3_1b0u.contains v) (b := fun v => !s3_1b0b.contains v) (by decide +kernel) s3_1b0ux s3_1b0bx (by decide +kernel)

def s3_1b1 : List Sig := [bin true (r3.getD 0 zero) (r3.getD 1 zero),r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1b1u0 : List Sig := [y3_53,x3_0,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u0x : Impossible 7 0 s3_1b1u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1u1 : List Sig := [y3_53,y3_15,x3_0,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u1x : Impossible 7 0 s3_1b1u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1u2 : List Sig := [y3_5,x3_0,y3_15,x3_1,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u2x : Impossible 7 0 s3_1b1u2 := impPerm (z := s3_1u0b17) (by decide +kernel) s3_1u0b17x

def s3_1b1u3 : List Sig := [y3_44,x3_1,y3_15,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u3x : Impossible 7 0 s3_1b1u3 := rotate_impossible sym3_6 (z := s3_1u0b17) (by simp only [s3_1b1u3,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b17x

def s3_1b1u4 : List Sig := [y3_34,x3_2,y3_15,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u4x : Impossible 7 0 s3_1b1u4 := impPerm (z := s3_1u2b25) (by decide +kernel) s3_1u2b25x

def s3_1b1u5 : List Sig := [y3_45,x3_3,y3_15,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u5x : Impossible 7 0 s3_1b1u5 := rotate_impossible sym3_2 (z := s3_1u2b25) (by simp only [s3_1b1u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b25x

def s3_1b1u6 : List Sig := [y3_46,x3_4,y3_15,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1u6x : Impossible 7 0 s3_1b1u6 := rotate_impossible sym3_3 (z := s3_1u2b25) (by simp only [s3_1b1u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b25x

def s3_1b1u : List (List Sig) := [s3_1b1u0,s3_1b1u1,s3_1b1u2,s3_1b1u3,s3_1b1u4,s3_1b1u5,s3_1b1u6]

lemma s3_1b1ux (v : List Sig) (h : (!s3_1b1u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b1u := by simpa using h
  simp only [s3_1b1u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b1u0x
  · exact s3_1b1u1x
  · exact s3_1b1u2x
  · exact s3_1b1u3x
  · exact s3_1b1u4x
  · exact s3_1b1u5x
  · exact s3_1b1u6x

def s3_1b1b7 : List Sig := [y3_54,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b7x : Impossible 7 1 s3_1b1b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b8 : List Sig := [y3_54,y3_15,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b8x : Impossible 7 1 s3_1b1b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b9 : List Sig := [y3_54,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b9x : Impossible 7 1 s3_1b1b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b10 : List Sig := [y3_54,y3_15,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b10x : Impossible 7 1 s3_1b1b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b11 : List Sig := [y3_55,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b11x : Impossible 7 1 s3_1b1b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b12 : List Sig := [y3_55,y3_15,x3_2,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b12x : Impossible 7 1 s3_1b1b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b13 : List Sig := [y3_56,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b13x : Impossible 7 1 s3_1b1b13 := rotate_impossible sym3_2 (z := s3_1b1b7) (by simp only [s3_1b1b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_56,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b7x

def s3_1b1b14 : List Sig := [y3_56,y3_15,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b14x : Impossible 7 1 s3_1b1b14 := rotate_impossible sym3_2 (z := s3_1b1b8) (by simp only [s3_1b1b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_56,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b8x

def s3_1b1b15 : List Sig := [y3_56,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b15x : Impossible 7 1 s3_1b1b15 := rotate_impossible sym3_2 (z := s3_1b1b9) (by simp only [s3_1b1b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_56,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b9x

def s3_1b1b16 : List Sig := [y3_56,y3_15,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b16x : Impossible 7 1 s3_1b1b16 := rotate_impossible sym3_2 (z := s3_1b1b10) (by simp only [s3_1b1b16,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_56,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b10x

def s3_1b1b17 : List Sig := [y3_57,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b17x : Impossible 7 1 s3_1b1b17 := rotate_impossible sym3_2 (z := s3_1b1b11) (by simp only [s3_1b1b17,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_57,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b11x

def s3_1b1b18 : List Sig := [y3_57,y3_15,x3_3,x3_0,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b18x : Impossible 7 1 s3_1b1b18 := rotate_impossible sym3_2 (z := s3_1b1b12) (by simp only [s3_1b1b18,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_57,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b12x

def s3_1b1b19 : List Sig := [y3_58,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b19x : Impossible 7 1 s3_1b1b19 := rotate_impossible sym3_3 (z := s3_1b1b7) (by simp only [s3_1b1b19,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_58,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b7x

def s3_1b1b20 : List Sig := [y3_58,y3_15,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b20x : Impossible 7 1 s3_1b1b20 := rotate_impossible sym3_3 (z := s3_1b1b8) (by simp only [s3_1b1b20,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_58,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b8x

def s3_1b1b21 : List Sig := [y3_58,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b21x : Impossible 7 1 s3_1b1b21 := rotate_impossible sym3_3 (z := s3_1b1b9) (by simp only [s3_1b1b21,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_58,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b9x

def s3_1b1b22 : List Sig := [y3_58,y3_15,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b22x : Impossible 7 1 s3_1b1b22 := rotate_impossible sym3_3 (z := s3_1b1b10) (by simp only [s3_1b1b22,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_58,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b10x

def s3_1b1b23 : List Sig := [y3_59,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b23x : Impossible 7 1 s3_1b1b23 := rotate_impossible sym3_3 (z := s3_1b1b11) (by simp only [s3_1b1b23,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_59,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b11x

def s3_1b1b24 : List Sig := [y3_59,y3_15,x3_4,x3_0,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b24x : Impossible 7 1 s3_1b1b24 := rotate_impossible sym3_3 (z := s3_1b1b12) (by simp only [s3_1b1b24,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_59,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b12x

def s3_1b1b25 : List Sig := [y3_14,y3_15,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b25x : Impossible 7 1 s3_1b1b25 := impPerm (z := s3_1b0b19) (by decide +kernel) s3_1b0b19x

def s3_1b1b26 : List Sig := [y3_14,x3_0,y3_15,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b26x : Impossible 7 1 s3_1b1b26 := impPerm (z := s3_1b0b20) (by decide +kernel) s3_1b0b20x

def s3_1b1b27 : List Sig := [y3_14,x3_1,y3_15,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b27x : Impossible 7 1 s3_1b1b27 := rotate_impossible sym3_6 (z := s3_1b0b20) (by simp only [s3_1b1b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_14,y3_15,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b0b20x

def s3_1b1b28 : List Sig := [y3_14,x3_0,x3_1,y3_15,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b28x : Impossible 7 1 s3_1b1b28 := impPerm (z := s3_1b0b22) (by decide +kernel) s3_1b0b22x

def s3_1b1b29 : List Sig := [y3_16,x3_0,x3_2,y3_15,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b29x : Impossible 7 1 s3_1b1b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b30 : List Sig := [y3_17,x3_0,x3_2,y3_15,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b30x : Impossible 7 1 s3_1b1b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b31 : List Sig := [y3_18,x3_0,x3_3,y3_15,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b31x : Impossible 7 1 s3_1b1b31 := rotate_impossible sym3_2 (z := s3_1b1b29) (by simp only [s3_1b1b31,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_18,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b29x

def s3_1b1b32 : List Sig := [y3_19,x3_0,x3_3,y3_15,x3_1,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b32x : Impossible 7 1 s3_1b1b32 := rotate_impossible sym3_2 (z := s3_1b1b30) (by simp only [s3_1b1b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_19,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b1b30x

def s3_1b1b33 : List Sig := [y3_20,x3_0,x3_4,y3_15,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b33x : Impossible 7 1 s3_1b1b33 := rotate_impossible sym3_3 (z := s3_1b1b29) (by simp only [s3_1b1b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_20,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b29x

def s3_1b1b34 : List Sig := [y3_21,x3_0,x3_4,y3_15,x3_1,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b34x : Impossible 7 1 s3_1b1b34 := rotate_impossible sym3_3 (z := s3_1b1b30) (by simp only [s3_1b1b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_21,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b1b30x

def s3_1b1b35 : List Sig := [y3_22,x3_1,x3_2,y3_15,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b35x : Impossible 7 1 s3_1b1b35 := rotate_impossible sym3_6 (z := s3_1b1b29) (by simp only [s3_1b1b35,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_22,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b1b29x

def s3_1b1b36 : List Sig := [y3_23,x3_1,x3_2,y3_15,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b36x : Impossible 7 1 s3_1b1b36 := rotate_impossible sym3_6 (z := s3_1b1b30) (by simp only [s3_1b1b36,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_23,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b1b30x

def s3_1b1b37 : List Sig := [y3_24,x3_1,x3_3,y3_15,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b37x : Impossible 7 1 s3_1b1b37 := rotate_impossible sym3_8 (z := s3_1b1b29) (by simp only [s3_1b1b37,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_24,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b1b29x

def s3_1b1b38 : List Sig := [y3_25,x3_1,x3_3,y3_15,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b38x : Impossible 7 1 s3_1b1b38 := rotate_impossible sym3_8 (z := s3_1b1b30) (by simp only [s3_1b1b38,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_25,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b1b30x

def s3_1b1b39 : List Sig := [y3_26,x3_1,x3_4,y3_15,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b39x : Impossible 7 1 s3_1b1b39 := rotate_impossible sym3_9 (z := s3_1b1b29) (by simp only [s3_1b1b39,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_26,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b1b29x

def s3_1b1b40 : List Sig := [y3_27,x3_1,x3_4,y3_15,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b40x : Impossible 7 1 s3_1b1b40 := rotate_impossible sym3_9 (z := s3_1b1b30) (by simp only [s3_1b1b40,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_27,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b1b30x

def s3_1b1b41 : List Sig := [y3_28,x3_2,x3_3,y3_15,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b41x : Impossible 7 1 s3_1b1b41 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b42 : List Sig := [y3_29,x3_2,x3_3,y3_15,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b42x : Impossible 7 1 s3_1b1b42 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b1b43 : List Sig := [y3_30,x3_2,x3_4,y3_15,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b43x : Impossible 7 1 s3_1b1b43 := rotate_impossible sym3_1 (z := s3_1b1b41) (by simp only [s3_1b1b43,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_30,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b1b41x

def s3_1b1b44 : List Sig := [y3_31,x3_2,x3_4,y3_15,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b44x : Impossible 7 1 s3_1b1b44 := rotate_impossible sym3_1 (z := s3_1b1b42) (by simp only [s3_1b1b44,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_31,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b1b42x

def s3_1b1b45 : List Sig := [y3_32,x3_3,x3_4,y3_15,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b45x : Impossible 7 1 s3_1b1b45 := rotate_impossible sym3_4 (z := s3_1b1b41) (by simp only [s3_1b1b45,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_32,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b1b41x

def s3_1b1b46 : List Sig := [y3_33,x3_3,x3_4,y3_15,x3_0,x3_1,x3_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1b46x : Impossible 7 1 s3_1b1b46 := rotate_impossible sym3_4 (z := s3_1b1b42) (by simp only [s3_1b1b46,x3_0,x3_1,x3_2,x3_3,x3_4,y3_15,y3_33,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b1b42x

def s3_1b1b : List (List Sig) := [s3_1b1b7,s3_1b1b8,s3_1b1b9,s3_1b1b10,s3_1b1b11,s3_1b1b12,s3_1b1b13,s3_1b1b14,s3_1b1b15,s3_1b1b16,s3_1b1b17,s3_1b1b18,s3_1b1b19,s3_1b1b20,s3_1b1b21,s3_1b1b22,s3_1b1b23,s3_1b1b24,s3_1b1b25,s3_1b1b26,s3_1b1b27,s3_1b1b28,s3_1b1b29,s3_1b1b30,s3_1b1b31,s3_1b1b32,s3_1b1b33,s3_1b1b34,s3_1b1b35,s3_1b1b36,s3_1b1b37,s3_1b1b38,s3_1b1b39,s3_1b1b40,s3_1b1b41,s3_1b1b42,s3_1b1b43,s3_1b1b44,s3_1b1b45,s3_1b1b46]

lemma s3_1b1bx (v : List Sig) (h : (!s3_1b1b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b1b := by simpa using h
  simp only [s3_1b1b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b1b7x
  · exact s3_1b1b8x
  · exact s3_1b1b9x
  · exact s3_1b1b10x
  · exact s3_1b1b11x
  · exact s3_1b1b12x
  · exact s3_1b1b13x
  · exact s3_1b1b14x
  · exact s3_1b1b15x
  · exact s3_1b1b16x
  · exact s3_1b1b17x
  · exact s3_1b1b18x
  · exact s3_1b1b19x
  · exact s3_1b1b20x
  · exact s3_1b1b21x
  · exact s3_1b1b22x
  · exact s3_1b1b23x
  · exact s3_1b1b24x
  · exact s3_1b1b25x
  · exact s3_1b1b26x
  · exact s3_1b1b27x
  · exact s3_1b1b28x
  · exact s3_1b1b29x
  · exact s3_1b1b30x
  · exact s3_1b1b31x
  · exact s3_1b1b32x
  · exact s3_1b1b33x
  · exact s3_1b1b34x
  · exact s3_1b1b35x
  · exact s3_1b1b36x
  · exact s3_1b1b37x
  · exact s3_1b1b38x
  · exact s3_1b1b39x
  · exact s3_1b1b40x
  · exact s3_1b1b41x
  · exact s3_1b1b42x
  · exact s3_1b1b43x
  · exact s3_1b1b44x
  · exact s3_1b1b45x
  · exact s3_1b1b46x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b1x : Impossible 8 1 s3_1b1 := exclude_step (u := fun v => !s3_1b1u.contains v) (b := fun v => !s3_1b1b.contains v) (by decide +kernel) s3_1b1ux s3_1b1bx (by decide +kernel)

def s3_1b2 : List Sig := [bin false (r3.getD 0 zero) (r3.getD 2 zero),r3.getD 0 zero,r3.getD 2 zero,r3.getD 1 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1b2u0 : List Sig := [y3_60,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u0x : Impossible 7 0 s3_1b2u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2u1 : List Sig := [y3_60,y3_16,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u1x : Impossible 7 0 s3_1b2u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2u2 : List Sig := [y3_5,x3_0,y3_16,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u2x : Impossible 7 0 s3_1b2u2 := impPerm (z := s3_1u0b18) (by decide +kernel) s3_1u0b18x

def s3_1b2u3 : List Sig := [y3_34,x3_2,y3_16,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u3x : Impossible 7 0 s3_1b2u3 := impPerm (z := s3_1u2b16) (by decide +kernel) s3_1u2b16x

def s3_1b2u4 : List Sig := [y3_44,x3_1,y3_16,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u4x : Impossible 7 0 s3_1b2u4 := rotate_impossible sym3_6 (z := s3_1u0b24) (by simp only [s3_1b2u4,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b24x

def s3_1b2u5 : List Sig := [y3_45,x3_3,y3_16,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u5x : Impossible 7 0 s3_1b2u5 := rotate_impossible sym3_2 (z := s3_1u2b26) (by simp only [s3_1b2u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b26x

def s3_1b2u6 : List Sig := [y3_46,x3_4,y3_16,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2u6x : Impossible 7 0 s3_1b2u6 := rotate_impossible sym3_3 (z := s3_1u2b26) (by simp only [s3_1b2u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b26x

def s3_1b2u : List (List Sig) := [s3_1b2u0,s3_1b2u1,s3_1b2u2,s3_1b2u3,s3_1b2u4,s3_1b2u5,s3_1b2u6]

lemma s3_1b2ux (v : List Sig) (h : (!s3_1b2u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b2u := by simpa using h
  simp only [s3_1b2u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b2u0x
  · exact s3_1b2u1x
  · exact s3_1b2u2x
  · exact s3_1b2u3x
  · exact s3_1b2u4x
  · exact s3_1b2u5x
  · exact s3_1b2u6x

def s3_1b2b7 : List Sig := [y3_47,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b7x : Impossible 7 1 s3_1b2b7 := impPerm (z := s3_1b0b7) (by decide +kernel) s3_1b0b7x

def s3_1b2b8 : List Sig := [y3_47,y3_16,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b8x : Impossible 7 1 s3_1b2b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b9 : List Sig := [y3_61,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b9x : Impossible 7 1 s3_1b2b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b10 : List Sig := [y3_61,y3_16,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b10x : Impossible 7 1 s3_1b2b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b11 : List Sig := [y3_62,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b11x : Impossible 7 1 s3_1b2b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b12 : List Sig := [y3_62,y3_16,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b12x : Impossible 7 1 s3_1b2b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b13 : List Sig := [y3_63,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b13x : Impossible 7 1 s3_1b2b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b14 : List Sig := [y3_63,y3_16,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b14x : Impossible 7 1 s3_1b2b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b15 : List Sig := [y3_64,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b15x : Impossible 7 1 s3_1b2b15 := rotate_impossible sym3_1 (z := s3_1b2b11) (by simp only [s3_1b2b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_64,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b11x

def s3_1b2b16 : List Sig := [y3_64,y3_16,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b16x : Impossible 7 1 s3_1b2b16 := rotate_impossible sym3_1 (z := s3_1b2b12) (by simp only [s3_1b2b16,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_64,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b12x

def s3_1b2b17 : List Sig := [y3_65,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b17x : Impossible 7 1 s3_1b2b17 := rotate_impossible sym3_1 (z := s3_1b2b13) (by simp only [s3_1b2b17,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_65,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b13x

def s3_1b2b18 : List Sig := [y3_65,y3_16,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b18x : Impossible 7 1 s3_1b2b18 := rotate_impossible sym3_1 (z := s3_1b2b14) (by simp only [s3_1b2b18,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_65,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b14x

def s3_1b2b19 : List Sig := [y3_17,x3_0,y3_16,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b19x : Impossible 7 1 s3_1b2b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b20 : List Sig := [y3_17,x3_2,y3_16,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b20x : Impossible 7 1 s3_1b2b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b21 : List Sig := [y3_17,x3_0,x3_2,y3_16,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b21x : Impossible 7 1 s3_1b2b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b22 : List Sig := [y3_14,x3_0,x3_1,y3_16,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b22x : Impossible 7 1 s3_1b2b22 := impPerm (z := s3_1b0b23) (by decide +kernel) s3_1b0b23x

def s3_1b2b23 : List Sig := [y3_15,x3_0,x3_1,y3_16,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b23x : Impossible 7 1 s3_1b2b23 := impPerm (z := s3_1b1b29) (by decide +kernel) s3_1b1b29x

def s3_1b2b24 : List Sig := [y3_18,x3_0,x3_3,y3_16,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b24x : Impossible 7 1 s3_1b2b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b25 : List Sig := [y3_19,x3_0,x3_3,y3_16,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b25x : Impossible 7 1 s3_1b2b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b26 : List Sig := [y3_20,x3_0,x3_4,y3_16,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b26x : Impossible 7 1 s3_1b2b26 := rotate_impossible sym3_1 (z := s3_1b2b24) (by simp only [s3_1b2b26,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_20,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b24x

def s3_1b2b27 : List Sig := [y3_21,x3_0,x3_4,y3_16,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b27x : Impossible 7 1 s3_1b2b27 := rotate_impossible sym3_1 (z := s3_1b2b25) (by simp only [s3_1b2b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_21,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b25x

def s3_1b2b28 : List Sig := [y3_22,x3_1,y3_16,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b28x : Impossible 7 1 s3_1b2b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b29 : List Sig := [y3_22,x3_2,x3_1,y3_16,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b29x : Impossible 7 1 s3_1b2b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b30 : List Sig := [y3_23,x3_2,x3_1,y3_16,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b30x : Impossible 7 1 s3_1b2b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b31 : List Sig := [y3_28,x3_2,x3_3,y3_16,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b31x : Impossible 7 1 s3_1b2b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b32 : List Sig := [y3_29,x3_2,x3_3,y3_16,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b32x : Impossible 7 1 s3_1b2b32 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b33 : List Sig := [y3_30,x3_2,x3_4,y3_16,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b33x : Impossible 7 1 s3_1b2b33 := rotate_impossible sym3_1 (z := s3_1b2b31) (by simp only [s3_1b2b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_30,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b31x

def s3_1b2b34 : List Sig := [y3_31,x3_2,x3_4,y3_16,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b34x : Impossible 7 1 s3_1b2b34 := rotate_impossible sym3_1 (z := s3_1b2b32) (by simp only [s3_1b2b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_31,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b32x

def s3_1b2b35 : List Sig := [y3_24,x3_1,x3_3,y3_16,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b35x : Impossible 7 1 s3_1b2b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b36 : List Sig := [y3_25,x3_1,x3_3,y3_16,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b36x : Impossible 7 1 s3_1b2b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b37 : List Sig := [y3_26,x3_1,x3_4,y3_16,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b37x : Impossible 7 1 s3_1b2b37 := rotate_impossible sym3_1 (z := s3_1b2b35) (by simp only [s3_1b2b37,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_26,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b35x

def s3_1b2b38 : List Sig := [y3_27,x3_1,x3_4,y3_16,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b38x : Impossible 7 1 s3_1b2b38 := rotate_impossible sym3_1 (z := s3_1b2b36) (by simp only [s3_1b2b38,x3_0,x3_1,x3_2,x3_3,x3_4,y3_16,y3_27,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b2b36x

def s3_1b2b39 : List Sig := [y3_32,x3_3,x3_4,y3_16,x3_0,x3_2,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b39x : Impossible 7 1 s3_1b2b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b40 : List Sig := [y3_33,x3_3,x3_4,y3_16,x3_0,x3_2,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2b40x : Impossible 7 1 s3_1b2b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b2b : List (List Sig) := [s3_1b2b7,s3_1b2b8,s3_1b2b9,s3_1b2b10,s3_1b2b11,s3_1b2b12,s3_1b2b13,s3_1b2b14,s3_1b2b15,s3_1b2b16,s3_1b2b17,s3_1b2b18,s3_1b2b19,s3_1b2b20,s3_1b2b21,s3_1b2b22,s3_1b2b23,s3_1b2b24,s3_1b2b25,s3_1b2b26,s3_1b2b27,s3_1b2b28,s3_1b2b29,s3_1b2b30,s3_1b2b31,s3_1b2b32,s3_1b2b33,s3_1b2b34,s3_1b2b35,s3_1b2b36,s3_1b2b37,s3_1b2b38,s3_1b2b39,s3_1b2b40]

lemma s3_1b2bx (v : List Sig) (h : (!s3_1b2b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b2b := by simpa using h
  simp only [s3_1b2b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b2b7x
  · exact s3_1b2b8x
  · exact s3_1b2b9x
  · exact s3_1b2b10x
  · exact s3_1b2b11x
  · exact s3_1b2b12x
  · exact s3_1b2b13x
  · exact s3_1b2b14x
  · exact s3_1b2b15x
  · exact s3_1b2b16x
  · exact s3_1b2b17x
  · exact s3_1b2b18x
  · exact s3_1b2b19x
  · exact s3_1b2b20x
  · exact s3_1b2b21x
  · exact s3_1b2b22x
  · exact s3_1b2b23x
  · exact s3_1b2b24x
  · exact s3_1b2b25x
  · exact s3_1b2b26x
  · exact s3_1b2b27x
  · exact s3_1b2b28x
  · exact s3_1b2b29x
  · exact s3_1b2b30x
  · exact s3_1b2b31x
  · exact s3_1b2b32x
  · exact s3_1b2b33x
  · exact s3_1b2b34x
  · exact s3_1b2b35x
  · exact s3_1b2b36x
  · exact s3_1b2b37x
  · exact s3_1b2b38x
  · exact s3_1b2b39x
  · exact s3_1b2b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b2x : Impossible 8 1 s3_1b2 := exclude_step (u := fun v => !s3_1b2u.contains v) (b := fun v => !s3_1b2b.contains v) (by decide +kernel) s3_1b2ux s3_1b2bx (by decide +kernel)

def s3_1b3 : List Sig := [bin true (r3.getD 0 zero) (r3.getD 2 zero),r3.getD 0 zero,r3.getD 2 zero,r3.getD 1 zero,r3.getD 3 zero,r3.getD 4 zero]

def s3_1b3u0 : List Sig := [y3_66,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u0x : Impossible 7 0 s3_1b3u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3u1 : List Sig := [y3_66,y3_17,x3_0,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u1x : Impossible 7 0 s3_1b3u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3u2 : List Sig := [y3_5,x3_0,y3_17,x3_2,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u2x : Impossible 7 0 s3_1b3u2 := impPerm (z := s3_1u0b19) (by decide +kernel) s3_1u0b19x

def s3_1b3u3 : List Sig := [y3_34,x3_2,y3_17,x3_0,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u3x : Impossible 7 0 s3_1b3u3 := impPerm (z := s3_1u2b17) (by decide +kernel) s3_1u2b17x

def s3_1b3u4 : List Sig := [y3_44,x3_1,y3_17,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u4x : Impossible 7 0 s3_1b3u4 := rotate_impossible sym3_6 (z := s3_1u0b25) (by simp only [s3_1b3u4,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b25x

def s3_1b3u5 : List Sig := [y3_45,x3_3,y3_17,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u5x : Impossible 7 0 s3_1b3u5 := rotate_impossible sym3_2 (z := s3_1u2b27) (by simp only [s3_1b3u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b27x

def s3_1b3u6 : List Sig := [y3_46,x3_4,y3_17,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3u6x : Impossible 7 0 s3_1b3u6 := rotate_impossible sym3_3 (z := s3_1u2b27) (by simp only [s3_1b3u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b27x

def s3_1b3u : List (List Sig) := [s3_1b3u0,s3_1b3u1,s3_1b3u2,s3_1b3u3,s3_1b3u4,s3_1b3u5,s3_1b3u6]

lemma s3_1b3ux (v : List Sig) (h : (!s3_1b3u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b3u := by simpa using h
  simp only [s3_1b3u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b3u0x
  · exact s3_1b3u1x
  · exact s3_1b3u2x
  · exact s3_1b3u3x
  · exact s3_1b3u4x
  · exact s3_1b3u5x
  · exact s3_1b3u6x

def s3_1b3b7 : List Sig := [y3_67,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b7x : Impossible 7 1 s3_1b3b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b8 : List Sig := [y3_67,y3_17,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b8x : Impossible 7 1 s3_1b3b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b9 : List Sig := [y3_55,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b9x : Impossible 7 1 s3_1b3b9 := impPerm (z := s3_1b1b11) (by decide +kernel) s3_1b1b11x

def s3_1b3b10 : List Sig := [y3_55,y3_17,x3_1,x3_0,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b10x : Impossible 7 1 s3_1b3b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b11 : List Sig := [y3_68,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b11x : Impossible 7 1 s3_1b3b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b12 : List Sig := [y3_68,y3_17,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b12x : Impossible 7 1 s3_1b3b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b13 : List Sig := [y3_69,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b13x : Impossible 7 1 s3_1b3b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b14 : List Sig := [y3_69,y3_17,x3_3,x3_0,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b14x : Impossible 7 1 s3_1b3b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b15 : List Sig := [y3_70,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b15x : Impossible 7 1 s3_1b3b15 := rotate_impossible sym3_1 (z := s3_1b3b11) (by simp only [s3_1b3b15,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_70,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b11x

def s3_1b3b16 : List Sig := [y3_70,y3_17,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b16x : Impossible 7 1 s3_1b3b16 := rotate_impossible sym3_1 (z := s3_1b3b12) (by simp only [s3_1b3b16,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_70,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b12x

def s3_1b3b17 : List Sig := [y3_71,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b17x : Impossible 7 1 s3_1b3b17 := rotate_impossible sym3_1 (z := s3_1b3b13) (by simp only [s3_1b3b17,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_71,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b13x

def s3_1b3b18 : List Sig := [y3_71,y3_17,x3_4,x3_0,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b18x : Impossible 7 1 s3_1b3b18 := rotate_impossible sym3_1 (z := s3_1b3b14) (by simp only [s3_1b3b18,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_71,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b14x

def s3_1b3b19 : List Sig := [y3_16,x3_0,y3_17,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b19x : Impossible 7 1 s3_1b3b19 := impPerm (z := s3_1b2b19) (by decide +kernel) s3_1b2b19x

def s3_1b3b20 : List Sig := [y3_16,x3_2,y3_17,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b20x : Impossible 7 1 s3_1b3b20 := impPerm (z := s3_1b2b20) (by decide +kernel) s3_1b2b20x

def s3_1b3b21 : List Sig := [y3_16,x3_0,x3_2,y3_17,x3_1,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b21x : Impossible 7 1 s3_1b3b21 := impPerm (z := s3_1b2b21) (by decide +kernel) s3_1b2b21x

def s3_1b3b22 : List Sig := [y3_14,x3_0,x3_1,y3_17,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b22x : Impossible 7 1 s3_1b3b22 := impPerm (z := s3_1b0b24) (by decide +kernel) s3_1b0b24x

def s3_1b3b23 : List Sig := [y3_15,x3_0,x3_1,y3_17,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b23x : Impossible 7 1 s3_1b3b23 := impPerm (z := s3_1b1b30) (by decide +kernel) s3_1b1b30x

def s3_1b3b24 : List Sig := [y3_18,x3_0,x3_3,y3_17,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b24x : Impossible 7 1 s3_1b3b24 := rotate_impossible sym3_2 (z := s3_1b2b25) (by simp only [s3_1b3b24,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_18,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b2b25x

def s3_1b3b25 : List Sig := [y3_19,x3_0,x3_3,y3_17,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b25x : Impossible 7 1 s3_1b3b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b26 : List Sig := [y3_20,x3_0,x3_4,y3_17,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b26x : Impossible 7 1 s3_1b3b26 := rotate_impossible sym3_3 (z := s3_1b2b25) (by simp only [s3_1b3b26,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_20,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b2b25x

def s3_1b3b27 : List Sig := [y3_21,x3_0,x3_4,y3_17,x3_2,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b27x : Impossible 7 1 s3_1b3b27 := rotate_impossible sym3_1 (z := s3_1b3b25) (by simp only [s3_1b3b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_21,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b25x

def s3_1b3b28 : List Sig := [y3_22,x3_2,x3_1,y3_17,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b28x : Impossible 7 1 s3_1b3b28 := rotate_impossible sym3_6 (z := s3_1b2b30) (by simp only [s3_1b3b28,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_22,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b2b30x

def s3_1b3b29 : List Sig := [y3_23,x3_2,x3_1,y3_17,x3_0,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b29x : Impossible 7 1 s3_1b3b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b30 : List Sig := [y3_28,x3_2,x3_3,y3_17,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b30x : Impossible 7 1 s3_1b3b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b31 : List Sig := [y3_29,x3_2,x3_3,y3_17,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b31x : Impossible 7 1 s3_1b3b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b32 : List Sig := [y3_30,x3_2,x3_4,y3_17,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b32x : Impossible 7 1 s3_1b3b32 := rotate_impossible sym3_1 (z := s3_1b3b30) (by simp only [s3_1b3b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_30,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b30x

def s3_1b3b33 : List Sig := [y3_31,x3_2,x3_4,y3_17,x3_0,x3_1,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b33x : Impossible 7 1 s3_1b3b33 := rotate_impossible sym3_1 (z := s3_1b3b31) (by simp only [s3_1b3b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_31,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b31x

def s3_1b3b34 : List Sig := [y3_24,x3_1,x3_3,y3_17,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b34x : Impossible 7 1 s3_1b3b34 := rotate_impossible sym3_8 (z := s3_1b2b36) (by simp only [s3_1b3b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_24,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b2b36x

def s3_1b3b35 : List Sig := [y3_25,x3_1,x3_3,y3_17,x3_0,x3_2,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b35x : Impossible 7 1 s3_1b3b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b36 : List Sig := [y3_26,x3_1,x3_4,y3_17,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b36x : Impossible 7 1 s3_1b3b36 := rotate_impossible sym3_9 (z := s3_1b2b36) (by simp only [s3_1b3b36,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_26,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b2b36x

def s3_1b3b37 : List Sig := [y3_27,x3_1,x3_4,y3_17,x3_0,x3_2,x3_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b37x : Impossible 7 1 s3_1b3b37 := rotate_impossible sym3_1 (z := s3_1b3b35) (by simp only [s3_1b3b37,x3_0,x3_1,x3_2,x3_3,x3_4,y3_17,y3_27,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b3b35x

def s3_1b3b38 : List Sig := [y3_32,x3_3,x3_4,y3_17,x3_0,x3_2,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b38x : Impossible 7 1 s3_1b3b38 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b39 : List Sig := [y3_33,x3_3,x3_4,y3_17,x3_0,x3_2,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3b39x : Impossible 7 1 s3_1b3b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b3b : List (List Sig) := [s3_1b3b7,s3_1b3b8,s3_1b3b9,s3_1b3b10,s3_1b3b11,s3_1b3b12,s3_1b3b13,s3_1b3b14,s3_1b3b15,s3_1b3b16,s3_1b3b17,s3_1b3b18,s3_1b3b19,s3_1b3b20,s3_1b3b21,s3_1b3b22,s3_1b3b23,s3_1b3b24,s3_1b3b25,s3_1b3b26,s3_1b3b27,s3_1b3b28,s3_1b3b29,s3_1b3b30,s3_1b3b31,s3_1b3b32,s3_1b3b33,s3_1b3b34,s3_1b3b35,s3_1b3b36,s3_1b3b37,s3_1b3b38,s3_1b3b39]

lemma s3_1b3bx (v : List Sig) (h : (!s3_1b3b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b3b := by simpa using h
  simp only [s3_1b3b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b3b7x
  · exact s3_1b3b8x
  · exact s3_1b3b9x
  · exact s3_1b3b10x
  · exact s3_1b3b11x
  · exact s3_1b3b12x
  · exact s3_1b3b13x
  · exact s3_1b3b14x
  · exact s3_1b3b15x
  · exact s3_1b3b16x
  · exact s3_1b3b17x
  · exact s3_1b3b18x
  · exact s3_1b3b19x
  · exact s3_1b3b20x
  · exact s3_1b3b21x
  · exact s3_1b3b22x
  · exact s3_1b3b23x
  · exact s3_1b3b24x
  · exact s3_1b3b25x
  · exact s3_1b3b26x
  · exact s3_1b3b27x
  · exact s3_1b3b28x
  · exact s3_1b3b29x
  · exact s3_1b3b30x
  · exact s3_1b3b31x
  · exact s3_1b3b32x
  · exact s3_1b3b33x
  · exact s3_1b3b34x
  · exact s3_1b3b35x
  · exact s3_1b3b36x
  · exact s3_1b3b37x
  · exact s3_1b3b38x
  · exact s3_1b3b39x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b3x : Impossible 8 1 s3_1b3 := exclude_step (u := fun v => !s3_1b3u.contains v) (b := fun v => !s3_1b3b.contains v) (by decide +kernel) s3_1b3ux s3_1b3bx (by decide +kernel)

def s3_1b4 : List Sig := [bin false (r3.getD 0 zero) (r3.getD 3 zero),r3.getD 0 zero,r3.getD 3 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b4x : Impossible 8 1 s3_1b4 := rotate_impossible sym3_2 (z := s3_1b2) (by simp only [s3_1b4,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b2x

def s3_1b5 : List Sig := [bin true (r3.getD 0 zero) (r3.getD 3 zero),r3.getD 0 zero,r3.getD 3 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b5x : Impossible 8 1 s3_1b5 := rotate_impossible sym3_2 (z := s3_1b3) (by simp only [s3_1b5,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b3x

def s3_1b6 : List Sig := [bin false (r3.getD 0 zero) (r3.getD 4 zero),r3.getD 0 zero,r3.getD 4 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b6x : Impossible 8 1 s3_1b6 := rotate_impossible sym3_3 (z := s3_1b2) (by simp only [s3_1b6,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b2x

def s3_1b7 : List Sig := [bin true (r3.getD 0 zero) (r3.getD 4 zero),r3.getD 0 zero,r3.getD 4 zero,r3.getD 1 zero,r3.getD 2 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b7x : Impossible 8 1 s3_1b7 := rotate_impossible sym3_3 (z := s3_1b3) (by simp only [s3_1b7,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b3x

def s3_1b8 : List Sig := [bin false (r3.getD 1 zero) (r3.getD 2 zero),r3.getD 1 zero,r3.getD 2 zero,r3.getD 0 zero,r3.getD 3 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b8x : Impossible 8 1 s3_1b8 := rotate_impossible sym3_6 (z := s3_1b2) (by simp only [s3_1b8,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b2x

def s3_1b9 : List Sig := [bin true (r3.getD 1 zero) (r3.getD 2 zero),r3.getD 1 zero,r3.getD 2 zero,r3.getD 0 zero,r3.getD 3 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b9x : Impossible 8 1 s3_1b9 := rotate_impossible sym3_6 (z := s3_1b3) (by simp only [s3_1b9,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b3x

def s3_1b10 : List Sig := [bin false (r3.getD 1 zero) (r3.getD 3 zero),r3.getD 1 zero,r3.getD 3 zero,r3.getD 0 zero,r3.getD 2 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b10x : Impossible 8 1 s3_1b10 := rotate_impossible sym3_8 (z := s3_1b2) (by simp only [s3_1b10,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b2x

def s3_1b11 : List Sig := [bin true (r3.getD 1 zero) (r3.getD 3 zero),r3.getD 1 zero,r3.getD 3 zero,r3.getD 0 zero,r3.getD 2 zero,r3.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b11x : Impossible 8 1 s3_1b11 := rotate_impossible sym3_8 (z := s3_1b3) (by simp only [s3_1b11,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b3x

def s3_1b12 : List Sig := [bin false (r3.getD 1 zero) (r3.getD 4 zero),r3.getD 1 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 2 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b12x : Impossible 8 1 s3_1b12 := rotate_impossible sym3_9 (z := s3_1b2) (by simp only [s3_1b12,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b2x

def s3_1b13 : List Sig := [bin true (r3.getD 1 zero) (r3.getD 4 zero),r3.getD 1 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 2 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b13x : Impossible 8 1 s3_1b13 := rotate_impossible sym3_9 (z := s3_1b3) (by simp only [s3_1b13,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b3x

def s3_1b14 : List Sig := [bin false (r3.getD 2 zero) (r3.getD 3 zero),r3.getD 2 zero,r3.getD 3 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 4 zero]

def s3_1b14u0 : List Sig := [y3_72,x3_2,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u0x : Impossible 7 0 s3_1b14u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14u1 : List Sig := [y3_72,y3_28,x3_2,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u1x : Impossible 7 0 s3_1b14u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14u2 : List Sig := [y3_34,x3_2,y3_28,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u2x : Impossible 7 0 s3_1b14u2 := impPerm (z := s3_1u2b20) (by decide +kernel) s3_1u2b20x

def s3_1b14u3 : List Sig := [y3_45,x3_3,y3_28,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u3x : Impossible 7 0 s3_1b14u3 := rotate_impossible sym3_2 (z := s3_1u2b20) (by simp only [s3_1b14u3,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b20x

def s3_1b14u4 : List Sig := [y3_5,x3_0,y3_28,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u4x : Impossible 7 0 s3_1b14u4 := impPerm (z := s3_1u0b30) (by decide +kernel) s3_1u0b30x

def s3_1b14u5 : List Sig := [y3_44,x3_1,y3_28,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u5x : Impossible 7 0 s3_1b14u5 := rotate_impossible sym3_6 (z := s3_1u0b30) (by simp only [s3_1b14u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b30x

def s3_1b14u6 : List Sig := [y3_46,x3_4,y3_28,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14u6x : Impossible 7 0 s3_1b14u6 := rotate_impossible sym3_3 (z := s3_1u2b34) (by simp only [s3_1b14u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b34x

def s3_1b14u : List (List Sig) := [s3_1b14u0,s3_1b14u1,s3_1b14u2,s3_1b14u3,s3_1b14u4,s3_1b14u5,s3_1b14u6]

lemma s3_1b14ux (v : List Sig) (h : (!s3_1b14u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b14u := by simpa using h
  simp only [s3_1b14u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b14u0x
  · exact s3_1b14u1x
  · exact s3_1b14u2x
  · exact s3_1b14u3x
  · exact s3_1b14u4x
  · exact s3_1b14u5x
  · exact s3_1b14u6x

def s3_1b14b7 : List Sig := [y3_62,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b7x : Impossible 7 1 s3_1b14b7 := impPerm (z := s3_1b2b11) (by decide +kernel) s3_1b2b11x

def s3_1b14b8 : List Sig := [y3_62,y3_28,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b8x : Impossible 7 1 s3_1b14b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b9 : List Sig := [y3_73,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b9x : Impossible 7 1 s3_1b14b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b10 : List Sig := [y3_73,y3_28,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b10x : Impossible 7 1 s3_1b14b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b11 : List Sig := [y3_74,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b11x : Impossible 7 1 s3_1b14b11 := rotate_impossible sym3_6 (z := s3_1b2b11) (by simp only [s3_1b14b11,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_74,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b2b11x

def s3_1b14b12 : List Sig := [y3_74,y3_28,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b12x : Impossible 7 1 s3_1b14b12 := rotate_impossible sym3_6 (z := s3_1b14b8) (by simp only [s3_1b14b12,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_74,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b14b8x

def s3_1b14b13 : List Sig := [y3_75,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b13x : Impossible 7 1 s3_1b14b13 := rotate_impossible sym3_6 (z := s3_1b14b9) (by simp only [s3_1b14b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_75,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b14b9x

def s3_1b14b14 : List Sig := [y3_75,y3_28,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b14x : Impossible 7 1 s3_1b14b14 := rotate_impossible sym3_6 (z := s3_1b14b10) (by simp only [s3_1b14b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_75,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b14b10x

def s3_1b14b15 : List Sig := [y3_76,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b15x : Impossible 7 1 s3_1b14b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b16 : List Sig := [y3_76,y3_28,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b16x : Impossible 7 1 s3_1b14b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b17 : List Sig := [y3_77,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b17x : Impossible 7 1 s3_1b14b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b18 : List Sig := [y3_77,y3_28,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b18x : Impossible 7 1 s3_1b14b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b19 : List Sig := [y3_77,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b19x : Impossible 7 1 s3_1b14b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b20 : List Sig := [y3_77,y3_28,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b20x : Impossible 7 1 s3_1b14b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b21 : List Sig := [y3_29,y3_28,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b21x : Impossible 7 1 s3_1b14b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b22 : List Sig := [y3_29,x3_2,y3_28,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b22x : Impossible 7 1 s3_1b14b22 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b23 : List Sig := [y3_29,x3_3,y3_28,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b23x : Impossible 7 1 s3_1b14b23 := rotate_impossible sym3_2 (z := s3_1b14b22) (by simp only [s3_1b14b23,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b14b22x

def s3_1b14b24 : List Sig := [y3_29,x3_2,x3_3,y3_28,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b24x : Impossible 7 1 s3_1b14b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b25 : List Sig := [y3_16,x3_2,x3_0,y3_28,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b25x : Impossible 7 1 s3_1b14b25 := impPerm (z := s3_1b2b31) (by decide +kernel) s3_1b2b31x

def s3_1b14b26 : List Sig := [y3_17,x3_2,x3_0,y3_28,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b26x : Impossible 7 1 s3_1b14b26 := impPerm (z := s3_1b3b30) (by decide +kernel) s3_1b3b30x

def s3_1b14b27 : List Sig := [y3_22,x3_2,x3_1,y3_28,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b27x : Impossible 7 1 s3_1b14b27 := rotate_impossible sym3_6 (z := s3_1b2b31) (by simp only [s3_1b14b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_22,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b2b31x

def s3_1b14b28 : List Sig := [y3_23,x3_2,x3_1,y3_28,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b28x : Impossible 7 1 s3_1b14b28 := rotate_impossible sym3_6 (z := s3_1b3b30) (by simp only [s3_1b14b28,x3_0,x3_1,x3_2,x3_3,x3_4,y3_23,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b3b30x

def s3_1b14b29 : List Sig := [y3_30,x3_2,x3_4,y3_28,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b29x : Impossible 7 1 s3_1b14b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b30 : List Sig := [y3_31,x3_2,x3_4,y3_28,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b30x : Impossible 7 1 s3_1b14b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b14b31 : List Sig := [y3_18,x3_3,x3_0,y3_28,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b31x : Impossible 7 1 s3_1b14b31 := rotate_impossible sym3_2 (z := s3_1b2b31) (by simp only [s3_1b14b31,x3_0,x3_1,x3_2,x3_3,x3_4,y3_18,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b2b31x

def s3_1b14b32 : List Sig := [y3_19,x3_3,x3_0,y3_28,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b32x : Impossible 7 1 s3_1b14b32 := rotate_impossible sym3_2 (z := s3_1b3b30) (by simp only [s3_1b14b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_19,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b3b30x

def s3_1b14b33 : List Sig := [y3_24,x3_3,x3_1,y3_28,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b33x : Impossible 7 1 s3_1b14b33 := rotate_impossible sym3_8 (z := s3_1b2b31) (by simp only [s3_1b14b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_24,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b2b31x

def s3_1b14b34 : List Sig := [y3_25,x3_3,x3_1,y3_28,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b34x : Impossible 7 1 s3_1b14b34 := rotate_impossible sym3_8 (z := s3_1b3b30) (by simp only [s3_1b14b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_25,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b3b30x

def s3_1b14b35 : List Sig := [y3_32,x3_3,x3_4,y3_28,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b35x : Impossible 7 1 s3_1b14b35 := rotate_impossible sym3_2 (z := s3_1b14b29) (by simp only [s3_1b14b35,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_32,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b14b29x

def s3_1b14b36 : List Sig := [y3_33,x3_3,x3_4,y3_28,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b36x : Impossible 7 1 s3_1b14b36 := rotate_impossible sym3_2 (z := s3_1b14b30) (by simp only [s3_1b14b36,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_33,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b14b30x

def s3_1b14b37 : List Sig := [y3_14,x3_0,x3_1,y3_28,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b37x : Impossible 7 1 s3_1b14b37 := impPerm (z := s3_1b0b35) (by decide +kernel) s3_1b0b35x

def s3_1b14b38 : List Sig := [y3_15,x3_0,x3_1,y3_28,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b38x : Impossible 7 1 s3_1b14b38 := impPerm (z := s3_1b1b41) (by decide +kernel) s3_1b1b41x

def s3_1b14b39 : List Sig := [y3_20,x3_0,x3_4,y3_28,x3_2,x3_3,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b39x : Impossible 7 1 s3_1b14b39 := rotate_impossible sym3_3 (z := s3_1b2b39) (by simp only [s3_1b14b39,x3_0,x3_1,x3_2,x3_3,x3_4,y3_20,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b2b39x

def s3_1b14b40 : List Sig := [y3_21,x3_0,x3_4,y3_28,x3_2,x3_3,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b40x : Impossible 7 1 s3_1b14b40 := rotate_impossible sym3_3 (z := s3_1b3b38) (by simp only [s3_1b14b40,x3_0,x3_1,x3_2,x3_3,x3_4,y3_21,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b3b38x

def s3_1b14b41 : List Sig := [y3_26,x3_1,x3_4,y3_28,x3_2,x3_3,x3_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b41x : Impossible 7 1 s3_1b14b41 := rotate_impossible sym3_9 (z := s3_1b2b39) (by simp only [s3_1b14b41,x3_0,x3_1,x3_2,x3_3,x3_4,y3_26,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b2b39x

def s3_1b14b42 : List Sig := [y3_27,x3_1,x3_4,y3_28,x3_2,x3_3,x3_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14b42x : Impossible 7 1 s3_1b14b42 := rotate_impossible sym3_9 (z := s3_1b3b38) (by simp only [s3_1b14b42,x3_0,x3_1,x3_2,x3_3,x3_4,y3_27,y3_28,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b3b38x

def s3_1b14b : List (List Sig) := [s3_1b14b7,s3_1b14b8,s3_1b14b9,s3_1b14b10,s3_1b14b11,s3_1b14b12,s3_1b14b13,s3_1b14b14,s3_1b14b15,s3_1b14b16,s3_1b14b17,s3_1b14b18,s3_1b14b19,s3_1b14b20,s3_1b14b21,s3_1b14b22,s3_1b14b23,s3_1b14b24,s3_1b14b25,s3_1b14b26,s3_1b14b27,s3_1b14b28,s3_1b14b29,s3_1b14b30,s3_1b14b31,s3_1b14b32,s3_1b14b33,s3_1b14b34,s3_1b14b35,s3_1b14b36,s3_1b14b37,s3_1b14b38,s3_1b14b39,s3_1b14b40,s3_1b14b41,s3_1b14b42]

lemma s3_1b14bx (v : List Sig) (h : (!s3_1b14b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b14b := by simpa using h
  simp only [s3_1b14b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b14b7x
  · exact s3_1b14b8x
  · exact s3_1b14b9x
  · exact s3_1b14b10x
  · exact s3_1b14b11x
  · exact s3_1b14b12x
  · exact s3_1b14b13x
  · exact s3_1b14b14x
  · exact s3_1b14b15x
  · exact s3_1b14b16x
  · exact s3_1b14b17x
  · exact s3_1b14b18x
  · exact s3_1b14b19x
  · exact s3_1b14b20x
  · exact s3_1b14b21x
  · exact s3_1b14b22x
  · exact s3_1b14b23x
  · exact s3_1b14b24x
  · exact s3_1b14b25x
  · exact s3_1b14b26x
  · exact s3_1b14b27x
  · exact s3_1b14b28x
  · exact s3_1b14b29x
  · exact s3_1b14b30x
  · exact s3_1b14b31x
  · exact s3_1b14b32x
  · exact s3_1b14b33x
  · exact s3_1b14b34x
  · exact s3_1b14b35x
  · exact s3_1b14b36x
  · exact s3_1b14b37x
  · exact s3_1b14b38x
  · exact s3_1b14b39x
  · exact s3_1b14b40x
  · exact s3_1b14b41x
  · exact s3_1b14b42x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b14x : Impossible 8 1 s3_1b14 := exclude_step (u := fun v => !s3_1b14u.contains v) (b := fun v => !s3_1b14b.contains v) (by decide +kernel) s3_1b14ux s3_1b14bx (by decide +kernel)

def s3_1b15 : List Sig := [bin true (r3.getD 2 zero) (r3.getD 3 zero),r3.getD 2 zero,r3.getD 3 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 4 zero]

def s3_1b15u0 : List Sig := [y3_78,x3_2,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u0x : Impossible 7 0 s3_1b15u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15u1 : List Sig := [y3_78,y3_29,x3_2,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u1x : Impossible 7 0 s3_1b15u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15u2 : List Sig := [y3_34,x3_2,y3_29,x3_3,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u2x : Impossible 7 0 s3_1b15u2 := impPerm (z := s3_1u2b21) (by decide +kernel) s3_1u2b21x

def s3_1b15u3 : List Sig := [y3_45,x3_3,y3_29,x3_2,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u3x : Impossible 7 0 s3_1b15u3 := rotate_impossible sym3_2 (z := s3_1u2b21) (by simp only [s3_1b15u3,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_45,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1u2b21x

def s3_1b15u4 : List Sig := [y3_5,x3_0,y3_29,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u4x : Impossible 7 0 s3_1b15u4 := impPerm (z := s3_1u0b31) (by decide +kernel) s3_1u0b31x

def s3_1b15u5 : List Sig := [y3_44,x3_1,y3_29,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u5x : Impossible 7 0 s3_1b15u5 := rotate_impossible sym3_6 (z := s3_1u0b31) (by simp only [s3_1b15u5,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_44,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1u0b31x

def s3_1b15u6 : List Sig := [y3_46,x3_4,y3_29,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15u6x : Impossible 7 0 s3_1b15u6 := rotate_impossible sym3_3 (z := s3_1u2b35) (by simp only [s3_1b15u6,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_46,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1u2b35x

def s3_1b15u : List (List Sig) := [s3_1b15u0,s3_1b15u1,s3_1b15u2,s3_1b15u3,s3_1b15u4,s3_1b15u5,s3_1b15u6]

lemma s3_1b15ux (v : List Sig) (h : (!s3_1b15u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s3_1b15u := by simpa using h
  simp only [s3_1b15u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b15u0x
  · exact s3_1b15u1x
  · exact s3_1b15u2x
  · exact s3_1b15u3x
  · exact s3_1b15u4x
  · exact s3_1b15u5x
  · exact s3_1b15u6x

def s3_1b15b7 : List Sig := [y3_79,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b7x : Impossible 7 1 s3_1b15b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b8 : List Sig := [y3_79,y3_29,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b8x : Impossible 7 1 s3_1b15b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b9 : List Sig := [y3_69,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b9x : Impossible 7 1 s3_1b15b9 := impPerm (z := s3_1b3b13) (by decide +kernel) s3_1b3b13x

def s3_1b15b10 : List Sig := [y3_69,y3_29,x3_0,x3_2,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b10x : Impossible 7 1 s3_1b15b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b11 : List Sig := [y3_80,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b11x : Impossible 7 1 s3_1b15b11 := rotate_impossible sym3_6 (z := s3_1b15b7) (by simp only [s3_1b15b11,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_80,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b15b7x

def s3_1b15b12 : List Sig := [y3_80,y3_29,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b12x : Impossible 7 1 s3_1b15b12 := rotate_impossible sym3_6 (z := s3_1b15b8) (by simp only [s3_1b15b12,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_80,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b15b8x

def s3_1b15b13 : List Sig := [y3_81,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b13x : Impossible 7 1 s3_1b15b13 := rotate_impossible sym3_6 (z := s3_1b3b13) (by simp only [s3_1b15b13,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_81,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b3b13x

def s3_1b15b14 : List Sig := [y3_81,y3_29,x3_1,x3_2,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b14x : Impossible 7 1 s3_1b15b14 := rotate_impossible sym3_6 (z := s3_1b15b10) (by simp only [s3_1b15b14,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_81,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b15b10x

def s3_1b15b15 : List Sig := [y3_82,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b15x : Impossible 7 1 s3_1b15b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b16 : List Sig := [y3_82,y3_29,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b16x : Impossible 7 1 s3_1b15b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b17 : List Sig := [y3_83,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b17x : Impossible 7 1 s3_1b15b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b18 : List Sig := [y3_83,y3_29,x3_4,x3_2,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b18x : Impossible 7 1 s3_1b15b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b19 : List Sig := [y3_28,y3_29,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b19x : Impossible 7 1 s3_1b15b19 := impPerm (z := s3_1b14b21) (by decide +kernel) s3_1b14b21x

def s3_1b15b20 : List Sig := [y3_28,x3_2,y3_29,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b20x : Impossible 7 1 s3_1b15b20 := impPerm (z := s3_1b14b22) (by decide +kernel) s3_1b14b22x

def s3_1b15b21 : List Sig := [y3_28,x3_3,y3_29,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b21x : Impossible 7 1 s3_1b15b21 := rotate_impossible sym3_2 (z := s3_1b14b22) (by simp only [s3_1b15b21,x3_0,x3_1,x3_2,x3_3,x3_4,y3_28,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b14b22x

def s3_1b15b22 : List Sig := [y3_28,x3_2,x3_3,y3_29,x3_0,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b22x : Impossible 7 1 s3_1b15b22 := impPerm (z := s3_1b14b24) (by decide +kernel) s3_1b14b24x

def s3_1b15b23 : List Sig := [y3_16,x3_2,x3_0,y3_29,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b23x : Impossible 7 1 s3_1b15b23 := impPerm (z := s3_1b2b32) (by decide +kernel) s3_1b2b32x

def s3_1b15b24 : List Sig := [y3_17,x3_2,x3_0,y3_29,x3_3,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b24x : Impossible 7 1 s3_1b15b24 := impPerm (z := s3_1b3b31) (by decide +kernel) s3_1b3b31x

def s3_1b15b25 : List Sig := [y3_22,x3_2,x3_1,y3_29,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b25x : Impossible 7 1 s3_1b15b25 := rotate_impossible sym3_6 (z := s3_1b2b32) (by simp only [s3_1b15b25,x3_0,x3_1,x3_2,x3_3,x3_4,y3_22,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b2b32x

def s3_1b15b26 : List Sig := [y3_23,x3_2,x3_1,y3_29,x3_3,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b26x : Impossible 7 1 s3_1b15b26 := rotate_impossible sym3_6 (z := s3_1b3b31) (by simp only [s3_1b15b26,x3_0,x3_1,x3_2,x3_3,x3_4,y3_23,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_6_0,rot3_6_1,rot3_6_2,rot3_6_3,rot3_6_4]; decide +kernel) s3_1b3b31x

def s3_1b15b27 : List Sig := [y3_30,x3_2,x3_4,y3_29,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b27x : Impossible 7 1 s3_1b15b27 := rotate_impossible sym3_1 (z := s3_1b14b30) (by simp only [s3_1b15b27,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_30,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b14b30x

def s3_1b15b28 : List Sig := [y3_31,x3_4,y3_29,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b28x : Impossible 7 1 s3_1b15b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b29 : List Sig := [y3_31,x3_2,x3_4,y3_29,x3_3,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b29x : Impossible 7 1 s3_1b15b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s3_1b15b30 : List Sig := [y3_18,x3_3,x3_0,y3_29,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b30x : Impossible 7 1 s3_1b15b30 := rotate_impossible sym3_2 (z := s3_1b2b32) (by simp only [s3_1b15b30,x3_0,x3_1,x3_2,x3_3,x3_4,y3_18,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b2b32x

def s3_1b15b31 : List Sig := [y3_19,x3_3,x3_0,y3_29,x3_2,x3_1,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b31x : Impossible 7 1 s3_1b15b31 := rotate_impossible sym3_2 (z := s3_1b3b31) (by simp only [s3_1b15b31,x3_0,x3_1,x3_2,x3_3,x3_4,y3_19,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b3b31x

def s3_1b15b32 : List Sig := [y3_24,x3_3,x3_1,y3_29,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b32x : Impossible 7 1 s3_1b15b32 := rotate_impossible sym3_8 (z := s3_1b2b32) (by simp only [s3_1b15b32,x3_0,x3_1,x3_2,x3_3,x3_4,y3_24,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b2b32x

def s3_1b15b33 : List Sig := [y3_25,x3_3,x3_1,y3_29,x3_2,x3_0,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b33x : Impossible 7 1 s3_1b15b33 := rotate_impossible sym3_8 (z := s3_1b3b31) (by simp only [s3_1b15b33,x3_0,x3_1,x3_2,x3_3,x3_4,y3_25,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_8_0,rot3_8_1,rot3_8_2,rot3_8_3,rot3_8_4]; decide +kernel) s3_1b3b31x

def s3_1b15b34 : List Sig := [y3_32,x3_3,x3_4,y3_29,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b34x : Impossible 7 1 s3_1b15b34 := rotate_impossible sym3_4 (z := s3_1b14b30) (by simp only [s3_1b15b34,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_32,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b14b30x

def s3_1b15b35 : List Sig := [y3_33,x3_4,y3_29,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b35x : Impossible 7 1 s3_1b15b35 := rotate_impossible sym3_2 (z := s3_1b15b28) (by simp only [s3_1b15b35,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_33,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b15b28x

def s3_1b15b36 : List Sig := [y3_33,x3_3,x3_4,y3_29,x3_2,x3_0,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b36x : Impossible 7 1 s3_1b15b36 := rotate_impossible sym3_2 (z := s3_1b15b29) (by simp only [s3_1b15b36,x3_0,x3_1,x3_2,x3_3,x3_4,y3_29,y3_33,List.map_cons,List.map_nil,action_bin,action_neg,rot3_2_0,rot3_2_1,rot3_2_2,rot3_2_3,rot3_2_4]; decide +kernel) s3_1b15b29x

def s3_1b15b37 : List Sig := [y3_14,x3_0,x3_1,y3_29,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b37x : Impossible 7 1 s3_1b15b37 := impPerm (z := s3_1b0b36) (by decide +kernel) s3_1b0b36x

def s3_1b15b38 : List Sig := [y3_15,x3_0,x3_1,y3_29,x3_2,x3_3,x3_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b38x : Impossible 7 1 s3_1b15b38 := impPerm (z := s3_1b1b42) (by decide +kernel) s3_1b1b42x

def s3_1b15b39 : List Sig := [y3_20,x3_0,x3_4,y3_29,x3_2,x3_3,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b39x : Impossible 7 1 s3_1b15b39 := rotate_impossible sym3_3 (z := s3_1b2b40) (by simp only [s3_1b15b39,x3_0,x3_1,x3_2,x3_3,x3_4,y3_20,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b2b40x

def s3_1b15b40 : List Sig := [y3_21,x3_0,x3_4,y3_29,x3_2,x3_3,x3_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b40x : Impossible 7 1 s3_1b15b40 := rotate_impossible sym3_3 (z := s3_1b3b39) (by simp only [s3_1b15b40,x3_0,x3_1,x3_2,x3_3,x3_4,y3_21,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_3_0,rot3_3_1,rot3_3_2,rot3_3_3,rot3_3_4]; decide +kernel) s3_1b3b39x

def s3_1b15b41 : List Sig := [y3_26,x3_1,x3_4,y3_29,x3_2,x3_3,x3_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b41x : Impossible 7 1 s3_1b15b41 := rotate_impossible sym3_9 (z := s3_1b2b40) (by simp only [s3_1b15b41,x3_0,x3_1,x3_2,x3_3,x3_4,y3_26,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b2b40x

def s3_1b15b42 : List Sig := [y3_27,x3_1,x3_4,y3_29,x3_2,x3_3,x3_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15b42x : Impossible 7 1 s3_1b15b42 := rotate_impossible sym3_9 (z := s3_1b3b39) (by simp only [s3_1b15b42,x3_0,x3_1,x3_2,x3_3,x3_4,y3_27,y3_29,List.map_cons,List.map_nil,action_bin,action_neg,rot3_9_0,rot3_9_1,rot3_9_2,rot3_9_3,rot3_9_4]; decide +kernel) s3_1b3b39x

def s3_1b15b : List (List Sig) := [s3_1b15b7,s3_1b15b8,s3_1b15b9,s3_1b15b10,s3_1b15b11,s3_1b15b12,s3_1b15b13,s3_1b15b14,s3_1b15b15,s3_1b15b16,s3_1b15b17,s3_1b15b18,s3_1b15b19,s3_1b15b20,s3_1b15b21,s3_1b15b22,s3_1b15b23,s3_1b15b24,s3_1b15b25,s3_1b15b26,s3_1b15b27,s3_1b15b28,s3_1b15b29,s3_1b15b30,s3_1b15b31,s3_1b15b32,s3_1b15b33,s3_1b15b34,s3_1b15b35,s3_1b15b36,s3_1b15b37,s3_1b15b38,s3_1b15b39,s3_1b15b40,s3_1b15b41,s3_1b15b42]

lemma s3_1b15bx (v : List Sig) (h : (!s3_1b15b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s3_1b15b := by simpa using h
  simp only [s3_1b15b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b15b7x
  · exact s3_1b15b8x
  · exact s3_1b15b9x
  · exact s3_1b15b10x
  · exact s3_1b15b11x
  · exact s3_1b15b12x
  · exact s3_1b15b13x
  · exact s3_1b15b14x
  · exact s3_1b15b15x
  · exact s3_1b15b16x
  · exact s3_1b15b17x
  · exact s3_1b15b18x
  · exact s3_1b15b19x
  · exact s3_1b15b20x
  · exact s3_1b15b21x
  · exact s3_1b15b22x
  · exact s3_1b15b23x
  · exact s3_1b15b24x
  · exact s3_1b15b25x
  · exact s3_1b15b26x
  · exact s3_1b15b27x
  · exact s3_1b15b28x
  · exact s3_1b15b29x
  · exact s3_1b15b30x
  · exact s3_1b15b31x
  · exact s3_1b15b32x
  · exact s3_1b15b33x
  · exact s3_1b15b34x
  · exact s3_1b15b35x
  · exact s3_1b15b36x
  · exact s3_1b15b37x
  · exact s3_1b15b38x
  · exact s3_1b15b39x
  · exact s3_1b15b40x
  · exact s3_1b15b41x
  · exact s3_1b15b42x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b15x : Impossible 8 1 s3_1b15 := exclude_step (u := fun v => !s3_1b15u.contains v) (b := fun v => !s3_1b15b.contains v) (by decide +kernel) s3_1b15ux s3_1b15bx (by decide +kernel)

def s3_1b16 : List Sig := [bin false (r3.getD 2 zero) (r3.getD 4 zero),r3.getD 2 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b16x : Impossible 8 1 s3_1b16 := rotate_impossible sym3_1 (z := s3_1b14) (by simp only [s3_1b16,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b14x

def s3_1b17 : List Sig := [bin true (r3.getD 2 zero) (r3.getD 4 zero),r3.getD 2 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b17x : Impossible 8 1 s3_1b17 := rotate_impossible sym3_1 (z := s3_1b15) (by simp only [s3_1b17,List.map_cons,List.map_nil,action_bin,action_neg,rot3_1_0,rot3_1_1,rot3_1_2,rot3_1_3,rot3_1_4]; decide +kernel) s3_1b15x

def s3_1b18 : List Sig := [bin false (r3.getD 3 zero) (r3.getD 4 zero),r3.getD 3 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b18x : Impossible 8 1 s3_1b18 := rotate_impossible sym3_4 (z := s3_1b14) (by simp only [s3_1b18,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b14x

def s3_1b19 : List Sig := [bin true (r3.getD 3 zero) (r3.getD 4 zero),r3.getD 3 zero,r3.getD 4 zero,r3.getD 0 zero,r3.getD 1 zero,r3.getD 2 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s3_1b19x : Impossible 8 1 s3_1b19 := rotate_impossible sym3_4 (z := s3_1b15) (by simp only [s3_1b19,List.map_cons,List.map_nil,action_bin,action_neg,rot3_4_0,rot3_4_1,rot3_4_2,rot3_4_3,rot3_4_4]; decide +kernel) s3_1b15x

def s3_1b : List (List Sig) := [s3_1b0,s3_1b1,s3_1b2,s3_1b3,s3_1b4,s3_1b5,s3_1b6,s3_1b7,s3_1b8,s3_1b9,s3_1b10,s3_1b11,s3_1b12,s3_1b13,s3_1b14,s3_1b15,s3_1b16,s3_1b17,s3_1b18,s3_1b19]

lemma s3_1bx (v : List Sig) (h : (!s3_1b.contains v) = false) : Impossible 8 1 v := by
  have hm : v ∈ s3_1b := by simpa using h
  simp only [s3_1b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s3_1b0x
  · exact s3_1b1x
  · exact s3_1b2x
  · exact s3_1b3x
  · exact s3_1b4x
  · exact s3_1b5x
  · exact s3_1b6x
  · exact s3_1b7x
  · exact s3_1b8x
  · exact s3_1b9x
  · exact s3_1b10x
  · exact s3_1b11x
  · exact s3_1b12x
  · exact s3_1b13x
  · exact s3_1b14x
  · exact s3_1b15x
  · exact s3_1b16x
  · exact s3_1b17x
  · exact s3_1b18x
  · exact s3_1b19x

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative3_1 : Impossible 9 1 r3 :=
  exclude_step (u := fun v => !s3_1u.contains v) (b := fun v => !s3_1b.contains v) (by decide +kernel) s3_1ux s3_1bx (by decide +kernel)


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008241280 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008241280 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008241280 r3 9 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative3_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.and,[5,2]⟩,⟨.or,[6,3]⟩,⟨.or,[5,2]⟩,⟨.or,[0,1]⟩,⟨.and,[8,7]⟩,⟨.or,[10,4]⟩,⟨.and,[9,11]⟩,⟨.or,[8,7]⟩,⟨.and,[12,13]⟩],14,by simp [Clean],rfl,by decide +kernel⟩

def r4 : List Sig := [(0xffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2000200020002000200020002000200020002000200020002000200020002),(0xffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,0x5554555455545554555455545554555455545554555455545554555455545554),(0xffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000,0x9998999899989998999899989998999899989998999899989998999899989998),(0xffffffffffffffffffff0000000000000000ffffffffffffffff000000000000,0xe1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative4_1 : Impossible 7 1 r4 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937053352 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3937053352 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3937053352 r4 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative4_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.and,[5,3]⟩,⟨.or,[0,6]⟩,⟨.or,[1,2]⟩,⟨.and,[7,4]⟩,⟨.or,[8,3]⟩,⟨.and,[0,10]⟩,⟨.or,[11,9]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r5 : List Sig := [(0xffff0000ffffffffffffffffffffffffffffffff0000ffffffffffffffffffff,0x42004200420042004200420042004200420042004200420042004200420042),(0xffffffff0000ffff0000ffff0000ffff0000ffffffff0000ffffffff0000ffff,0x5494549454945494549454945494549454945494549454945494549454945494),(0xffffffffffff00000000ffffffff00000000ffffffffffff0000ffffffff0000,0x9918991899189918991899189918991899189918991899189918991899189918),(0xffffffffffffffffffff0000000000000000ffffffffffffffff000000000000,0xe1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative5_1 : Impossible 5 1 r5 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937069224 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3937069224 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3937069224 r5 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative5_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.and,[5,3]⟩,⟨.or,[0,6]⟩,⟨.or,[1,2]⟩,⟨.or,[8,4]⟩,⟨.and,[7,9]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

def r6 : List Sig := [(0xffff0000ffffffffffffffff0000ffffffffffff0000ffffffffffffffffffff,0x442044204420442044204420442044204420442044204420442044204420442),(0xffffffff0000ffff0000ffffffff0000ffffffffffff0000ffffffff0000ffff,0x4894489448944894489448944894489448944894489448944894489448944894),(0xffffffffffff00000000ffffffffffff0000ffffffffffff0000ffffffff0000,0x9118911891189118911891189118911891189118911891189118911891189118),(0xffffffffffffffffffff0000000000000000ffffffffffffffff000000000000,0xe1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative6_1 : Impossible 7 1 r6 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132456 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132456 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132456 r6 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative6_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[3,4]⟩,⟨.or,[6,7]⟩,⟨.and,[0,8]⟩,⟨.or,[3,4]⟩,⟨.and,[5,10]⟩,⟨.or,[9,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r7 : List Sig := [(0xffff0000ffffffffffffffff0000ffffffffffff0000ffffffffffff0000ffff,0x452045204520452045204520452045204520452045204520452045204520452),(0xffffffff0000ffff0000ffffffff0000ffffffffffff0000ffffffffffffffff,0x4884488448844884488448844884488448844884488448844884488448844884),(0xffffffffffff00000000ffffffffffff0000ffffffffffff0000ffffffff0000,0x9118911891189118911891189118911891189118911891189118911891189118),(0xffffffffffffffffffff0000000000000000ffffffffffffffff000000000000,0xe1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0e1e0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative7_1 : Impossible 7 1 r7 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132488 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132488 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132488 r7 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative7_1 gs o legal hn he
    ⟨[⟨.or,[0,2]⟩,⟨.and,[1,5]⟩,⟨.and,[2,3]⟩,⟨.or,[7,4]⟩,⟨.and,[0,8]⟩,⟨.or,[2,3]⟩,⟨.and,[9,10]⟩,⟨.or,[11,6]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r8 : List Sig := [(0xffff0000ffffffffffffffff0000ffffffffffff0000ffffffffffffffffffff,0x412041204120412041204120412041204120412041204120412041204120412),(0xffffffff0000ffff0000ffffffff0000ffffffffffff0000ffff0000ffffffff,0x48a448a448a448a448a448a448a448a448a448a448a448a448a448a448a448a4),(0xffffffffffff00000000ffffffffffff0000ffffffffffff00000000ffff0000,0x9138913891389138913891389138913891389138913891389138913891389138),(0xffffffffffffffffffff0000000000000000ffffffffffffffffffff00000000,0xe1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative8_1 : Impossible 6 1 r8 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132936 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132936 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132936 r8 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative8_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[5,3]⟩,⟨.and,[1,2]⟩,⟨.or,[0,7]⟩,⟨.and,[2,4]⟩,⟨.or,[9,6]⟩,⟨.and,[8,10]⟩],11,by simp [Clean],rfl,by decide +kernel⟩

def r9 : List Sig := [(0xffff0000ffffffffffffffff0000ffffffffffff0000ffffffffffffffff0000,0x42a042a042a042a042a042a042a042a042a042a042a042a042a042a042a042a),(0xffffffff0000ffff0000ffffffff0000ffffffffffff0000ffff0000ffffffff,0x488c488c488c488c488c488c488c488c488c488c488c488c488c488c488c488c),(0xffffffffffff00000000ffffffffffff0000ffffffffffff00000000ffffffff,0x9130913091309130913091309130913091309130913091309130913091309130),(0xffffffffffffffffffff0000000000000000ffffffffffffffffffff00000000,0xe1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0e1c0),(0xffffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative9_1 : Impossible 5 1 r9 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132992 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132992 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132992 r9 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative9_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[6,4]⟩,⟨.or,[7,3]⟩,⟨.and,[0,8]⟩,⟨.or,[9,5]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

end PEqualNP.Outside.L_meta_1431_aux

theorem PEqualNP.Outside.L_meta_1431 : ∀ T ∈ ({0xeae8ea80, 0xeaeaea00, 0xeee0e8a0, 0xeee8e880, 0xeaaaaaa8, 0xeaaae8a8, 0xeae8e8a8, 0xeae8e8c8, 0xeae8ea88, 0xeae8eac0} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1431_aux.fn0
  · exact PEqualNP.Outside.L_meta_1431_aux.fn1
  · exact PEqualNP.Outside.L_meta_1431_aux.fn2
  · exact PEqualNP.Outside.L_meta_1431_aux.fn3
  · exact PEqualNP.Outside.L_meta_1431_aux.fn4
  · exact PEqualNP.Outside.L_meta_1431_aux.fn5
  · exact PEqualNP.Outside.L_meta_1431_aux.fn6
  · exact PEqualNP.Outside.L_meta_1431_aux.fn7
  · exact PEqualNP.Outside.L_meta_1431_aux.fn8
  · exact PEqualNP.Outside.L_meta_1431_aux.fn9
