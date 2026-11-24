import Mathlib.Tactic.FinCases
import PEqualNP.Defs
-- The live-wire semantics and search are adapted from L-meta-1007, Apache-2.0.
namespace PEqualNP.Outside.L_meta_1437_aux

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
def r0 : List Sig := [(0xffffc000ffffffffffffff0003fffffffffffffc000ffffffffffffff0003fff,0x2004801200480120048012004801200480120048012004801200480120048012),(0xffffffff0003fff0003ffffffc000fffc000fffffff0003fff0003ffffffffff,0x4491124449112444911244491124449112444911244491124449112444911244),(0xffffffffffc0000003ffffffffff0000000ffffffffffc0000003ffffffc000,0x8926249892624989262498926249892624989262498926249892624989262498),(0xfffffffffffffffffc00000000000000000fffffffffffffffffc0000000000,0xe3838e0e3838e0e3838e0e3838e0e3838e0e3838e0e3838e0e3838e0e3838e0),(0xfffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative0_1 : Impossible 4 1 r0 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941264072 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941264072 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941264072 r0 4 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative0_1 gs o legal hn he
    ⟨[⟨.or,[0,2]⟩,⟨.and,[1,5]⟩,⟨.or,[3,4]⟩,⟨.and,[0,7]⟩,⟨.or,[8,6]⟩],9,by simp [Clean],rfl,by decide +kernel⟩

def r1 : List Sig := [(0xffffc000fffffff0003ffffffc000ffffffffffc000ffffffffffc000fffffff,0x2088822208882220888222088822208882220888222088822208882220888222),(0xffffffff0003ffffffc000fffffff0003ffffffffff0003ffffffffff0003fff,0x4111044411104441110444111044411104441110444111044411104441110444),(0xffffffffffc0000000000ffffffffffc000ffffffffffc000ffffffffffc000,0x8a222888a222888a222888a222888a222888a222888a222888a222888a222888),(0xfffffffffffffffffffff00000000000000ffffffffffffff00000000000000,0xc3c30f0c3c30f0c3c30f0c3c30f0c3c30f0c3c30f0c3c30f0c3c30f0c3c30f0),(0xfffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative1_1 : Impossible 5 1 r1 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008241384 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008241384 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008241384 r1 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative1_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[5,2]⟩,⟨.or,[0,1]⟩,⟨.and,[3,4]⟩,⟨.or,[6,8]⟩,⟨.and,[7,9]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

def r2 : List Sig := [(0xffffc000fffffff0003ffffffc000ffffffffffc000fffffffffffffffffffff,0x2080820208082020808202080820208082020808202080820208082020808202),(0xffffffff0003ffffffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x4115045411504541150454115045411504541150454115045411504541150454),(0xffffffffffc0000000000ffffffffffc000ffffffffffc0000003ffffffc000,0x8a262898a262898a262898a262898a262898a262898a262898a262898a262898),(0xfffffffffffffffffffff00000000000000fffffffffffffffffc0000000000,0xc3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0),(0xfffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative2_1 : Impossible 7 1 r2 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008241832 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008241832 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008241832 r2 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative2_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[5,2]⟩,⟨.and,[6,3]⟩,⟨.or,[7,4]⟩,⟨.and,[1,8]⟩,⟨.or,[0,9]⟩,⟨.or,[6,3]⟩,⟨.and,[10,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r3 : List Sig := [(0xffffc000fffffff0003ffffffc000ffffffffffc000ffffffffffffff0003fff,0x2084821208482120848212084821208482120848212084821208482120848212),(0xffffffff0003ffffffc000fffffff0003ffffffffff0003fff0003ffffffffff,0x4111044411104441110444111044411104441110444111044411104441110444),(0xffffffffffc0000000000ffffffffffc000ffffffffffc0000003ffffffc000,0x8a262898a262898a262898a262898a262898a262898a262898a262898a262898),(0xfffffffffffffffffffff00000000000000fffffffffffffffffc0000000000,0xc3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0),(0xfffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative3_1 : Impossible 7 1 r3 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008241864 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008241864 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008241864 r3 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative3_1 gs o legal hn he
    ⟨[⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.or,[2,3]⟩,⟨.and,[6,7]⟩,⟨.and,[8,4]⟩,⟨.or,[9,10]⟩,⟨.and,[5,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r4 : List Sig := [(0xffffc000fffffff0003ffffffc000ffffffffffc000ffffffffffffff0003fff,0xa082820a082820a082820a082820a082820a082820a082820a082820a082820a),(0xfffffff0003ffffffc000fffffff0003ffffffffff0003fff0003ffffffc000,0xc113044c113044c113044c113044c113044c113044c113044c113044c113044c),(0xfffffffffffc0000000000ffffffffffc000ffffffffffc0000003ffffffffff,0xa242890a242890a242890a242890a242890a242890a242890a242890a242890),(0xfffffffffffffffffffff00000000000000fffffffffffffffffc0000000000,0xc3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0c3830e0),(0xfffffffffffffffffffffffffffffffffff0000000000000000000000000000,0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative4_1 : Impossible 6 1 r4 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008241888 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008241888 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008241888 r4 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative4_1 gs o legal hn he
    ⟨[⟨.or,[0,3]⟩,⟨.or,[2,3]⟩,⟨.and,[0,6]⟩,⟨.and,[5,4]⟩,⟨.or,[2,8]⟩,⟨.and,[1,9]⟩,⟨.or,[7,10]⟩],11,by simp [Clean],rfl,by decide +kernel⟩

def r5 : List Sig := [(0xffffc000fffffff0003ffffffc000ffffffffffffff0003fffffffffffffffff,0xa002800a002800a002800a002800a002800a002800a002800a002800a002800a),(0xfffffff0003ffffffc000fffffff0003fff0003ffffffc000fffc000fffc000,0xc12b04ac12b04ac12b04ac12b04ac12b04ac12b04ac12b04ac12b04ac12b04ac),(0xfffffffffffc0000000000ffffffffffc0000003ffffffffff0000000fffffff,0xa4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930),(0xfffffffffffffffffffff000000000000000003fffffffffffffffff0000000,0xc7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0),(0xffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative5_1 : Impossible 7 1 r5 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008372896 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008372896 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008372896 r5 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative5_1 gs o legal hn he
    ⟨[⟨.and,[0,2]⟩,⟨.or,[5,3]⟩,⟨.and,[6,4]⟩,⟨.or,[2,7]⟩,⟨.and,[1,8]⟩,⟨.or,[0,9]⟩,⟨.or,[6,4]⟩,⟨.and,[10,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r6 : List Sig := [(0xfffc000fffffff0003ffffffc000ffffffffffffff0003fffffffffffffc000,0xa00a802a00a802a00a802a00a802a00a802a00a802a00a802a00a802a00a802a),(0xffffffff0003ffffffc000fffffff0003fff0003ffffffc000fffc000fffffff,0xc123048c123048c123048c123048c123048c123048c123048c123048c123048c),(0xfffffffffffc0000000000ffffffffffc0000003ffffffffff0000000fffffff,0xa4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930a4c2930),(0xfffffffffffffffffffff000000000000000003fffffffffffffffff0000000,0xc7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0c7031c0),(0xffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative6_1 : Impossible 5 1 r6 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008372928 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008372928 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4008372928 r6 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative6_1 gs o legal hn he
    ⟨[⟨.and,[3,4]⟩,⟨.or,[2,5]⟩,⟨.and,[1,6]⟩,⟨.or,[3,4]⟩,⟨.and,[0,8]⟩,⟨.or,[9,7]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym7_2 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfbf9faf8f7f5f6f4f3f2f0f1efeeedebeceae9e7e8e6e5e4e2e3e1e0c3c1c2c0bfbdbebcbbbab8b9b7b6b5b3b4b2b1afb0aeadacaaaba9a8dfdddedcdbd9dad8d7d6d4d5d3d2d1cfd0cecdcbcccac9c8c6c7c5c4a7a5a6a4a3a1a2a09f9e9c9d9b9a999798969593949291908e8f8d8c8b898a8887858684838280817f7e6f6d6e6c6b696a686766646563627d7b7c7a79777876757472737170615f605e5d5b5c5a595856575554535152504f4d4e4c4b4a4849474637353634333132302f2e2c2d2b2a45434442413f403e3d3c3a3b3938292728262523242221201e1f1d1c0d0b0c0a090708060504020301001b191a1817151614131210110f0e,index 0xfffefdfcfbf9faf8f7f5f6f4f3f2f0f1efeeedebeceae9e7e8e6e5e4e2e3e1e0c3c1c2c0bfbdbebcbbbab8b9b7b6b5b3b4b2b1afb0aeadacaaaba9a8dfdddedcdbd9dad8d7d6d4d5d3d2d1cfd0cecdcbcccac9c8c6c7c5c4a7a5a6a4a3a1a2a09f9e9c9d9b9a999798969593949291908e8f8d8c8b898a8887858684838280817f7e6f6d6e6c6b696a686766646563627d7b7c7a79777876757472737170615f605e5d5b5c5a595856575554535152504f4d4e4c4b4a4849474637353634333132302f2e2c2d2b2a45434442413f403e3d3c3a3b3938292728262523242221201e1f1d1c0d0b0c0a090708060504020301001b191a1817151614131210110f0e,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym7_1 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfbf6f5f4f3faf9f8f7f2f1f0efeeede8e7e6e5ecebeae9e4e3e2e1e0dfdad9d8d7dedddcdbd6d5d4d3d2d1cccbcac9d0cfcecdc8c7c6c5c4c3bebdbcbbc2c1c0bfbab9b8b7b6b5b0afaeadb4b3b2b1acabaaa9a8a7a2a1a09fa6a5a4a39e9d9c9b9a615c5b5a59605f5e5d5857565554534e4d4c4b5251504f4a4948474645403f3e3d444342413c3b3a3938373231302f363534332e2d2c2b2a999493929198979695908f8e8d8c8b868584838a8988878281807f7e7d787776757c7b7a7974737271706f6a6968676e6d6c6b6665646362292423222128272625201f1e1d1c1b161514131a1918171211100f0e0d080706050c0b0a090403020100,index 0xfffefdfcfbf6f5f4f3faf9f8f7f2f1f0efeeede8e7e6e5ecebeae9e4e3e2e1e0dfdad9d8d7dedddcdbd6d5d4d3d2d1cccbcac9d0cfcecdc8c7c6c5c4c3bebdbcbbc2c1c0bfbab9b8b7b6b5b0afaeadb4b3b2b1acabaaa9a8a7a2a1a09fa6a5a4a39e9d9c9b9a615c5b5a59605f5e5d5857565554534e4d4c4b5251504f4a4948474645403f3e3d444342413c3b3a3938373231302f363534332e2d2c2b2a999493929198979695908f8e8d8c8b868584838a8988878281807f7e7d787776757c7b7a7974737271706f6a6968676e6d6c6b6665646362292423222128272625201f1e1d1c1b161514131a1918171211100f0e0d080706050c0b0a090403020100,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym7_3 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfbf5f6f4f3f9faf8f7f2f0f1efeeede7e8e6e5ebeceae9e4e2e3e1e0c3bdbebcbbc1c2c0bfbab8b9b7b6b5afb0aeadb3b4b2b1acaaaba9a8dfd9dad8d7dddedcdbd6d4d5d3d2d1cbcccac9cfd0cecdc8c6c7c5c4a7a1a2a09fa5a6a4a39e9c9d9b9a615b5c5a595f605e5d5856575554534d4e4c4b5152504f4a48494746373132302f353634332e2c2d2b2a453f403e3d434442413c3a3b3938999394929197989695908e8f8d8c8b85868483898a88878280817f7e6f696a68676d6e6c6b66646563627d777876757b7c7a797472737170292324222127282625201e1f1d1c0d070806050b0c0a0904020301001b15161413191a18171210110f0e,index 0xfffefdfcfbf5f6f4f3f9faf8f7f2f0f1efeeede7e8e6e5ebeceae9e4e2e3e1e0c3bdbebcbbc1c2c0bfbab8b9b7b6b5afb0aeadb3b4b2b1acaaaba9a8dfd9dad8d7dddedcdbd6d4d5d3d2d1cbcccac9cfd0cecdc8c6c7c5c4a7a1a2a09fa5a6a4a39e9c9d9b9a615b5c5a595f605e5d5856575554534d4e4c4b5152504f4a48494746373132302f353634332e2c2d2b2a453f403e3d434442413c3a3b3938999394929197989695908e8f8d8c8b85868483898a88878280817f7e6f696a68676d6e6c6b66646563627d777876757b7c7a797472737170292324222127282625201e1f1d1c0d070806050b0c0a0904020301001b15161413191a18171210110f0e,by decide +kernel,by decide +kernel⟩

def r7 : List Sig := [(0xffffc000fffc000fffc000fffffff0003ffffffffff0003fffffffffffffffff,0x110844211084421108442110844211084421108442110844211084421108442),(0xffffffff0000000fffffff0003ffffffc000ffffffffffc000fffffff0003fff,0x225089422508942250894225089422508942250894225089422508942250894),(0xfffffffffffffff00000000003ffffffffff0003ffffffffff0003ffffffc000,0x446111844611184461118446111844611184461118446111844611184461118),(0xfffffffffffffffffffffffffc00000000000003fffffffffffffc0000000000,0x87821e087821e087821e087821e087821e087821e087821e087821e087821e0),(0xfffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_1_0 : action sym7_1 (r7.getD 0 zero) = r7.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_1_1 : action sym7_1 (r7.getD 1 zero) = r7.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_1_2 : action sym7_1 (r7.getD 2 zero) = r7.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_1_3 : action sym7_1 (r7.getD 3 zero) = r7.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_1_4 : action sym7_1 (r7.getD 4 zero) = r7.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_2_0 : action sym7_2 (r7.getD 0 zero) = r7.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_2_1 : action sym7_2 (r7.getD 1 zero) = r7.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_2_2 : action sym7_2 (r7.getD 2 zero) = r7.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_2_3 : action sym7_2 (r7.getD 3 zero) = r7.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_2_4 : action sym7_2 (r7.getD 4 zero) = r7.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_3_0 : action sym7_3 (r7.getD 0 zero) = r7.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_3_1 : action sym7_3 (r7.getD 1 zero) = r7.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_3_2 : action sym7_3 (r7.getD 2 zero) = r7.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_3_3 : action sym7_3 (r7.getD 3 zero) = r7.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot7_3_4 : action sym7_3 (r7.getD 4 zero) = r7.getD 3 zero := by decide +kernel

def x7_0 : Sig := r7.getD 0 zero

def x7_1 : Sig := r7.getD 1 zero

def x7_2 : Sig := r7.getD 2 zero

def x7_3 : Sig := r7.getD 3 zero

def x7_4 : Sig := r7.getD 4 zero

def y7_5 : Sig := neg x7_0

def y7_6 : Sig := bin false y7_5 x7_1

def y7_7 : Sig := bin true y7_5 x7_1

def y7_8 : Sig := bin false y7_5 x7_2

def y7_9 : Sig := bin true y7_5 x7_2

def y7_10 : Sig := bin false y7_5 x7_3

def y7_11 : Sig := bin true y7_5 x7_3

def y7_12 : Sig := bin false y7_5 x7_4

def y7_13 : Sig := bin true y7_5 x7_4

def y7_14 : Sig := bin false x7_0 x7_1

def y7_15 : Sig := bin true x7_0 x7_1

def y7_16 : Sig := bin false x7_0 x7_2

def y7_17 : Sig := bin true x7_0 x7_2

def y7_18 : Sig := bin false x7_0 x7_3

def y7_19 : Sig := bin true x7_0 x7_3

def y7_20 : Sig := bin false x7_0 x7_4

def y7_21 : Sig := bin true x7_0 x7_4

def y7_22 : Sig := bin false x7_1 x7_2

def y7_23 : Sig := bin true x7_1 x7_2

def y7_24 : Sig := bin false x7_1 x7_3

def y7_25 : Sig := bin true x7_1 x7_3

def y7_26 : Sig := bin false x7_1 x7_4

def y7_27 : Sig := bin true x7_1 x7_4

def y7_28 : Sig := bin false x7_2 x7_3

def y7_29 : Sig := bin true x7_2 x7_3

def y7_30 : Sig := bin false x7_2 x7_4

def y7_31 : Sig := bin true x7_2 x7_4

def y7_32 : Sig := bin false x7_3 x7_4

def y7_33 : Sig := bin true x7_3 x7_4

def y7_34 : Sig := neg x7_1

def y7_35 : Sig := bin false y7_34 x7_0

def y7_36 : Sig := bin true y7_34 x7_0

def y7_37 : Sig := bin false y7_34 x7_2

def y7_38 : Sig := bin true y7_34 x7_2

def y7_39 : Sig := bin false y7_34 x7_3

def y7_40 : Sig := bin true y7_34 x7_3

def y7_41 : Sig := bin false y7_34 x7_4

def y7_42 : Sig := bin true y7_34 x7_4

def y7_43 : Sig := neg x7_3

def y7_44 : Sig := bin false y7_43 x7_0

def y7_45 : Sig := bin true y7_43 x7_0

def y7_46 : Sig := bin false y7_43 x7_1

def y7_47 : Sig := bin true y7_43 x7_1

def y7_48 : Sig := bin false y7_43 x7_2

def y7_49 : Sig := bin true y7_43 x7_2

def y7_50 : Sig := bin false y7_43 x7_4

def y7_51 : Sig := bin true y7_43 x7_4

def y7_52 : Sig := neg y7_14

def y7_53 : Sig := neg x7_2

def y7_54 : Sig := neg x7_4

def y7_55 : Sig := bin false y7_14 x7_2

def y7_56 : Sig := bin true y7_14 x7_2

def y7_57 : Sig := bin false y7_14 x7_3

def y7_58 : Sig := bin true y7_14 x7_3

def y7_59 : Sig := bin false y7_14 x7_4

def y7_60 : Sig := bin true y7_14 x7_4

def y7_61 : Sig := neg y7_15

def y7_62 : Sig := bin false y7_15 x7_2

def y7_63 : Sig := bin true y7_15 x7_2

def y7_64 : Sig := bin false y7_15 x7_3

def y7_65 : Sig := bin true y7_15 x7_3

def y7_66 : Sig := bin false y7_15 x7_4

def y7_67 : Sig := bin true y7_15 x7_4

def y7_68 : Sig := neg y7_18

def y7_69 : Sig := bin true y7_18 x7_1

def y7_70 : Sig := bin false y7_18 x7_2

def y7_71 : Sig := bin true y7_18 x7_2

def y7_72 : Sig := bin false y7_18 x7_4

def y7_73 : Sig := bin true y7_18 x7_4

def y7_74 : Sig := neg y7_19

def y7_75 : Sig := bin false y7_19 x7_1

def y7_76 : Sig := bin false y7_19 x7_2

def y7_77 : Sig := bin true y7_19 x7_2

def y7_78 : Sig := bin false y7_19 x7_4

def y7_79 : Sig := bin true y7_19 x7_4

def y7_80 : Sig := neg y7_22

def y7_81 : Sig := bin true y7_22 x7_0

def y7_82 : Sig := bin false y7_22 x7_3

def y7_83 : Sig := bin true y7_22 x7_3

def y7_84 : Sig := bin false y7_22 x7_4

def y7_85 : Sig := bin true y7_22 x7_4

def y7_86 : Sig := neg y7_23

def y7_87 : Sig := bin false y7_23 x7_0

def y7_88 : Sig := bin false y7_23 x7_3

def y7_89 : Sig := bin true y7_23 x7_3

def y7_90 : Sig := bin false y7_23 x7_4

def y7_91 : Sig := bin true y7_23 x7_4

def y7_92 : Sig := neg y7_24

def y7_93 : Sig := bin true y7_24 x7_0

def y7_94 : Sig := bin true y7_24 x7_2

def y7_95 : Sig := bin false y7_24 x7_4

def y7_96 : Sig := bin true y7_24 x7_4

def y7_97 : Sig := neg y7_25

def y7_98 : Sig := bin false y7_25 x7_0

def y7_99 : Sig := bin false y7_25 x7_2

def y7_100 : Sig := bin false y7_25 x7_4

def y7_101 : Sig := bin true y7_25 x7_4

def y7_102 : Sig := neg y7_32

def y7_103 : Sig := bin true y7_32 x7_0

def y7_104 : Sig := bin true y7_32 x7_1

def y7_105 : Sig := bin false y7_32 x7_2

def y7_106 : Sig := bin true y7_32 x7_2

def y7_107 : Sig := neg y7_33

def y7_108 : Sig := bin false y7_33 x7_0

def y7_109 : Sig := bin false y7_33 x7_1

def y7_110 : Sig := bin false y7_33 x7_2

def y7_111 : Sig := bin true y7_33 x7_2

def s7_1u0 : List Sig := [neg (r7.getD 0 zero),r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1u0u : List (List Sig) := []

lemma s7_1u0ux (v : List Sig) (h : (!s7_1u0u.contains v) = false) : Impossible 7 0 v := by
  simp [s7_1u0u] at h

def s7_1u0b0 : List Sig := [y7_6,x7_1,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b0x : Impossible 7 0 s7_1u0b0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b1 : List Sig := [y7_6,y7_5,x7_1,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b1x : Impossible 7 0 s7_1u0b1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b2 : List Sig := [y7_7,x7_1,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b2x : Impossible 7 0 s7_1u0b2 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b3 : List Sig := [y7_7,y7_5,x7_1,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b3x : Impossible 7 0 s7_1u0b3 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b4 : List Sig := [y7_8,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b4x : Impossible 7 0 s7_1u0b4 := rotate_impossible sym7_2 (z := s7_1u0b0) (by simp only [s7_1u0b4,x7_0,x7_1,x7_2,x7_3,x7_4,y7_5,y7_8,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b0x

def s7_1u0b5 : List Sig := [y7_8,y7_5,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b5x : Impossible 7 0 s7_1u0b5 := rotate_impossible sym7_2 (z := s7_1u0b1) (by simp only [s7_1u0b5,x7_0,x7_1,x7_2,x7_3,x7_4,y7_5,y7_8,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b1x

def s7_1u0b6 : List Sig := [y7_9,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b6x : Impossible 7 0 s7_1u0b6 := rotate_impossible sym7_2 (z := s7_1u0b2) (by simp only [s7_1u0b6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_5,y7_9,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b2x

def s7_1u0b7 : List Sig := [y7_9,y7_5,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b7x : Impossible 7 0 s7_1u0b7 := rotate_impossible sym7_2 (z := s7_1u0b3) (by simp only [s7_1u0b7,x7_0,x7_1,x7_2,x7_3,x7_4,y7_5,y7_9,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b3x

def s7_1u0b8 : List Sig := [y7_10,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b8x : Impossible 7 0 s7_1u0b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b9 : List Sig := [y7_10,y7_5,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b9x : Impossible 7 0 s7_1u0b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b10 : List Sig := [y7_11,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b10x : Impossible 7 0 s7_1u0b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b11 : List Sig := [y7_11,y7_5,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b11x : Impossible 7 0 s7_1u0b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b12 : List Sig := [y7_12,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b12x : Impossible 7 0 s7_1u0b12 := rotate_impossible sym7_1 (z := s7_1u0b8) (by simp only [s7_1u0b12,x7_0,x7_1,x7_2,x7_3,x7_4,y7_12,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b8x

def s7_1u0b13 : List Sig := [y7_12,y7_5,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b13x : Impossible 7 0 s7_1u0b13 := rotate_impossible sym7_1 (z := s7_1u0b9) (by simp only [s7_1u0b13,x7_0,x7_1,x7_2,x7_3,x7_4,y7_12,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b9x

def s7_1u0b14 : List Sig := [y7_13,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b14x : Impossible 7 0 s7_1u0b14 := rotate_impossible sym7_1 (z := s7_1u0b10) (by simp only [s7_1u0b14,x7_0,x7_1,x7_2,x7_3,x7_4,y7_13,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b10x

def s7_1u0b15 : List Sig := [y7_13,y7_5,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b15x : Impossible 7 0 s7_1u0b15 := rotate_impossible sym7_1 (z := s7_1u0b11) (by simp only [s7_1u0b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_13,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b11x

def s7_1u0b16 : List Sig := [y7_14,x7_0,x7_1,y7_5,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b16x : Impossible 7 0 s7_1u0b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b17 : List Sig := [y7_15,x7_0,x7_1,y7_5,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b17x : Impossible 7 0 s7_1u0b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b18 : List Sig := [y7_16,x7_0,x7_2,y7_5,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b18x : Impossible 7 0 s7_1u0b18 := rotate_impossible sym7_2 (z := s7_1u0b16) (by simp only [s7_1u0b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b16x

def s7_1u0b19 : List Sig := [y7_17,x7_0,x7_2,y7_5,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b19x : Impossible 7 0 s7_1u0b19 := rotate_impossible sym7_2 (z := s7_1u0b17) (by simp only [s7_1u0b19,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b17x

def s7_1u0b20 : List Sig := [y7_18,x7_0,x7_3,y7_5,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b20x : Impossible 7 0 s7_1u0b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b21 : List Sig := [y7_19,x7_0,x7_3,y7_5,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b21x : Impossible 7 0 s7_1u0b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b22 : List Sig := [y7_20,x7_0,x7_4,y7_5,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b22x : Impossible 7 0 s7_1u0b22 := rotate_impossible sym7_1 (z := s7_1u0b20) (by simp only [s7_1u0b22,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b20x

def s7_1u0b23 : List Sig := [y7_21,x7_0,x7_4,y7_5,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b23x : Impossible 7 0 s7_1u0b23 := rotate_impossible sym7_1 (z := s7_1u0b21) (by simp only [s7_1u0b23,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b21x

def s7_1u0b24 : List Sig := [y7_22,x7_1,x7_2,y7_5,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b24x : Impossible 7 0 s7_1u0b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b25 : List Sig := [y7_23,x7_1,x7_2,y7_5,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b25x : Impossible 7 0 s7_1u0b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b26 : List Sig := [y7_24,x7_1,x7_3,y7_5,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b26x : Impossible 7 0 s7_1u0b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b27 : List Sig := [y7_25,x7_1,x7_3,y7_5,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b27x : Impossible 7 0 s7_1u0b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b28 : List Sig := [y7_26,x7_1,x7_4,y7_5,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b28x : Impossible 7 0 s7_1u0b28 := rotate_impossible sym7_1 (z := s7_1u0b26) (by simp only [s7_1u0b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_26,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b26x

def s7_1u0b29 : List Sig := [y7_27,x7_1,x7_4,y7_5,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b29x : Impossible 7 0 s7_1u0b29 := rotate_impossible sym7_1 (z := s7_1u0b27) (by simp only [s7_1u0b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_27,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u0b27x

def s7_1u0b30 : List Sig := [y7_28,x7_2,x7_3,y7_5,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b30x : Impossible 7 0 s7_1u0b30 := rotate_impossible sym7_2 (z := s7_1u0b26) (by simp only [s7_1u0b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_28,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b26x

def s7_1u0b31 : List Sig := [y7_29,x7_2,x7_3,y7_5,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b31x : Impossible 7 0 s7_1u0b31 := rotate_impossible sym7_2 (z := s7_1u0b27) (by simp only [s7_1u0b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_29,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u0b27x

def s7_1u0b32 : List Sig := [y7_30,x7_2,x7_4,y7_5,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b32x : Impossible 7 0 s7_1u0b32 := rotate_impossible sym7_3 (z := s7_1u0b26) (by simp only [s7_1u0b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1u0b26x

def s7_1u0b33 : List Sig := [y7_31,x7_2,x7_4,y7_5,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b33x : Impossible 7 0 s7_1u0b33 := rotate_impossible sym7_3 (z := s7_1u0b27) (by simp only [s7_1u0b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_31,y7_5,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1u0b27x

def s7_1u0b34 : List Sig := [y7_32,x7_3,x7_4,y7_5,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b34x : Impossible 7 0 s7_1u0b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b35 : List Sig := [y7_33,x7_3,x7_4,y7_5,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0b35x : Impossible 7 0 s7_1u0b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u0b : List (List Sig) := [s7_1u0b0,s7_1u0b1,s7_1u0b2,s7_1u0b3,s7_1u0b4,s7_1u0b5,s7_1u0b6,s7_1u0b7,s7_1u0b8,s7_1u0b9,s7_1u0b10,s7_1u0b11,s7_1u0b12,s7_1u0b13,s7_1u0b14,s7_1u0b15,s7_1u0b16,s7_1u0b17,s7_1u0b18,s7_1u0b19,s7_1u0b20,s7_1u0b21,s7_1u0b22,s7_1u0b23,s7_1u0b24,s7_1u0b25,s7_1u0b26,s7_1u0b27,s7_1u0b28,s7_1u0b29,s7_1u0b30,s7_1u0b31,s7_1u0b32,s7_1u0b33,s7_1u0b34,s7_1u0b35]

lemma s7_1u0bx (v : List Sig) (h : (!s7_1u0b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1u0b := by simpa using h
  simp only [s7_1u0b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1u0b0x
  · exact s7_1u0b1x
  · exact s7_1u0b2x
  · exact s7_1u0b3x
  · exact s7_1u0b4x
  · exact s7_1u0b5x
  · exact s7_1u0b6x
  · exact s7_1u0b7x
  · exact s7_1u0b8x
  · exact s7_1u0b9x
  · exact s7_1u0b10x
  · exact s7_1u0b11x
  · exact s7_1u0b12x
  · exact s7_1u0b13x
  · exact s7_1u0b14x
  · exact s7_1u0b15x
  · exact s7_1u0b16x
  · exact s7_1u0b17x
  · exact s7_1u0b18x
  · exact s7_1u0b19x
  · exact s7_1u0b20x
  · exact s7_1u0b21x
  · exact s7_1u0b22x
  · exact s7_1u0b23x
  · exact s7_1u0b24x
  · exact s7_1u0b25x
  · exact s7_1u0b26x
  · exact s7_1u0b27x
  · exact s7_1u0b28x
  · exact s7_1u0b29x
  · exact s7_1u0b30x
  · exact s7_1u0b31x
  · exact s7_1u0b32x
  · exact s7_1u0b33x
  · exact s7_1u0b34x
  · exact s7_1u0b35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u0x : Impossible 8 0 s7_1u0 := exclude_step (u := fun v => !s7_1u0u.contains v) (b := fun v => !s7_1u0b.contains v) (by decide +kernel) s7_1u0ux s7_1u0bx (by decide +kernel)

def s7_1u1 : List Sig := [neg (r7.getD 1 zero),r7.getD 1 zero,r7.getD 0 zero,r7.getD 2 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1u1u : List (List Sig) := []

lemma s7_1u1ux (v : List Sig) (h : (!s7_1u1u.contains v) = false) : Impossible 7 0 v := by
  simp [s7_1u1u] at h

def s7_1u1b0 : List Sig := [y7_35,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b0x : Impossible 7 0 s7_1u1b0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b1 : List Sig := [y7_35,y7_34,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b1x : Impossible 7 0 s7_1u1b1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b2 : List Sig := [y7_36,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b2x : Impossible 7 0 s7_1u1b2 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b3 : List Sig := [y7_36,y7_34,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b3x : Impossible 7 0 s7_1u1b3 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b4 : List Sig := [y7_37,x7_2,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b4x : Impossible 7 0 s7_1u1b4 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b5 : List Sig := [y7_37,y7_34,x7_2,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b5x : Impossible 7 0 s7_1u1b5 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b6 : List Sig := [y7_38,x7_2,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b6x : Impossible 7 0 s7_1u1b6 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b7 : List Sig := [y7_38,y7_34,x7_2,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b7x : Impossible 7 0 s7_1u1b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b8 : List Sig := [y7_39,x7_3,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b8x : Impossible 7 0 s7_1u1b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b9 : List Sig := [y7_39,y7_34,x7_3,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b9x : Impossible 7 0 s7_1u1b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b10 : List Sig := [y7_40,x7_3,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b10x : Impossible 7 0 s7_1u1b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b11 : List Sig := [y7_40,y7_34,x7_3,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b11x : Impossible 7 0 s7_1u1b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b12 : List Sig := [y7_41,x7_4,x7_1,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b12x : Impossible 7 0 s7_1u1b12 := rotate_impossible sym7_1 (z := s7_1u1b8) (by simp only [s7_1u1b12,x7_0,x7_1,x7_2,x7_3,x7_4,y7_34,y7_41,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b8x

def s7_1u1b13 : List Sig := [y7_41,y7_34,x7_4,x7_1,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b13x : Impossible 7 0 s7_1u1b13 := rotate_impossible sym7_1 (z := s7_1u1b9) (by simp only [s7_1u1b13,x7_0,x7_1,x7_2,x7_3,x7_4,y7_34,y7_41,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b9x

def s7_1u1b14 : List Sig := [y7_42,x7_4,x7_1,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b14x : Impossible 7 0 s7_1u1b14 := rotate_impossible sym7_1 (z := s7_1u1b10) (by simp only [s7_1u1b14,x7_0,x7_1,x7_2,x7_3,x7_4,y7_34,y7_42,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b10x

def s7_1u1b15 : List Sig := [y7_42,y7_34,x7_4,x7_1,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b15x : Impossible 7 0 s7_1u1b15 := rotate_impossible sym7_1 (z := s7_1u1b11) (by simp only [s7_1u1b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_34,y7_42,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b11x

def s7_1u1b16 : List Sig := [y7_14,x7_1,x7_0,y7_34,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b16x : Impossible 7 0 s7_1u1b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b17 : List Sig := [y7_15,x7_1,x7_0,y7_34,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b17x : Impossible 7 0 s7_1u1b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b18 : List Sig := [y7_22,x7_1,x7_2,y7_34,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b18x : Impossible 7 0 s7_1u1b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b19 : List Sig := [y7_23,x7_1,x7_2,y7_34,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b19x : Impossible 7 0 s7_1u1b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b20 : List Sig := [y7_24,x7_1,x7_3,y7_34,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b20x : Impossible 7 0 s7_1u1b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b21 : List Sig := [y7_25,x7_1,x7_3,y7_34,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b21x : Impossible 7 0 s7_1u1b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b22 : List Sig := [y7_26,x7_1,x7_4,y7_34,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b22x : Impossible 7 0 s7_1u1b22 := rotate_impossible sym7_1 (z := s7_1u1b20) (by simp only [s7_1u1b22,x7_0,x7_1,x7_2,x7_3,x7_4,y7_26,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b20x

def s7_1u1b23 : List Sig := [y7_27,x7_1,x7_4,y7_34,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b23x : Impossible 7 0 s7_1u1b23 := rotate_impossible sym7_1 (z := s7_1u1b21) (by simp only [s7_1u1b23,x7_0,x7_1,x7_2,x7_3,x7_4,y7_27,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b21x

def s7_1u1b24 : List Sig := [y7_16,x7_0,x7_2,y7_34,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b24x : Impossible 7 0 s7_1u1b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b25 : List Sig := [y7_17,x7_0,x7_2,y7_34,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b25x : Impossible 7 0 s7_1u1b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b26 : List Sig := [y7_18,x7_0,x7_3,y7_34,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b26x : Impossible 7 0 s7_1u1b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b27 : List Sig := [y7_19,x7_0,x7_3,y7_34,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b27x : Impossible 7 0 s7_1u1b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b28 : List Sig := [y7_20,x7_0,x7_4,y7_34,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b28x : Impossible 7 0 s7_1u1b28 := rotate_impossible sym7_1 (z := s7_1u1b26) (by simp only [s7_1u1b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b26x

def s7_1u1b29 : List Sig := [y7_21,x7_0,x7_4,y7_34,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b29x : Impossible 7 0 s7_1u1b29 := rotate_impossible sym7_1 (z := s7_1u1b27) (by simp only [s7_1u1b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b27x

def s7_1u1b30 : List Sig := [y7_28,x7_2,x7_3,y7_34,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b30x : Impossible 7 0 s7_1u1b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b31 : List Sig := [y7_29,x7_2,x7_3,y7_34,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b31x : Impossible 7 0 s7_1u1b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b32 : List Sig := [y7_30,x7_2,x7_4,y7_34,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b32x : Impossible 7 0 s7_1u1b32 := rotate_impossible sym7_1 (z := s7_1u1b30) (by simp only [s7_1u1b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b30x

def s7_1u1b33 : List Sig := [y7_31,x7_2,x7_4,y7_34,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b33x : Impossible 7 0 s7_1u1b33 := rotate_impossible sym7_1 (z := s7_1u1b31) (by simp only [s7_1u1b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_31,y7_34,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u1b31x

def s7_1u1b34 : List Sig := [y7_32,x7_3,x7_4,y7_34,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b34x : Impossible 7 0 s7_1u1b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b35 : List Sig := [y7_33,x7_3,x7_4,y7_34,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1b35x : Impossible 7 0 s7_1u1b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u1b : List (List Sig) := [s7_1u1b0,s7_1u1b1,s7_1u1b2,s7_1u1b3,s7_1u1b4,s7_1u1b5,s7_1u1b6,s7_1u1b7,s7_1u1b8,s7_1u1b9,s7_1u1b10,s7_1u1b11,s7_1u1b12,s7_1u1b13,s7_1u1b14,s7_1u1b15,s7_1u1b16,s7_1u1b17,s7_1u1b18,s7_1u1b19,s7_1u1b20,s7_1u1b21,s7_1u1b22,s7_1u1b23,s7_1u1b24,s7_1u1b25,s7_1u1b26,s7_1u1b27,s7_1u1b28,s7_1u1b29,s7_1u1b30,s7_1u1b31,s7_1u1b32,s7_1u1b33,s7_1u1b34,s7_1u1b35]

lemma s7_1u1bx (v : List Sig) (h : (!s7_1u1b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1u1b := by simpa using h
  simp only [s7_1u1b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1u1b0x
  · exact s7_1u1b1x
  · exact s7_1u1b2x
  · exact s7_1u1b3x
  · exact s7_1u1b4x
  · exact s7_1u1b5x
  · exact s7_1u1b6x
  · exact s7_1u1b7x
  · exact s7_1u1b8x
  · exact s7_1u1b9x
  · exact s7_1u1b10x
  · exact s7_1u1b11x
  · exact s7_1u1b12x
  · exact s7_1u1b13x
  · exact s7_1u1b14x
  · exact s7_1u1b15x
  · exact s7_1u1b16x
  · exact s7_1u1b17x
  · exact s7_1u1b18x
  · exact s7_1u1b19x
  · exact s7_1u1b20x
  · exact s7_1u1b21x
  · exact s7_1u1b22x
  · exact s7_1u1b23x
  · exact s7_1u1b24x
  · exact s7_1u1b25x
  · exact s7_1u1b26x
  · exact s7_1u1b27x
  · exact s7_1u1b28x
  · exact s7_1u1b29x
  · exact s7_1u1b30x
  · exact s7_1u1b31x
  · exact s7_1u1b32x
  · exact s7_1u1b33x
  · exact s7_1u1b34x
  · exact s7_1u1b35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u1x : Impossible 8 0 s7_1u1 := exclude_step (u := fun v => !s7_1u1u.contains v) (b := fun v => !s7_1u1b.contains v) (by decide +kernel) s7_1u1ux s7_1u1bx (by decide +kernel)

def s7_1u2 : List Sig := [neg (r7.getD 2 zero),r7.getD 2 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 3 zero,r7.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u2x : Impossible 8 0 s7_1u2 := rotate_impossible sym7_2 (z := s7_1u1) (by simp only [s7_1u2,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1x

def s7_1u3 : List Sig := [neg (r7.getD 3 zero),r7.getD 3 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 4 zero]

def s7_1u3u : List (List Sig) := []

lemma s7_1u3ux (v : List Sig) (h : (!s7_1u3u.contains v) = false) : Impossible 7 0 v := by
  simp [s7_1u3u] at h

def s7_1u3b0 : List Sig := [y7_44,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b0x : Impossible 7 0 s7_1u3b0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b1 : List Sig := [y7_44,y7_43,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b1x : Impossible 7 0 s7_1u3b1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b2 : List Sig := [y7_45,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b2x : Impossible 7 0 s7_1u3b2 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b3 : List Sig := [y7_45,y7_43,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b3x : Impossible 7 0 s7_1u3b3 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b4 : List Sig := [y7_46,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b4x : Impossible 7 0 s7_1u3b4 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b5 : List Sig := [y7_46,y7_43,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b5x : Impossible 7 0 s7_1u3b5 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b6 : List Sig := [y7_47,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b6x : Impossible 7 0 s7_1u3b6 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b7 : List Sig := [y7_47,y7_43,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b7x : Impossible 7 0 s7_1u3b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b8 : List Sig := [y7_48,x7_2,x7_3,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b8x : Impossible 7 0 s7_1u3b8 := rotate_impossible sym7_2 (z := s7_1u3b4) (by simp only [s7_1u3b8,x7_0,x7_1,x7_2,x7_3,x7_4,y7_43,y7_48,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b4x

def s7_1u3b9 : List Sig := [y7_48,y7_43,x7_2,x7_3,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b9x : Impossible 7 0 s7_1u3b9 := rotate_impossible sym7_2 (z := s7_1u3b5) (by simp only [s7_1u3b9,x7_0,x7_1,x7_2,x7_3,x7_4,y7_43,y7_48,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b5x

def s7_1u3b10 : List Sig := [y7_49,x7_2,x7_3,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b10x : Impossible 7 0 s7_1u3b10 := rotate_impossible sym7_2 (z := s7_1u3b6) (by simp only [s7_1u3b10,x7_0,x7_1,x7_2,x7_3,x7_4,y7_43,y7_49,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b6x

def s7_1u3b11 : List Sig := [y7_49,y7_43,x7_2,x7_3,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b11x : Impossible 7 0 s7_1u3b11 := rotate_impossible sym7_2 (z := s7_1u3b7) (by simp only [s7_1u3b11,x7_0,x7_1,x7_2,x7_3,x7_4,y7_43,y7_49,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b7x

def s7_1u3b12 : List Sig := [y7_50,x7_4,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b12x : Impossible 7 0 s7_1u3b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b13 : List Sig := [y7_50,y7_43,x7_4,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b13x : Impossible 7 0 s7_1u3b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b14 : List Sig := [y7_51,x7_4,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b14x : Impossible 7 0 s7_1u3b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b15 : List Sig := [y7_51,y7_43,x7_4,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b15x : Impossible 7 0 s7_1u3b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b16 : List Sig := [y7_18,x7_3,x7_0,y7_43,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b16x : Impossible 7 0 s7_1u3b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b17 : List Sig := [y7_19,x7_3,x7_0,y7_43,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b17x : Impossible 7 0 s7_1u3b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b18 : List Sig := [y7_24,x7_3,x7_1,y7_43,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b18x : Impossible 7 0 s7_1u3b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b19 : List Sig := [y7_25,x7_3,x7_1,y7_43,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b19x : Impossible 7 0 s7_1u3b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b20 : List Sig := [y7_28,x7_3,x7_2,y7_43,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b20x : Impossible 7 0 s7_1u3b20 := rotate_impossible sym7_2 (z := s7_1u3b18) (by simp only [s7_1u3b20,x7_0,x7_1,x7_2,x7_3,x7_4,y7_28,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b18x

def s7_1u3b21 : List Sig := [y7_29,x7_3,x7_2,y7_43,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b21x : Impossible 7 0 s7_1u3b21 := rotate_impossible sym7_2 (z := s7_1u3b19) (by simp only [s7_1u3b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_29,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b19x

def s7_1u3b22 : List Sig := [y7_32,x7_3,x7_4,y7_43,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b22x : Impossible 7 0 s7_1u3b22 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b23 : List Sig := [y7_33,x7_3,x7_4,y7_43,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b23x : Impossible 7 0 s7_1u3b23 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b24 : List Sig := [y7_14,x7_0,x7_1,y7_43,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b24x : Impossible 7 0 s7_1u3b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b25 : List Sig := [y7_15,x7_0,x7_1,y7_43,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b25x : Impossible 7 0 s7_1u3b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b26 : List Sig := [y7_16,x7_0,x7_2,y7_43,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b26x : Impossible 7 0 s7_1u3b26 := rotate_impossible sym7_2 (z := s7_1u3b24) (by simp only [s7_1u3b26,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b24x

def s7_1u3b27 : List Sig := [y7_17,x7_0,x7_2,y7_43,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b27x : Impossible 7 0 s7_1u3b27 := rotate_impossible sym7_2 (z := s7_1u3b25) (by simp only [s7_1u3b27,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b25x

def s7_1u3b28 : List Sig := [y7_20,x7_0,x7_4,y7_43,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b28x : Impossible 7 0 s7_1u3b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b29 : List Sig := [y7_21,x7_0,x7_4,y7_43,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b29x : Impossible 7 0 s7_1u3b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b30 : List Sig := [y7_22,x7_1,x7_2,y7_43,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b30x : Impossible 7 0 s7_1u3b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b31 : List Sig := [y7_23,x7_1,x7_2,y7_43,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b31x : Impossible 7 0 s7_1u3b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b32 : List Sig := [y7_26,x7_1,x7_4,y7_43,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b32x : Impossible 7 0 s7_1u3b32 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b33 : List Sig := [y7_27,x7_1,x7_4,y7_43,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b33x : Impossible 7 0 s7_1u3b33 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1u3b34 : List Sig := [y7_30,x7_2,x7_4,y7_43,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b34x : Impossible 7 0 s7_1u3b34 := rotate_impossible sym7_2 (z := s7_1u3b32) (by simp only [s7_1u3b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b32x

def s7_1u3b35 : List Sig := [y7_31,x7_2,x7_4,y7_43,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3b35x : Impossible 7 0 s7_1u3b35 := rotate_impossible sym7_2 (z := s7_1u3b33) (by simp only [s7_1u3b35,x7_0,x7_1,x7_2,x7_3,x7_4,y7_31,y7_43,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u3b33x

def s7_1u3b : List (List Sig) := [s7_1u3b0,s7_1u3b1,s7_1u3b2,s7_1u3b3,s7_1u3b4,s7_1u3b5,s7_1u3b6,s7_1u3b7,s7_1u3b8,s7_1u3b9,s7_1u3b10,s7_1u3b11,s7_1u3b12,s7_1u3b13,s7_1u3b14,s7_1u3b15,s7_1u3b16,s7_1u3b17,s7_1u3b18,s7_1u3b19,s7_1u3b20,s7_1u3b21,s7_1u3b22,s7_1u3b23,s7_1u3b24,s7_1u3b25,s7_1u3b26,s7_1u3b27,s7_1u3b28,s7_1u3b29,s7_1u3b30,s7_1u3b31,s7_1u3b32,s7_1u3b33,s7_1u3b34,s7_1u3b35]

lemma s7_1u3bx (v : List Sig) (h : (!s7_1u3b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1u3b := by simpa using h
  simp only [s7_1u3b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1u3b0x
  · exact s7_1u3b1x
  · exact s7_1u3b2x
  · exact s7_1u3b3x
  · exact s7_1u3b4x
  · exact s7_1u3b5x
  · exact s7_1u3b6x
  · exact s7_1u3b7x
  · exact s7_1u3b8x
  · exact s7_1u3b9x
  · exact s7_1u3b10x
  · exact s7_1u3b11x
  · exact s7_1u3b12x
  · exact s7_1u3b13x
  · exact s7_1u3b14x
  · exact s7_1u3b15x
  · exact s7_1u3b16x
  · exact s7_1u3b17x
  · exact s7_1u3b18x
  · exact s7_1u3b19x
  · exact s7_1u3b20x
  · exact s7_1u3b21x
  · exact s7_1u3b22x
  · exact s7_1u3b23x
  · exact s7_1u3b24x
  · exact s7_1u3b25x
  · exact s7_1u3b26x
  · exact s7_1u3b27x
  · exact s7_1u3b28x
  · exact s7_1u3b29x
  · exact s7_1u3b30x
  · exact s7_1u3b31x
  · exact s7_1u3b32x
  · exact s7_1u3b33x
  · exact s7_1u3b34x
  · exact s7_1u3b35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u3x : Impossible 8 0 s7_1u3 := exclude_step (u := fun v => !s7_1u3u.contains v) (b := fun v => !s7_1u3b.contains v) (by decide +kernel) s7_1u3ux s7_1u3bx (by decide +kernel)

def s7_1u4 : List Sig := [neg (r7.getD 4 zero),r7.getD 4 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1u4x : Impossible 8 0 s7_1u4 := rotate_impossible sym7_1 (z := s7_1u3) (by simp only [s7_1u4,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3x

def s7_1u : List (List Sig) := [s7_1u0,s7_1u1,s7_1u2,s7_1u3,s7_1u4]

lemma s7_1ux (v : List Sig) (h : (!s7_1u.contains v) = false) : Impossible 8 0 v := by
  have hm : v ∈ s7_1u := by simpa using h
  simp only [s7_1u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact s7_1u0x
  · exact s7_1u1x
  · exact s7_1u2x
  · exact s7_1u3x
  · exact s7_1u4x

def s7_1b0 : List Sig := [bin false (r7.getD 0 zero) (r7.getD 1 zero),r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1b0u0 : List Sig := [y7_52,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u0x : Impossible 7 0 s7_1b0u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0u1 : List Sig := [y7_52,y7_14,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u1x : Impossible 7 0 s7_1b0u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0u2 : List Sig := [y7_5,x7_0,y7_14,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u2x : Impossible 7 0 s7_1b0u2 := impPerm (z := s7_1u0b16) (by decide +kernel) s7_1u0b16x

def s7_1b0u3 : List Sig := [y7_34,x7_1,y7_14,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u3x : Impossible 7 0 s7_1b0u3 := impPerm (z := s7_1u1b16) (by decide +kernel) s7_1u1b16x

def s7_1b0u4 : List Sig := [y7_53,x7_2,y7_14,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u4x : Impossible 7 0 s7_1b0u4 := rotate_impossible sym7_2 (z := s7_1u1b24) (by simp only [s7_1b0u4,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b24x

def s7_1b0u5 : List Sig := [y7_43,x7_3,y7_14,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u5x : Impossible 7 0 s7_1b0u5 := impPerm (z := s7_1u3b24) (by decide +kernel) s7_1u3b24x

def s7_1b0u6 : List Sig := [y7_54,x7_4,y7_14,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0u6x : Impossible 7 0 s7_1b0u6 := rotate_impossible sym7_1 (z := s7_1u3b24) (by simp only [s7_1b0u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b24x

def s7_1b0u : List (List Sig) := [s7_1b0u0,s7_1b0u1,s7_1b0u2,s7_1b0u3,s7_1b0u4,s7_1b0u5,s7_1b0u6]

lemma s7_1b0ux (v : List Sig) (h : (!s7_1b0u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b0u := by simpa using h
  simp only [s7_1b0u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b0u0x
  · exact s7_1b0u1x
  · exact s7_1b0u2x
  · exact s7_1b0u3x
  · exact s7_1b0u4x
  · exact s7_1b0u5x
  · exact s7_1b0u6x

def s7_1b0b7 : List Sig := [y7_55,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b7x : Impossible 7 1 s7_1b0b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b8 : List Sig := [y7_55,y7_14,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b8x : Impossible 7 1 s7_1b0b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b9 : List Sig := [y7_56,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b9x : Impossible 7 1 s7_1b0b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b10 : List Sig := [y7_56,y7_14,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b10x : Impossible 7 1 s7_1b0b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b11 : List Sig := [y7_56,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b11x : Impossible 7 1 s7_1b0b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b12 : List Sig := [y7_56,y7_14,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b12x : Impossible 7 1 s7_1b0b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b13 : List Sig := [y7_57,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b13x : Impossible 7 1 s7_1b0b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b14 : List Sig := [y7_57,y7_14,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b14x : Impossible 7 1 s7_1b0b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b15 : List Sig := [y7_58,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b15x : Impossible 7 1 s7_1b0b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b16 : List Sig := [y7_58,y7_14,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b16x : Impossible 7 1 s7_1b0b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b17 : List Sig := [y7_58,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b17x : Impossible 7 1 s7_1b0b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b18 : List Sig := [y7_58,y7_14,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b18x : Impossible 7 1 s7_1b0b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b19 : List Sig := [y7_59,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b19x : Impossible 7 1 s7_1b0b19 := rotate_impossible sym7_1 (z := s7_1b0b13) (by simp only [s7_1b0b19,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_59,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b13x

def s7_1b0b20 : List Sig := [y7_59,y7_14,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b20x : Impossible 7 1 s7_1b0b20 := rotate_impossible sym7_1 (z := s7_1b0b14) (by simp only [s7_1b0b20,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_59,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b14x

def s7_1b0b21 : List Sig := [y7_60,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b21x : Impossible 7 1 s7_1b0b21 := rotate_impossible sym7_1 (z := s7_1b0b15) (by simp only [s7_1b0b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_60,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b15x

def s7_1b0b22 : List Sig := [y7_60,y7_14,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b22x : Impossible 7 1 s7_1b0b22 := rotate_impossible sym7_1 (z := s7_1b0b16) (by simp only [s7_1b0b22,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_60,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b16x

def s7_1b0b23 : List Sig := [y7_60,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b23x : Impossible 7 1 s7_1b0b23 := rotate_impossible sym7_1 (z := s7_1b0b17) (by simp only [s7_1b0b23,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_60,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b17x

def s7_1b0b24 : List Sig := [y7_60,y7_14,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b24x : Impossible 7 1 s7_1b0b24 := rotate_impossible sym7_1 (z := s7_1b0b18) (by simp only [s7_1b0b24,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_60,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b18x

def s7_1b0b25 : List Sig := [y7_15,x7_0,y7_14,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b25x : Impossible 7 1 s7_1b0b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b26 : List Sig := [y7_15,x7_1,y7_14,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b26x : Impossible 7 1 s7_1b0b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b27 : List Sig := [y7_15,x7_0,x7_1,y7_14,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b27x : Impossible 7 1 s7_1b0b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b28 : List Sig := [y7_16,x7_0,x7_2,y7_14,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b28x : Impossible 7 1 s7_1b0b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b29 : List Sig := [y7_17,x7_0,x7_2,y7_14,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b29x : Impossible 7 1 s7_1b0b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b30 : List Sig := [y7_18,x7_0,x7_3,y7_14,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b30x : Impossible 7 1 s7_1b0b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b31 : List Sig := [y7_19,x7_0,x7_3,y7_14,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b31x : Impossible 7 1 s7_1b0b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b32 : List Sig := [y7_20,x7_0,x7_4,y7_14,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b32x : Impossible 7 1 s7_1b0b32 := rotate_impossible sym7_1 (z := s7_1b0b30) (by simp only [s7_1b0b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_20,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b30x

def s7_1b0b33 : List Sig := [y7_21,x7_0,x7_4,y7_14,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b33x : Impossible 7 1 s7_1b0b33 := rotate_impossible sym7_1 (z := s7_1b0b31) (by simp only [s7_1b0b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_21,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b31x

def s7_1b0b34 : List Sig := [y7_22,x7_1,x7_2,y7_14,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b34x : Impossible 7 1 s7_1b0b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b35 : List Sig := [y7_23,x7_1,x7_2,y7_14,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b35x : Impossible 7 1 s7_1b0b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b36 : List Sig := [y7_24,x7_1,x7_3,y7_14,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b36x : Impossible 7 1 s7_1b0b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b37 : List Sig := [y7_25,x7_1,x7_3,y7_14,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b37x : Impossible 7 1 s7_1b0b37 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b38 : List Sig := [y7_26,x7_1,x7_4,y7_14,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b38x : Impossible 7 1 s7_1b0b38 := rotate_impossible sym7_1 (z := s7_1b0b36) (by simp only [s7_1b0b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_26,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b36x

def s7_1b0b39 : List Sig := [y7_27,x7_1,x7_4,y7_14,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b39x : Impossible 7 1 s7_1b0b39 := rotate_impossible sym7_1 (z := s7_1b0b37) (by simp only [s7_1b0b39,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_27,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b37x

def s7_1b0b40 : List Sig := [y7_28,x7_2,x7_3,y7_14,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b40x : Impossible 7 1 s7_1b0b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b41 : List Sig := [y7_29,x7_2,x7_3,y7_14,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b41x : Impossible 7 1 s7_1b0b41 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b42 : List Sig := [y7_30,x7_2,x7_4,y7_14,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b42x : Impossible 7 1 s7_1b0b42 := rotate_impossible sym7_1 (z := s7_1b0b40) (by simp only [s7_1b0b42,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b40x

def s7_1b0b43 : List Sig := [y7_31,x7_2,x7_4,y7_14,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b43x : Impossible 7 1 s7_1b0b43 := rotate_impossible sym7_1 (z := s7_1b0b41) (by simp only [s7_1b0b43,x7_0,x7_1,x7_2,x7_3,x7_4,y7_14,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b0b41x

def s7_1b0b44 : List Sig := [y7_32,x7_3,x7_4,y7_14,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b44x : Impossible 7 1 s7_1b0b44 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b45 : List Sig := [y7_33,x7_3,x7_4,y7_14,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0b45x : Impossible 7 1 s7_1b0b45 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b0b : List (List Sig) := [s7_1b0b7,s7_1b0b8,s7_1b0b9,s7_1b0b10,s7_1b0b11,s7_1b0b12,s7_1b0b13,s7_1b0b14,s7_1b0b15,s7_1b0b16,s7_1b0b17,s7_1b0b18,s7_1b0b19,s7_1b0b20,s7_1b0b21,s7_1b0b22,s7_1b0b23,s7_1b0b24,s7_1b0b25,s7_1b0b26,s7_1b0b27,s7_1b0b28,s7_1b0b29,s7_1b0b30,s7_1b0b31,s7_1b0b32,s7_1b0b33,s7_1b0b34,s7_1b0b35,s7_1b0b36,s7_1b0b37,s7_1b0b38,s7_1b0b39,s7_1b0b40,s7_1b0b41,s7_1b0b42,s7_1b0b43,s7_1b0b44,s7_1b0b45]

lemma s7_1b0bx (v : List Sig) (h : (!s7_1b0b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b0b := by simpa using h
  simp only [s7_1b0b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b0b7x
  · exact s7_1b0b8x
  · exact s7_1b0b9x
  · exact s7_1b0b10x
  · exact s7_1b0b11x
  · exact s7_1b0b12x
  · exact s7_1b0b13x
  · exact s7_1b0b14x
  · exact s7_1b0b15x
  · exact s7_1b0b16x
  · exact s7_1b0b17x
  · exact s7_1b0b18x
  · exact s7_1b0b19x
  · exact s7_1b0b20x
  · exact s7_1b0b21x
  · exact s7_1b0b22x
  · exact s7_1b0b23x
  · exact s7_1b0b24x
  · exact s7_1b0b25x
  · exact s7_1b0b26x
  · exact s7_1b0b27x
  · exact s7_1b0b28x
  · exact s7_1b0b29x
  · exact s7_1b0b30x
  · exact s7_1b0b31x
  · exact s7_1b0b32x
  · exact s7_1b0b33x
  · exact s7_1b0b34x
  · exact s7_1b0b35x
  · exact s7_1b0b36x
  · exact s7_1b0b37x
  · exact s7_1b0b38x
  · exact s7_1b0b39x
  · exact s7_1b0b40x
  · exact s7_1b0b41x
  · exact s7_1b0b42x
  · exact s7_1b0b43x
  · exact s7_1b0b44x
  · exact s7_1b0b45x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b0x : Impossible 8 1 s7_1b0 := exclude_step (u := fun v => !s7_1b0u.contains v) (b := fun v => !s7_1b0b.contains v) (by decide +kernel) s7_1b0ux s7_1b0bx (by decide +kernel)

def s7_1b1 : List Sig := [bin true (r7.getD 0 zero) (r7.getD 1 zero),r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1b1u0 : List Sig := [y7_61,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u0x : Impossible 7 0 s7_1b1u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1u1 : List Sig := [y7_61,y7_15,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u1x : Impossible 7 0 s7_1b1u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1u2 : List Sig := [y7_5,x7_0,y7_15,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u2x : Impossible 7 0 s7_1b1u2 := impPerm (z := s7_1u0b17) (by decide +kernel) s7_1u0b17x

def s7_1b1u3 : List Sig := [y7_34,x7_1,y7_15,x7_0,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u3x : Impossible 7 0 s7_1b1u3 := impPerm (z := s7_1u1b17) (by decide +kernel) s7_1u1b17x

def s7_1b1u4 : List Sig := [y7_53,x7_2,y7_15,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u4x : Impossible 7 0 s7_1b1u4 := rotate_impossible sym7_2 (z := s7_1u1b25) (by simp only [s7_1b1u4,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b25x

def s7_1b1u5 : List Sig := [y7_43,x7_3,y7_15,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u5x : Impossible 7 0 s7_1b1u5 := impPerm (z := s7_1u3b25) (by decide +kernel) s7_1u3b25x

def s7_1b1u6 : List Sig := [y7_54,x7_4,y7_15,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1u6x : Impossible 7 0 s7_1b1u6 := rotate_impossible sym7_1 (z := s7_1u3b25) (by simp only [s7_1b1u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b25x

def s7_1b1u : List (List Sig) := [s7_1b1u0,s7_1b1u1,s7_1b1u2,s7_1b1u3,s7_1b1u4,s7_1b1u5,s7_1b1u6]

lemma s7_1b1ux (v : List Sig) (h : (!s7_1b1u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b1u := by simpa using h
  simp only [s7_1b1u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b1u0x
  · exact s7_1b1u1x
  · exact s7_1b1u2x
  · exact s7_1b1u3x
  · exact s7_1b1u4x
  · exact s7_1b1u5x
  · exact s7_1b1u6x

def s7_1b1b7 : List Sig := [y7_62,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b7x : Impossible 7 1 s7_1b1b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b8 : List Sig := [y7_62,y7_15,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b8x : Impossible 7 1 s7_1b1b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b9 : List Sig := [y7_63,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b9x : Impossible 7 1 s7_1b1b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b10 : List Sig := [y7_63,y7_15,x7_2,x7_0,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b10x : Impossible 7 1 s7_1b1b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b11 : List Sig := [y7_64,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b11x : Impossible 7 1 s7_1b1b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b12 : List Sig := [y7_64,y7_15,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b12x : Impossible 7 1 s7_1b1b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b13 : List Sig := [y7_65,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b13x : Impossible 7 1 s7_1b1b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b14 : List Sig := [y7_65,y7_15,x7_3,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b14x : Impossible 7 1 s7_1b1b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b15 : List Sig := [y7_66,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b15x : Impossible 7 1 s7_1b1b15 := rotate_impossible sym7_1 (z := s7_1b1b11) (by simp only [s7_1b1b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_66,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b11x

def s7_1b1b16 : List Sig := [y7_66,y7_15,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b16x : Impossible 7 1 s7_1b1b16 := rotate_impossible sym7_1 (z := s7_1b1b12) (by simp only [s7_1b1b16,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_66,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b12x

def s7_1b1b17 : List Sig := [y7_67,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b17x : Impossible 7 1 s7_1b1b17 := rotate_impossible sym7_1 (z := s7_1b1b13) (by simp only [s7_1b1b17,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_67,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b13x

def s7_1b1b18 : List Sig := [y7_67,y7_15,x7_4,x7_0,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b18x : Impossible 7 1 s7_1b1b18 := rotate_impossible sym7_1 (z := s7_1b1b14) (by simp only [s7_1b1b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_67,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b14x

def s7_1b1b19 : List Sig := [y7_14,x7_0,y7_15,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b19x : Impossible 7 1 s7_1b1b19 := impPerm (z := s7_1b0b25) (by decide +kernel) s7_1b0b25x

def s7_1b1b20 : List Sig := [y7_14,x7_1,y7_15,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b20x : Impossible 7 1 s7_1b1b20 := impPerm (z := s7_1b0b26) (by decide +kernel) s7_1b0b26x

def s7_1b1b21 : List Sig := [y7_14,x7_0,x7_1,y7_15,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b21x : Impossible 7 1 s7_1b1b21 := impPerm (z := s7_1b0b27) (by decide +kernel) s7_1b0b27x

def s7_1b1b22 : List Sig := [y7_16,x7_0,x7_2,y7_15,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b22x : Impossible 7 1 s7_1b1b22 := rotate_impossible sym7_2 (z := s7_1b0b29) (by simp only [s7_1b1b22,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_16,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b29x

def s7_1b1b23 : List Sig := [y7_17,x7_0,x7_2,y7_15,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b23x : Impossible 7 1 s7_1b1b23 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b24 : List Sig := [y7_18,x7_0,x7_3,y7_15,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b24x : Impossible 7 1 s7_1b1b24 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b25 : List Sig := [y7_19,x7_0,x7_3,y7_15,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b25x : Impossible 7 1 s7_1b1b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b26 : List Sig := [y7_20,x7_0,x7_4,y7_15,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b26x : Impossible 7 1 s7_1b1b26 := rotate_impossible sym7_1 (z := s7_1b1b24) (by simp only [s7_1b1b26,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_20,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b24x

def s7_1b1b27 : List Sig := [y7_21,x7_0,x7_4,y7_15,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b27x : Impossible 7 1 s7_1b1b27 := rotate_impossible sym7_1 (z := s7_1b1b25) (by simp only [s7_1b1b27,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_21,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b25x

def s7_1b1b28 : List Sig := [y7_22,x7_1,x7_2,y7_15,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b28x : Impossible 7 1 s7_1b1b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b29 : List Sig := [y7_23,x7_2,y7_15,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b29x : Impossible 7 1 s7_1b1b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b30 : List Sig := [y7_23,x7_1,x7_2,y7_15,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b30x : Impossible 7 1 s7_1b1b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b31 : List Sig := [y7_24,x7_1,x7_3,y7_15,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b31x : Impossible 7 1 s7_1b1b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b32 : List Sig := [y7_25,x7_1,x7_3,y7_15,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b32x : Impossible 7 1 s7_1b1b32 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b33 : List Sig := [y7_26,x7_1,x7_4,y7_15,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b33x : Impossible 7 1 s7_1b1b33 := rotate_impossible sym7_1 (z := s7_1b1b31) (by simp only [s7_1b1b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_26,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b31x

def s7_1b1b34 : List Sig := [y7_27,x7_1,x7_4,y7_15,x7_0,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b34x : Impossible 7 1 s7_1b1b34 := rotate_impossible sym7_1 (z := s7_1b1b32) (by simp only [s7_1b1b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_27,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b32x

def s7_1b1b35 : List Sig := [y7_28,x7_2,x7_3,y7_15,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b35x : Impossible 7 1 s7_1b1b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b36 : List Sig := [y7_29,x7_2,x7_3,y7_15,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b36x : Impossible 7 1 s7_1b1b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b37 : List Sig := [y7_30,x7_2,x7_4,y7_15,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b37x : Impossible 7 1 s7_1b1b37 := rotate_impossible sym7_1 (z := s7_1b1b35) (by simp only [s7_1b1b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b35x

def s7_1b1b38 : List Sig := [y7_31,x7_2,x7_4,y7_15,x7_0,x7_1,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b38x : Impossible 7 1 s7_1b1b38 := rotate_impossible sym7_1 (z := s7_1b1b36) (by simp only [s7_1b1b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_15,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b1b36x

def s7_1b1b39 : List Sig := [y7_32,x7_3,x7_4,y7_15,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b39x : Impossible 7 1 s7_1b1b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b40 : List Sig := [y7_33,x7_3,x7_4,y7_15,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1b40x : Impossible 7 1 s7_1b1b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b1b : List (List Sig) := [s7_1b1b7,s7_1b1b8,s7_1b1b9,s7_1b1b10,s7_1b1b11,s7_1b1b12,s7_1b1b13,s7_1b1b14,s7_1b1b15,s7_1b1b16,s7_1b1b17,s7_1b1b18,s7_1b1b19,s7_1b1b20,s7_1b1b21,s7_1b1b22,s7_1b1b23,s7_1b1b24,s7_1b1b25,s7_1b1b26,s7_1b1b27,s7_1b1b28,s7_1b1b29,s7_1b1b30,s7_1b1b31,s7_1b1b32,s7_1b1b33,s7_1b1b34,s7_1b1b35,s7_1b1b36,s7_1b1b37,s7_1b1b38,s7_1b1b39,s7_1b1b40]

lemma s7_1b1bx (v : List Sig) (h : (!s7_1b1b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b1b := by simpa using h
  simp only [s7_1b1b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b1b7x
  · exact s7_1b1b8x
  · exact s7_1b1b9x
  · exact s7_1b1b10x
  · exact s7_1b1b11x
  · exact s7_1b1b12x
  · exact s7_1b1b13x
  · exact s7_1b1b14x
  · exact s7_1b1b15x
  · exact s7_1b1b16x
  · exact s7_1b1b17x
  · exact s7_1b1b18x
  · exact s7_1b1b19x
  · exact s7_1b1b20x
  · exact s7_1b1b21x
  · exact s7_1b1b22x
  · exact s7_1b1b23x
  · exact s7_1b1b24x
  · exact s7_1b1b25x
  · exact s7_1b1b26x
  · exact s7_1b1b27x
  · exact s7_1b1b28x
  · exact s7_1b1b29x
  · exact s7_1b1b30x
  · exact s7_1b1b31x
  · exact s7_1b1b32x
  · exact s7_1b1b33x
  · exact s7_1b1b34x
  · exact s7_1b1b35x
  · exact s7_1b1b36x
  · exact s7_1b1b37x
  · exact s7_1b1b38x
  · exact s7_1b1b39x
  · exact s7_1b1b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b1x : Impossible 8 1 s7_1b1 := exclude_step (u := fun v => !s7_1b1u.contains v) (b := fun v => !s7_1b1b.contains v) (by decide +kernel) s7_1b1ux s7_1b1bx (by decide +kernel)

def s7_1b2 : List Sig := [bin false (r7.getD 0 zero) (r7.getD 2 zero),r7.getD 0 zero,r7.getD 2 zero,r7.getD 1 zero,r7.getD 3 zero,r7.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b2x : Impossible 8 1 s7_1b2 := rotate_impossible sym7_2 (z := s7_1b0) (by simp only [s7_1b2,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0x

def s7_1b3 : List Sig := [bin true (r7.getD 0 zero) (r7.getD 2 zero),r7.getD 0 zero,r7.getD 2 zero,r7.getD 1 zero,r7.getD 3 zero,r7.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b3x : Impossible 8 1 s7_1b3 := rotate_impossible sym7_2 (z := s7_1b1) (by simp only [s7_1b3,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1x

def s7_1b4 : List Sig := [bin false (r7.getD 0 zero) (r7.getD 3 zero),r7.getD 0 zero,r7.getD 3 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 4 zero]

def s7_1b4u0 : List Sig := [y7_68,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u0x : Impossible 7 0 s7_1b4u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4u1 : List Sig := [y7_68,y7_18,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u1x : Impossible 7 0 s7_1b4u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4u2 : List Sig := [y7_5,x7_0,y7_18,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u2x : Impossible 7 0 s7_1b4u2 := impPerm (z := s7_1u0b20) (by decide +kernel) s7_1u0b20x

def s7_1b4u3 : List Sig := [y7_43,x7_3,y7_18,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u3x : Impossible 7 0 s7_1b4u3 := impPerm (z := s7_1u3b16) (by decide +kernel) s7_1u3b16x

def s7_1b4u4 : List Sig := [y7_34,x7_1,y7_18,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u4x : Impossible 7 0 s7_1b4u4 := impPerm (z := s7_1u1b26) (by decide +kernel) s7_1u1b26x

def s7_1b4u5 : List Sig := [y7_53,x7_2,y7_18,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u5x : Impossible 7 0 s7_1b4u5 := rotate_impossible sym7_2 (z := s7_1u1b26) (by simp only [s7_1b4u5,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b26x

def s7_1b4u6 : List Sig := [y7_54,x7_4,y7_18,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4u6x : Impossible 7 0 s7_1b4u6 := rotate_impossible sym7_1 (z := s7_1u3b28) (by simp only [s7_1b4u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b28x

def s7_1b4u : List (List Sig) := [s7_1b4u0,s7_1b4u1,s7_1b4u2,s7_1b4u3,s7_1b4u4,s7_1b4u5,s7_1b4u6]

lemma s7_1b4ux (v : List Sig) (h : (!s7_1b4u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b4u := by simpa using h
  simp only [s7_1b4u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b4u0x
  · exact s7_1b4u1x
  · exact s7_1b4u2x
  · exact s7_1b4u3x
  · exact s7_1b4u4x
  · exact s7_1b4u5x
  · exact s7_1b4u6x

def s7_1b4b7 : List Sig := [y7_57,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b7x : Impossible 7 1 s7_1b4b7 := impPerm (z := s7_1b0b13) (by decide +kernel) s7_1b0b13x

def s7_1b4b8 : List Sig := [y7_57,y7_18,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b8x : Impossible 7 1 s7_1b4b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b9 : List Sig := [y7_69,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b9x : Impossible 7 1 s7_1b4b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b10 : List Sig := [y7_69,y7_18,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b10x : Impossible 7 1 s7_1b4b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b11 : List Sig := [y7_70,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b11x : Impossible 7 1 s7_1b4b11 := rotate_impossible sym7_2 (z := s7_1b0b13) (by simp only [s7_1b4b11,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_70,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b13x

def s7_1b4b12 : List Sig := [y7_70,y7_18,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b12x : Impossible 7 1 s7_1b4b12 := rotate_impossible sym7_2 (z := s7_1b4b8) (by simp only [s7_1b4b12,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_70,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b8x

def s7_1b4b13 : List Sig := [y7_71,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b13x : Impossible 7 1 s7_1b4b13 := rotate_impossible sym7_2 (z := s7_1b4b9) (by simp only [s7_1b4b13,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_71,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b9x

def s7_1b4b14 : List Sig := [y7_71,y7_18,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b14x : Impossible 7 1 s7_1b4b14 := rotate_impossible sym7_2 (z := s7_1b4b10) (by simp only [s7_1b4b14,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_71,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b10x

def s7_1b4b15 : List Sig := [y7_72,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b15x : Impossible 7 1 s7_1b4b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b16 : List Sig := [y7_72,y7_18,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b16x : Impossible 7 1 s7_1b4b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b17 : List Sig := [y7_73,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b17x : Impossible 7 1 s7_1b4b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b18 : List Sig := [y7_73,y7_18,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b18x : Impossible 7 1 s7_1b4b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b19 : List Sig := [y7_19,x7_0,y7_18,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b19x : Impossible 7 1 s7_1b4b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b20 : List Sig := [y7_19,x7_3,y7_18,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b20x : Impossible 7 1 s7_1b4b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b21 : List Sig := [y7_19,x7_0,x7_3,y7_18,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b21x : Impossible 7 1 s7_1b4b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b22 : List Sig := [y7_14,x7_0,x7_1,y7_18,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b22x : Impossible 7 1 s7_1b4b22 := impPerm (z := s7_1b0b30) (by decide +kernel) s7_1b0b30x

def s7_1b4b23 : List Sig := [y7_15,x7_0,x7_1,y7_18,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b23x : Impossible 7 1 s7_1b4b23 := impPerm (z := s7_1b1b24) (by decide +kernel) s7_1b1b24x

def s7_1b4b24 : List Sig := [y7_16,x7_0,x7_2,y7_18,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b24x : Impossible 7 1 s7_1b4b24 := rotate_impossible sym7_2 (z := s7_1b0b30) (by simp only [s7_1b4b24,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_18,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b30x

def s7_1b4b25 : List Sig := [y7_17,x7_0,x7_2,y7_18,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b25x : Impossible 7 1 s7_1b4b25 := rotate_impossible sym7_2 (z := s7_1b1b24) (by simp only [s7_1b4b25,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_18,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b24x

def s7_1b4b26 : List Sig := [y7_20,x7_0,x7_4,y7_18,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b26x : Impossible 7 1 s7_1b4b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b27 : List Sig := [y7_21,x7_0,x7_4,y7_18,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b27x : Impossible 7 1 s7_1b4b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b28 : List Sig := [y7_24,x7_3,x7_1,y7_18,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b28x : Impossible 7 1 s7_1b4b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b29 : List Sig := [y7_25,x7_3,x7_1,y7_18,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b29x : Impossible 7 1 s7_1b4b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b30 : List Sig := [y7_28,x7_3,x7_2,y7_18,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b30x : Impossible 7 1 s7_1b4b30 := rotate_impossible sym7_2 (z := s7_1b4b28) (by simp only [s7_1b4b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_28,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b28x

def s7_1b4b31 : List Sig := [y7_29,x7_3,x7_2,y7_18,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b31x : Impossible 7 1 s7_1b4b31 := rotate_impossible sym7_2 (z := s7_1b4b29) (by simp only [s7_1b4b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_29,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b29x

def s7_1b4b32 : List Sig := [y7_32,x7_3,x7_4,y7_18,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b32x : Impossible 7 1 s7_1b4b32 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b33 : List Sig := [y7_33,x7_3,x7_4,y7_18,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b33x : Impossible 7 1 s7_1b4b33 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b34 : List Sig := [y7_22,x7_1,x7_2,y7_18,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b34x : Impossible 7 1 s7_1b4b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b35 : List Sig := [y7_23,x7_1,x7_2,y7_18,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b35x : Impossible 7 1 s7_1b4b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b36 : List Sig := [y7_26,x7_1,x7_4,y7_18,x7_0,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b36x : Impossible 7 1 s7_1b4b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b37 : List Sig := [y7_27,x7_1,x7_4,y7_18,x7_0,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b37x : Impossible 7 1 s7_1b4b37 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b4b38 : List Sig := [y7_30,x7_2,x7_4,y7_18,x7_0,x7_3,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b38x : Impossible 7 1 s7_1b4b38 := rotate_impossible sym7_2 (z := s7_1b4b36) (by simp only [s7_1b4b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b36x

def s7_1b4b39 : List Sig := [y7_31,x7_2,x7_4,y7_18,x7_0,x7_3,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4b39x : Impossible 7 1 s7_1b4b39 := rotate_impossible sym7_2 (z := s7_1b4b37) (by simp only [s7_1b4b39,x7_0,x7_1,x7_2,x7_3,x7_4,y7_18,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b4b37x

def s7_1b4b : List (List Sig) := [s7_1b4b7,s7_1b4b8,s7_1b4b9,s7_1b4b10,s7_1b4b11,s7_1b4b12,s7_1b4b13,s7_1b4b14,s7_1b4b15,s7_1b4b16,s7_1b4b17,s7_1b4b18,s7_1b4b19,s7_1b4b20,s7_1b4b21,s7_1b4b22,s7_1b4b23,s7_1b4b24,s7_1b4b25,s7_1b4b26,s7_1b4b27,s7_1b4b28,s7_1b4b29,s7_1b4b30,s7_1b4b31,s7_1b4b32,s7_1b4b33,s7_1b4b34,s7_1b4b35,s7_1b4b36,s7_1b4b37,s7_1b4b38,s7_1b4b39]

lemma s7_1b4bx (v : List Sig) (h : (!s7_1b4b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b4b := by simpa using h
  simp only [s7_1b4b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b4b7x
  · exact s7_1b4b8x
  · exact s7_1b4b9x
  · exact s7_1b4b10x
  · exact s7_1b4b11x
  · exact s7_1b4b12x
  · exact s7_1b4b13x
  · exact s7_1b4b14x
  · exact s7_1b4b15x
  · exact s7_1b4b16x
  · exact s7_1b4b17x
  · exact s7_1b4b18x
  · exact s7_1b4b19x
  · exact s7_1b4b20x
  · exact s7_1b4b21x
  · exact s7_1b4b22x
  · exact s7_1b4b23x
  · exact s7_1b4b24x
  · exact s7_1b4b25x
  · exact s7_1b4b26x
  · exact s7_1b4b27x
  · exact s7_1b4b28x
  · exact s7_1b4b29x
  · exact s7_1b4b30x
  · exact s7_1b4b31x
  · exact s7_1b4b32x
  · exact s7_1b4b33x
  · exact s7_1b4b34x
  · exact s7_1b4b35x
  · exact s7_1b4b36x
  · exact s7_1b4b37x
  · exact s7_1b4b38x
  · exact s7_1b4b39x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b4x : Impossible 8 1 s7_1b4 := exclude_step (u := fun v => !s7_1b4u.contains v) (b := fun v => !s7_1b4b.contains v) (by decide +kernel) s7_1b4ux s7_1b4bx (by decide +kernel)

def s7_1b5 : List Sig := [bin true (r7.getD 0 zero) (r7.getD 3 zero),r7.getD 0 zero,r7.getD 3 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 4 zero]

def s7_1b5u0 : List Sig := [y7_74,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u0x : Impossible 7 0 s7_1b5u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5u1 : List Sig := [y7_74,y7_19,x7_0,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u1x : Impossible 7 0 s7_1b5u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5u2 : List Sig := [y7_5,x7_0,y7_19,x7_3,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u2x : Impossible 7 0 s7_1b5u2 := impPerm (z := s7_1u0b21) (by decide +kernel) s7_1u0b21x

def s7_1b5u3 : List Sig := [y7_43,x7_3,y7_19,x7_0,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u3x : Impossible 7 0 s7_1b5u3 := impPerm (z := s7_1u3b17) (by decide +kernel) s7_1u3b17x

def s7_1b5u4 : List Sig := [y7_34,x7_1,y7_19,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u4x : Impossible 7 0 s7_1b5u4 := impPerm (z := s7_1u1b27) (by decide +kernel) s7_1u1b27x

def s7_1b5u5 : List Sig := [y7_53,x7_2,y7_19,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u5x : Impossible 7 0 s7_1b5u5 := rotate_impossible sym7_2 (z := s7_1u1b27) (by simp only [s7_1b5u5,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b27x

def s7_1b5u6 : List Sig := [y7_54,x7_4,y7_19,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5u6x : Impossible 7 0 s7_1b5u6 := rotate_impossible sym7_1 (z := s7_1u3b29) (by simp only [s7_1b5u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b29x

def s7_1b5u : List (List Sig) := [s7_1b5u0,s7_1b5u1,s7_1b5u2,s7_1b5u3,s7_1b5u4,s7_1b5u5,s7_1b5u6]

lemma s7_1b5ux (v : List Sig) (h : (!s7_1b5u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b5u := by simpa using h
  simp only [s7_1b5u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b5u0x
  · exact s7_1b5u1x
  · exact s7_1b5u2x
  · exact s7_1b5u3x
  · exact s7_1b5u4x
  · exact s7_1b5u5x
  · exact s7_1b5u6x

def s7_1b5b7 : List Sig := [y7_75,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b7x : Impossible 7 1 s7_1b5b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b8 : List Sig := [y7_75,y7_19,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b8x : Impossible 7 1 s7_1b5b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b9 : List Sig := [y7_65,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b9x : Impossible 7 1 s7_1b5b9 := impPerm (z := s7_1b1b13) (by decide +kernel) s7_1b1b13x

def s7_1b5b10 : List Sig := [y7_65,y7_19,x7_1,x7_0,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b10x : Impossible 7 1 s7_1b5b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b11 : List Sig := [y7_76,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b11x : Impossible 7 1 s7_1b5b11 := rotate_impossible sym7_2 (z := s7_1b5b7) (by simp only [s7_1b5b11,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_76,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b7x

def s7_1b5b12 : List Sig := [y7_76,y7_19,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b12x : Impossible 7 1 s7_1b5b12 := rotate_impossible sym7_2 (z := s7_1b5b8) (by simp only [s7_1b5b12,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_76,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b8x

def s7_1b5b13 : List Sig := [y7_77,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b13x : Impossible 7 1 s7_1b5b13 := rotate_impossible sym7_2 (z := s7_1b1b13) (by simp only [s7_1b5b13,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_77,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b13x

def s7_1b5b14 : List Sig := [y7_77,y7_19,x7_2,x7_0,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b14x : Impossible 7 1 s7_1b5b14 := rotate_impossible sym7_2 (z := s7_1b5b10) (by simp only [s7_1b5b14,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_77,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b10x

def s7_1b5b15 : List Sig := [y7_78,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b15x : Impossible 7 1 s7_1b5b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b16 : List Sig := [y7_78,y7_19,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b16x : Impossible 7 1 s7_1b5b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b17 : List Sig := [y7_79,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b17x : Impossible 7 1 s7_1b5b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b18 : List Sig := [y7_79,y7_19,x7_4,x7_0,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b18x : Impossible 7 1 s7_1b5b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b19 : List Sig := [y7_18,x7_0,y7_19,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b19x : Impossible 7 1 s7_1b5b19 := impPerm (z := s7_1b4b19) (by decide +kernel) s7_1b4b19x

def s7_1b5b20 : List Sig := [y7_18,x7_3,y7_19,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b20x : Impossible 7 1 s7_1b5b20 := impPerm (z := s7_1b4b20) (by decide +kernel) s7_1b4b20x

def s7_1b5b21 : List Sig := [y7_18,x7_0,x7_3,y7_19,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b21x : Impossible 7 1 s7_1b5b21 := impPerm (z := s7_1b4b21) (by decide +kernel) s7_1b4b21x

def s7_1b5b22 : List Sig := [y7_14,x7_0,x7_1,y7_19,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b22x : Impossible 7 1 s7_1b5b22 := impPerm (z := s7_1b0b31) (by decide +kernel) s7_1b0b31x

def s7_1b5b23 : List Sig := [y7_15,x7_0,x7_1,y7_19,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b23x : Impossible 7 1 s7_1b5b23 := impPerm (z := s7_1b1b25) (by decide +kernel) s7_1b1b25x

def s7_1b5b24 : List Sig := [y7_16,x7_0,x7_2,y7_19,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b24x : Impossible 7 1 s7_1b5b24 := rotate_impossible sym7_2 (z := s7_1b0b31) (by simp only [s7_1b5b24,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_19,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b31x

def s7_1b5b25 : List Sig := [y7_17,x7_0,x7_2,y7_19,x7_3,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b25x : Impossible 7 1 s7_1b5b25 := rotate_impossible sym7_2 (z := s7_1b1b25) (by simp only [s7_1b5b25,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_19,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b25x

def s7_1b5b26 : List Sig := [y7_20,x7_0,x7_4,y7_19,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b26x : Impossible 7 1 s7_1b5b26 := rotate_impossible sym7_1 (z := s7_1b4b27) (by simp only [s7_1b5b26,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_20,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b27x

def s7_1b5b27 : List Sig := [y7_21,x7_0,x7_4,y7_19,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b27x : Impossible 7 1 s7_1b5b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b28 : List Sig := [y7_24,x7_3,x7_1,y7_19,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b28x : Impossible 7 1 s7_1b5b28 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b29 : List Sig := [y7_25,x7_1,y7_19,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b29x : Impossible 7 1 s7_1b5b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b30 : List Sig := [y7_25,x7_3,x7_1,y7_19,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b30x : Impossible 7 1 s7_1b5b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b31 : List Sig := [y7_28,x7_3,x7_2,y7_19,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b31x : Impossible 7 1 s7_1b5b31 := rotate_impossible sym7_2 (z := s7_1b5b28) (by simp only [s7_1b5b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_28,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b28x

def s7_1b5b32 : List Sig := [y7_29,x7_2,y7_19,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b32x : Impossible 7 1 s7_1b5b32 := rotate_impossible sym7_2 (z := s7_1b5b29) (by simp only [s7_1b5b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_29,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b29x

def s7_1b5b33 : List Sig := [y7_29,x7_3,x7_2,y7_19,x7_0,x7_1,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b33x : Impossible 7 1 s7_1b5b33 := rotate_impossible sym7_2 (z := s7_1b5b30) (by simp only [s7_1b5b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_29,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b30x

def s7_1b5b34 : List Sig := [y7_32,x7_4,y7_19,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b34x : Impossible 7 1 s7_1b5b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b35 : List Sig := [y7_32,x7_3,x7_4,y7_19,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b35x : Impossible 7 1 s7_1b5b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b36 : List Sig := [y7_33,x7_3,x7_4,y7_19,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b36x : Impossible 7 1 s7_1b5b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b37 : List Sig := [y7_22,x7_1,x7_2,y7_19,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b37x : Impossible 7 1 s7_1b5b37 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b38 : List Sig := [y7_23,x7_1,x7_2,y7_19,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b38x : Impossible 7 1 s7_1b5b38 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b39 : List Sig := [y7_26,x7_1,x7_4,y7_19,x7_0,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b39x : Impossible 7 1 s7_1b5b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b40 : List Sig := [y7_27,x7_1,x7_4,y7_19,x7_0,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b40x : Impossible 7 1 s7_1b5b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b5b41 : List Sig := [y7_30,x7_2,x7_4,y7_19,x7_0,x7_3,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b41x : Impossible 7 1 s7_1b5b41 := rotate_impossible sym7_2 (z := s7_1b5b39) (by simp only [s7_1b5b41,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b39x

def s7_1b5b42 : List Sig := [y7_31,x7_2,x7_4,y7_19,x7_0,x7_3,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5b42x : Impossible 7 1 s7_1b5b42 := rotate_impossible sym7_2 (z := s7_1b5b40) (by simp only [s7_1b5b42,x7_0,x7_1,x7_2,x7_3,x7_4,y7_19,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b5b40x

def s7_1b5b : List (List Sig) := [s7_1b5b7,s7_1b5b8,s7_1b5b9,s7_1b5b10,s7_1b5b11,s7_1b5b12,s7_1b5b13,s7_1b5b14,s7_1b5b15,s7_1b5b16,s7_1b5b17,s7_1b5b18,s7_1b5b19,s7_1b5b20,s7_1b5b21,s7_1b5b22,s7_1b5b23,s7_1b5b24,s7_1b5b25,s7_1b5b26,s7_1b5b27,s7_1b5b28,s7_1b5b29,s7_1b5b30,s7_1b5b31,s7_1b5b32,s7_1b5b33,s7_1b5b34,s7_1b5b35,s7_1b5b36,s7_1b5b37,s7_1b5b38,s7_1b5b39,s7_1b5b40,s7_1b5b41,s7_1b5b42]

lemma s7_1b5bx (v : List Sig) (h : (!s7_1b5b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b5b := by simpa using h
  simp only [s7_1b5b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b5b7x
  · exact s7_1b5b8x
  · exact s7_1b5b9x
  · exact s7_1b5b10x
  · exact s7_1b5b11x
  · exact s7_1b5b12x
  · exact s7_1b5b13x
  · exact s7_1b5b14x
  · exact s7_1b5b15x
  · exact s7_1b5b16x
  · exact s7_1b5b17x
  · exact s7_1b5b18x
  · exact s7_1b5b19x
  · exact s7_1b5b20x
  · exact s7_1b5b21x
  · exact s7_1b5b22x
  · exact s7_1b5b23x
  · exact s7_1b5b24x
  · exact s7_1b5b25x
  · exact s7_1b5b26x
  · exact s7_1b5b27x
  · exact s7_1b5b28x
  · exact s7_1b5b29x
  · exact s7_1b5b30x
  · exact s7_1b5b31x
  · exact s7_1b5b32x
  · exact s7_1b5b33x
  · exact s7_1b5b34x
  · exact s7_1b5b35x
  · exact s7_1b5b36x
  · exact s7_1b5b37x
  · exact s7_1b5b38x
  · exact s7_1b5b39x
  · exact s7_1b5b40x
  · exact s7_1b5b41x
  · exact s7_1b5b42x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b5x : Impossible 8 1 s7_1b5 := exclude_step (u := fun v => !s7_1b5u.contains v) (b := fun v => !s7_1b5b.contains v) (by decide +kernel) s7_1b5ux s7_1b5bx (by decide +kernel)

def s7_1b6 : List Sig := [bin false (r7.getD 0 zero) (r7.getD 4 zero),r7.getD 0 zero,r7.getD 4 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b6x : Impossible 8 1 s7_1b6 := rotate_impossible sym7_1 (z := s7_1b4) (by simp only [s7_1b6,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4x

def s7_1b7 : List Sig := [bin true (r7.getD 0 zero) (r7.getD 4 zero),r7.getD 0 zero,r7.getD 4 zero,r7.getD 1 zero,r7.getD 2 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b7x : Impossible 8 1 s7_1b7 := rotate_impossible sym7_1 (z := s7_1b5) (by simp only [s7_1b7,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5x

def s7_1b8 : List Sig := [bin false (r7.getD 1 zero) (r7.getD 2 zero),r7.getD 1 zero,r7.getD 2 zero,r7.getD 0 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1b8u0 : List Sig := [y7_80,x7_1,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u0x : Impossible 7 0 s7_1b8u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8u1 : List Sig := [y7_80,y7_22,x7_1,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u1x : Impossible 7 0 s7_1b8u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8u2 : List Sig := [y7_34,x7_1,y7_22,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u2x : Impossible 7 0 s7_1b8u2 := impPerm (z := s7_1u1b18) (by decide +kernel) s7_1u1b18x

def s7_1b8u3 : List Sig := [y7_53,x7_2,y7_22,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u3x : Impossible 7 0 s7_1b8u3 := rotate_impossible sym7_2 (z := s7_1u1b18) (by simp only [s7_1b8u3,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b18x

def s7_1b8u4 : List Sig := [y7_5,x7_0,y7_22,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u4x : Impossible 7 0 s7_1b8u4 := impPerm (z := s7_1u0b24) (by decide +kernel) s7_1u0b24x

def s7_1b8u5 : List Sig := [y7_43,x7_3,y7_22,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u5x : Impossible 7 0 s7_1b8u5 := impPerm (z := s7_1u3b30) (by decide +kernel) s7_1u3b30x

def s7_1b8u6 : List Sig := [y7_54,x7_4,y7_22,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8u6x : Impossible 7 0 s7_1b8u6 := rotate_impossible sym7_1 (z := s7_1u3b30) (by simp only [s7_1b8u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b30x

def s7_1b8u : List (List Sig) := [s7_1b8u0,s7_1b8u1,s7_1b8u2,s7_1b8u3,s7_1b8u4,s7_1b8u5,s7_1b8u6]

lemma s7_1b8ux (v : List Sig) (h : (!s7_1b8u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b8u := by simpa using h
  simp only [s7_1b8u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b8u0x
  · exact s7_1b8u1x
  · exact s7_1b8u2x
  · exact s7_1b8u3x
  · exact s7_1b8u4x
  · exact s7_1b8u5x
  · exact s7_1b8u6x

def s7_1b8b7 : List Sig := [y7_55,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b7x : Impossible 7 1 s7_1b8b7 := impPerm (z := s7_1b0b7) (by decide +kernel) s7_1b0b7x

def s7_1b8b8 : List Sig := [y7_55,y7_22,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b8x : Impossible 7 1 s7_1b8b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b9 : List Sig := [y7_81,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b9x : Impossible 7 1 s7_1b8b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b10 : List Sig := [y7_81,y7_22,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b10x : Impossible 7 1 s7_1b8b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b11 : List Sig := [y7_82,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b11x : Impossible 7 1 s7_1b8b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b12 : List Sig := [y7_82,y7_22,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b12x : Impossible 7 1 s7_1b8b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b13 : List Sig := [y7_83,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b13x : Impossible 7 1 s7_1b8b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b14 : List Sig := [y7_83,y7_22,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b14x : Impossible 7 1 s7_1b8b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b15 : List Sig := [y7_84,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b15x : Impossible 7 1 s7_1b8b15 := rotate_impossible sym7_1 (z := s7_1b8b11) (by simp only [s7_1b8b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_84,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b11x

def s7_1b8b16 : List Sig := [y7_84,y7_22,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b16x : Impossible 7 1 s7_1b8b16 := rotate_impossible sym7_1 (z := s7_1b8b12) (by simp only [s7_1b8b16,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_84,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b12x

def s7_1b8b17 : List Sig := [y7_85,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b17x : Impossible 7 1 s7_1b8b17 := rotate_impossible sym7_1 (z := s7_1b8b13) (by simp only [s7_1b8b17,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_85,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b13x

def s7_1b8b18 : List Sig := [y7_85,y7_22,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b18x : Impossible 7 1 s7_1b8b18 := rotate_impossible sym7_1 (z := s7_1b8b14) (by simp only [s7_1b8b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_85,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b14x

def s7_1b8b19 : List Sig := [y7_23,y7_22,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b19x : Impossible 7 1 s7_1b8b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b20 : List Sig := [y7_23,x7_1,y7_22,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b20x : Impossible 7 1 s7_1b8b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b21 : List Sig := [y7_23,x7_2,y7_22,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b21x : Impossible 7 1 s7_1b8b21 := rotate_impossible sym7_2 (z := s7_1b8b20) (by simp only [s7_1b8b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b8b20x

def s7_1b8b22 : List Sig := [y7_23,x7_1,x7_2,y7_22,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b22x : Impossible 7 1 s7_1b8b22 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b23 : List Sig := [y7_14,x7_1,x7_0,y7_22,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b23x : Impossible 7 1 s7_1b8b23 := impPerm (z := s7_1b0b34) (by decide +kernel) s7_1b0b34x

def s7_1b8b24 : List Sig := [y7_15,x7_1,x7_0,y7_22,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b24x : Impossible 7 1 s7_1b8b24 := impPerm (z := s7_1b1b28) (by decide +kernel) s7_1b1b28x

def s7_1b8b25 : List Sig := [y7_24,x7_1,x7_3,y7_22,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b25x : Impossible 7 1 s7_1b8b25 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b26 : List Sig := [y7_25,x7_1,x7_3,y7_22,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b26x : Impossible 7 1 s7_1b8b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b27 : List Sig := [y7_26,x7_1,x7_4,y7_22,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b27x : Impossible 7 1 s7_1b8b27 := rotate_impossible sym7_1 (z := s7_1b8b25) (by simp only [s7_1b8b27,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_26,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b25x

def s7_1b8b28 : List Sig := [y7_27,x7_1,x7_4,y7_22,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b28x : Impossible 7 1 s7_1b8b28 := rotate_impossible sym7_1 (z := s7_1b8b26) (by simp only [s7_1b8b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_27,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b8b26x

def s7_1b8b29 : List Sig := [y7_16,x7_2,x7_0,y7_22,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b29x : Impossible 7 1 s7_1b8b29 := rotate_impossible sym7_2 (z := s7_1b0b34) (by simp only [s7_1b8b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_22,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b34x

def s7_1b8b30 : List Sig := [y7_17,x7_2,x7_0,y7_22,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b30x : Impossible 7 1 s7_1b8b30 := rotate_impossible sym7_2 (z := s7_1b1b28) (by simp only [s7_1b8b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_22,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b28x

def s7_1b8b31 : List Sig := [y7_28,x7_2,x7_3,y7_22,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b31x : Impossible 7 1 s7_1b8b31 := rotate_impossible sym7_2 (z := s7_1b8b25) (by simp only [s7_1b8b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_28,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b8b25x

def s7_1b8b32 : List Sig := [y7_29,x7_2,x7_3,y7_22,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b32x : Impossible 7 1 s7_1b8b32 := rotate_impossible sym7_2 (z := s7_1b8b26) (by simp only [s7_1b8b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_29,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b8b26x

def s7_1b8b33 : List Sig := [y7_30,x7_2,x7_4,y7_22,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b33x : Impossible 7 1 s7_1b8b33 := rotate_impossible sym7_3 (z := s7_1b8b25) (by simp only [s7_1b8b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b8b25x

def s7_1b8b34 : List Sig := [y7_31,x7_2,x7_4,y7_22,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b34x : Impossible 7 1 s7_1b8b34 := rotate_impossible sym7_3 (z := s7_1b8b26) (by simp only [s7_1b8b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b8b26x

def s7_1b8b35 : List Sig := [y7_18,x7_0,x7_3,y7_22,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b35x : Impossible 7 1 s7_1b8b35 := impPerm (z := s7_1b4b34) (by decide +kernel) s7_1b4b34x

def s7_1b8b36 : List Sig := [y7_19,x7_0,x7_3,y7_22,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b36x : Impossible 7 1 s7_1b8b36 := impPerm (z := s7_1b5b37) (by decide +kernel) s7_1b5b37x

def s7_1b8b37 : List Sig := [y7_20,x7_0,x7_4,y7_22,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b37x : Impossible 7 1 s7_1b8b37 := rotate_impossible sym7_1 (z := s7_1b4b34) (by simp only [s7_1b8b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_22,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b34x

def s7_1b8b38 : List Sig := [y7_21,x7_0,x7_4,y7_22,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b38x : Impossible 7 1 s7_1b8b38 := rotate_impossible sym7_1 (z := s7_1b5b37) (by simp only [s7_1b8b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_22,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b37x

def s7_1b8b39 : List Sig := [y7_32,x7_3,x7_4,y7_22,x7_1,x7_2,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b39x : Impossible 7 1 s7_1b8b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b40 : List Sig := [y7_33,x7_3,x7_4,y7_22,x7_1,x7_2,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8b40x : Impossible 7 1 s7_1b8b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b8b : List (List Sig) := [s7_1b8b7,s7_1b8b8,s7_1b8b9,s7_1b8b10,s7_1b8b11,s7_1b8b12,s7_1b8b13,s7_1b8b14,s7_1b8b15,s7_1b8b16,s7_1b8b17,s7_1b8b18,s7_1b8b19,s7_1b8b20,s7_1b8b21,s7_1b8b22,s7_1b8b23,s7_1b8b24,s7_1b8b25,s7_1b8b26,s7_1b8b27,s7_1b8b28,s7_1b8b29,s7_1b8b30,s7_1b8b31,s7_1b8b32,s7_1b8b33,s7_1b8b34,s7_1b8b35,s7_1b8b36,s7_1b8b37,s7_1b8b38,s7_1b8b39,s7_1b8b40]

lemma s7_1b8bx (v : List Sig) (h : (!s7_1b8b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b8b := by simpa using h
  simp only [s7_1b8b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b8b7x
  · exact s7_1b8b8x
  · exact s7_1b8b9x
  · exact s7_1b8b10x
  · exact s7_1b8b11x
  · exact s7_1b8b12x
  · exact s7_1b8b13x
  · exact s7_1b8b14x
  · exact s7_1b8b15x
  · exact s7_1b8b16x
  · exact s7_1b8b17x
  · exact s7_1b8b18x
  · exact s7_1b8b19x
  · exact s7_1b8b20x
  · exact s7_1b8b21x
  · exact s7_1b8b22x
  · exact s7_1b8b23x
  · exact s7_1b8b24x
  · exact s7_1b8b25x
  · exact s7_1b8b26x
  · exact s7_1b8b27x
  · exact s7_1b8b28x
  · exact s7_1b8b29x
  · exact s7_1b8b30x
  · exact s7_1b8b31x
  · exact s7_1b8b32x
  · exact s7_1b8b33x
  · exact s7_1b8b34x
  · exact s7_1b8b35x
  · exact s7_1b8b36x
  · exact s7_1b8b37x
  · exact s7_1b8b38x
  · exact s7_1b8b39x
  · exact s7_1b8b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b8x : Impossible 8 1 s7_1b8 := exclude_step (u := fun v => !s7_1b8u.contains v) (b := fun v => !s7_1b8b.contains v) (by decide +kernel) s7_1b8ux s7_1b8bx (by decide +kernel)

def s7_1b9 : List Sig := [bin true (r7.getD 1 zero) (r7.getD 2 zero),r7.getD 1 zero,r7.getD 2 zero,r7.getD 0 zero,r7.getD 3 zero,r7.getD 4 zero]

def s7_1b9u0 : List Sig := [y7_86,x7_1,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u0x : Impossible 7 0 s7_1b9u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9u1 : List Sig := [y7_86,y7_23,x7_1,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u1x : Impossible 7 0 s7_1b9u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9u2 : List Sig := [y7_34,x7_1,y7_23,x7_2,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u2x : Impossible 7 0 s7_1b9u2 := impPerm (z := s7_1u1b19) (by decide +kernel) s7_1u1b19x

def s7_1b9u3 : List Sig := [y7_53,x7_2,y7_23,x7_1,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u3x : Impossible 7 0 s7_1b9u3 := rotate_impossible sym7_2 (z := s7_1u1b19) (by simp only [s7_1b9u3,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b19x

def s7_1b9u4 : List Sig := [y7_5,x7_0,y7_23,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u4x : Impossible 7 0 s7_1b9u4 := impPerm (z := s7_1u0b25) (by decide +kernel) s7_1u0b25x

def s7_1b9u5 : List Sig := [y7_43,x7_3,y7_23,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u5x : Impossible 7 0 s7_1b9u5 := impPerm (z := s7_1u3b31) (by decide +kernel) s7_1u3b31x

def s7_1b9u6 : List Sig := [y7_54,x7_4,y7_23,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9u6x : Impossible 7 0 s7_1b9u6 := rotate_impossible sym7_1 (z := s7_1u3b31) (by simp only [s7_1b9u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b31x

def s7_1b9u : List (List Sig) := [s7_1b9u0,s7_1b9u1,s7_1b9u2,s7_1b9u3,s7_1b9u4,s7_1b9u5,s7_1b9u6]

lemma s7_1b9ux (v : List Sig) (h : (!s7_1b9u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b9u := by simpa using h
  simp only [s7_1b9u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b9u0x
  · exact s7_1b9u1x
  · exact s7_1b9u2x
  · exact s7_1b9u3x
  · exact s7_1b9u4x
  · exact s7_1b9u5x
  · exact s7_1b9u6x

def s7_1b9b7 : List Sig := [y7_87,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b7x : Impossible 7 1 s7_1b9b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b8 : List Sig := [y7_87,y7_23,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b8x : Impossible 7 1 s7_1b9b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b9 : List Sig := [y7_63,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b9x : Impossible 7 1 s7_1b9b9 := impPerm (z := s7_1b1b9) (by decide +kernel) s7_1b1b9x

def s7_1b9b10 : List Sig := [y7_63,y7_23,x7_0,x7_1,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b10x : Impossible 7 1 s7_1b9b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b11 : List Sig := [y7_88,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b11x : Impossible 7 1 s7_1b9b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b12 : List Sig := [y7_88,y7_23,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b12x : Impossible 7 1 s7_1b9b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b13 : List Sig := [y7_89,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b13x : Impossible 7 1 s7_1b9b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b14 : List Sig := [y7_89,y7_23,x7_3,x7_1,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b14x : Impossible 7 1 s7_1b9b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b15 : List Sig := [y7_90,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b15x : Impossible 7 1 s7_1b9b15 := rotate_impossible sym7_1 (z := s7_1b9b11) (by simp only [s7_1b9b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_90,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b11x

def s7_1b9b16 : List Sig := [y7_90,y7_23,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b16x : Impossible 7 1 s7_1b9b16 := rotate_impossible sym7_1 (z := s7_1b9b12) (by simp only [s7_1b9b16,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_90,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b12x

def s7_1b9b17 : List Sig := [y7_91,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b17x : Impossible 7 1 s7_1b9b17 := rotate_impossible sym7_1 (z := s7_1b9b13) (by simp only [s7_1b9b17,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_91,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b13x

def s7_1b9b18 : List Sig := [y7_91,y7_23,x7_4,x7_1,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b18x : Impossible 7 1 s7_1b9b18 := rotate_impossible sym7_1 (z := s7_1b9b14) (by simp only [s7_1b9b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_91,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b14x

def s7_1b9b19 : List Sig := [y7_22,y7_23,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b19x : Impossible 7 1 s7_1b9b19 := impPerm (z := s7_1b8b19) (by decide +kernel) s7_1b8b19x

def s7_1b9b20 : List Sig := [y7_22,x7_1,y7_23,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b20x : Impossible 7 1 s7_1b9b20 := impPerm (z := s7_1b8b20) (by decide +kernel) s7_1b8b20x

def s7_1b9b21 : List Sig := [y7_22,x7_2,y7_23,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b21x : Impossible 7 1 s7_1b9b21 := rotate_impossible sym7_2 (z := s7_1b8b20) (by simp only [s7_1b9b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_22,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b8b20x

def s7_1b9b22 : List Sig := [y7_22,x7_1,x7_2,y7_23,x7_0,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b22x : Impossible 7 1 s7_1b9b22 := impPerm (z := s7_1b8b22) (by decide +kernel) s7_1b8b22x

def s7_1b9b23 : List Sig := [y7_14,x7_1,x7_0,y7_23,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b23x : Impossible 7 1 s7_1b9b23 := impPerm (z := s7_1b0b35) (by decide +kernel) s7_1b0b35x

def s7_1b9b24 : List Sig := [y7_15,x7_0,y7_23,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b24x : Impossible 7 1 s7_1b9b24 := impPerm (z := s7_1b1b29) (by decide +kernel) s7_1b1b29x

def s7_1b9b25 : List Sig := [y7_15,x7_1,x7_0,y7_23,x7_2,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b25x : Impossible 7 1 s7_1b9b25 := impPerm (z := s7_1b1b30) (by decide +kernel) s7_1b1b30x

def s7_1b9b26 : List Sig := [y7_24,x7_1,x7_3,y7_23,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b26x : Impossible 7 1 s7_1b9b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b27 : List Sig := [y7_25,x7_1,x7_3,y7_23,x7_2,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b27x : Impossible 7 1 s7_1b9b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b28 : List Sig := [y7_26,x7_1,x7_4,y7_23,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b28x : Impossible 7 1 s7_1b9b28 := rotate_impossible sym7_1 (z := s7_1b9b26) (by simp only [s7_1b9b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_26,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b26x

def s7_1b9b29 : List Sig := [y7_27,x7_1,x7_4,y7_23,x7_2,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b29x : Impossible 7 1 s7_1b9b29 := rotate_impossible sym7_1 (z := s7_1b9b27) (by simp only [s7_1b9b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_27,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b9b27x

def s7_1b9b30 : List Sig := [y7_16,x7_2,x7_0,y7_23,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b30x : Impossible 7 1 s7_1b9b30 := rotate_impossible sym7_2 (z := s7_1b0b35) (by simp only [s7_1b9b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b35x

def s7_1b9b31 : List Sig := [y7_17,x7_0,y7_23,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b31x : Impossible 7 1 s7_1b9b31 := rotate_impossible sym7_2 (z := s7_1b1b29) (by simp only [s7_1b9b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b29x

def s7_1b9b32 : List Sig := [y7_17,x7_2,x7_0,y7_23,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b32x : Impossible 7 1 s7_1b9b32 := rotate_impossible sym7_2 (z := s7_1b1b30) (by simp only [s7_1b9b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b30x

def s7_1b9b33 : List Sig := [y7_28,x7_2,x7_3,y7_23,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b33x : Impossible 7 1 s7_1b9b33 := rotate_impossible sym7_2 (z := s7_1b9b26) (by simp only [s7_1b9b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_28,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b9b26x

def s7_1b9b34 : List Sig := [y7_29,x7_2,x7_3,y7_23,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b34x : Impossible 7 1 s7_1b9b34 := rotate_impossible sym7_2 (z := s7_1b9b27) (by simp only [s7_1b9b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_29,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b9b27x

def s7_1b9b35 : List Sig := [y7_30,x7_2,x7_4,y7_23,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b35x : Impossible 7 1 s7_1b9b35 := rotate_impossible sym7_3 (z := s7_1b9b26) (by simp only [s7_1b9b35,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b9b26x

def s7_1b9b36 : List Sig := [y7_31,x7_2,x7_4,y7_23,x7_1,x7_0,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b36x : Impossible 7 1 s7_1b9b36 := rotate_impossible sym7_3 (z := s7_1b9b27) (by simp only [s7_1b9b36,x7_0,x7_1,x7_2,x7_3,x7_4,y7_23,y7_31,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b9b27x

def s7_1b9b37 : List Sig := [y7_18,x7_0,x7_3,y7_23,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b37x : Impossible 7 1 s7_1b9b37 := impPerm (z := s7_1b4b35) (by decide +kernel) s7_1b4b35x

def s7_1b9b38 : List Sig := [y7_19,x7_0,x7_3,y7_23,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b38x : Impossible 7 1 s7_1b9b38 := impPerm (z := s7_1b5b38) (by decide +kernel) s7_1b5b38x

def s7_1b9b39 : List Sig := [y7_20,x7_0,x7_4,y7_23,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b39x : Impossible 7 1 s7_1b9b39 := rotate_impossible sym7_1 (z := s7_1b4b35) (by simp only [s7_1b9b39,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b35x

def s7_1b9b40 : List Sig := [y7_21,x7_0,x7_4,y7_23,x7_1,x7_2,x7_3]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b40x : Impossible 7 1 s7_1b9b40 := rotate_impossible sym7_1 (z := s7_1b5b38) (by simp only [s7_1b9b40,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_23,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b38x

def s7_1b9b41 : List Sig := [y7_32,x7_3,x7_4,y7_23,x7_1,x7_2,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b41x : Impossible 7 1 s7_1b9b41 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b42 : List Sig := [y7_33,x7_3,x7_4,y7_23,x7_1,x7_2,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9b42x : Impossible 7 1 s7_1b9b42 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b9b : List (List Sig) := [s7_1b9b7,s7_1b9b8,s7_1b9b9,s7_1b9b10,s7_1b9b11,s7_1b9b12,s7_1b9b13,s7_1b9b14,s7_1b9b15,s7_1b9b16,s7_1b9b17,s7_1b9b18,s7_1b9b19,s7_1b9b20,s7_1b9b21,s7_1b9b22,s7_1b9b23,s7_1b9b24,s7_1b9b25,s7_1b9b26,s7_1b9b27,s7_1b9b28,s7_1b9b29,s7_1b9b30,s7_1b9b31,s7_1b9b32,s7_1b9b33,s7_1b9b34,s7_1b9b35,s7_1b9b36,s7_1b9b37,s7_1b9b38,s7_1b9b39,s7_1b9b40,s7_1b9b41,s7_1b9b42]

lemma s7_1b9bx (v : List Sig) (h : (!s7_1b9b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b9b := by simpa using h
  simp only [s7_1b9b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b9b7x
  · exact s7_1b9b8x
  · exact s7_1b9b9x
  · exact s7_1b9b10x
  · exact s7_1b9b11x
  · exact s7_1b9b12x
  · exact s7_1b9b13x
  · exact s7_1b9b14x
  · exact s7_1b9b15x
  · exact s7_1b9b16x
  · exact s7_1b9b17x
  · exact s7_1b9b18x
  · exact s7_1b9b19x
  · exact s7_1b9b20x
  · exact s7_1b9b21x
  · exact s7_1b9b22x
  · exact s7_1b9b23x
  · exact s7_1b9b24x
  · exact s7_1b9b25x
  · exact s7_1b9b26x
  · exact s7_1b9b27x
  · exact s7_1b9b28x
  · exact s7_1b9b29x
  · exact s7_1b9b30x
  · exact s7_1b9b31x
  · exact s7_1b9b32x
  · exact s7_1b9b33x
  · exact s7_1b9b34x
  · exact s7_1b9b35x
  · exact s7_1b9b36x
  · exact s7_1b9b37x
  · exact s7_1b9b38x
  · exact s7_1b9b39x
  · exact s7_1b9b40x
  · exact s7_1b9b41x
  · exact s7_1b9b42x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b9x : Impossible 8 1 s7_1b9 := exclude_step (u := fun v => !s7_1b9u.contains v) (b := fun v => !s7_1b9b.contains v) (by decide +kernel) s7_1b9ux s7_1b9bx (by decide +kernel)

def s7_1b10 : List Sig := [bin false (r7.getD 1 zero) (r7.getD 3 zero),r7.getD 1 zero,r7.getD 3 zero,r7.getD 0 zero,r7.getD 2 zero,r7.getD 4 zero]

def s7_1b10u0 : List Sig := [y7_92,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u0x : Impossible 7 0 s7_1b10u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10u1 : List Sig := [y7_92,y7_24,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u1x : Impossible 7 0 s7_1b10u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10u2 : List Sig := [y7_34,x7_1,y7_24,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u2x : Impossible 7 0 s7_1b10u2 := impPerm (z := s7_1u1b20) (by decide +kernel) s7_1u1b20x

def s7_1b10u3 : List Sig := [y7_43,x7_3,y7_24,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u3x : Impossible 7 0 s7_1b10u3 := impPerm (z := s7_1u3b18) (by decide +kernel) s7_1u3b18x

def s7_1b10u4 : List Sig := [y7_5,x7_0,y7_24,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u4x : Impossible 7 0 s7_1b10u4 := impPerm (z := s7_1u0b26) (by decide +kernel) s7_1u0b26x

def s7_1b10u5 : List Sig := [y7_53,x7_2,y7_24,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u5x : Impossible 7 0 s7_1b10u5 := rotate_impossible sym7_2 (z := s7_1u1b30) (by simp only [s7_1b10u5,x7_0,x7_1,x7_2,x7_3,x7_4,y7_24,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b30x

def s7_1b10u6 : List Sig := [y7_54,x7_4,y7_24,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10u6x : Impossible 7 0 s7_1b10u6 := rotate_impossible sym7_1 (z := s7_1u3b32) (by simp only [s7_1b10u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_24,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b32x

def s7_1b10u : List (List Sig) := [s7_1b10u0,s7_1b10u1,s7_1b10u2,s7_1b10u3,s7_1b10u4,s7_1b10u5,s7_1b10u6]

lemma s7_1b10ux (v : List Sig) (h : (!s7_1b10u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b10u := by simpa using h
  simp only [s7_1b10u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b10u0x
  · exact s7_1b10u1x
  · exact s7_1b10u2x
  · exact s7_1b10u3x
  · exact s7_1b10u4x
  · exact s7_1b10u5x
  · exact s7_1b10u6x

def s7_1b10b7 : List Sig := [y7_57,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b7x : Impossible 7 1 s7_1b10b7 := impPerm (z := s7_1b0b13) (by decide +kernel) s7_1b0b13x

def s7_1b10b8 : List Sig := [y7_57,y7_24,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b8x : Impossible 7 1 s7_1b10b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b9 : List Sig := [y7_93,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b9x : Impossible 7 1 s7_1b10b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b10 : List Sig := [y7_93,y7_24,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b10x : Impossible 7 1 s7_1b10b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b11 : List Sig := [y7_82,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b11x : Impossible 7 1 s7_1b10b11 := impPerm (z := s7_1b8b11) (by decide +kernel) s7_1b8b11x

def s7_1b10b12 : List Sig := [y7_82,y7_24,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b12x : Impossible 7 1 s7_1b10b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b13 : List Sig := [y7_94,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b13x : Impossible 7 1 s7_1b10b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b14 : List Sig := [y7_94,y7_24,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b14x : Impossible 7 1 s7_1b10b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b15 : List Sig := [y7_95,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b15x : Impossible 7 1 s7_1b10b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b16 : List Sig := [y7_95,y7_24,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b16x : Impossible 7 1 s7_1b10b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b17 : List Sig := [y7_96,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b17x : Impossible 7 1 s7_1b10b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b18 : List Sig := [y7_96,y7_24,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b18x : Impossible 7 1 s7_1b10b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b19 : List Sig := [y7_25,x7_1,y7_24,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b19x : Impossible 7 1 s7_1b10b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b20 : List Sig := [y7_25,x7_3,y7_24,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b20x : Impossible 7 1 s7_1b10b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b21 : List Sig := [y7_25,x7_1,x7_3,y7_24,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b21x : Impossible 7 1 s7_1b10b21 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b22 : List Sig := [y7_14,x7_1,x7_0,y7_24,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b22x : Impossible 7 1 s7_1b10b22 := impPerm (z := s7_1b0b36) (by decide +kernel) s7_1b0b36x

def s7_1b10b23 : List Sig := [y7_15,x7_1,x7_0,y7_24,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b23x : Impossible 7 1 s7_1b10b23 := impPerm (z := s7_1b1b31) (by decide +kernel) s7_1b1b31x

def s7_1b10b24 : List Sig := [y7_22,x7_1,x7_2,y7_24,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b24x : Impossible 7 1 s7_1b10b24 := impPerm (z := s7_1b8b25) (by decide +kernel) s7_1b8b25x

def s7_1b10b25 : List Sig := [y7_23,x7_1,x7_2,y7_24,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b25x : Impossible 7 1 s7_1b10b25 := impPerm (z := s7_1b9b26) (by decide +kernel) s7_1b9b26x

def s7_1b10b26 : List Sig := [y7_26,x7_1,x7_4,y7_24,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b26x : Impossible 7 1 s7_1b10b26 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b27 : List Sig := [y7_27,x7_1,x7_4,y7_24,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b27x : Impossible 7 1 s7_1b10b27 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b28 : List Sig := [y7_18,x7_3,x7_0,y7_24,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b28x : Impossible 7 1 s7_1b10b28 := impPerm (z := s7_1b4b28) (by decide +kernel) s7_1b4b28x

def s7_1b10b29 : List Sig := [y7_19,x7_3,x7_0,y7_24,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b29x : Impossible 7 1 s7_1b10b29 := impPerm (z := s7_1b5b28) (by decide +kernel) s7_1b5b28x

def s7_1b10b30 : List Sig := [y7_28,x7_3,x7_2,y7_24,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b30x : Impossible 7 1 s7_1b10b30 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b31 : List Sig := [y7_29,x7_3,x7_2,y7_24,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b31x : Impossible 7 1 s7_1b10b31 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b32 : List Sig := [y7_32,x7_4,y7_24,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b32x : Impossible 7 1 s7_1b10b32 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b33 : List Sig := [y7_32,x7_3,x7_4,y7_24,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b33x : Impossible 7 1 s7_1b10b33 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b34 : List Sig := [y7_33,x7_3,x7_4,y7_24,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b34x : Impossible 7 1 s7_1b10b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b35 : List Sig := [y7_16,x7_0,x7_2,y7_24,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b35x : Impossible 7 1 s7_1b10b35 := rotate_impossible sym7_2 (z := s7_1b0b40) (by simp only [s7_1b10b35,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_24,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b40x

def s7_1b10b36 : List Sig := [y7_17,x7_0,x7_2,y7_24,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b36x : Impossible 7 1 s7_1b10b36 := rotate_impossible sym7_2 (z := s7_1b1b35) (by simp only [s7_1b10b36,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_24,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b35x

def s7_1b10b37 : List Sig := [y7_20,x7_0,x7_4,y7_24,x7_1,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b37x : Impossible 7 1 s7_1b10b37 := rotate_impossible sym7_1 (z := s7_1b4b36) (by simp only [s7_1b10b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_24,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b36x

def s7_1b10b38 : List Sig := [y7_21,x7_0,x7_4,y7_24,x7_1,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b38x : Impossible 7 1 s7_1b10b38 := rotate_impossible sym7_1 (z := s7_1b5b39) (by simp only [s7_1b10b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_24,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b39x

def s7_1b10b39 : List Sig := [y7_30,x7_2,x7_4,y7_24,x7_1,x7_3,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b39x : Impossible 7 1 s7_1b10b39 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b40 : List Sig := [y7_31,x7_2,x7_4,y7_24,x7_1,x7_3,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10b40x : Impossible 7 1 s7_1b10b40 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b10b : List (List Sig) := [s7_1b10b7,s7_1b10b8,s7_1b10b9,s7_1b10b10,s7_1b10b11,s7_1b10b12,s7_1b10b13,s7_1b10b14,s7_1b10b15,s7_1b10b16,s7_1b10b17,s7_1b10b18,s7_1b10b19,s7_1b10b20,s7_1b10b21,s7_1b10b22,s7_1b10b23,s7_1b10b24,s7_1b10b25,s7_1b10b26,s7_1b10b27,s7_1b10b28,s7_1b10b29,s7_1b10b30,s7_1b10b31,s7_1b10b32,s7_1b10b33,s7_1b10b34,s7_1b10b35,s7_1b10b36,s7_1b10b37,s7_1b10b38,s7_1b10b39,s7_1b10b40]

lemma s7_1b10bx (v : List Sig) (h : (!s7_1b10b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b10b := by simpa using h
  simp only [s7_1b10b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b10b7x
  · exact s7_1b10b8x
  · exact s7_1b10b9x
  · exact s7_1b10b10x
  · exact s7_1b10b11x
  · exact s7_1b10b12x
  · exact s7_1b10b13x
  · exact s7_1b10b14x
  · exact s7_1b10b15x
  · exact s7_1b10b16x
  · exact s7_1b10b17x
  · exact s7_1b10b18x
  · exact s7_1b10b19x
  · exact s7_1b10b20x
  · exact s7_1b10b21x
  · exact s7_1b10b22x
  · exact s7_1b10b23x
  · exact s7_1b10b24x
  · exact s7_1b10b25x
  · exact s7_1b10b26x
  · exact s7_1b10b27x
  · exact s7_1b10b28x
  · exact s7_1b10b29x
  · exact s7_1b10b30x
  · exact s7_1b10b31x
  · exact s7_1b10b32x
  · exact s7_1b10b33x
  · exact s7_1b10b34x
  · exact s7_1b10b35x
  · exact s7_1b10b36x
  · exact s7_1b10b37x
  · exact s7_1b10b38x
  · exact s7_1b10b39x
  · exact s7_1b10b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b10x : Impossible 8 1 s7_1b10 := exclude_step (u := fun v => !s7_1b10u.contains v) (b := fun v => !s7_1b10b.contains v) (by decide +kernel) s7_1b10ux s7_1b10bx (by decide +kernel)

def s7_1b11 : List Sig := [bin true (r7.getD 1 zero) (r7.getD 3 zero),r7.getD 1 zero,r7.getD 3 zero,r7.getD 0 zero,r7.getD 2 zero,r7.getD 4 zero]

def s7_1b11u0 : List Sig := [y7_97,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u0x : Impossible 7 0 s7_1b11u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11u1 : List Sig := [y7_97,y7_25,x7_1,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u1x : Impossible 7 0 s7_1b11u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11u2 : List Sig := [y7_34,x7_1,y7_25,x7_3,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u2x : Impossible 7 0 s7_1b11u2 := impPerm (z := s7_1u1b21) (by decide +kernel) s7_1u1b21x

def s7_1b11u3 : List Sig := [y7_43,x7_3,y7_25,x7_1,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u3x : Impossible 7 0 s7_1b11u3 := impPerm (z := s7_1u3b19) (by decide +kernel) s7_1u3b19x

def s7_1b11u4 : List Sig := [y7_5,x7_0,y7_25,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u4x : Impossible 7 0 s7_1b11u4 := impPerm (z := s7_1u0b27) (by decide +kernel) s7_1u0b27x

def s7_1b11u5 : List Sig := [y7_53,x7_2,y7_25,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u5x : Impossible 7 0 s7_1b11u5 := rotate_impossible sym7_2 (z := s7_1u1b31) (by simp only [s7_1b11u5,x7_0,x7_1,x7_2,x7_3,x7_4,y7_25,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b31x

def s7_1b11u6 : List Sig := [y7_54,x7_4,y7_25,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11u6x : Impossible 7 0 s7_1b11u6 := rotate_impossible sym7_1 (z := s7_1u3b33) (by simp only [s7_1b11u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_25,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b33x

def s7_1b11u : List (List Sig) := [s7_1b11u0,s7_1b11u1,s7_1b11u2,s7_1b11u3,s7_1b11u4,s7_1b11u5,s7_1b11u6]

lemma s7_1b11ux (v : List Sig) (h : (!s7_1b11u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b11u := by simpa using h
  simp only [s7_1b11u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b11u0x
  · exact s7_1b11u1x
  · exact s7_1b11u2x
  · exact s7_1b11u3x
  · exact s7_1b11u4x
  · exact s7_1b11u5x
  · exact s7_1b11u6x

def s7_1b11b7 : List Sig := [y7_98,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b7x : Impossible 7 1 s7_1b11b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b8 : List Sig := [y7_98,y7_25,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b8x : Impossible 7 1 s7_1b11b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b9 : List Sig := [y7_65,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b9x : Impossible 7 1 s7_1b11b9 := impPerm (z := s7_1b1b13) (by decide +kernel) s7_1b1b13x

def s7_1b11b10 : List Sig := [y7_65,y7_25,x7_0,x7_1,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b10x : Impossible 7 1 s7_1b11b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b11 : List Sig := [y7_99,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b11x : Impossible 7 1 s7_1b11b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b12 : List Sig := [y7_99,y7_25,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b12x : Impossible 7 1 s7_1b11b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b13 : List Sig := [y7_89,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b13x : Impossible 7 1 s7_1b11b13 := impPerm (z := s7_1b9b13) (by decide +kernel) s7_1b9b13x

def s7_1b11b14 : List Sig := [y7_89,y7_25,x7_2,x7_1,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b14x : Impossible 7 1 s7_1b11b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b15 : List Sig := [y7_100,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b15x : Impossible 7 1 s7_1b11b15 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b16 : List Sig := [y7_100,y7_25,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b16x : Impossible 7 1 s7_1b11b16 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b17 : List Sig := [y7_100,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b17x : Impossible 7 1 s7_1b11b17 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b18 : List Sig := [y7_100,y7_25,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b18x : Impossible 7 1 s7_1b11b18 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b19 : List Sig := [y7_101,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b19x : Impossible 7 1 s7_1b11b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b20 : List Sig := [y7_101,y7_25,x7_4,x7_1,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b20x : Impossible 7 1 s7_1b11b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b21 : List Sig := [y7_24,x7_1,y7_25,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b21x : Impossible 7 1 s7_1b11b21 := impPerm (z := s7_1b10b19) (by decide +kernel) s7_1b10b19x

def s7_1b11b22 : List Sig := [y7_24,x7_3,y7_25,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b22x : Impossible 7 1 s7_1b11b22 := impPerm (z := s7_1b10b20) (by decide +kernel) s7_1b10b20x

def s7_1b11b23 : List Sig := [y7_24,x7_1,x7_3,y7_25,x7_0,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b23x : Impossible 7 1 s7_1b11b23 := impPerm (z := s7_1b10b21) (by decide +kernel) s7_1b10b21x

def s7_1b11b24 : List Sig := [y7_14,x7_1,x7_0,y7_25,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b24x : Impossible 7 1 s7_1b11b24 := impPerm (z := s7_1b0b37) (by decide +kernel) s7_1b0b37x

def s7_1b11b25 : List Sig := [y7_15,x7_1,x7_0,y7_25,x7_3,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b25x : Impossible 7 1 s7_1b11b25 := impPerm (z := s7_1b1b32) (by decide +kernel) s7_1b1b32x

def s7_1b11b26 : List Sig := [y7_22,x7_1,x7_2,y7_25,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b26x : Impossible 7 1 s7_1b11b26 := impPerm (z := s7_1b8b26) (by decide +kernel) s7_1b8b26x

def s7_1b11b27 : List Sig := [y7_23,x7_1,x7_2,y7_25,x7_3,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b27x : Impossible 7 1 s7_1b11b27 := impPerm (z := s7_1b9b27) (by decide +kernel) s7_1b9b27x

def s7_1b11b28 : List Sig := [y7_26,x7_1,x7_4,y7_25,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b28x : Impossible 7 1 s7_1b11b28 := rotate_impossible sym7_1 (z := s7_1b10b27) (by simp only [s7_1b11b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_25,y7_26,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b10b27x

def s7_1b11b29 : List Sig := [y7_27,x7_1,x7_4,y7_25,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b29x : Impossible 7 1 s7_1b11b29 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b30 : List Sig := [y7_18,x7_3,x7_0,y7_25,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b30x : Impossible 7 1 s7_1b11b30 := impPerm (z := s7_1b4b29) (by decide +kernel) s7_1b4b29x

def s7_1b11b31 : List Sig := [y7_19,x7_0,y7_25,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b31x : Impossible 7 1 s7_1b11b31 := impPerm (z := s7_1b5b29) (by decide +kernel) s7_1b5b29x

def s7_1b11b32 : List Sig := [y7_19,x7_3,x7_0,y7_25,x7_1,x7_2,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b32x : Impossible 7 1 s7_1b11b32 := impPerm (z := s7_1b5b30) (by decide +kernel) s7_1b5b30x

def s7_1b11b33 : List Sig := [y7_28,x7_3,x7_2,y7_25,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b33x : Impossible 7 1 s7_1b11b33 := rotate_impossible sym7_2 (z := s7_1b10b31) (by simp only [s7_1b11b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_25,y7_28,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10b31x

def s7_1b11b34 : List Sig := [y7_29,x7_3,x7_2,y7_25,x7_1,x7_0,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b34x : Impossible 7 1 s7_1b11b34 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b35 : List Sig := [y7_32,x7_3,x7_4,y7_25,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b35x : Impossible 7 1 s7_1b11b35 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b36 : List Sig := [y7_33,x7_3,x7_4,y7_25,x7_1,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b36x : Impossible 7 1 s7_1b11b36 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b37 : List Sig := [y7_16,x7_0,x7_2,y7_25,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b37x : Impossible 7 1 s7_1b11b37 := rotate_impossible sym7_2 (z := s7_1b0b41) (by simp only [s7_1b11b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_25,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b41x

def s7_1b11b38 : List Sig := [y7_17,x7_0,x7_2,y7_25,x7_1,x7_3,x7_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b38x : Impossible 7 1 s7_1b11b38 := rotate_impossible sym7_2 (z := s7_1b1b36) (by simp only [s7_1b11b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_25,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b36x

def s7_1b11b39 : List Sig := [y7_20,x7_0,x7_4,y7_25,x7_1,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b39x : Impossible 7 1 s7_1b11b39 := rotate_impossible sym7_1 (z := s7_1b4b37) (by simp only [s7_1b11b39,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_25,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b37x

def s7_1b11b40 : List Sig := [y7_21,x7_0,x7_4,y7_25,x7_1,x7_3,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b40x : Impossible 7 1 s7_1b11b40 := rotate_impossible sym7_1 (z := s7_1b5b40) (by simp only [s7_1b11b40,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_25,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b40x

def s7_1b11b41 : List Sig := [y7_30,x7_2,x7_4,y7_25,x7_1,x7_3,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b41x : Impossible 7 1 s7_1b11b41 := rotate_impossible sym7_3 (z := s7_1b10b40) (by simp only [s7_1b11b41,x7_0,x7_1,x7_2,x7_3,x7_4,y7_25,y7_30,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b10b40x

def s7_1b11b42 : List Sig := [y7_31,x7_2,x7_4,y7_25,x7_1,x7_3,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11b42x : Impossible 7 1 s7_1b11b42 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b11b : List (List Sig) := [s7_1b11b7,s7_1b11b8,s7_1b11b9,s7_1b11b10,s7_1b11b11,s7_1b11b12,s7_1b11b13,s7_1b11b14,s7_1b11b15,s7_1b11b16,s7_1b11b17,s7_1b11b18,s7_1b11b19,s7_1b11b20,s7_1b11b21,s7_1b11b22,s7_1b11b23,s7_1b11b24,s7_1b11b25,s7_1b11b26,s7_1b11b27,s7_1b11b28,s7_1b11b29,s7_1b11b30,s7_1b11b31,s7_1b11b32,s7_1b11b33,s7_1b11b34,s7_1b11b35,s7_1b11b36,s7_1b11b37,s7_1b11b38,s7_1b11b39,s7_1b11b40,s7_1b11b41,s7_1b11b42]

lemma s7_1b11bx (v : List Sig) (h : (!s7_1b11b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b11b := by simpa using h
  simp only [s7_1b11b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b11b7x
  · exact s7_1b11b8x
  · exact s7_1b11b9x
  · exact s7_1b11b10x
  · exact s7_1b11b11x
  · exact s7_1b11b12x
  · exact s7_1b11b13x
  · exact s7_1b11b14x
  · exact s7_1b11b15x
  · exact s7_1b11b16x
  · exact s7_1b11b17x
  · exact s7_1b11b18x
  · exact s7_1b11b19x
  · exact s7_1b11b20x
  · exact s7_1b11b21x
  · exact s7_1b11b22x
  · exact s7_1b11b23x
  · exact s7_1b11b24x
  · exact s7_1b11b25x
  · exact s7_1b11b26x
  · exact s7_1b11b27x
  · exact s7_1b11b28x
  · exact s7_1b11b29x
  · exact s7_1b11b30x
  · exact s7_1b11b31x
  · exact s7_1b11b32x
  · exact s7_1b11b33x
  · exact s7_1b11b34x
  · exact s7_1b11b35x
  · exact s7_1b11b36x
  · exact s7_1b11b37x
  · exact s7_1b11b38x
  · exact s7_1b11b39x
  · exact s7_1b11b40x
  · exact s7_1b11b41x
  · exact s7_1b11b42x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b11x : Impossible 8 1 s7_1b11 := exclude_step (u := fun v => !s7_1b11u.contains v) (b := fun v => !s7_1b11b.contains v) (by decide +kernel) s7_1b11ux s7_1b11bx (by decide +kernel)

def s7_1b12 : List Sig := [bin false (r7.getD 1 zero) (r7.getD 4 zero),r7.getD 1 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 2 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b12x : Impossible 8 1 s7_1b12 := rotate_impossible sym7_1 (z := s7_1b10) (by simp only [s7_1b12,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b10x

def s7_1b13 : List Sig := [bin true (r7.getD 1 zero) (r7.getD 4 zero),r7.getD 1 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 2 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b13x : Impossible 8 1 s7_1b13 := rotate_impossible sym7_1 (z := s7_1b11) (by simp only [s7_1b13,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b11x

def s7_1b14 : List Sig := [bin false (r7.getD 2 zero) (r7.getD 3 zero),r7.getD 2 zero,r7.getD 3 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b14x : Impossible 8 1 s7_1b14 := rotate_impossible sym7_2 (z := s7_1b10) (by simp only [s7_1b14,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10x

def s7_1b15 : List Sig := [bin true (r7.getD 2 zero) (r7.getD 3 zero),r7.getD 2 zero,r7.getD 3 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 4 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b15x : Impossible 8 1 s7_1b15 := rotate_impossible sym7_2 (z := s7_1b11) (by simp only [s7_1b15,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b11x

def s7_1b16 : List Sig := [bin false (r7.getD 2 zero) (r7.getD 4 zero),r7.getD 2 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b16x : Impossible 8 1 s7_1b16 := rotate_impossible sym7_3 (z := s7_1b10) (by simp only [s7_1b16,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b10x

def s7_1b17 : List Sig := [bin true (r7.getD 2 zero) (r7.getD 4 zero),r7.getD 2 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 3 zero]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b17x : Impossible 8 1 s7_1b17 := rotate_impossible sym7_3 (z := s7_1b11) (by simp only [s7_1b17,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b11x

def s7_1b18 : List Sig := [bin false (r7.getD 3 zero) (r7.getD 4 zero),r7.getD 3 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero]

def s7_1b18u0 : List Sig := [y7_102,x7_3,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u0x : Impossible 7 0 s7_1b18u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18u1 : List Sig := [y7_102,y7_32,x7_3,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u1x : Impossible 7 0 s7_1b18u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18u2 : List Sig := [y7_43,x7_3,y7_32,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u2x : Impossible 7 0 s7_1b18u2 := impPerm (z := s7_1u3b22) (by decide +kernel) s7_1u3b22x

def s7_1b18u3 : List Sig := [y7_54,x7_4,y7_32,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u3x : Impossible 7 0 s7_1b18u3 := rotate_impossible sym7_1 (z := s7_1u3b22) (by simp only [s7_1b18u3,x7_0,x7_1,x7_2,x7_3,x7_4,y7_32,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b22x

def s7_1b18u4 : List Sig := [y7_5,x7_0,y7_32,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u4x : Impossible 7 0 s7_1b18u4 := impPerm (z := s7_1u0b34) (by decide +kernel) s7_1u0b34x

def s7_1b18u5 : List Sig := [y7_34,x7_1,y7_32,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u5x : Impossible 7 0 s7_1b18u5 := impPerm (z := s7_1u1b34) (by decide +kernel) s7_1u1b34x

def s7_1b18u6 : List Sig := [y7_53,x7_2,y7_32,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18u6x : Impossible 7 0 s7_1b18u6 := rotate_impossible sym7_2 (z := s7_1u1b34) (by simp only [s7_1b18u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_32,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b34x

def s7_1b18u : List (List Sig) := [s7_1b18u0,s7_1b18u1,s7_1b18u2,s7_1b18u3,s7_1b18u4,s7_1b18u5,s7_1b18u6]

lemma s7_1b18ux (v : List Sig) (h : (!s7_1b18u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b18u := by simpa using h
  simp only [s7_1b18u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b18u0x
  · exact s7_1b18u1x
  · exact s7_1b18u2x
  · exact s7_1b18u3x
  · exact s7_1b18u4x
  · exact s7_1b18u5x
  · exact s7_1b18u6x

def s7_1b18b7 : List Sig := [y7_72,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b7x : Impossible 7 1 s7_1b18b7 := impPerm (z := s7_1b4b15) (by decide +kernel) s7_1b4b15x

def s7_1b18b8 : List Sig := [y7_72,y7_32,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b8x : Impossible 7 1 s7_1b18b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b9 : List Sig := [y7_103,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b9x : Impossible 7 1 s7_1b18b9 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b10 : List Sig := [y7_103,y7_32,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b10x : Impossible 7 1 s7_1b18b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b11 : List Sig := [y7_95,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b11x : Impossible 7 1 s7_1b18b11 := impPerm (z := s7_1b10b15) (by decide +kernel) s7_1b10b15x

def s7_1b18b12 : List Sig := [y7_95,y7_32,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b12x : Impossible 7 1 s7_1b18b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b13 : List Sig := [y7_104,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b13x : Impossible 7 1 s7_1b18b13 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b14 : List Sig := [y7_104,y7_32,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b14x : Impossible 7 1 s7_1b18b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b15 : List Sig := [y7_105,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b15x : Impossible 7 1 s7_1b18b15 := rotate_impossible sym7_2 (z := s7_1b10b15) (by simp only [s7_1b18b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_105,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10b15x

def s7_1b18b16 : List Sig := [y7_105,y7_32,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b16x : Impossible 7 1 s7_1b18b16 := rotate_impossible sym7_2 (z := s7_1b18b12) (by simp only [s7_1b18b16,x7_0,x7_1,x7_2,x7_3,x7_4,y7_105,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b18b12x

def s7_1b18b17 : List Sig := [y7_106,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b17x : Impossible 7 1 s7_1b18b17 := rotate_impossible sym7_2 (z := s7_1b18b13) (by simp only [s7_1b18b17,x7_0,x7_1,x7_2,x7_3,x7_4,y7_106,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b18b13x

def s7_1b18b18 : List Sig := [y7_106,y7_32,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b18x : Impossible 7 1 s7_1b18b18 := rotate_impossible sym7_2 (z := s7_1b18b14) (by simp only [s7_1b18b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_106,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b18b14x

def s7_1b18b19 : List Sig := [y7_33,y7_32,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b19x : Impossible 7 1 s7_1b18b19 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b20 : List Sig := [y7_33,x7_3,y7_32,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b20x : Impossible 7 1 s7_1b18b20 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b21 : List Sig := [y7_33,x7_4,y7_32,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b21x : Impossible 7 1 s7_1b18b21 := rotate_impossible sym7_1 (z := s7_1b18b20) (by simp only [s7_1b18b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_32,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b18b20x

def s7_1b18b22 : List Sig := [y7_33,x7_3,x7_4,y7_32,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b22x : Impossible 7 1 s7_1b18b22 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b18b23 : List Sig := [y7_18,x7_3,x7_0,y7_32,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b23x : Impossible 7 1 s7_1b18b23 := impPerm (z := s7_1b4b32) (by decide +kernel) s7_1b4b32x

def s7_1b18b24 : List Sig := [y7_19,x7_0,y7_32,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b24x : Impossible 7 1 s7_1b18b24 := impPerm (z := s7_1b5b34) (by decide +kernel) s7_1b5b34x

def s7_1b18b25 : List Sig := [y7_19,x7_3,x7_0,y7_32,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b25x : Impossible 7 1 s7_1b18b25 := impPerm (z := s7_1b5b35) (by decide +kernel) s7_1b5b35x

def s7_1b18b26 : List Sig := [y7_24,x7_1,y7_32,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b26x : Impossible 7 1 s7_1b18b26 := impPerm (z := s7_1b10b32) (by decide +kernel) s7_1b10b32x

def s7_1b18b27 : List Sig := [y7_24,x7_3,x7_1,y7_32,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b27x : Impossible 7 1 s7_1b18b27 := impPerm (z := s7_1b10b33) (by decide +kernel) s7_1b10b33x

def s7_1b18b28 : List Sig := [y7_25,x7_3,x7_1,y7_32,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b28x : Impossible 7 1 s7_1b18b28 := impPerm (z := s7_1b11b35) (by decide +kernel) s7_1b11b35x

def s7_1b18b29 : List Sig := [y7_28,x7_2,y7_32,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b29x : Impossible 7 1 s7_1b18b29 := rotate_impossible sym7_2 (z := s7_1b10b32) (by simp only [s7_1b18b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_28,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10b32x

def s7_1b18b30 : List Sig := [y7_28,x7_3,x7_2,y7_32,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b30x : Impossible 7 1 s7_1b18b30 := rotate_impossible sym7_2 (z := s7_1b10b33) (by simp only [s7_1b18b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_28,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10b33x

def s7_1b18b31 : List Sig := [y7_29,x7_3,x7_2,y7_32,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b31x : Impossible 7 1 s7_1b18b31 := rotate_impossible sym7_2 (z := s7_1b11b35) (by simp only [s7_1b18b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_29,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b11b35x

def s7_1b18b32 : List Sig := [y7_20,x7_4,x7_0,y7_32,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b32x : Impossible 7 1 s7_1b18b32 := rotate_impossible sym7_1 (z := s7_1b4b32) (by simp only [s7_1b18b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b32x

def s7_1b18b33 : List Sig := [y7_21,x7_0,y7_32,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b33x : Impossible 7 1 s7_1b18b33 := rotate_impossible sym7_1 (z := s7_1b5b34) (by simp only [s7_1b18b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b34x

def s7_1b18b34 : List Sig := [y7_21,x7_4,x7_0,y7_32,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b34x : Impossible 7 1 s7_1b18b34 := rotate_impossible sym7_1 (z := s7_1b5b35) (by simp only [s7_1b18b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b35x

def s7_1b18b35 : List Sig := [y7_26,x7_1,y7_32,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b35x : Impossible 7 1 s7_1b18b35 := rotate_impossible sym7_1 (z := s7_1b10b32) (by simp only [s7_1b18b35,x7_0,x7_1,x7_2,x7_3,x7_4,y7_26,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b10b32x

def s7_1b18b36 : List Sig := [y7_26,x7_4,x7_1,y7_32,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b36x : Impossible 7 1 s7_1b18b36 := rotate_impossible sym7_1 (z := s7_1b10b33) (by simp only [s7_1b18b36,x7_0,x7_1,x7_2,x7_3,x7_4,y7_26,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b10b33x

def s7_1b18b37 : List Sig := [y7_27,x7_4,x7_1,y7_32,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b37x : Impossible 7 1 s7_1b18b37 := rotate_impossible sym7_1 (z := s7_1b11b35) (by simp only [s7_1b18b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_27,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b11b35x

def s7_1b18b38 : List Sig := [y7_30,x7_2,y7_32,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b38x : Impossible 7 1 s7_1b18b38 := rotate_impossible sym7_3 (z := s7_1b10b32) (by simp only [s7_1b18b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b10b32x

def s7_1b18b39 : List Sig := [y7_30,x7_4,x7_2,y7_32,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b39x : Impossible 7 1 s7_1b18b39 := rotate_impossible sym7_3 (z := s7_1b10b33) (by simp only [s7_1b18b39,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b10b33x

def s7_1b18b40 : List Sig := [y7_31,x7_4,x7_2,y7_32,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b40x : Impossible 7 1 s7_1b18b40 := rotate_impossible sym7_3 (z := s7_1b11b35) (by simp only [s7_1b18b40,x7_0,x7_1,x7_2,x7_3,x7_4,y7_31,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b11b35x

def s7_1b18b41 : List Sig := [y7_14,x7_0,x7_1,y7_32,x7_3,x7_4,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b41x : Impossible 7 1 s7_1b18b41 := impPerm (z := s7_1b0b44) (by decide +kernel) s7_1b0b44x

def s7_1b18b42 : List Sig := [y7_15,x7_0,x7_1,y7_32,x7_3,x7_4,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b42x : Impossible 7 1 s7_1b18b42 := impPerm (z := s7_1b1b39) (by decide +kernel) s7_1b1b39x

def s7_1b18b43 : List Sig := [y7_16,x7_0,x7_2,y7_32,x7_3,x7_4,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b43x : Impossible 7 1 s7_1b18b43 := rotate_impossible sym7_2 (z := s7_1b0b44) (by simp only [s7_1b18b43,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b44x

def s7_1b18b44 : List Sig := [y7_17,x7_0,x7_2,y7_32,x7_3,x7_4,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b44x : Impossible 7 1 s7_1b18b44 := rotate_impossible sym7_2 (z := s7_1b1b39) (by simp only [s7_1b18b44,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_32,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b39x

def s7_1b18b45 : List Sig := [y7_22,x7_1,x7_2,y7_32,x7_3,x7_4,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b45x : Impossible 7 1 s7_1b18b45 := impPerm (z := s7_1b8b39) (by decide +kernel) s7_1b8b39x

def s7_1b18b46 : List Sig := [y7_23,x7_1,x7_2,y7_32,x7_3,x7_4,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18b46x : Impossible 7 1 s7_1b18b46 := impPerm (z := s7_1b9b41) (by decide +kernel) s7_1b9b41x

def s7_1b18b : List (List Sig) := [s7_1b18b7,s7_1b18b8,s7_1b18b9,s7_1b18b10,s7_1b18b11,s7_1b18b12,s7_1b18b13,s7_1b18b14,s7_1b18b15,s7_1b18b16,s7_1b18b17,s7_1b18b18,s7_1b18b19,s7_1b18b20,s7_1b18b21,s7_1b18b22,s7_1b18b23,s7_1b18b24,s7_1b18b25,s7_1b18b26,s7_1b18b27,s7_1b18b28,s7_1b18b29,s7_1b18b30,s7_1b18b31,s7_1b18b32,s7_1b18b33,s7_1b18b34,s7_1b18b35,s7_1b18b36,s7_1b18b37,s7_1b18b38,s7_1b18b39,s7_1b18b40,s7_1b18b41,s7_1b18b42,s7_1b18b43,s7_1b18b44,s7_1b18b45,s7_1b18b46]

lemma s7_1b18bx (v : List Sig) (h : (!s7_1b18b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b18b := by simpa using h
  simp only [s7_1b18b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b18b7x
  · exact s7_1b18b8x
  · exact s7_1b18b9x
  · exact s7_1b18b10x
  · exact s7_1b18b11x
  · exact s7_1b18b12x
  · exact s7_1b18b13x
  · exact s7_1b18b14x
  · exact s7_1b18b15x
  · exact s7_1b18b16x
  · exact s7_1b18b17x
  · exact s7_1b18b18x
  · exact s7_1b18b19x
  · exact s7_1b18b20x
  · exact s7_1b18b21x
  · exact s7_1b18b22x
  · exact s7_1b18b23x
  · exact s7_1b18b24x
  · exact s7_1b18b25x
  · exact s7_1b18b26x
  · exact s7_1b18b27x
  · exact s7_1b18b28x
  · exact s7_1b18b29x
  · exact s7_1b18b30x
  · exact s7_1b18b31x
  · exact s7_1b18b32x
  · exact s7_1b18b33x
  · exact s7_1b18b34x
  · exact s7_1b18b35x
  · exact s7_1b18b36x
  · exact s7_1b18b37x
  · exact s7_1b18b38x
  · exact s7_1b18b39x
  · exact s7_1b18b40x
  · exact s7_1b18b41x
  · exact s7_1b18b42x
  · exact s7_1b18b43x
  · exact s7_1b18b44x
  · exact s7_1b18b45x
  · exact s7_1b18b46x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b18x : Impossible 8 1 s7_1b18 := exclude_step (u := fun v => !s7_1b18u.contains v) (b := fun v => !s7_1b18b.contains v) (by decide +kernel) s7_1b18ux s7_1b18bx (by decide +kernel)

def s7_1b19 : List Sig := [bin true (r7.getD 3 zero) (r7.getD 4 zero),r7.getD 3 zero,r7.getD 4 zero,r7.getD 0 zero,r7.getD 1 zero,r7.getD 2 zero]

def s7_1b19u0 : List Sig := [y7_107,x7_3,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u0x : Impossible 7 0 s7_1b19u0 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19u1 : List Sig := [y7_107,y7_33,x7_3,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u1x : Impossible 7 0 s7_1b19u1 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19u2 : List Sig := [y7_43,x7_3,y7_33,x7_4,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u2x : Impossible 7 0 s7_1b19u2 := impPerm (z := s7_1u3b23) (by decide +kernel) s7_1u3b23x

def s7_1b19u3 : List Sig := [y7_54,x7_4,y7_33,x7_3,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u3x : Impossible 7 0 s7_1b19u3 := rotate_impossible sym7_1 (z := s7_1u3b23) (by simp only [s7_1b19u3,x7_0,x7_1,x7_2,x7_3,x7_4,y7_33,y7_54,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1u3b23x

def s7_1b19u4 : List Sig := [y7_5,x7_0,y7_33,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u4x : Impossible 7 0 s7_1b19u4 := impPerm (z := s7_1u0b35) (by decide +kernel) s7_1u0b35x

def s7_1b19u5 : List Sig := [y7_34,x7_1,y7_33,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u5x : Impossible 7 0 s7_1b19u5 := impPerm (z := s7_1u1b35) (by decide +kernel) s7_1u1b35x

def s7_1b19u6 : List Sig := [y7_53,x7_2,y7_33,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19u6x : Impossible 7 0 s7_1b19u6 := rotate_impossible sym7_2 (z := s7_1u1b35) (by simp only [s7_1b19u6,x7_0,x7_1,x7_2,x7_3,x7_4,y7_33,y7_53,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1u1b35x

def s7_1b19u : List (List Sig) := [s7_1b19u0,s7_1b19u1,s7_1b19u2,s7_1b19u3,s7_1b19u4,s7_1b19u5,s7_1b19u6]

lemma s7_1b19ux (v : List Sig) (h : (!s7_1b19u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s7_1b19u := by simpa using h
  simp only [s7_1b19u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b19u0x
  · exact s7_1b19u1x
  · exact s7_1b19u2x
  · exact s7_1b19u3x
  · exact s7_1b19u4x
  · exact s7_1b19u5x
  · exact s7_1b19u6x

def s7_1b19b7 : List Sig := [y7_108,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b7x : Impossible 7 1 s7_1b19b7 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b8 : List Sig := [y7_108,y7_33,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b8x : Impossible 7 1 s7_1b19b8 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b9 : List Sig := [y7_79,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b9x : Impossible 7 1 s7_1b19b9 := impPerm (z := s7_1b5b17) (by decide +kernel) s7_1b5b17x

def s7_1b19b10 : List Sig := [y7_79,y7_33,x7_0,x7_3,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b10x : Impossible 7 1 s7_1b19b10 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b11 : List Sig := [y7_109,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b11x : Impossible 7 1 s7_1b19b11 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b12 : List Sig := [y7_109,y7_33,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b12x : Impossible 7 1 s7_1b19b12 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b13 : List Sig := [y7_101,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b13x : Impossible 7 1 s7_1b19b13 := impPerm (z := s7_1b11b19) (by decide +kernel) s7_1b11b19x

def s7_1b19b14 : List Sig := [y7_101,y7_33,x7_1,x7_3,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b14x : Impossible 7 1 s7_1b19b14 := exclude_search (by decide +kernel) (by decide +kernel)

def s7_1b19b15 : List Sig := [y7_110,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b15x : Impossible 7 1 s7_1b19b15 := rotate_impossible sym7_2 (z := s7_1b19b11) (by simp only [s7_1b19b15,x7_0,x7_1,x7_2,x7_3,x7_4,y7_110,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b19b11x

def s7_1b19b16 : List Sig := [y7_110,y7_33,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b16x : Impossible 7 1 s7_1b19b16 := rotate_impossible sym7_2 (z := s7_1b19b12) (by simp only [s7_1b19b16,x7_0,x7_1,x7_2,x7_3,x7_4,y7_110,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b19b12x

def s7_1b19b17 : List Sig := [y7_111,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b17x : Impossible 7 1 s7_1b19b17 := rotate_impossible sym7_2 (z := s7_1b11b19) (by simp only [s7_1b19b17,x7_0,x7_1,x7_2,x7_3,x7_4,y7_111,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b11b19x

def s7_1b19b18 : List Sig := [y7_111,y7_33,x7_2,x7_3,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b18x : Impossible 7 1 s7_1b19b18 := rotate_impossible sym7_2 (z := s7_1b19b14) (by simp only [s7_1b19b18,x7_0,x7_1,x7_2,x7_3,x7_4,y7_111,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b19b14x

def s7_1b19b19 : List Sig := [y7_32,y7_33,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b19x : Impossible 7 1 s7_1b19b19 := impPerm (z := s7_1b18b19) (by decide +kernel) s7_1b18b19x

def s7_1b19b20 : List Sig := [y7_32,x7_3,y7_33,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b20x : Impossible 7 1 s7_1b19b20 := impPerm (z := s7_1b18b20) (by decide +kernel) s7_1b18b20x

def s7_1b19b21 : List Sig := [y7_32,x7_4,y7_33,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b21x : Impossible 7 1 s7_1b19b21 := rotate_impossible sym7_1 (z := s7_1b18b20) (by simp only [s7_1b19b21,x7_0,x7_1,x7_2,x7_3,x7_4,y7_32,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b18b20x

def s7_1b19b22 : List Sig := [y7_32,x7_3,x7_4,y7_33,x7_0,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b22x : Impossible 7 1 s7_1b19b22 := impPerm (z := s7_1b18b22) (by decide +kernel) s7_1b18b22x

def s7_1b19b23 : List Sig := [y7_18,x7_3,x7_0,y7_33,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b23x : Impossible 7 1 s7_1b19b23 := impPerm (z := s7_1b4b33) (by decide +kernel) s7_1b4b33x

def s7_1b19b24 : List Sig := [y7_19,x7_3,x7_0,y7_33,x7_4,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b24x : Impossible 7 1 s7_1b19b24 := impPerm (z := s7_1b5b36) (by decide +kernel) s7_1b5b36x

def s7_1b19b25 : List Sig := [y7_24,x7_3,x7_1,y7_33,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b25x : Impossible 7 1 s7_1b19b25 := impPerm (z := s7_1b10b34) (by decide +kernel) s7_1b10b34x

def s7_1b19b26 : List Sig := [y7_25,x7_3,x7_1,y7_33,x7_4,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b26x : Impossible 7 1 s7_1b19b26 := impPerm (z := s7_1b11b36) (by decide +kernel) s7_1b11b36x

def s7_1b19b27 : List Sig := [y7_28,x7_3,x7_2,y7_33,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b27x : Impossible 7 1 s7_1b19b27 := rotate_impossible sym7_2 (z := s7_1b10b34) (by simp only [s7_1b19b27,x7_0,x7_1,x7_2,x7_3,x7_4,y7_28,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b10b34x

def s7_1b19b28 : List Sig := [y7_29,x7_3,x7_2,y7_33,x7_4,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b28x : Impossible 7 1 s7_1b19b28 := rotate_impossible sym7_2 (z := s7_1b11b36) (by simp only [s7_1b19b28,x7_0,x7_1,x7_2,x7_3,x7_4,y7_29,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b11b36x

def s7_1b19b29 : List Sig := [y7_20,x7_4,x7_0,y7_33,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b29x : Impossible 7 1 s7_1b19b29 := rotate_impossible sym7_1 (z := s7_1b4b33) (by simp only [s7_1b19b29,x7_0,x7_1,x7_2,x7_3,x7_4,y7_20,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b4b33x

def s7_1b19b30 : List Sig := [y7_21,x7_4,x7_0,y7_33,x7_3,x7_1,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b30x : Impossible 7 1 s7_1b19b30 := rotate_impossible sym7_1 (z := s7_1b5b36) (by simp only [s7_1b19b30,x7_0,x7_1,x7_2,x7_3,x7_4,y7_21,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b5b36x

def s7_1b19b31 : List Sig := [y7_26,x7_4,x7_1,y7_33,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b31x : Impossible 7 1 s7_1b19b31 := rotate_impossible sym7_1 (z := s7_1b10b34) (by simp only [s7_1b19b31,x7_0,x7_1,x7_2,x7_3,x7_4,y7_26,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b10b34x

def s7_1b19b32 : List Sig := [y7_27,x7_4,x7_1,y7_33,x7_3,x7_0,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b32x : Impossible 7 1 s7_1b19b32 := rotate_impossible sym7_1 (z := s7_1b11b36) (by simp only [s7_1b19b32,x7_0,x7_1,x7_2,x7_3,x7_4,y7_27,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_1_0,rot7_1_1,rot7_1_2,rot7_1_3,rot7_1_4]; decide +kernel) s7_1b11b36x

def s7_1b19b33 : List Sig := [y7_30,x7_4,x7_2,y7_33,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b33x : Impossible 7 1 s7_1b19b33 := rotate_impossible sym7_3 (z := s7_1b10b34) (by simp only [s7_1b19b33,x7_0,x7_1,x7_2,x7_3,x7_4,y7_30,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b10b34x

def s7_1b19b34 : List Sig := [y7_31,x7_4,x7_2,y7_33,x7_3,x7_0,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b34x : Impossible 7 1 s7_1b19b34 := rotate_impossible sym7_3 (z := s7_1b11b36) (by simp only [s7_1b19b34,x7_0,x7_1,x7_2,x7_3,x7_4,y7_31,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_3_0,rot7_3_1,rot7_3_2,rot7_3_3,rot7_3_4]; decide +kernel) s7_1b11b36x

def s7_1b19b35 : List Sig := [y7_14,x7_0,x7_1,y7_33,x7_3,x7_4,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b35x : Impossible 7 1 s7_1b19b35 := impPerm (z := s7_1b0b45) (by decide +kernel) s7_1b0b45x

def s7_1b19b36 : List Sig := [y7_15,x7_0,x7_1,y7_33,x7_3,x7_4,x7_2]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b36x : Impossible 7 1 s7_1b19b36 := impPerm (z := s7_1b1b40) (by decide +kernel) s7_1b1b40x

def s7_1b19b37 : List Sig := [y7_16,x7_0,x7_2,y7_33,x7_3,x7_4,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b37x : Impossible 7 1 s7_1b19b37 := rotate_impossible sym7_2 (z := s7_1b0b45) (by simp only [s7_1b19b37,x7_0,x7_1,x7_2,x7_3,x7_4,y7_16,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b0b45x

def s7_1b19b38 : List Sig := [y7_17,x7_0,x7_2,y7_33,x7_3,x7_4,x7_1]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b38x : Impossible 7 1 s7_1b19b38 := rotate_impossible sym7_2 (z := s7_1b1b40) (by simp only [s7_1b19b38,x7_0,x7_1,x7_2,x7_3,x7_4,y7_17,y7_33,List.map_cons,List.map_nil,action_bin,action_neg,rot7_2_0,rot7_2_1,rot7_2_2,rot7_2_3,rot7_2_4]; decide +kernel) s7_1b1b40x

def s7_1b19b39 : List Sig := [y7_22,x7_1,x7_2,y7_33,x7_3,x7_4,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b39x : Impossible 7 1 s7_1b19b39 := impPerm (z := s7_1b8b40) (by decide +kernel) s7_1b8b40x

def s7_1b19b40 : List Sig := [y7_23,x7_1,x7_2,y7_33,x7_3,x7_4,x7_0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19b40x : Impossible 7 1 s7_1b19b40 := impPerm (z := s7_1b9b42) (by decide +kernel) s7_1b9b42x

def s7_1b19b : List (List Sig) := [s7_1b19b7,s7_1b19b8,s7_1b19b9,s7_1b19b10,s7_1b19b11,s7_1b19b12,s7_1b19b13,s7_1b19b14,s7_1b19b15,s7_1b19b16,s7_1b19b17,s7_1b19b18,s7_1b19b19,s7_1b19b20,s7_1b19b21,s7_1b19b22,s7_1b19b23,s7_1b19b24,s7_1b19b25,s7_1b19b26,s7_1b19b27,s7_1b19b28,s7_1b19b29,s7_1b19b30,s7_1b19b31,s7_1b19b32,s7_1b19b33,s7_1b19b34,s7_1b19b35,s7_1b19b36,s7_1b19b37,s7_1b19b38,s7_1b19b39,s7_1b19b40]

lemma s7_1b19bx (v : List Sig) (h : (!s7_1b19b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s7_1b19b := by simpa using h
  simp only [s7_1b19b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b19b7x
  · exact s7_1b19b8x
  · exact s7_1b19b9x
  · exact s7_1b19b10x
  · exact s7_1b19b11x
  · exact s7_1b19b12x
  · exact s7_1b19b13x
  · exact s7_1b19b14x
  · exact s7_1b19b15x
  · exact s7_1b19b16x
  · exact s7_1b19b17x
  · exact s7_1b19b18x
  · exact s7_1b19b19x
  · exact s7_1b19b20x
  · exact s7_1b19b21x
  · exact s7_1b19b22x
  · exact s7_1b19b23x
  · exact s7_1b19b24x
  · exact s7_1b19b25x
  · exact s7_1b19b26x
  · exact s7_1b19b27x
  · exact s7_1b19b28x
  · exact s7_1b19b29x
  · exact s7_1b19b30x
  · exact s7_1b19b31x
  · exact s7_1b19b32x
  · exact s7_1b19b33x
  · exact s7_1b19b34x
  · exact s7_1b19b35x
  · exact s7_1b19b36x
  · exact s7_1b19b37x
  · exact s7_1b19b38x
  · exact s7_1b19b39x
  · exact s7_1b19b40x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s7_1b19x : Impossible 8 1 s7_1b19 := exclude_step (u := fun v => !s7_1b19u.contains v) (b := fun v => !s7_1b19b.contains v) (by decide +kernel) s7_1b19ux s7_1b19bx (by decide +kernel)

def s7_1b : List (List Sig) := [s7_1b0,s7_1b1,s7_1b2,s7_1b3,s7_1b4,s7_1b5,s7_1b6,s7_1b7,s7_1b8,s7_1b9,s7_1b10,s7_1b11,s7_1b12,s7_1b13,s7_1b14,s7_1b15,s7_1b16,s7_1b17,s7_1b18,s7_1b19]

lemma s7_1bx (v : List Sig) (h : (!s7_1b.contains v) = false) : Impossible 8 1 v := by
  have hm : v ∈ s7_1b := by simpa using h
  simp only [s7_1b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s7_1b0x
  · exact s7_1b1x
  · exact s7_1b2x
  · exact s7_1b3x
  · exact s7_1b4x
  · exact s7_1b5x
  · exact s7_1b6x
  · exact s7_1b7x
  · exact s7_1b8x
  · exact s7_1b9x
  · exact s7_1b10x
  · exact s7_1b11x
  · exact s7_1b12x
  · exact s7_1b13x
  · exact s7_1b14x
  · exact s7_1b15x
  · exact s7_1b16x
  · exact s7_1b17x
  · exact s7_1b18x
  · exact s7_1b19x

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative7_1 : Impossible 9 1 r7 :=
  exclude_step (u := fun v => !s7_1u.contains v) (b := fun v => !s7_1b.contains v) (by decide +kernel) s7_1ux s7_1bx (by decide +kernel)


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276676776 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276676776 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4276676776 r7 9 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative7_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[5,2]⟩,⟨.and,[1,3]⟩,⟨.or,[0,7]⟩,⟨.or,[1,3]⟩,⟨.and,[8,6]⟩,⟨.or,[8,6]⟩,⟨.and,[11,9]⟩,⟨.and,[12,4]⟩,⟨.or,[10,13]⟩],14,by simp [Clean],rfl,by decide +kernel⟩

def r8 : List Sig := [(0xfffc000fffc000fffc000fffffff0003ffffffffff0003fffffffffffffc000,0xa10a842a10a842a10a842a10a842a10a842a10a842a10a842a10a842a10a842a),(0xffffffff0000000fffffff0003ffffffc000ffffffffffc000fffc000fffffff,0xc223088c223088c223088c223088c223088c223088c223088c223088c223088c),(0xfffffffffffffff00000000003ffffffffff0003ffffffffff0000000fffffff,0x44c113044c113044c113044c113044c113044c113044c113044c113044c1130),(0xffffffffffffffffffffffffc00000000000003fffffffffffffffff0000000,0x87021c087021c087021c087021c087021c087021c087021c087021c087021c0),(0xffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative8_1 : Impossible 7 1 r8 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276677312 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276677312 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 4276677312 r8 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative8_1 gs o legal hn he
    ⟨[⟨.and,[0,3]⟩,⟨.or,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[5,7]⟩,⟨.or,[1,2]⟩,⟨.and,[9,6]⟩,⟨.and,[10,4]⟩,⟨.or,[8,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r9 : List Sig := [(0xfffffc001ffffffffffffe000fffffffffffff0007ffffffffffffffffffffff,0x0),(0x7fffffe000fff8003ffffff0007ffc001ffffff8003ffe000fff8003ffe000,0x9524a925492a49524a925492a49524a925492a49524a925492a49524a925492a),(0x7fffffffff0000003fffffffff8000001fffffffffc000000ffffffc000000,0x26493249924c926493249924c926493249924c926493249924c926493249924c),(0x7fffffffffffffffc0000000000000001ffffffffffffffff0000000000000,0x3871c38e1c70e3871c38e1c70e3871c38e1c70e3871c38e1c70e3871c38e1c70),(0x7fffffffffffffffffffffffffffffffe00000000000000000000000000000,0xc07e03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80)]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative9_1 : Impossible 3 1 r9 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941264042 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941264042 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941264042 r9 3 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative9_1 gs o legal hn he
    ⟨[⟨.and,[1,2]⟩,⟨.or,[3,4]⟩,⟨.and,[5,6]⟩,⟨.or,[0,7]⟩],8,by simp [Clean],rfl,by decide +kernel⟩

end PEqualNP.Outside.L_meta_1437_aux

theorem PEqualNP.Outside.L_meta_1437 : ∀ T ∈ ({0xeaeaeac8, 0xeee8e8e8, 0xeee8eaa8, 0xeee8eac8, 0xeee8eae0, 0xeeeaeaa0, 0xeeeaeac0, 0xfee8e8a8, 0xfee8eac0, 0xeaeaeaaa} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1437_aux.fn0
  · exact PEqualNP.Outside.L_meta_1437_aux.fn1
  · exact PEqualNP.Outside.L_meta_1437_aux.fn2
  · exact PEqualNP.Outside.L_meta_1437_aux.fn3
  · exact PEqualNP.Outside.L_meta_1437_aux.fn4
  · exact PEqualNP.Outside.L_meta_1437_aux.fn5
  · exact PEqualNP.Outside.L_meta_1437_aux.fn6
  · exact PEqualNP.Outside.L_meta_1437_aux.fn7
  · exact PEqualNP.Outside.L_meta_1437_aux.fn8
  · exact PEqualNP.Outside.L_meta_1437_aux.fn9
