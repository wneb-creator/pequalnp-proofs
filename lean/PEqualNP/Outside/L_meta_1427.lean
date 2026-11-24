import PEqualNP.Defs
-- Adapted from PEqualNP/Outside/L_meta_1445.lean and L-meta-1007 (Apache-2.0), extended with V4-symmetric BST barrier.
namespace PEqualNP.Outside.L_meta_1427_aux

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
  (allow = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

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
  exact Or.inr (Or.inr ⟨rfl,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

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
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ k' - t' ≤ k - t + (!flag).toNat ∧
      Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  have htk := (live_size h).1
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨flagOff,d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,Nat.le_refl _,by omega,by simp [flagOff]; omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧
      k - t ≤ gs.countP (fun g => !isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,hbin,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hlbin,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,?_,hu,hT⟩
    · cases hf : isNot g.op <;> simp [hf] at hcnt ⊢ <;> omega
    · cases hf : isNot g.op <;> simp [hf] at hlbin ⊢ <;> omega

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

theorem cost_from_nolive (T : ℕ) (raw : List Sig) (s : ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (no0 : ∀ k ≤ s - 1, ¬ Live k 0 raw.toFinset)
    (no1 : ∀ k ≤ s, ¬ Live k 1 raw.toFinset)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : s < C.gates.length := by
  by_contra! small
  obtain ⟨k,t,S,hk,count,hbin,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have oneNot := notCount C.gates single
  have eq := necessary raw essential live sub
  have hbin_lt : C.gates.countP (fun g => !isNot g.op) < C.gates.length := by
    obtain ⟨g, hgm, hgn⟩ := hasNot
    generalize hgs : C.gates = gs at hgm
    clear * - hgm hgn
    induction gs with
    | nil => simp at hgm
    | cons x xs ih =>
      simp only [List.mem_cons] at hgm
      rcases hgm with rfl | hm
      · simp only [List.countP_cons, isNot, hgn, Bool.not_true, Bool.false_eq_true, ite_false, List.length_cons]
        exact Nat.lt_succ_of_le List.countP_le_length
      · have hlt := ih hm
        simp only [List.countP_cons, List.length_cons]
        split <;> omega
  have ht : t = 0 ∨ t = 1 := by omega
  rcases ht with rfl | rfl
  · exact no0 k (by omega) (eq ▸ live)
  · exact no1 k (by omega) (eq ▸ live)

theorem replace_from_nolive (T m : ℕ) (raw : List Sig)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (no0 : ∀ k ≤ m - 2, ¬ Live k 0 raw.toFinset)
    (no1 : ∀ k ≤ m - 1, ¬ Live k 1 raw.toFinset)
    (upper : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT T x)
    (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT T x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT T x := by
  by_cases hnot : ∃ g ∈ gs, g.op = .not
  · have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs, o⟩ : Circuit) := by
      simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
    have bound := cost_from_nolive T raw (m - 1) raw_id samples essential
      (by simpa [show m - 1 - 1 = m - 2 by omega] using no0) no1 ⟨gs, o⟩ legal hn hnot he
    obtain ⟨gs', o', hok, hlen, hev⟩ := upper
    dsimp at bound
    exact ⟨gs', o', hok, by omega, hev⟩
  · refine ⟨gs, o, ?_, le_rfl, he⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := h g hg
    exact ⟨hop.elim Or.inl (fun h2 => h2.elim Or.inr (fun eq => (hnot ⟨g, hg, eq⟩).elim)), hlen⟩

theorem replace_fn (T m : ℕ) (raw : List Sig)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (nd : raw.Nodup)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test0 : search (m - 2) 0 raw = false)
    (test1 : search (m - 1) 1 raw = false)
    (upper : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT T x)
    (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT T x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT T x :=
  replace_from_nolive T m raw raw_id samples essential
    (fun k hk hl => Bool.false_ne_true (test0.symm.trans (search_complete hl (m - 2) hk raw nd rfl)))
    (fun k hk hl => Bool.false_ne_true (test1.symm.trans (search_complete hl (m - 1) hk raw nd rfl)))
    upper gs o h hn he


open PEqualNP.CircuitLowerBounds

-- V4-symmetric balanced-BST memoized barrier on top of Live / reduced_step

def permB (f0 l1 h1 l2 h2 : B) (x : B) : B :=
  (x &&& f0) ||| ((x &&& l1) <<< 1) ||| ((x &&& h1) >>> 1) ||| ((x &&& l2) <<< 2) ||| ((x &&& h2) >>> 2)

def permBValid (f0 l1 h1 l2 h2 : B) (pi : Fin 256 → Fin 256) : Bool :=
  (List.finRange 256).all fun i =>
    let j := pi i
    let c0 := f0.getLsbD i.val
    let c1 := decide (1 ≤ i.val) && l1.getLsbD (i.val - 1)
    let c2 := decide (i.val + 1 < 256) && h1.getLsbD (i.val + 1)
    let c3 := decide (2 ≤ i.val) && l2.getLsbD (i.val - 2)
    let c4 := decide (i.val + 2 < 256) && h2.getLsbD (i.val + 2)
    (pi j == i) &&
    ((c0 && !c1 && !c2 && !c3 && !c4 && (j.val == i.val)) ||
     (!c0 && c1 && !c2 && !c3 && !c4 && (j.val == i.val - 1)) ||
     (!c0 && !c1 && c2 && !c3 && !c4 && (j.val == i.val + 1)) ||
     (!c0 && !c1 && !c2 && c3 && !c4 && (j.val == i.val - 2)) ||
     (!c0 && !c1 && !c2 && !c3 && c4 && (j.val == i.val + 2)))

lemma permB_getLsbD (f0 l1 h1 l2 h2 : B) (pi : Fin 256 → Fin 256)
    (hv : permBValid f0 l1 h1 l2 h2 pi = true) (x : B) (i : Fin 256) :
    (permB f0 l1 h1 l2 h2 x).getLsbD i.val = x.getLsbD (pi i).val := by
  have hi := List.all_eq_true.mp hv i (List.mem_finRange i)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hi
  obtain ⟨_, hcases⟩ := hi
  have hshl1 : ((x &&& l1) <<< 1).getLsbD i.val =
      ((decide (1 ≤ i.val) && l1.getLsbD (i.val - 1)) && x.getLsbD (i.val - 1)) := by
    rw [BitVec.getLsbD_shiftLeft]
    by_cases h1 : 1 ≤ i.val
    · have h0 : ¬ i.val < 1 := by omega
      simp [i.isLt, h1, h0, BitVec.getLsbD_and, Bool.and_comm]
    · have h0 : i.val < 1 := by omega
      simp [h1, h0]
  have hshr1 : ((x &&& h1) >>> 1).getLsbD i.val =
      ((decide (i.val + 1 < 256) && h1.getLsbD (i.val + 1)) && x.getLsbD (i.val + 1)) := by
    rw [BitVec.getLsbD_ushiftRight]
    by_cases h1 : i.val + 1 < 256
    · simp [h1, Nat.add_comm, BitVec.getLsbD_and, Bool.and_comm]
    · have hge : 256 ≤ 1 + i.val := by omega
      simp [h1, BitVec.getLsbD_of_ge _ _ hge]
  have hshl2 : ((x &&& l2) <<< 2).getLsbD i.val =
      ((decide (2 ≤ i.val) && l2.getLsbD (i.val - 2)) && x.getLsbD (i.val - 2)) := by
    rw [BitVec.getLsbD_shiftLeft]
    by_cases h2 : 2 ≤ i.val
    · have h0 : ¬ i.val < 2 := by omega
      simp [i.isLt, h2, h0, BitVec.getLsbD_and, Bool.and_comm]
    · have h0 : i.val < 2 := by omega
      simp [h2, h0]
  have hshr2 : ((x &&& h2) >>> 2).getLsbD i.val =
      ((decide (i.val + 2 < 256) && h2.getLsbD (i.val + 2)) && x.getLsbD (i.val + 2)) := by
    rw [BitVec.getLsbD_ushiftRight]
    by_cases h2 : i.val + 2 < 256
    · simp [h2, Nat.add_comm, BitVec.getLsbD_and, Bool.and_comm]
    · have hge : 256 ≤ 2 + i.val := by omega
      simp [h2, BitVec.getLsbD_of_ge _ _ hge]
  simp only [permB, BitVec.getLsbD_or, BitVec.getLsbD_and, hshl1, hshr1, hshl2, hshr2]
  rcases hcases with (((⟨⟨⟨⟨⟨h0,hc1⟩,hc2⟩,hc3⟩,hc4⟩,hj⟩ | ⟨⟨⟨⟨⟨h0,hc1⟩,hc2⟩,hc3⟩,hc4⟩,hj⟩) |
      ⟨⟨⟨⟨⟨h0,hc1⟩,hc2⟩,hc3⟩,hc4⟩,hj⟩) | ⟨⟨⟨⟨⟨h0,hc1⟩,hc2⟩,hc3⟩,hc4⟩,hj⟩) | ⟨⟨⟨⟨⟨h0,hc1⟩,hc2⟩,hc3⟩,hc4⟩,hj⟩
  all_goals simp only [hj]
  all_goals simp only [BitVec.getLsbD_eq_getElem i.isLt] at h0
  · simp [h0, hc1, hc2, hc3, hc4]
  · simp [h0, hc1, hc2, hc3, hc4]
  · simp [h0, hc1, hc2, hc3, hc4]
  · simp [h0, hc1, hc2, hc3, hc4]
  · simp [h0, hc1, hc2, hc3, hc4]

structure SigAut where
  fn : Sig → Sig
  inj : Function.Injective fn
  map_zero : fn zero = zero
  map_one : fn one = one
  map_target : fn target = target
  map_neg : ∀ a, fn (neg a) = neg (fn a)
  map_bin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)

def mkSigAut (f0 l1 h1 l2 h2 : B) (pi : Fin 256 → Fin 256)
    (hv : permBValid f0 l1 h1 l2 h2 pi = true) : SigAut where
  fn := fun a => (permB f0 l1 h1 l2 h2 a.1, permB f0 l1 h1 l2 h2 a.2)
  inj := by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have hinv : ∀ i : Fin 256, pi (pi i) = i := fun i => by
      have hi := List.all_eq_true.mp hv i (List.mem_finRange i)
      simp only [Bool.and_eq_true, beq_iff_eq] at hi
      exact hi.1
    have hgg : ∀ x, permB f0 l1 h1 l2 h2 (permB f0 l1 h1 l2 h2 x) = x := fun x => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit _ ⟨i, hi⟩, hbit x (pi ⟨i, hi⟩), hinv ⟨i, hi⟩]
    intro a b hab
    dsimp only at hab
    have hfst : permB f0 l1 h1 l2 h2 a.1 = permB f0 l1 h1 l2 h2 b.1 := congrArg Prod.fst hab
    have hsnd : permB f0 l1 h1 l2 h2 a.2 = permB f0 l1 h1 l2 h2 b.2 := congrArg Prod.snd hab
    exact Prod.ext (by rw [← hgg a.1, ← hgg b.1, hfst]) (by rw [← hgg a.2, ← hgg b.2, hsnd])
  map_zero := by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have h0 : permB f0 l1 h1 l2 h2 0 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [hbit 0 ⟨i, hi⟩]; simp
    exact Prod.ext h0 h0
  map_one := by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have htop : permB f0 l1 h1 l2 h2 top = top := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit top ⟨i, hi⟩, top, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes]
      simp [(pi ⟨i, hi⟩).isLt, hi]
    exact Prod.ext htop htop
  map_target := by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have h0 : permB f0 l1 h1 l2 h2 0 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [hbit 0 ⟨i, hi⟩]; simp
    have htop : permB f0 l1 h1 l2 h2 top = top := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit top ⟨i, hi⟩, top, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes]
      simp [(pi ⟨i, hi⟩).isLt, hi]
    exact Prod.ext htop h0
  map_neg := fun a => by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have hnot : ∀ x, permB f0 l1 h1 l2 h2 (~~~x) = ~~~(permB f0 l1 h1 l2 h2 x) := fun x => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit (~~~x) ⟨i, hi⟩, BitVec.getLsbD_not, BitVec.getLsbD_not, hbit x ⟨i, hi⟩]
      simp [hi, (pi ⟨i, hi⟩).isLt]
    exact Prod.ext (hnot a.1) (hnot a.2)
  map_bin := fun d a b => by
    have hbit := permB_getLsbD f0 l1 h1 l2 h2 pi hv
    have hand : ∀ x y, permB f0 l1 h1 l2 h2 (x &&& y) = permB f0 l1 h1 l2 h2 x &&& permB f0 l1 h1 l2 h2 y := fun x y => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit _ ⟨i, hi⟩, BitVec.getLsbD_and, BitVec.getLsbD_and, hbit x ⟨i, hi⟩, hbit y ⟨i, hi⟩]
    have hor : ∀ x y, permB f0 l1 h1 l2 h2 (x ||| y) = permB f0 l1 h1 l2 h2 x ||| permB f0 l1 h1 l2 h2 y := fun x y => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [hbit _ ⟨i, hi⟩, BitVec.getLsbD_or, BitVec.getLsbD_or, hbit x ⟨i, hi⟩, hbit y ⟨i, hi⟩]
    cases d <;> simp [bin, hand, hor]

def idAut : SigAut := ⟨id, Function.injective_id, rfl, rfl, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

def compAut (A B : SigAut) : SigAut :=
  ⟨fun x => A.fn (B.fn x), A.inj.comp B.inj,
   by rw [B.map_zero, A.map_zero], by rw [B.map_one, A.map_one], by rw [B.map_target, A.map_target],
   fun a => by rw [B.map_neg, A.map_neg], fun d a b => by rw [B.map_bin, A.map_bin]⟩

lemma live_aut (A : SigAut) {k t S} (h : Live k t S) : Live k t (S.image A.fn) := by
  have hprop : ∀ a, proper a → proper (A.fn a) := fun a ⟨h0, h1⟩ =>
    ⟨fun h => h0 (A.inj (h.trans A.map_zero.symm)), fun h => h1 (A.inj (h.trans A.map_one.symm))⟩
  induction h using liveInd with
  | stop => simpa [A.map_target] using Live.stop
  | @unary k t U a ha hf tail ih =>
    rw [Finset.image_insert]
    apply Live.unary (hprop a ha)
    · rw [← A.map_neg, ← Finset.image_insert, Finset.mem_image]
      rintro ⟨x, hx, hxe⟩; exact hf (A.inj hxe ▸ hx)
    · simpa [Finset.image_insert, A.map_neg] using ih
  | @binary k t U a b d ha hb hab hf tail ih =>
    rw [Finset.image_insert, Finset.image_insert]
    apply Live.binary (hprop a ha) (hprop b hb) (fun h => hab (A.inj h))
    · rw [← A.map_bin, ← Finset.image_insert, ← Finset.image_insert, Finset.mem_image]
      rintro ⟨x, hx, hxe⟩; exact hf (A.inj hxe ▸ hx)
    · simpa [Finset.image_insert, A.map_bin] using ih

def sigLt (a b : Sig) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def insertSig (x : Sig) : List Sig → List Sig
  | [] => [x]
  | y :: ys => if sigLt x y then x :: y :: ys else y :: insertSig x ys

def sortSig : List Sig → List Sig
  | [] => []
  | x :: xs => insertSig x (sortSig xs)

lemma insertSig_perm (x : Sig) (l : List Sig) : (insertSig x l).Perm (x :: l) := by
  induction l with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [insertSig]
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap _ _ _)

lemma sortSig_perm (l : List Sig) : (sortSig l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insertSig_perm x (sortSig xs)).trans (ih.cons x)

def listSigLt : List Sig → List Sig → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then listSigLt xs ys else sigLt x y

def minListSig (a b : List Sig) : List Sig :=
  if listSigLt b a then b else a

def canon4 (s12 s34 : Sig → Sig) (w : List Sig) : List Sig :=
  let v0 := sortSig w
  let v1 := sortSig (w.map s12)
  let v2 := sortSig (w.map s34)
  let v3 := sortSig (w.map (fun x => s12 (s34 x)))
  minListSig (minListSig v0 v1) (minListSig v2 v3)

lemma canon4_spec (A12 A34 : SigAut) (w : List Sig) :
    ∃ A : SigAut, (canon4 A12.fn A34.fn w).toFinset = w.toFinset.image A.fn := by
  have h1 : ∀ A : SigAut, (sortSig (w.map A.fn)).toFinset = w.toFinset.image A.fn := by
    intro A; ext x
    simp only [List.mem_toFinset, (sortSig_perm _).mem_iff, List.mem_map, Finset.mem_image]
  have h0 : (sortSig w).toFinset = w.toFinset.image idAut.fn := by
    simpa [idAut] using h1 idAut
  dsimp only [canon4, minListSig]
  split_ifs
  all_goals first
    | exact ⟨compAut A12 A34, h1 (compAut A12 A34)⟩
    | exact ⟨A34, h1 A34⟩
    | exact ⟨A12, h1 A12⟩
    | exact ⟨idAut, h0⟩

inductive STree
  | leaf
  | node (v : List Sig) (l r : STree)

abbrev L : STree := STree.leaf
abbrev N : List Sig → STree → STree → STree := STree.node

def MemSTree (x : List Sig) : STree → Prop
  | .leaf => False
  | .node y l r => x = y ∨ MemSTree x l ∨ MemSTree x r

def inSTree (x : List Sig) : STree → Bool
  | .leaf => false
  | .node y l r => if x == y then true else if listSigLt x y then inSTree x l else inSTree x r

lemma inSTree_mem (x : List Sig) (T : STree) (h : inSTree x T = true) : MemSTree x T := by
  induction T with
  | leaf => simp [inSTree] at h
  | node y l r ihl ihr =>
    simp only [inSTree] at h
    split_ifs at h with heq hlt
    · exact Or.inl (beq_iff_eq.mp heq)
    · exact Or.inr (Or.inl (ihl h))
    · exact Or.inr (Or.inr (ihr h))

def inTbl (s12 s34 : Sig → Sig) (T : STree) (w : List Sig) : Bool :=
  inSTree (canon4 s12 s34 w) T

lemma inTbl_sound (A12 A34 : SigAut) (T : STree) (w : List Sig)
    (h : inTbl A12.fn A34.fn T w = true) :
    ∃ (v : List Sig) (A : SigAut), MemSTree v T ∧ v.toFinset = w.toFinset.image A.fn := by
  have hm := inSTree_mem _ T h
  obtain ⟨A, hA⟩ := canon4_spec A12 A34 w
  exact ⟨canon4 A12.fn A34.fn w, A, hm, hA⟩

def nodupSig : List Sig → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupSig xs

lemma nodupSig_sound {l : List Sig} (h : nodupSig l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [nodupSig, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, ih h.2⟩

def checkNode (s12 s34 : Sig → Sig) (S t : Nat) (nxtU nxtB : STree) (v : List Sig) : Bool :=
  nodupSig v && !stepTest S t v (fun w => !inTbl s12 s34 nxtU w) (fun w => !inTbl s12 s34 nxtB w)

def checkSTree (s12 s34 : Sig → Sig) (S t : Nat) (nxtU nxtB : STree) : STree → Bool
  | .leaf => true
  | .node v l r => checkNode s12 s34 S t nxtU nxtB v &&
      checkSTree s12 s34 S t nxtU nxtB l && checkSTree s12 s34 S t nxtU nxtB r

lemma checkSTree_node {s12 s34 : Sig → Sig} {S t : Nat} {nxtU nxtB l r : STree} {v : List Sig}
    (hv : checkNode s12 s34 S t nxtU nxtB v = true)
    (hl : checkSTree s12 s34 S t nxtU nxtB l = true)
    (hr : checkSTree s12 s34 S t nxtU nxtB r = true) :
    checkSTree s12 s34 S t nxtU nxtB (.node v l r) = true := by
  simp [checkSTree, hv, hl, hr]

lemma checkSTree_mem {s12 s34 : Sig → Sig} {S t : Nat} {nxtU nxtB T : STree}
    (h : checkSTree s12 s34 S t nxtU nxtB T = true) {v : List Sig} (hm : MemSTree v T) :
    checkNode s12 s34 S t nxtU nxtB v = true := by
  induction T with
  | leaf => exact False.elim hm
  | node y l r ihl ihr =>
    simp only [checkSTree, Bool.and_eq_true] at h
    rcases hm with rfl | hl | hr
    · exact h.1.1
    · exact ihl h.1.2 hl
    · exact ihr h.2 hr

lemma layer_step_sound (A12 A34 : SigAut) (S t : Nat) (T nxtU nxtB : STree)
    (hu : ∀ v, MemSTree v nxtU → ∀ l ≤ S, ¬ Live l (t - 1) v.toFinset)
    (hb : ∀ v, MemSTree v nxtB → ∀ l ≤ S, ¬ Live l t v.toFinset)
    (hcheck : checkSTree A12.fn A34.fn S t nxtU nxtB T = true) :
    ∀ v, MemSTree v T → ∀ m ≤ S + 1, ¬ Live m t v.toFinset := by
  intro v hv m hm hlive
  have hn := checkSTree_mem hcheck hv
  simp only [checkNode, Bool.and_eq_true, Bool.not_eq_true'] at hn
  have htrue := reduced_step (u := fun w => !inTbl A12.fn A34.fn nxtU w)
    (b := fun w => !inTbl A12.fn A34.fn nxtB w) hlive hm (nodupSig_sound hn.1) rfl
    (fun w _ l hl hlw => by
      cases hin : inTbl A12.fn A34.fn nxtU w
      · rfl
      · obtain ⟨u, A, hmu, hA⟩ := inTbl_sound A12 A34 nxtU w hin
        exact False.elim (hu u hmu l hl (hA.symm ▸ live_aut A hlw)))
    (fun w _ l hl hlw => by
      cases hin : inTbl A12.fn A34.fn nxtB w
      · rfl
      · obtain ⟨u, A, hmu, hA⟩ := inTbl_sound A12 A34 nxtB w hin
        exact False.elim (hb u hmu l hl (hA.symm ▸ live_aut A hlw)))
  rw [hn.2] at htrue
  exact Bool.false_ne_true htrue


open PEqualNP.CircuitLowerBounds
def r0 : List Sig := [(0xfffffff00001ffffffffffffffffffe00003fffffffffffffe00003fffffffff,0x22aa0455408aa81155022aa0455408aa81155022aa0455408aa81155022aa),(0xfffffffffffe00003ffff80000fffffffffc00007fffffffffffffc00007ffff,0x244cc48998913312266244cc48998913312266244cc48998913312266244cc),(0x7fffffffffffffc000000000ffffffffffffff80000ffffffffffffff80000,0x488f0911e1223c24478488f0911e1223c24478488f0911e1223c24478488f0),(0xffffffffffffffffffffffffff0000000000000000000fffffffffffffffffff,0x70f00e1e01c3c03878070f00e1e01c3c03878070f00e1e01c3c03878070f00),(0x7ffffffffffffffffffffffffffffffffffffffffff0000000000000000000,0x7f000fe001fc003f8007f000fe001fc003f8007f000fe001fc003f8007f000)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg0_0 : search 6 0 r0 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg0_1 : search 7 1 r0 = false := by decide +kernel
lemma upper0 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8e800 x :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[0,2]⟩,⟨.and,[3,4]⟩,⟨.or,[2,7]⟩,⟨.and,[5,6]⟩,⟨.and,[0,8]⟩,⟨.or,[1,10]⟩,⟨.and,[9,11]⟩], 12, by simp, rfl, by decide +kernel⟩
lemma fn0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeae8e800 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8e800 x :=
  replace_fn 0xeae8e800 8 r0 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg0_0 neg0_1 upper0 gs o h hn he

def r1 : List Sig := [(0xfffffc0000fffffffffffffc0000fffffffffffffc0000ffffffffffffffffff,0x222488892222488892222488892222488892222488892222488892222488892),(0xffffffffff00003fffffffffffff00003fffffffffffff00003fffffffffffff,0x444911124444911124444911124444911124444911124444911124444911124),(0xfffffffffffffc0000fffffffffffffc0000fffffffffffffc0000ffffc0000,0x888e22238888e22238888e22238888e22238888e22238888e22238888e22238),(0xffffffffffffffffff000000000000000000ffffffffffffffffff000000000,0xf0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg1_0 : search 4 0 r1 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg1_1 : search 5 1 r1 = false := by decide +kernel
lemma upper1 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xe8e8e888 x :=
  ⟨[⟨.or,[0,1]⟩,⟨.and,[2,5]⟩,⟨.and,[0,1]⟩,⟨.or,[3,4]⟩,⟨.and,[6,8]⟩,⟨.or,[7,9]⟩], 10, by simp, rfl, by decide +kernel⟩
lemma fn1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xe8e8e888 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xe8e8e888 x :=
  replace_fn 0xe8e8e888 6 r1 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg1_0 neg1_1 upper1 gs o h hn he

def r2 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x21080842021080842021080842021080842021080842021080842021080842),(0xffffffffff00003ffff00003ffff00003ffffffffc0000fffffffff00003ffff,0x54a51529454a51529454a51529454a51529454a51529454a51529454a515294),(0xfffffffffffffc000000003ffffffffc0000fffffffff00003ffffffffc0000,0x98c62631898c62631898c62631898c62631898c62631898c62631898c626318),(0xffffffffffffffffffffffc0000000000000fffffffffffffc0000000000000,0xe0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg2_0 : search 5 0 r2 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg2_1 : search 6 1 r2 = false := by decide +kernel
lemma upper2 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 7 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaa8a8a8 x :=
  ⟨[⟨.and,[1,2]⟩,⟨.or,[0,5]⟩,⟨.and,[4,6]⟩,⟨.or,[1,2]⟩,⟨.and,[0,8]⟩,⟨.and,[3,7]⟩,⟨.or,[9,10]⟩], 11, by simp, rfl, by decide +kernel⟩
lemma fn2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeaa8a8a8 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaa8a8a8 x :=
  replace_fn 0xeaa8a8a8 7 r2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg2_0 neg2_1 upper2 gs o h hn he

def r3 : List Sig := [(0xfffffc0000fffffffffffffffffffffffffffffffc0000ffffffffffffffffff,0x22480892022480892022480892022480892022480892022480892022480892),(0xffffffffff00003ffff00003ffff00003fffffffffffff00003fffffffffffff,0x544915124544915124544915124544915124544915124544915124544915124),(0xfffffffffffffc000000003ffffffffc0000fffffffffffffc0000ffffc0000,0x988e26238988e26238988e26238988e26238988e26238988e26238988e26238),(0xffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg3_0 : search 6 0 r3 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg3_1 : search 7 1 r3 = false := by decide +kernel
lemma upper3 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaa8e888 x :=
  ⟨[⟨.and,[2,3]⟩,⟨.or,[1,4]⟩,⟨.or,[2,3]⟩,⟨.and,[0,7]⟩,⟨.or,[1,8]⟩,⟨.and,[0,6]⟩,⟨.or,[5,10]⟩,⟨.and,[9,11]⟩], 12, by simp, rfl, by decide +kernel⟩
lemma fn3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeaa8e888 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaa8e888 x :=
  replace_fn 0xeaa8e888 8 r3 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg3_0 neg3_1 upper3 gs o h hn he

def r4 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffff00003fffffffffffff,0x12480492012480492012480492012480492012480492012480492012480492),(0xffffffffff00003ffff00003ffff00003ffff00003ffffffffffffffffffffff,0x544915124544915124544915124544915124544915124544915124544915124),(0xfffffffffffffc000000003ffffffffc000000003ffffffffc0000ffffc0000,0x998e26638998e26638998e26638998e26638998e26638998e26638998e26638),(0xffffffffffffffffffffffc000000000000000003fffffffffffff000000000,0xe1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0),(0xffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg4_0 : search 3 0 r4 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg4_1 : search 4 1 r4 = false := by decide +kernel
lemma upper4 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 5 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaaac888 x :=
  ⟨[⟨.and,[1,2]⟩,⟨.or,[1,4]⟩,⟨.and,[3,5]⟩,⟨.and,[0,6]⟩,⟨.or,[7,8]⟩], 9, by simp, rfl, by decide +kernel⟩
lemma fn4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeaaac888 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaaac888 x :=
  replace_fn 0xeaaac888 5 r4 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg4_0 neg4_1 upper4 gs o h hn he

def r5 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffff00003fffffffffffff,0x4a8012a004a8012a004a8012a004a8012a004a8012a004a8012a004a8012a),(0xffffffffff00003ffff00003ffff00003ffff00003ffffffffc0000fffffffff,0x54931524c54931524c54931524c54931524c54931524c54931524c54931524c),(0xffffffffffffffc000000003ffffffffc000000003fffffffffffff00003ffff,0x991c26470991c26470991c26470991c26470991c26470991c26470991c26470),(0xffffffffffffffffffffffc000000000000000003fffffffffffffffffc0000,0xe1e038780e1e038780e1e038780e1e038780e1e038780e1e038780e1e038780),(0xffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg5_0 : search 6 0 r5 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg5_1 : search 7 1 r5 = false := by decide +kernel
lemma upper5 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaaae880 x :=
  ⟨[⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.or,[1,6]⟩,⟨.and,[5,7]⟩,⟨.or,[4,8]⟩,⟨.and,[1,6]⟩,⟨.or,[0,10]⟩,⟨.and,[9,11]⟩], 12, by simp, rfl, by decide +kernel⟩
lemma fn5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeaaae880 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeaaae880 x :=
  replace_fn 0xeaaae880 8 r5 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg5_0 neg5_1 upper5 gs o h hn he

def r6 : List Sig := [(0xfffffc0000ffffffffffffffffff00003ffffffffc0000ffffffffffffffffff,0x122484892122484892122484892122484892122484892122484892122484892),(0xffffffffff00003ffff00003ffffffffffffffffffffff00003fffffffffffff,0x444911124444911124444911124444911124444911124444911124444911124),(0xfffffffffffffc000000003ffffffffc0000fffffffffffffc0000ffffc0000,0x988e26238988e26238988e26238988e26238988e26238988e26238988e26238),(0xffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg6_0 : search 6 0 r6 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg6_1 : search 7 1 r6 = false := by decide +kernel
lemma upper6 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeac8e888 x :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[2,4]⟩,⟨.and,[1,5]⟩,⟨.and,[2,7]⟩,⟨.or,[0,8]⟩,⟨.and,[3,6]⟩,⟨.or,[1,10]⟩,⟨.and,[9,11]⟩], 12, by simp, rfl, by decide +kernel⟩
lemma fn6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeac8e888 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeac8e888 x :=
  replace_fn 0xeac8e888 8 r6 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg6_0 neg6_1 upper6 gs o h hn he

def r7 : List Sig := [(0xffffc0000ffffffffffffffffff00003ffffffffc0000fffffffffffffc0000,0x122a848aa122a848aa122a848aa122a848aa122a848aa122a848aa122a848aa),(0xffffffffff00003ffff00003ffffffffffffffffffffff00003fffffffffffff,0x44431110c44431110c44431110c44431110c44431110c44431110c44431110c),(0xffffffffffffffc000000003ffffffffc0000fffffffffffffc0000fffffffff,0x988c26230988c26230988c26230988c26230988c26230988c26230988c26230),(0xffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg7_0 : search 5 0 r7 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg7_1 : search 6 1 r7 = false := by decide +kernel
lemma upper7 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 7 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeac8e8c0 x :=
  ⟨[⟨.and,[0,4]⟩,⟨.or,[2,5]⟩,⟨.or,[1,6]⟩,⟨.and,[1,6]⟩,⟨.and,[3,7]⟩,⟨.and,[0,9]⟩,⟨.or,[8,10]⟩], 11, by simp, rfl, by decide +kernel⟩
lemma fn7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeac8e8c0 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeac8e8c0 x :=
  replace_fn 0xeac8e8c0 7 r7 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg7_0 neg7_1 upper7 gs o h hn he

def r9 : List Sig := [(0xfffffc0000ffffffffffffffffff00003fffffffffffff00003fffffffffffff,0x42a810aa042a810aa042a810aa042a810aa042a810aa042a810aa042a810aa),(0xfffffffff00003ffff00003ffffffffc0000fffffffffffffc0000ffffc0000,0x48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc),(0xfffffffffffffc000000003fffffffffffff00003fffffffffffff000000000,0x913c244f0913c244f0913c244f0913c244f0913c244f0913c244f0913c244f0),(0xfffffffffffffffffffffffc000000000000000003ffffffffffffffffffffff,0xe1c038700e1c038700e1c038700e1c038700e1c038700e1c038700e1c038700),(0xffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg9_0 : search 4 0 r9 = false := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma neg9_1 : search 5 1 r9 = false := by decide +kernel
lemma upper9 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8ea00 x :=
  ⟨[⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.and,[4,5]⟩,⟨.or,[3,8]⟩,⟨.and,[7,9]⟩], 10, by simp, rfl, by decide +kernel⟩
lemma fn9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeae8ea00 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8ea00 x :=
  replace_fn 0xeae8ea00 6 r9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) neg9_0 neg9_1 upper9 gs o h hn he

def f0_12 : B := 0xfffffffffffffffff
def l1_12 : B := 0x5555555555555555555555555555555555555555555555500000000000000000
def h1_12 : B := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000
def f0_34 : B := 0xfffffffffff000000000000fffff
def l1_34 : B := 0x55555555555500000
def h1_34 : B := 0xaaaaaaaaaaaa00000
def l2_34 : B := 0x3333333333333333333333333333333333330000000000000000000000000000
def h2_34 : B := 0xcccccccccccccccccccccccccccccccccccc0000000000000000000000000000
def pi12Fn (i : Fin 256) : Fin 256 :=
  have := i.isLt
  if _ : i.val < 68 then i
  else if h : i.val % 2 = 0 then ⟨i.val + 1, by omega⟩
  else ⟨i.val - 1, by omega⟩

def pi34Fn (i : Fin 256) : Fin 256 :=
  have := i.isLt
  if _ : i.val < 20 then i
  else if h1 : i.val < 68 then
    if h2 : i.val % 2 = 0 then ⟨i.val + 1, by omega⟩ else ⟨i.val - 1, by omega⟩
  else if _ : i.val < 112 then i
  else if h3 : i.val % 4 < 2 then ⟨i.val + 2, by omega⟩
  else ⟨i.val - 2, by omega⟩

set_option maxHeartbeats 2000000 in
lemma valid12 : permBValid f0_12 l1_12 h1_12 0 0 pi12Fn = true := by decide +kernel
set_option maxHeartbeats 2000000 in
lemma valid34 : permBValid f0_34 l1_34 h1_34 l2_34 h2_34 pi34Fn = true := by decide +kernel

def aut12 : SigAut := mkSigAut f0_12 l1_12 h1_12 0 0 pi12Fn valid12
def aut34 : SigAut := mkSigAut f0_34 l1_34 h1_34 l2_34 h2_34 pi34Fn valid34

def w0 : Sig := (0xf0ffffffffff00000ffffffffffffffffffffc0fffffffff0fffff0000fff0ff,0xf00000f0000f000000f000f00f0f0f0030c00ccc30cccc330c330cc02222)
def w1 : Sig := (0xff55550ffffffffff555555555555555555ffff5555503fff0ffffffffffff0f,0x55a50055555555555a50a500a500faa5500555593a5055500000300030004444)
def w2 : Sig := (0xffaaaa0ffffffffffaaaaaaaaaaaaaaaaaaffffaaaaa03fff0ffffffffffff0f,0xaa5a00aaaaaaaaaaa5a05a005a00f55aa00aaaa635a0aaa00000300030004444)
def w3 : Sig := (0xfffffff33333333333333333333333333330fffffffffc0fff555555550ffff0,0x3333333fc300fc300fffcccc333300000003c30fc000c30555e940e940508888)
def w4 : Sig := (0xfffffffcccccccccccccccccccccccccccc0fffffffffc0fffaaaaaaaa0ffff0,0xcccccccf3c00f3c00fff3333cccc0000000cc30fc000c30aaad680d680a08888)
def w5 : Sig := neg w0
def w6 : Sig := neg w1
def w7 : Sig := neg w2
def w8 : Sig := neg w3
def w9 : Sig := neg w4
def w10 : Sig := bin false w0 w1
def w11 : Sig := bin true w0 w1
def w12 : Sig := bin false w0 w2
def w13 : Sig := bin true w0 w2
def w14 : Sig := bin false w0 w3
def w15 : Sig := bin true w0 w3
def w16 : Sig := bin false w0 w4
def w17 : Sig := bin true w0 w4
def w18 : Sig := bin false w1 w2
def w19 : Sig := bin true w1 w2
def w20 : Sig := bin false w1 w3
def w21 : Sig := bin true w1 w3
def w22 : Sig := bin false w1 w4
def w23 : Sig := bin true w1 w4
def w24 : Sig := bin false w2 w3
def w25 : Sig := bin true w2 w3
def w26 : Sig := bin false w2 w4
def w27 : Sig := bin true w2 w4
def w28 : Sig := bin false w3 w4
def w29 : Sig := bin true w3 w4
def w30 : Sig := neg w10
def w31 : Sig := neg w12
def w32 : Sig := bin false w10 w2
def w33 : Sig := bin true w10 w2
def w34 : Sig := bin true w12 w1
def w35 : Sig := bin false w10 w3
def w36 : Sig := bin true w10 w3
def w37 : Sig := bin false w10 w4
def w38 : Sig := bin true w10 w4
def w39 : Sig := neg w14
def w40 : Sig := neg w16
def w41 : Sig := bin true w14 w1
def w42 : Sig := bin false w14 w2
def w43 : Sig := bin true w14 w2
def w44 : Sig := bin false w14 w4
def w45 : Sig := bin true w14 w4
def w46 : Sig := bin true w16 w3
def w47 : Sig := neg w18
def w48 : Sig := bin true w0 w18
def w49 : Sig := bin false w18 w3
def w50 : Sig := bin true w18 w3
def w51 : Sig := bin false w18 w4
def w52 : Sig := bin true w18 w4
def w53 : Sig := neg w20
def w54 : Sig := neg w26
def w55 : Sig := bin true w0 w20
def w56 : Sig := bin true w20 w2
def w57 : Sig := bin true w24 w1
def w58 : Sig := bin false w20 w4
def w59 : Sig := bin true w20 w4
def w60 : Sig := bin true w22 w3
def w61 : Sig := neg w19
def w62 : Sig := bin false w0 w19
def w63 : Sig := bin true w0 w19
def w64 : Sig := bin false w19 w3
def w65 : Sig := bin true w19 w3
def w66 : Sig := bin false w19 w4
def w67 : Sig := bin true w19 w4
def w68 : Sig := neg w28
def w69 : Sig := bin true w0 w28
def w70 : Sig := bin true w1 w28
def w71 : Sig := bin false w2 w28
def w72 : Sig := bin true w2 w28
def w73 : Sig := neg w15
def w74 : Sig := neg w17
def w75 : Sig := bin false w1 w15
def w76 : Sig := bin true w1 w15
def w77 : Sig := bin false w2 w15
def w78 : Sig := bin true w2 w15
def w79 : Sig := bin false w4 w15
def w80 : Sig := bin false w3 w17
def w81 : Sig := bin true w4 w15
def w82 : Sig := neg w21
def w83 : Sig := neg w27
def w84 : Sig := bin false w0 w21
def w85 : Sig := bin false w2 w21
def w86 : Sig := bin false w1 w25
def w87 : Sig := bin false w4 w21
def w88 : Sig := bin false w3 w23
def w89 : Sig := bin true w4 w21
def w90 : Sig := neg w29
def w91 : Sig := bin false w0 w29
def w92 : Sig := bin false w1 w29
def w93 : Sig := bin false w2 w29
def w94 : Sig := bin true w2 w29
def w95 : Sig := neg w11
def w96 : Sig := neg w13
def w97 : Sig := bin false w2 w11
def w98 : Sig := bin false w1 w13
def w99 : Sig := bin false w3 w11
def w100 : Sig := bin false w4 w11
def w101 : Sig := bin true w4 w11
def w102 : Sig := bin false w9 w0
def w103 : Sig := bin true w9 w0
def w104 : Sig := bin false w9 w1
def w105 : Sig := bin true w9 w1
def w106 : Sig := bin false w9 w2
def w107 : Sig := bin true w9 w2
def w108 : Sig := bin false w9 w3
def w109 : Sig := bin true w9 w3
def w110 : Sig := bin false w7 w0
def w111 : Sig := bin true w7 w0
def w112 : Sig := bin false w7 w1
def w113 : Sig := bin true w7 w1
def w114 : Sig := bin false w7 w3
def w115 : Sig := bin true w7 w3
def w116 : Sig := bin false w7 w4
def w117 : Sig := bin true w7 w4
def w118 : Sig := bin false w5 w1
def w119 : Sig := bin true w5 w1
def w120 : Sig := bin false w5 w2
def w121 : Sig := bin true w5 w2
def w122 : Sig := bin false w5 w3
def w123 : Sig := bin true w5 w3
def w124 : Sig := bin false w5 w4
def w125 : Sig := bin true w5 w4
def w126 : Sig := neg w32
def w127 : Sig := bin true w32 w3
def w128 : Sig := bin true w32 w4
def w129 : Sig := bin false w32 w3
def w130 : Sig := bin false w32 w4
def w131 : Sig := bin false w12 w4
def w132 : Sig := neg w131
def w133 : Sig := bin true w35 w2
def w134 : Sig := bin true w35 w4
def w135 : Sig := bin true w42 w1
def w136 : Sig := bin false w35 w4
def w137 : Sig := bin true w37 w3
def w138 : Sig := neg w24
def w139 : Sig := bin true w10 w24
def w140 : Sig := bin true w24 w4
def w141 : Sig := neg w33
def w142 : Sig := bin true w10 w28
def w143 : Sig := bin true w12 w3
def w144 : Sig := bin true w12 w4
def w145 : Sig := neg w144
def w146 : Sig := neg w25
def w147 : Sig := bin false w10 w25
def w148 : Sig := bin true w10 w25
def w149 : Sig := bin true w12 w21
def w150 : Sig := bin false w0 w25
def w151 : Sig := bin false w10 w29
def w152 : Sig := bin true w10 w29
def w153 : Sig := bin false w3 w13
def w154 : Sig := bin false w4 w13
def w155 : Sig := neg w62
def w156 : Sig := bin false w62 w3
def w157 : Sig := bin true w62 w3
def w158 : Sig := bin false w62 w4
def w159 : Sig := bin true w62 w4
def w160 : Sig := neg w44
def w161 : Sig := bin true w44 w1
def w162 : Sig := bin true w44 w2
def w163 : Sig := bin false w44 w2
def w164 : Sig := bin true w14 w18
def w165 : Sig := neg w22
def w166 : Sig := bin true w16 w20
def w167 : Sig := bin true w14 w19
def w168 : Sig := neg w45
def w169 : Sig := bin true w16 w1
def w170 : Sig := neg w41
def w171 : Sig := bin true w16 w2
def w172 : Sig := neg w171
def w173 : Sig := neg w23
def w174 : Sig := bin false w14 w23
def w175 : Sig := bin true w14 w23
def w176 : Sig := bin true w16 w21
def w177 : Sig := bin false w0 w23
def w178 : Sig := bin false w0 w27
def w179 : Sig := neg w178
def w180 : Sig := bin true w84 w2
def w181 : Sig := bin true w150 w1
def w182 : Sig := bin true w177 w3
def w183 : Sig := neg w91
def w184 : Sig := bin true w91 w1
def w185 : Sig := bin false w91 w2
def w186 : Sig := bin true w91 w2
def w187 : Sig := neg w51
def w188 : Sig := bin true w0 w49
def w189 : Sig := bin true w49 w4
def w190 : Sig := bin false w49 w4
def w191 : Sig := bin true w51 w3
def w192 : Sig := bin true w18 w28
def w193 : Sig := bin false w18 w15
def w194 : Sig := bin true w18 w15
def w195 : Sig := neg w52
def w196 : Sig := bin false w18 w29
def w197 : Sig := bin true w18 w29
def w198 : Sig := neg w48
def w199 : Sig := bin false w3 w48
def w200 : Sig := bin false w4 w48
def w201 : Sig := neg w71
def w202 : Sig := bin true w0 w58
def w203 : Sig := bin true w58 w2
def w204 : Sig := bin true w71 w1
def w205 : Sig := bin true w20 w26
def w206 : Sig := bin true w24 w22
def w207 : Sig := bin true w26 w3
def w208 : Sig := bin true w26 w1
def w209 : Sig := bin true w22 w2
def w210 : Sig := neg w209
def w211 : Sig := bin true w0 w26
def w212 : Sig := neg w211
def w213 : Sig := bin false w20 w17
def w214 : Sig := bin true w20 w17
def w215 : Sig := bin true w22 w15
def w216 : Sig := bin false w1 w17
def w217 : Sig := neg w140
def w218 : Sig := bin false w20 w27
def w219 : Sig := bin true w20 w27
def w220 : Sig := bin true w26 w21
def w221 : Sig := bin false w1 w27
def w222 : Sig := bin false w3 w27
def w223 : Sig := bin false w20 w13
def w224 : Sig := bin true w20 w13
def w225 : Sig := bin true w24 w11
def w226 : Sig := bin false w2 w17
def w227 : Sig := neg w226
def w228 : Sig := bin true w77 w1
def w229 : Sig := bin true w216 w3
def w230 : Sig := bin false w2 w23
def w231 : Sig := neg w230
def w232 : Sig := bin true w0 w86
def w233 : Sig := bin true w221 w3
def w234 : Sig := neg w93
def w235 : Sig := bin true w0 w92
def w236 : Sig := bin true w92 w2
def w237 : Sig := bin true w93 w1
def w238 : Sig := neg w98
def w239 : Sig := neg w97
def w240 : Sig := bin true w98 w3
def w241 : Sig := bin true w4 w13
def w242 : Sig := neg w66
def w243 : Sig := bin true w64 w4
def w244 : Sig := bin true w0 w64
def w245 : Sig := bin false w64 w4
def w246 : Sig := bin true w66 w3
def w247 : Sig := bin false w0 w57
def w248 : Sig := bin false w208 w3
def w249 : Sig := bin false w34 w3
def w250 : Sig := bin true w34 w4
def w251 : Sig := bin true w19 w28
def w252 : Sig := bin false w19 w15
def w253 : Sig := bin true w19 w15
def w254 : Sig := bin false w19 w29
def w255 : Sig := bin true w19 w29
def w256 : Sig := neg w65
def w257 : Sig := neg w67
def w258 : Sig := bin false w0 w65
def w259 : Sig := bin false w4 w65
def w260 : Sig := bin false w3 w67
def w261 : Sig := neg w63
def w262 : Sig := bin false w3 w63
def w263 : Sig := bin false w4 w63
def w264 : Sig := neg w69
def w265 : Sig := neg w72
def w266 : Sig := bin false w28 w11
def w267 : Sig := bin true w28 w11
def w268 : Sig := neg w79
def w269 : Sig := bin true w1 w80
def w270 : Sig := bin false w4 w25
def w271 : Sig := neg w270
def w272 : Sig := bin true w0 w88
def w273 : Sig := bin true w1 w222
def w274 : Sig := neg w99
def w275 : Sig := neg w154
def w276 : Sig := bin false w2 w99
def w277 : Sig := bin true w2 w99
def w278 : Sig := bin true w1 w153
def w279 : Sig := bin true w99 w4
def w280 : Sig := bin true w100 w3
def w281 : Sig := bin false w1 w69
def w282 : Sig := bin false w2 w69
def w283 : Sig := bin true w2 w69
def w284 : Sig := bin false w1 w143
def w285 : Sig := bin false w3 w38
def w286 : Sig := bin false w1 w46
def w287 : Sig := bin true w2 w46
def w288 : Sig := bin true w0 w24
def w289 : Sig := bin true w0 w22
def w290 : Sig := bin false w1 w288
def w291 : Sig := bin false w3 w289
def w292 : Sig := bin false w15 w23
def w293 : Sig := bin true w15 w23
def w294 : Sig := neg w76
def w295 : Sig := neg w241
def w296 : Sig := bin false w2 w76
def w297 : Sig := bin false w1 w78
def w298 : Sig := bin false w4 w76
def w299 : Sig := bin false w3 w101
def w300 : Sig := neg w81
def w301 : Sig := bin false w1 w81
def w302 : Sig := bin false w2 w81
def w303 : Sig := bin false w0 w50
def w304 : Sig := bin false w4 w50
def w305 : Sig := bin false w3 w52
def w306 : Sig := bin false w0 w70
def w307 : Sig := bin false w2 w70
def w308 : Sig := bin false w1 w72
def w309 : Sig := bin false w0 w60
def w310 : Sig := bin false w1 w207
def w311 : Sig := bin false w1 w43
def w312 : Sig := bin false w3 w169
def w313 : Sig := bin false w21 w27
def w314 : Sig := bin false w21 w13
def w315 : Sig := neg w89
def w316 : Sig := neg w94
def w317 : Sig := bin false w0 w89
def w318 : Sig := bin false w2 w89
def w319 : Sig := bin false w1 w94
def w320 : Sig := bin false w29 w11
def w321 : Sig := bin true w4 w48
def w322 : Sig := bin true w4 w63
def w323 : Sig := bin true w2 w81
def w324 : Sig := bin false w2 w59
def w325 : Sig := bin false w96 w1
def w326 : Sig := bin true w96 w1
def w327 : Sig := bin true w95 w2
def w328 : Sig := bin false w96 w3
def w329 : Sig := bin true w96 w3
def w330 : Sig := bin true w96 w4
def w331 : Sig := bin false w96 w4
def w332 : Sig := bin false w90 w0
def w333 : Sig := bin true w90 w0
def w334 : Sig := bin false w90 w1
def w335 : Sig := bin true w90 w1
def w336 : Sig := bin false w90 w2
def w337 : Sig := bin true w90 w2
def w338 : Sig := bin true w90 w4
def w339 : Sig := bin false w83 w0
def w340 : Sig := bin true w83 w0
def w341 : Sig := bin false w83 w1
def w342 : Sig := bin true w83 w1
def w343 : Sig := bin false w83 w3
def w344 : Sig := bin true w83 w3
def w345 : Sig := bin false w74 w1
def w346 : Sig := bin true w74 w1
def w347 : Sig := bin false w74 w2
def w348 : Sig := bin true w74 w2
def w349 : Sig := bin false w74 w3
def w350 : Sig := bin true w74 w3
def w351 : Sig := bin false w102 w1
def w352 : Sig := bin true w102 w1
def w353 : Sig := bin false w102 w2
def w354 : Sig := bin true w102 w2
def w355 : Sig := bin false w102 w3
def w356 : Sig := bin true w102 w3
def w357 : Sig := bin true w104 w0
def w358 : Sig := bin false w104 w2
def w359 : Sig := bin true w104 w2
def w360 : Sig := bin true w106 w1
def w361 : Sig := bin false w104 w3
def w362 : Sig := bin true w104 w3
def w363 : Sig := bin true w108 w0
def w364 : Sig := bin true w108 w1
def w365 : Sig := bin false w108 w2
def w366 : Sig := bin true w108 w2
def w367 : Sig := bin true w9 w10
def w368 : Sig := bin true w9 w14
def w369 : Sig := bin true w8 w0
def w370 : Sig := bin true w8 w1
def w371 : Sig := bin false w103 w1
def w372 : Sig := bin true w103 w1
def w373 : Sig := bin false w103 w2
def w374 : Sig := bin true w103 w2
def w375 : Sig := bin false w103 w3
def w376 : Sig := bin true w103 w3
def w377 : Sig := bin true w9 w18
def w378 : Sig := bin true w9 w20
def w379 : Sig := bin true w8 w2
def w380 : Sig := bin false w0 w105
def w381 : Sig := bin false w107 w1
def w382 : Sig := bin true w105 w2
def w383 : Sig := bin false w105 w3
def w384 : Sig := bin true w105 w3
def w385 : Sig := bin false w9 w19
def w386 : Sig := bin false w0 w109
def w387 : Sig := bin false w1 w109
def w388 : Sig := bin false w2 w109
def w389 : Sig := bin true w2 w109
def w390 : Sig := bin false w9 w15
def w391 : Sig := bin false w9 w21
def w392 : Sig := bin false w9 w11
def w393 : Sig := bin false w68 w0
def w394 : Sig := bin true w68 w0
def w395 : Sig := bin false w68 w1
def w396 : Sig := bin true w68 w1
def w397 : Sig := bin false w68 w2
def w398 : Sig := bin true w68 w2
def w399 : Sig := bin false w68 w4
def w400 : Sig := bin false w61 w0
def w401 : Sig := bin true w61 w0
def w402 : Sig := bin true w6 w2
def w403 : Sig := bin false w61 w3
def w404 : Sig := bin true w61 w3
def w405 : Sig := bin false w61 w4
def w406 : Sig := bin true w61 w4
def w407 : Sig := bin false w112 w0
def w408 : Sig := bin true w112 w0
def w409 : Sig := bin false w112 w3
def w410 : Sig := bin true w112 w3
def w411 : Sig := bin false w112 w4
def w412 : Sig := bin true w112 w4
def w413 : Sig := bin false w114 w0
def w414 : Sig := bin true w114 w0
def w415 : Sig := bin true w114 w1
def w416 : Sig := bin false w114 w4
def w417 : Sig := bin true w114 w4
def w418 : Sig := bin true w116 w3
def w419 : Sig := bin true w110 w1
def w420 : Sig := bin true w110 w3
def w421 : Sig := bin false w110 w4
def w422 : Sig := bin true w110 w4
def w423 : Sig := bin true w7 w10
def w424 : Sig := bin true w6 w0
def w425 : Sig := bin true w6 w3
def w426 : Sig := bin true w7 w14
def w427 : Sig := bin false w111 w1
def w428 : Sig := bin true w111 w1
def w429 : Sig := bin false w111 w3
def w430 : Sig := bin true w111 w3
def w431 : Sig := bin false w111 w4
def w432 : Sig := bin true w111 w4
def w433 : Sig := bin true w7 w20
def w434 : Sig := bin false w0 w113
def w435 : Sig := bin false w113 w3
def w436 : Sig := bin true w113 w3
def w437 : Sig := bin false w113 w4
def w438 : Sig := bin true w113 w4
def w439 : Sig := bin true w6 w4
def w440 : Sig := bin true w7 w28
def w441 : Sig := bin false w0 w115
def w442 : Sig := bin false w1 w115
def w443 : Sig := bin false w117 w3
def w444 : Sig := bin true w115 w4
def w445 : Sig := bin false w7 w15
def w446 : Sig := bin false w7 w21
def w447 : Sig := bin false w7 w29
def w448 : Sig := bin false w7 w11
def w449 : Sig := bin false w54 w0
def w450 : Sig := bin true w54 w0
def w451 : Sig := bin false w54 w1
def w452 : Sig := bin true w54 w1
def w453 : Sig := bin true w53 w2
def w454 : Sig := bin false w54 w3
def w455 : Sig := bin true w54 w3
def w456 : Sig := bin true w53 w4
def w457 : Sig := bin false w47 w0
def w458 : Sig := bin true w47 w0
def w459 : Sig := bin false w47 w2
def w460 : Sig := bin false w47 w3
def w461 : Sig := bin true w47 w3
def w462 : Sig := bin false w47 w4
def w463 : Sig := bin true w47 w4
def w464 : Sig := bin false w122 w1
def w465 : Sig := bin true w122 w1
def w466 : Sig := bin false w122 w2
def w467 : Sig := bin true w122 w2
def w468 : Sig := bin false w122 w4
def w469 : Sig := bin true w122 w4
def w470 : Sig := bin true w124 w3
def w471 : Sig := bin false w118 w2
def w472 : Sig := bin true w118 w2
def w473 : Sig := bin true w120 w1
def w474 : Sig := bin true w118 w3
def w475 : Sig := bin false w118 w4
def w476 : Sig := bin true w118 w4
def w477 : Sig := bin true w5 w18
def w478 : Sig := bin true w5 w20
def w479 : Sig := bin false w121 w1
def w480 : Sig := bin true w119 w2
def w481 : Sig := bin false w119 w3
def w482 : Sig := bin true w119 w3
def w483 : Sig := bin false w119 w4
def w484 : Sig := bin true w119 w4
def w485 : Sig := bin false w5 w19
def w486 : Sig := bin true w5 w28
def w487 : Sig := bin false w1 w123
def w488 : Sig := bin false w2 w123
def w489 : Sig := bin true w2 w123
def w490 : Sig := bin false w125 w3
def w491 : Sig := bin true w123 w4
def w492 : Sig := bin false w5 w21
def w493 : Sig := bin false w5 w29
def w494 : Sig := bin false w40 w1
def w495 : Sig := bin true w40 w1
def w496 : Sig := bin true w39 w1
def w497 : Sig := bin false w40 w2
def w498 : Sig := bin true w40 w2
def w499 : Sig := bin false w40 w3
def w500 : Sig := bin true w40 w3
def w501 : Sig := bin true w39 w4
def w502 : Sig := bin false w31 w1
def w503 : Sig := bin true w31 w1
def w504 : Sig := bin true w30 w2
def w505 : Sig := bin false w31 w3
def w506 : Sig := bin true w31 w3
def w507 : Sig := bin true w30 w3
def w508 : Sig := bin false w31 w4
def w509 : Sig := bin true w31 w4
def w510 : Sig := neg w130
def w511 : Sig := bin true w129 w4
def w512 : Sig := neg w163
def w513 : Sig := bin true w136 w2
def w514 : Sig := bin true w131 w3
def w515 : Sig := bin true w131 w1
def w516 : Sig := bin true w42 w4
def w517 : Sig := bin false w12 w23
def w518 : Sig := neg w517
def w519 : Sig := bin true w147 w4
def w520 : Sig := neg w185
def w521 : Sig := bin true w151 w2
def w522 : Sig := neg w158
def w523 : Sig := bin true w156 w4
def w524 : Sig := bin false w0 w209
def w525 : Sig := neg w524
def w526 : Sig := bin true w62 w18
def w527 : Sig := bin false w16 w25
def w528 : Sig := neg w527
def w529 : Sig := bin true w174 w2
def w530 : Sig := bin true w16 w92
def w531 : Sig := bin true w37 w2
def w532 : Sig := bin false w0 w52
def w533 : Sig := neg w532
def w534 : Sig := bin false w0 w72
def w535 : Sig := neg w534
def w536 : Sig := bin false w0 w140
def w537 : Sig := neg w536
def w538 : Sig := bin false w0 w67
def w539 : Sig := neg w538
def w540 : Sig := bin false w0 w94
def w541 : Sig := neg w540
def w542 : Sig := neg w190
def w543 : Sig := bin true w0 w190
def w544 : Sig := bin true w0 w51
def w545 : Sig := bin false w18 w17
def w546 : Sig := neg w545
def w547 : Sig := bin true w193 w4
def w548 : Sig := neg w196
def w549 : Sig := bin true w0 w196
def w550 : Sig := bin false w26 w15
def w551 : Sig := neg w550
def w552 : Sig := bin false w26 w21
def w553 : Sig := neg w552
def w554 : Sig := bin false w26 w11
def w555 : Sig := neg w554
def w556 : Sig := bin true w223 w4
def w557 : Sig := bin true w276 w4
def w558 : Sig := bin true w20 w154
def w559 : Sig := neg w282
def w560 : Sig := bin false w2 w38
def w561 : Sig := neg w560
def w562 : Sig := bin true w284 w4
def w563 : Sig := bin false w2 w45
def w564 : Sig := neg w563
def w565 : Sig := bin false w2 w289
def w566 : Sig := neg w565
def w567 : Sig := neg w307
def w568 : Sig := neg w324
def w569 : Sig := bin false w2 w169
def w570 : Sig := neg w569
def w571 : Sig := bin true w92 w28
def w572 : Sig := bin true w97 w4
def w573 : Sig := neg w572
def w574 : Sig := neg w78
def w575 : Sig := bin false w4 w78
def w576 : Sig := bin false w3 w241
def w577 : Sig := bin false w2 w101
def w578 : Sig := neg w577
def w579 : Sig := bin false w1 w241
def w580 : Sig := neg w318
def w581 : Sig := neg w302
def w582 : Sig := neg w245
def w583 : Sig := bin false w56 w4
def w584 : Sig := neg w583
def w585 : Sig := bin false w33 w4
def w586 : Sig := neg w585
def w587 : Sig := bin true w249 w4
def w588 : Sig := bin true w12 w22
def w589 : Sig := neg w588
def w590 : Sig := bin false w19 w17
def w591 : Sig := neg w590
def w592 : Sig := neg w203
def w593 : Sig := neg w205
def w594 : Sig := neg w531
def w595 : Sig := neg w254
def w596 : Sig := bin true w216 w2
def w597 : Sig := neg w596
def w598 : Sig := neg w236
def w599 : Sig := bin false w28 w13
def w600 : Sig := neg w599
def w601 : Sig := bin false w4 w143
def w602 : Sig := neg w601
def w603 : Sig := bin false w4 w288
def w604 : Sig := neg w603
def w605 : Sig := neg w304
def w606 : Sig := bin false w4 w43
def w607 : Sig := neg w606
def w608 : Sig := neg w200
def w609 : Sig := bin true w2 w100
def w610 : Sig := neg w609
def w611 : Sig := bin true w153 w4
def w612 : Sig := neg w611
def w613 : Sig := neg w101
def w614 : Sig := neg w575
def w615 : Sig := neg w259
def w616 : Sig := neg w263
def w617 : Sig := bin true w12 w28
def w618 : Sig := neg w617
def w619 : Sig := bin true w0 w71
def w620 : Sig := neg w619
def w621 : Sig := neg w128
def w622 : Sig := neg w516
def w623 : Sig := bin true w14 w26
def w624 : Sig := neg w623
def w625 : Sig := bin false w17 w25
def w626 : Sig := neg w625
def w627 : Sig := neg w544
def w628 : Sig := bin true w0 w270
def w629 : Sig := neg w628
def w630 : Sig := neg w159
def w631 : Sig := bin true w0 w66
def w632 : Sig := neg w631
def w633 : Sig := bin true w150 w4
def w634 : Sig := neg w633
def w635 : Sig := neg w192
def w636 : Sig := neg w189
def w637 : Sig := bin true w16 w18
def w638 : Sig := neg w637
def w639 : Sig := neg w162
def w640 : Sig := bin false w25 w23
def w641 : Sig := neg w640
def w642 : Sig := bin false w27 w11
def w643 : Sig := neg w642
def w644 : Sig := bin true w2 w79
def w645 : Sig := neg w644
def w646 : Sig := bin true w2 w87
def w647 : Sig := neg w646
def w648 : Sig := bin true w85 w4
def w649 : Sig := neg w648
def w650 : Sig := bin true w77 w4
def w651 : Sig := neg w650
def w652 : Sig := bin false w29 w13
def w653 : Sig := neg w652
def w654 : Sig := neg w243
def w655 : Sig := bin true w0 w230
def w656 : Sig := neg w655
def w657 : Sig := bin true w0 w221
def w658 : Sig := bin false w3 w657
def w659 : Sig := neg w194
def w660 : Sig := neg w321
def w661 : Sig := bin false w3 w321
def w662 : Sig := bin true w177 w2
def w663 : Sig := neg w662
def w664 : Sig := bin true w178 w1
def w665 : Sig := bin false w3 w664
def w666 : Sig := neg w184
def w667 : Sig := neg w186
def w668 : Sig := bin false w1 w186
def w669 : Sig := neg w235
def w670 : Sig := bin true w0 w93
def w671 : Sig := neg w670
def w672 : Sig := bin false w1 w670
def w673 : Sig := neg w267
def w674 : Sig := neg w283
def w675 : Sig := bin false w1 w283
def w676 : Sig := bin true w10 w27
def w677 : Sig := neg w676
def w678 : Sig := bin false w3 w250
def w679 : Sig := bin true w22 w13
def w680 : Sig := neg w679
def w681 : Sig := bin true w26 w11
def w682 : Sig := bin false w3 w681
def w683 : Sig := bin true w14 w27
def w684 : Sig := neg w683
def w685 : Sig := bin false w1 w287
def w686 : Sig := bin true w24 w17
def w687 : Sig := neg w686
def w688 : Sig := bin true w26 w15
def w689 : Sig := bin false w1 w688
def w690 : Sig := neg w251
def w691 : Sig := bin false w0 w251
def w692 : Sig := neg w167
def w693 : Sig := bin true w16 w19
def w694 : Sig := neg w693
def w695 : Sig := bin false w3 w693
def w696 : Sig := neg w219
def w697 : Sig := bin false w0 w220
def w698 : Sig := neg w253
def w699 : Sig := neg w322
def w700 : Sig := bin false w3 w322
def w701 : Sig := neg w197
def w702 : Sig := bin false w0 w197
def w703 : Sig := neg w152
def w704 : Sig := bin true w12 w29
def w705 : Sig := neg w704
def w706 : Sig := bin false w1 w704
def w707 : Sig := neg w293
def w708 : Sig := neg w323
def w709 : Sig := bin false w1 w323
def w710 : Sig := neg w255
def w711 : Sig := bin false w0 w255
def w712 : Sig := bin false w59 w13
def w713 : Sig := neg w214
def w714 : Sig := bin false w300 w1
def w715 : Sig := bin true w300 w1
def w716 : Sig := bin true w300 w2
def w717 : Sig := bin true w300 w4
def w718 : Sig := bin false w316 w0
def w719 : Sig := bin true w316 w0
def w720 : Sig := bin false w316 w1
def w721 : Sig := bin true w316 w1
def w722 : Sig := bin true w315 w2
def w723 : Sig := bin true w316 w4
def w724 : Sig := bin true w261 w3
def w725 : Sig := bin true w261 w4
def w726 : Sig := bin false w261 w3
def w727 : Sig := bin true w257 w0
def w728 : Sig := bin true w173 w2
def w729 : Sig := bin true w257 w3
def w730 : Sig := bin true w256 w4
def w731 : Sig := bin false w257 w0
def w732 : Sig := bin false w257 w3
def w733 : Sig := bin false w295 w1
def w734 : Sig := bin true w295 w1
def w735 : Sig := bin true w613 w2
def w736 : Sig := bin false w295 w3
def w737 : Sig := bin true w295 w3
def w738 : Sig := bin true w574 w4
def w739 : Sig := bin true w295 w27
def w740 : Sig := bin true w328 w1
def w741 : Sig := bin true w328 w4
def w742 : Sig := bin false w328 w1
def w743 : Sig := bin false w95 w3
def w744 : Sig := bin true w743 w2
def w745 : Sig := bin false w328 w4
def w746 : Sig := bin true w331 w3
def w747 : Sig := bin true w325 w3
def w748 : Sig := bin true w325 w4
def w749 : Sig := bin true w96 w10
def w750 : Sig := bin true w95 w10
def w751 : Sig := bin true w95 w4
def w752 : Sig := bin true w96 w14
def w753 : Sig := bin true w96 w18
def w754 : Sig := bin true w96 w20
def w755 : Sig := bin true w95 w20
def w756 : Sig := bin true w95 w3
def w757 : Sig := bin true w96 w28
def w758 : Sig := bin false w96 w21
def w759 : Sig := bin true w96 w21
def w760 : Sig := bin false w96 w29
def w761 : Sig := bin true w96 w29
def w762 : Sig := bin true w198 w3
def w763 : Sig := bin true w198 w4
def w764 : Sig := bin false w198 w2
def w765 : Sig := bin false w198 w3
def w766 : Sig := bin false w334 w0
def w767 : Sig := bin true w334 w0
def w768 : Sig := bin false w334 w2
def w769 : Sig := bin true w336 w1
def w770 : Sig := bin true w334 w4
def w771 : Sig := bin true w332 w1
def w772 : Sig := bin true w332 w4
def w773 : Sig := bin true w90 w10
def w774 : Sig := bin true w90 w14
def w775 : Sig := bin true w90 w18
def w776 : Sig := bin true w90 w20
def w777 : Sig := bin false w90 w19
def w778 : Sig := bin true w90 w19
def w779 : Sig := bin true w90 w28
def w780 : Sig := bin false w90 w11
def w781 : Sig := bin true w90 w11
def w782 : Sig := bin true w90 w23
def w783 : Sig := bin false w339 w1
def w784 : Sig := bin true w339 w1
def w785 : Sig := bin false w339 w3
def w786 : Sig := bin true w339 w3
def w787 : Sig := bin true w341 w0
def w788 : Sig := bin false w341 w3
def w789 : Sig := bin true w341 w3
def w790 : Sig := bin true w343 w0
def w791 : Sig := bin true w343 w1
def w792 : Sig := bin true w83 w10
def w793 : Sig := bin true w173 w10
def w794 : Sig := bin true w83 w14
def w795 : Sig := bin true w146 w14
def w796 : Sig := bin true w83 w18
def w797 : Sig := bin true w83 w20
def w798 : Sig := bin true w146 w20
def w799 : Sig := bin true w173 w20
def w800 : Sig := bin true w82 w20
def w801 : Sig := bin true w83 w28
def w802 : Sig := bin false w83 w15
def w803 : Sig := bin true w83 w15
def w804 : Sig := bin false w83 w21
def w805 : Sig := bin true w83 w21
def w806 : Sig := bin false w83 w11
def w807 : Sig := bin true w83 w11
def w808 : Sig := bin true w425 w4
def w809 : Sig := bin true w172 w16
def w810 : Sig := bin false w172 w1
def w811 : Sig := bin true w172 w1
def w812 : Sig := bin false w172 w3
def w813 : Sig := bin true w172 w3
def w814 : Sig := bin true w217 w24
def w815 : Sig := bin false w217 w0
def w816 : Sig := bin true w217 w0
def w817 : Sig := bin false w217 w1
def w818 : Sig := bin true w217 w1
def w819 : Sig := bin true w217 w4
def w820 : Sig := bin false w195 w0
def w821 : Sig := bin true w195 w0
def w822 : Sig := bin false w195 w3
def w823 : Sig := bin true w195 w3
def w824 : Sig := bin false w265 w0
def w825 : Sig := bin true w265 w0
def w826 : Sig := bin false w265 w1
def w827 : Sig := bin true w265 w1
def w828 : Sig := bin false w345 w2
def w829 : Sig := bin true w347 w1
def w830 : Sig := bin false w345 w3
def w831 : Sig := bin true w345 w3
def w832 : Sig := bin true w349 w1
def w833 : Sig := bin true w74 w10
def w834 : Sig := bin true w74 w14
def w835 : Sig := bin true w73 w14
def w836 : Sig := bin true w74 w18
def w837 : Sig := bin true w74 w20
def w838 : Sig := bin true w73 w20
def w839 : Sig := bin false w74 w19
def w840 : Sig := bin true w74 w19
def w841 : Sig := bin true w74 w28
def w842 : Sig := bin false w74 w21
def w843 : Sig := bin true w74 w21
def w844 : Sig := bin false w212 w1
def w845 : Sig := bin true w212 w1
def w846 : Sig := bin false w212 w3
def w847 : Sig := bin true w212 w3
def w848 : Sig := bin false w168 w1
def w849 : Sig := bin true w168 w1
def w850 : Sig := bin true w145 w12
def w851 : Sig := bin false w145 w1
def w852 : Sig := bin true w145 w1
def w853 : Sig := bin false w145 w3
def w854 : Sig := bin true w145 w3
def w855 : Sig := bin false w264 w1
def w856 : Sig := bin true w264 w1
def w857 : Sig := bin false w351 w2
def w858 : Sig := bin true w353 w1
def w859 : Sig := bin false w351 w3
def w860 : Sig := bin true w351 w3
def w861 : Sig := bin true w355 w1
def w862 : Sig := bin true w102 w18
def w863 : Sig := bin true w102 w20
def w864 : Sig := bin false w8 w0
def w865 : Sig := bin true w864 w20
def w866 : Sig := bin false w102 w19
def w867 : Sig := bin true w102 w19
def w868 : Sig := bin true w102 w28
def w869 : Sig := bin false w102 w21
def w870 : Sig := bin true w102 w21
def w871 : Sig := bin true w358 w0
def w872 : Sig := bin false w358 w3
def w873 : Sig := bin true w358 w3
def w874 : Sig := bin true w361 w0
def w875 : Sig := bin true w365 w1
def w876 : Sig := bin false w165 w3
def w877 : Sig := bin false w165 w4
def w878 : Sig := bin true w106 w10
def w879 : Sig := bin true w104 w14
def w880 : Sig := bin true w104 w16
def w881 : Sig := bin false w357 w3
def w882 : Sig := bin true w106 w20
def w883 : Sig := bin true w106 w22
def w884 : Sig := bin true w104 w28
def w885 : Sig := bin false w104 w15
def w886 : Sig := bin true w104 w15
def w887 : Sig := bin false w104 w25
def w888 : Sig := bin true w106 w21
def w889 : Sig := bin false w104 w13
def w890 : Sig := bin true w106 w11
def w891 : Sig := bin true w108 w10
def w892 : Sig := bin true w108 w16
def w893 : Sig := bin true w108 w18
def w894 : Sig := bin true w108 w22
def w895 : Sig := bin false w108 w19
def w896 : Sig := bin true w108 w19
def w897 : Sig := bin false w108 w11
def w898 : Sig := bin true w108 w11
def w899 : Sig := bin false w9 w13
def w900 : Sig := bin true w899 w1
def w901 : Sig := bin true w392 w3
def w902 : Sig := bin true w385 w0
def w903 : Sig := bin true w385 w3
def w904 : Sig := bin true w391 w0
def w905 : Sig := bin false w9 w25
def w906 : Sig := bin true w905 w1
def w907 : Sig := bin true w390 w1
def w908 : Sig := bin true w9 w32
def w909 : Sig := bin true w9 w35
def w910 : Sig := bin true w9 w62
def w911 : Sig := bin true w9 w84
def w912 : Sig := bin true w9 w49
def w913 : Sig := bin true w9 w75
def w914 : Sig := bin true w9 w86
def w915 : Sig := bin true w9 w98
def w916 : Sig := bin true w9 w64
def w917 : Sig := bin false w9 w57
def w918 : Sig := bin true w9 w57
def w919 : Sig := bin false w9 w34
def w920 : Sig := bin true w9 w34
def w921 : Sig := bin true w9 w99
def w922 : Sig := bin true w369 w1
def w923 : Sig := bin false w9 w36
def w924 : Sig := bin true w9 w36
def w925 : Sig := bin false w9 w55
def w926 : Sig := bin true w9 w55
def w927 : Sig := bin false w9 w50
def w928 : Sig := bin true w9 w50
def w929 : Sig := bin false w9 w41
def w930 : Sig := bin true w9 w41
def w931 : Sig := bin false w9 w48
def w932 : Sig := bin true w9 w48
def w933 : Sig := bin false w2 w372
def w934 : Sig := bin false w1 w374
def w935 : Sig := bin false w3 w372
def w936 : Sig := bin false w9 w76
def w937 : Sig := bin true w9 w76
def w938 : Sig := bin false w9 w65
def w939 : Sig := bin true w9 w65
def w940 : Sig := bin false w9 w63
def w941 : Sig := bin true w9 w63
def w942 : Sig := bin false w275 w1
def w943 : Sig := bin true w275 w1
def w944 : Sig := bin false w275 w3
def w945 : Sig := bin true w275 w3
def w946 : Sig := bin true w274 w4
def w947 : Sig := bin false w271 w0
def w948 : Sig := bin true w271 w0
def w949 : Sig := bin false w271 w1
def w950 : Sig := bin true w271 w1
def w951 : Sig := bin false w268 w1
def w952 : Sig := bin true w268 w1
def w953 : Sig := bin false w393 w1
def w954 : Sig := bin true w393 w1
def w955 : Sig := bin true w393 w2
def w956 : Sig := bin true w395 w0
def w957 : Sig := bin false w395 w2
def w958 : Sig := bin true w397 w1
def w959 : Sig := bin true w68 w10
def w960 : Sig := bin false w394 w4
def w961 : Sig := bin true w68 w18
def w962 : Sig := bin false w396 w2
def w963 : Sig := bin false w398 w1
def w964 : Sig := bin false w68 w19
def w965 : Sig := bin true w68 w19
def w966 : Sig := bin false w68 w29
def w967 : Sig := bin false w68 w15
def w968 : Sig := bin false w68 w21
def w969 : Sig := bin false w68 w11
def w970 : Sig := bin true w68 w11
def w971 : Sig := bin false w6 w3
def w972 : Sig := bin true w971 w2
def w973 : Sig := bin false w403 w0
def w974 : Sig := bin true w403 w0
def w975 : Sig := bin false w403 w4
def w976 : Sig := bin true w405 w3
def w977 : Sig := bin false w6 w0
def w978 : Sig := bin true w977 w2
def w979 : Sig := bin true w400 w3
def w980 : Sig := bin true w61 w10
def w981 : Sig := bin true w61 w14
def w982 : Sig := bin true w61 w18
def w983 : Sig := bin true w61 w20
def w984 : Sig := bin true w61 w28
def w985 : Sig := bin false w61 w15
def w986 : Sig := bin true w61 w15
def w987 : Sig := bin false w61 w29
def w988 : Sig := bin true w61 w29
def w989 : Sig := bin false w141 w3
def w990 : Sig := bin true w141 w3
def w991 : Sig := bin true w210 w22
def w992 : Sig := bin true w210 w2
def w993 : Sig := bin false w210 w0
def w994 : Sig := bin true w210 w0
def w995 : Sig := bin false w210 w3
def w996 : Sig := bin true w210 w3
def w997 : Sig := bin false w242 w3
def w998 : Sig := bin false w242 w0
def w999 : Sig := bin true w242 w0
def w1000 : Sig := bin true w242 w3
def w1001 : Sig := bin true w409 w4
def w1002 : Sig := bin false w409 w0
def w1003 : Sig := bin true w409 w0
def w1004 : Sig := bin false w409 w4
def w1005 : Sig := bin true w411 w3
def w1006 : Sig := bin true w407 w3
def w1007 : Sig := bin true w112 w12
def w1008 : Sig := bin true w112 w14
def w1009 : Sig := bin true w112 w24
def w1010 : Sig := bin true w112 w28
def w1011 : Sig := bin false w112 w15
def w1012 : Sig := bin true w112 w15
def w1013 : Sig := bin false w112 w29
def w1014 : Sig := bin true w112 w29
def w1015 : Sig := bin false w451 w0
def w1016 : Sig := bin true w451 w0
def w1017 : Sig := bin false w451 w3
def w1018 : Sig := bin true w451 w3
def w1019 : Sig := bin true w416 w1
def w1020 : Sig := bin false w971 w4
def w1021 : Sig := bin true w1020 w2
def w1022 : Sig := bin false w416 w0
def w1023 : Sig := bin true w416 w0
def w1024 : Sig := bin true w413 w1
def w1025 : Sig := bin true w421 w3
def w1026 : Sig := bin false w138 w4
def w1027 : Sig := bin true w114 w10
def w1028 : Sig := bin true w971 w10
def w1029 : Sig := bin true w116 w14
def w1030 : Sig := bin true w114 w18
def w1031 : Sig := bin true w116 w20
def w1032 : Sig := bin true w116 w24
def w1033 : Sig := bin false w114 w17
def w1034 : Sig := bin true w116 w15
def w1035 : Sig := bin false w114 w23
def w1036 : Sig := bin true w116 w21
def w1037 : Sig := bin false w114 w11
def w1038 : Sig := bin true w114 w11
def w1039 : Sig := bin true w110 w18
def w1040 : Sig := bin true w110 w20
def w1041 : Sig := bin true w110 w24
def w1042 : Sig := bin true w110 w28
def w1043 : Sig := bin false w110 w21
def w1044 : Sig := bin true w110 w21
def w1045 : Sig := bin false w110 w29
def w1046 : Sig := bin true w110 w29
def w1047 : Sig := bin true w445 w1
def w1048 : Sig := bin false w7 w17
def w1049 : Sig := bin true w1048 w3
def w1050 : Sig := bin true w446 w0
def w1051 : Sig := bin false w7 w23
def w1052 : Sig := bin true w1051 w3
def w1053 : Sig := bin true w448 w3
def w1054 : Sig := bin true w447 w0
def w1055 : Sig := bin true w447 w1
def w1056 : Sig := bin true w7 w35
def w1057 : Sig := bin true w7 w44
def w1058 : Sig := bin true w7 w84
def w1059 : Sig := bin true w7 w91
def w1060 : Sig := bin true w7 w58
def w1061 : Sig := bin true w7 w75
def w1062 : Sig := bin true w7 w92
def w1063 : Sig := bin true w424 w2
def w1064 : Sig := bin true w7 w80
def w1065 : Sig := bin true w7 w88
def w1066 : Sig := bin true w7 w99
def w1067 : Sig := bin false w7 w69
def w1068 : Sig := bin true w7 w69
def w1069 : Sig := bin false w7 w36
def w1070 : Sig := bin true w7 w36
def w1071 : Sig := bin false w7 w46
def w1072 : Sig := bin true w7 w46
def w1073 : Sig := bin false w7 w55
def w1074 : Sig := bin true w7 w55
def w1075 : Sig := bin false w7 w70
def w1076 : Sig := bin true w7 w70
def w1077 : Sig := bin false w7 w60
def w1078 : Sig := bin true w7 w60
def w1079 : Sig := bin false w7 w41
def w1080 : Sig := bin true w7 w41
def w1081 : Sig := bin false w3 w428
def w1082 : Sig := bin false w4 w428
def w1083 : Sig := bin false w7 w76
def w1084 : Sig := bin true w7 w76
def w1085 : Sig := bin false w7 w89
def w1086 : Sig := bin true w7 w89
def w1087 : Sig := bin false w7 w81
def w1088 : Sig := bin true w7 w81
def w1089 : Sig := bin true w7 w59
def w1090 : Sig := bin false w239 w3
def w1091 : Sig := bin true w239 w3
def w1092 : Sig := bin true w238 w3
def w1093 : Sig := bin false w234 w0
def w1094 : Sig := bin true w234 w0
def w1095 : Sig := bin false w234 w1
def w1096 : Sig := bin true w234 w1
def w1097 : Sig := bin false w231 w0
def w1098 : Sig := bin true w231 w0
def w1099 : Sig := bin false w231 w3
def w1100 : Sig := bin true w231 w3
def w1101 : Sig := bin false w227 w1
def w1102 : Sig := bin true w227 w1
def w1103 : Sig := bin false w227 w3
def w1104 : Sig := bin true w227 w3
def w1105 : Sig := bin true w449 w1
def w1106 : Sig := bin false w449 w3
def w1107 : Sig := bin true w449 w3
def w1108 : Sig := bin true w454 w0
def w1109 : Sig := bin true w454 w1
def w1110 : Sig := bin true w54 w10
def w1111 : Sig := bin true w54 w14
def w1112 : Sig := bin false w450 w3
def w1113 : Sig := bin true w54 w20
def w1114 : Sig := bin false w452 w3
def w1115 : Sig := bin false w54 w27
def w1116 : Sig := bin false w54 w19
def w1117 : Sig := bin false w54 w15
def w1118 : Sig := bin true w54 w15
def w1119 : Sig := bin false w54 w17
def w1120 : Sig := bin false w54 w21
def w1121 : Sig := bin true w54 w21
def w1122 : Sig := bin false w54 w25
def w1123 : Sig := bin false w54 w23
def w1124 : Sig := bin false w54 w29
def w1125 : Sig := bin false w54 w11
def w1126 : Sig := bin true w54 w11
def w1127 : Sig := bin false w54 w13
def w1128 : Sig := bin false w201 w0
def w1129 : Sig := bin true w201 w0
def w1130 : Sig := bin false w201 w1
def w1131 : Sig := bin true w201 w1
def w1132 : Sig := bin false w460 w0
def w1133 : Sig := bin true w460 w0
def w1134 : Sig := bin false w460 w2
def w1135 : Sig := bin false w460 w4
def w1136 : Sig := bin true w462 w3
def w1137 : Sig := bin true w457 w3
def w1138 : Sig := bin true w47 w14
def w1139 : Sig := bin false w47 w19
def w1140 : Sig := bin true w47 w28
def w1141 : Sig := bin false w47 w15
def w1142 : Sig := bin true w47 w15
def w1143 : Sig := bin false w47 w21
def w1144 : Sig := bin false w47 w29
def w1145 : Sig := bin true w47 w29
def w1146 : Sig := bin false w47 w11
def w1147 : Sig := bin false w187 w0
def w1148 : Sig := bin false w187 w3
def w1149 : Sig := bin true w187 w0
def w1150 : Sig := bin true w187 w3
def w1151 : Sig := bin false w468 w1
def w1152 : Sig := bin true w468 w1
def w1153 : Sig := bin true w464 w4
def w1154 : Sig := bin false w464 w2
def w1155 : Sig := bin true w466 w1
def w1156 : Sig := bin true w475 w3
def w1157 : Sig := bin true w122 w10
def w1158 : Sig := bin true w124 w14
def w1159 : Sig := bin true w122 w18
def w1160 : Sig := bin true w124 w20
def w1161 : Sig := bin false w122 w19
def w1162 : Sig := bin true w122 w19
def w1163 : Sig := bin false w122 w23
def w1164 : Sig := bin true w122 w23
def w1165 : Sig := bin true w124 w21
def w1166 : Sig := bin true w471 w3
def w1167 : Sig := bin true w120 w10
def w1168 : Sig := bin true w118 w14
def w1169 : Sig := bin true w120 w20
def w1170 : Sig := bin true w120 w3
def w1171 : Sig := bin true w118 w28
def w1172 : Sig := bin false w118 w25
def w1173 : Sig := bin true w120 w21
def w1174 : Sig := bin false w118 w29
def w1175 : Sig := bin true w118 w29
def w1176 : Sig := bin false w5 w25
def w1177 : Sig := bin true w1176 w1
def w1178 : Sig := bin false w5 w23
def w1179 : Sig := bin true w1178 w3
def w1180 : Sig := bin true w485 w3
def w1181 : Sig := bin true w493 w1
def w1182 : Sig := bin true w5 w49
def w1183 : Sig := bin true w5 w58
def w1184 : Sig := bin true w481 w4
def w1185 : Sig := bin true w5 w86
def w1186 : Sig := bin true w5 w92
def w1187 : Sig := bin true w5 w64
def w1188 : Sig := bin false w5 w57
def w1189 : Sig := bin true w5 w57
def w1190 : Sig := bin true w5 w88
def w1191 : Sig := bin false w5 w50
def w1192 : Sig := bin true w5 w50
def w1193 : Sig := bin false w5 w70
def w1194 : Sig := bin true w5 w70
def w1195 : Sig := bin false w5 w60
def w1196 : Sig := bin true w5 w60
def w1197 : Sig := bin false w5 w65
def w1198 : Sig := bin true w5 w65
def w1199 : Sig := bin false w5 w89
def w1200 : Sig := bin true w5 w89
def w1201 : Sig := bin true w5 w59
def w1202 : Sig := bin false w183 w1
def w1203 : Sig := bin true w183 w1
def w1204 : Sig := bin false w179 w1
def w1205 : Sig := bin true w179 w1
def w1206 : Sig := bin false w179 w3
def w1207 : Sig := bin true w179 w3
def w1208 : Sig := bin false w499 w1
def w1209 : Sig := bin true w499 w1
def w1210 : Sig := bin false w494 w2
def w1211 : Sig := bin true w497 w1
def w1212 : Sig := bin true w494 w3
def w1213 : Sig := bin false w40 w17
def w1214 : Sig := bin false w40 w29
def w1215 : Sig := bin true w40 w18
def w1216 : Sig := bin true w40 w20
def w1217 : Sig := bin false w40 w19
def w1218 : Sig := bin true w40 w19
def w1219 : Sig := bin false w40 w15
def w1220 : Sig := bin false w40 w21
def w1221 : Sig := bin true w40 w21
def w1222 : Sig := bin false w40 w23
def w1223 : Sig := bin false w40 w11
def w1224 : Sig := bin false w160 w1
def w1225 : Sig := bin false w160 w2
def w1226 : Sig := bin true w160 w1
def w1227 : Sig := bin true w160 w2
def w1228 : Sig := bin false w155 w3
def w1229 : Sig := bin true w155 w3
def w1230 : Sig := bin false w502 w3
def w1231 : Sig := bin true w502 w3
def w1232 : Sig := bin true w505 w1
def w1233 : Sig := bin false w505 w4
def w1234 : Sig := bin true w508 w3
def w1235 : Sig := bin false w31 w13
def w1236 : Sig := bin true w31 w20
def w1237 : Sig := bin false w31 w19
def w1238 : Sig := bin true w31 w28
def w1239 : Sig := bin false w31 w15
def w1240 : Sig := bin false w31 w21
def w1241 : Sig := bin true w31 w21
def w1242 : Sig := bin false w31 w25
def w1243 : Sig := bin false w31 w29
def w1244 : Sig := bin true w31 w29
def w1245 : Sig := bin false w31 w11
def w1246 : Sig := bin false w132 w1
def w1247 : Sig := bin false w132 w3
def w1248 : Sig := bin true w132 w1
def w1249 : Sig := bin true w132 w3
def w1250 : Sig := bin false w126 w3
def w1251 : Sig := bin false w126 w4
def w1252 : Sig := bin true w126 w3
def w1253 : Sig := bin true w126 w4
def w1254 : Sig := bin false w10 w107
def w1255 : Sig := bin false w0 w402
def w1256 : Sig := bin false w10 w109
def w1257 : Sig := bin false w10 w115
def w1258 : Sig := bin false w0 w425
def w1259 : Sig := bin false w427 w3
def w1260 : Sig := bin true w427 w3
def w1261 : Sig := bin false w0 w107
def w1262 : Sig := bin true w1261 w1
def w1263 : Sig := bin false w380 w3
def w1264 : Sig := bin true w380 w3
def w1265 : Sig := bin false w371 w2
def w1266 : Sig := bin true w373 w1
def w1267 : Sig := bin false w371 w3
def w1268 : Sig := bin true w371 w3
def w1269 : Sig := bin false w850 w1
def w1270 : Sig := bin false w367 w3
def w1271 : Sig := bin false w434 w3
def w1272 : Sig := bin true w434 w3
def w1273 : Sig := bin false w423 w3
def w1274 : Sig := bin false w0 w338
def w1275 : Sig := bin false w14 w117
def w1276 : Sig := bin true w429 w1
def w1277 : Sig := bin false w429 w4
def w1278 : Sig := bin true w431 w3
def w1279 : Sig := bin true w386 w1
def w1280 : Sig := bin true w441 w1
def w1281 : Sig := bin false w0 w117
def w1282 : Sig := bin true w1281 w3
def w1283 : Sig := bin false w426 w1
def w1284 : Sig := bin false w809 w3
def w1285 : Sig := bin true w375 w1
def w1286 : Sig := bin false w368 w1
def w1287 : Sig := bin false w333 w1
def w1288 : Sig := bin true w333 w2
def w1289 : Sig := bin false w401 w3
def w1290 : Sig := bin false w340 w1
def w1291 : Sig := bin false w340 w3
def w1292 : Sig := bin false w414 w1
def w1293 : Sig := bin true w116 w0
def w1294 : Sig := bin false w1293 w3
def w1295 : Sig := bin false w408 w3
def w1296 : Sig := bin false w111 w21
def w1297 : Sig := bin false w111 w29
def w1298 : Sig := bin false w458 w3
def w1299 : Sig := bin true w106 w0
def w1300 : Sig := bin false w1299 w1
def w1301 : Sig := bin false w363 w1
def w1302 : Sig := bin true w363 w2
def w1303 : Sig := bin false w103 w19
def w1304 : Sig := bin false w103 w21
def w1305 : Sig := bin false w450 w1
def w1306 : Sig := bin false w394 w1
def w1307 : Sig := bin true w394 w2
def w1308 : Sig := bin false w18 w109
def w1309 : Sig := bin false w18 w123
def w1310 : Sig := bin false w479 w3
def w1311 : Sig := bin true w479 w3
def w1312 : Sig := bin false w477 w3
def w1313 : Sig := bin true w0 w381
def w1314 : Sig := bin false w381 w3
def w1315 : Sig := bin true w381 w3
def w1316 : Sig := bin false w0 w377
def w1317 : Sig := bin false w377 w3
def w1318 : Sig := bin false w402 w3
def w1319 : Sig := bin false w453 w4
def w1320 : Sig := bin false w1 w338
def w1321 : Sig := bin false w20 w117
def w1322 : Sig := bin false w3 w439
def w1323 : Sig := bin false w20 w125
def w1324 : Sig := bin false w121 w3
def w1325 : Sig := bin true w1324 w1
def w1326 : Sig := bin false w481 w4
def w1327 : Sig := bin true w483 w3
def w1328 : Sig := bin true w0 w387
def w1329 : Sig := bin true w388 w1
def w1330 : Sig := bin true w0 w383
def w1331 : Sig := bin false w107 w3
def w1332 : Sig := bin true w1331 w1
def w1333 : Sig := bin false w0 w378
def w1334 : Sig := bin false w814 w1
def w1335 : Sig := bin true w0 w442
def w1336 : Sig := bin false w1 w117
def w1337 : Sig := bin true w1336 w3
def w1338 : Sig := bin true w488 w1
def w1339 : Sig := bin false w1 w125
def w1340 : Sig := bin true w1339 w3
def w1341 : Sig := bin true w5 w24
def w1342 : Sig := bin false w1341 w1
def w1343 : Sig := bin true w5 w22
def w1344 : Sig := bin false w1343 w3
def w1345 : Sig := bin false w0 w335
def w1346 : Sig := bin false w337 w1
def w1347 : Sig := bin false w326 w3
def w1348 : Sig := bin true w326 w4
def w1349 : Sig := bin false w0 w342
def w1350 : Sig := bin false w342 w3
def w1351 : Sig := bin false w348 w1
def w1352 : Sig := bin false w346 w3
def w1353 : Sig := bin false w467 w1
def w1354 : Sig := bin true w124 w1
def w1355 : Sig := bin false w1354 w3
def w1356 : Sig := bin false w473 w3
def w1357 : Sig := bin false w119 w25
def w1358 : Sig := bin false w119 w29
def w1359 : Sig := bin false w354 w1
def w1360 : Sig := bin false w352 w3
def w1361 : Sig := bin false w0 w360
def w1362 : Sig := bin false w360 w3
def w1363 : Sig := bin false w0 w364
def w1364 : Sig := bin false w366 w1
def w1365 : Sig := bin false w105 w15
def w1366 : Sig := bin false w105 w25
def w1367 : Sig := bin false w105 w13
def w1368 : Sig := bin false w498 w1
def w1369 : Sig := bin false w495 w3
def w1370 : Sig := bin false w0 w396
def w1371 : Sig := bin true w0 w435
def w1372 : Sig := bin false w435 w4
def w1373 : Sig := bin true w437 w3
def w1374 : Sig := bin false w0 w433
def w1375 : Sig := bin false w991 w3
def w1376 : Sig := bin false w0 w415
def w1377 : Sig := bin true w116 w1
def w1378 : Sig := bin false w1377 w3
def w1379 : Sig := bin false w419 w3
def w1380 : Sig := bin false w113 w15
def w1381 : Sig := bin false w113 w29
def w1382 : Sig := bin false w503 w3
def w1383 : Sig := bin false w0 w452
def w1384 : Sig := bin false w19 w109
def w1385 : Sig := bin false w19 w123
def w1386 : Sig := bin false w480 w3
def w1387 : Sig := bin true w480 w4
def w1388 : Sig := bin false w0 w382
def w1389 : Sig := bin false w382 w3
def w1390 : Sig := bin true w0 w443
def w1391 : Sig := bin true w1 w443
def w1392 : Sig := bin false w0 w440
def w1393 : Sig := bin false w1 w440
def w1394 : Sig := bin true w1 w490
def w1395 : Sig := bin false w1 w486
def w1396 : Sig := bin false w1 w350
def w1397 : Sig := bin false w0 w344
def w1398 : Sig := bin false w1 w344
def w1399 : Sig := bin false w0 w404
def w1400 : Sig := bin false w406 w3
def w1401 : Sig := bin false w1 w329
def w1402 : Sig := bin false w330 w3
def w1403 : Sig := bin false w0 w362
def w1404 : Sig := bin true w106 w3
def w1405 : Sig := bin false w1 w1404
def w1406 : Sig := bin false w1 w356
def w1407 : Sig := bin false w109 w11
def w1408 : Sig := bin false w1 w420
def w1409 : Sig := bin false w422 w3
def w1410 : Sig := bin false w0 w410
def w1411 : Sig := bin false w412 w3
def w1412 : Sig := bin false w0 w418
def w1413 : Sig := bin false w1 w418
def w1414 : Sig := bin false w115 w17
def w1415 : Sig := bin false w115 w23
def w1416 : Sig := bin false w115 w11
def w1417 : Sig := bin false w0 w455
def w1418 : Sig := bin false w1 w455
def w1419 : Sig := bin false w0 w461
def w1420 : Sig := bin false w463 w3
def w1421 : Sig := bin false w1 w1170
def w1422 : Sig := bin false w476 w3
def w1423 : Sig := bin false w1 w470
def w1424 : Sig := bin false w123 w23
def w1425 : Sig := bin false w1 w500
def w1426 : Sig := bin false w1 w506
def w1427 : Sig := bin false w509 w3
def w1428 : Sig := bin false w1 w376
def w1429 : Sig := bin true w2 w376
def w1430 : Sig := bin false w1 w430
def w1431 : Sig := bin false w3 w432
def w1432 : Sig := bin false w0 w384
def w1433 : Sig := bin false w1 w389
def w1434 : Sig := bin false w0 w436
def w1435 : Sig := bin false w3 w438
def w1436 : Sig := bin false w1 w489
def w1437 : Sig := bin false w3 w484
def w1438 : Sig := bin false w1 w491
def w1439 : Sig := bin true w2 w491
def w1440 : Sig := bin false w0 w444
def w1441 : Sig := bin false w1 w444
def w1442 : Sig := bin true w4 w428
def w1443 : Sig := bin false w327 w3
def w1444 : Sig := bin true w327 w3
def w1445 : Sig := bin true w14 w93
def w1446 : Sig := bin true w64 w259
def w1447 : Sig := bin true w154 w3
def w1448 : Sig := bin true w710 w0
def w1449 : Sig := bin true w707 w2
def w1450 : Sig := bin true w714 w2
def w1451 : Sig := bin true w300 w28
def w1452 : Sig := bin false w315 w0
def w1453 : Sig := bin true w1452 w2
def w1454 : Sig := bin true w720 w0
def w1455 : Sig := bin true w82 w4
def w1456 : Sig := bin true w316 w28
def w1457 : Sig := bin true w703 w2
def w1458 : Sig := bin true w701 w0
def w1459 : Sig := bin false w743 w4
def w1460 : Sig := bin true w1459 w2
def w1461 : Sig := bin true w698 w4
def w1462 : Sig := bin true w726 w4
def w1463 : Sig := bin true w261 w18
def w1464 : Sig := bin true w261 w98
def w1465 : Sig := bin true w261 w99
def w1466 : Sig := bin false w256 w0
def w1467 : Sig := bin true w1466 w4
def w1468 : Sig := bin true w732 w0
def w1469 : Sig := bin true w82 w2
def w1470 : Sig := bin true w257 w18
def w1471 : Sig := bin true w696 w0
def w1472 : Sig := bin true w692 w4
def w1473 : Sig := bin true w690 w0
def w1474 : Sig := bin false w574 w1
def w1475 : Sig := bin true w1474 w4
def w1476 : Sig := bin true w742 w4
def w1477 : Sig := bin false w613 w3
def w1478 : Sig := bin true w1477 w2
def w1479 : Sig := bin true w295 w98
def w1480 : Sig := bin true w73 w2
def w1481 : Sig := bin true w613 w99
def w1482 : Sig := bin true w294 w4
def w1483 : Sig := bin true w613 w100
def w1484 : Sig := bin true w613 w3
def w1485 : Sig := bin true w713 w2
def w1486 : Sig := neg w175
def w1487 : Sig := bin true w1486 w2
def w1488 : Sig := bin true w328 w98
def w1489 : Sig := bin true w743 w4
def w1490 : Sig := bin true w743 w100
def w1491 : Sig := neg w224
def w1492 : Sig := bin true w1491 w4
def w1493 : Sig := neg w148
def w1494 : Sig := bin true w1493 w4
def w1495 : Sig := bin true w659 w4
def w1496 : Sig := bin true w765 w4
def w1497 : Sig := bin true w325 w154
def w1498 : Sig := bin true w764 w4
def w1499 : Sig := bin true w758 w4
def w1500 : Sig := bin true w673 w2
def w1501 : Sig := bin false w95 w29
def w1502 : Sig := bin true w1501 w2
def w1503 : Sig := bin true w96 w100
def w1504 : Sig := bin true w96 w59
def w1505 : Sig := bin true w95 w59
def w1506 : Sig := bin true w669 w2
def w1507 : Sig := bin true w666 w2
def w1508 : Sig := neg w180
def w1509 : Sig := bin true w1508 w4
def w1510 : Sig := bin true w0 w85
def w1511 : Sig := neg w1510
def w1512 : Sig := bin true w1511 w4
def w1513 : Sig := bin true w198 w10
def w1514 : Sig := bin true w334 w28
def w1515 : Sig := bin true w332 w28
def w1516 : Sig := bin true w90 w44
def w1517 : Sig := bin true w90 w88
def w1518 : Sig := bin true w90 w70
def w1519 : Sig := bin true w864 w1
def w1520 : Sig := bin false w8 w1
def w1521 : Sig := bin true w1520 w2
def w1522 : Sig := bin true w971 w4
def w1523 : Sig := bin true w83 w93
def w1524 : Sig := bin true w170 w20
def w1525 : Sig := bin false w864 w1
def w1526 : Sig := bin false w1525 w2
def w1527 : Sig := bin true w1526 w4
def w1528 : Sig := bin true w859 w2
def w1529 : Sig := bin true w872 w0
def w1530 : Sig := bin true w108 w26
def w1531 : Sig := bin false w271 w29
def w1532 : Sig := bin true w403 w18
def w1533 : Sig := bin true w400 w18
def w1534 : Sig := bin true w141 w18
def w1535 : Sig := bin false w586 w3
def w1536 : Sig := bin true w1002 w4
def w1537 : Sig := bin true w1134 w4
def w1538 : Sig := bin false w1020 w0
def w1539 : Sig := bin true w1538 w2
def w1540 : Sig := bin true w977 w18
def w1541 : Sig := bin false w234 w25
def w1542 : Sig := bin false w561 w3
def w1543 : Sig := bin true w876 w37
def w1544 : Sig := bin true w454 w51
def w1545 : Sig := bin true w454 w22
def w1546 : Sig := bin false w454 w11
def w1547 : Sig := bin false w454 w13
def w1548 : Sig := bin false w54 w171
def w1549 : Sig := bin false w54 w60
def w1550 : Sig := bin false w555 w3
def w1551 : Sig := bin false w201 w29
def w1552 : Sig := bin false w201 w207
def w1553 : Sig := bin false w1139 w0
def w1554 : Sig := bin false w47 w34
def w1555 : Sig := bin false w548 w0
def w1556 : Sig := bin false w546 w3
def w1557 : Sig := bin false w187 w19
def w1558 : Sig := bin false w187 w60
def w1559 : Sig := bin false w542 w0
def w1560 : Sig := bin true w1154 w4
def w1561 : Sig := bin true w1161 w4
def w1562 : Sig := bin true w122 w100
def w1563 : Sig := bin true w493 w28
def w1564 : Sig := bin true w183 w28
def w1565 : Sig := bin false w528 w1
def w1566 : Sig := bin false w160 w29
def w1567 : Sig := bin false w522 w3
def w1568 : Sig := bin true w1230 w4
def w1569 : Sig := bin false w31 w48
def w1570 : Sig := bin false w520 w1
def w1571 : Sig := bin false w518 w3
def w1572 : Sig := bin false w132 w207
def w1573 : Sig := bin false w512 w1
def w1574 : Sig := bin false w126 w19
def w1575 : Sig := bin false w510 w3
def w1576 : Sig := bin true w1259 w4
def w1577 : Sig := bin false w1110 w3
def w1578 : Sig := bin false w424 w3
def w1579 : Sig := bin false w1578 w4
def w1580 : Sig := bin true w1579 w2
def w1581 : Sig := bin true w960 w20
def w1582 : Sig := bin false w458 w19
def w1583 : Sig := bin false w871 w3
def w1584 : Sig := bin false w902 w3
def w1585 : Sig := bin false w103 w60
def w1586 : Sig := bin false w999 w3
def w1587 : Sig := bin false w1016 w3
def w1588 : Sig := bin false w1149 w3
def w1589 : Sig := bin false w394 w29
def w1590 : Sig := bin true w1310 w4
def w1591 : Sig := bin true w1312 w4
def w1592 : Sig := bin false w19 w461
def w1593 : Sig := bin true w1347 w4
def w1594 : Sig := bin true w1443 w4
def w1595 : Sig := bin true w1356 w4
def w1596 : Sig := bin true w1401 w4
def w1597 : Sig := bin false w3 w1063
def w1598 : Sig := bin false w3 w374
def w1599 : Sig := bin false w955 w1
def w1600 : Sig := bin false w396 w29
def w1601 : Sig := bin false w1227 w1
def w1602 : Sig := bin false w1105 w3
def w1603 : Sig := bin false w1248 w3
def w1604 : Sig := bin true w1386 w4
def w1605 : Sig := bin false w0 w779
def w1606 : Sig := bin false w4 w922
def w1607 : Sig := bin false w0 w1150
def w1608 : Sig := bin false w1 w1249
def w1609 : Sig := bin false w1253 w3
def w1610 : Sig := bin false w3 w1313
def w1611 : Sig := bin false w3 w932
def w1612 : Sig := bin false w1 w1288
def w1613 : Sig := bin false w3 w807
def w1614 : Sig := bin true w116 w11
def w1615 : Sig := bin false w3 w1614
def w1616 : Sig := bin false w3 w890
def w1617 : Sig := bin false w1 w1302
def w1618 : Sig := bin false w1 w1429
def w1619 : Sig := bin false w3 w1126
def w1620 : Sig := bin false w3 w1442
def w1621 : Sig := bin false w0 w939
def w1622 : Sig := bin false w3 w1387
def w1623 : Sig := bin false w3 w941
def w1624 : Sig := bin false w1 w1307
def w1625 : Sig := bin false w0 w1086
def w1626 : Sig := bin false w1 w1439
def w1627 : Sig := bin false w1 w1088
def w1628 : Sig := bin false w330 w11
def w1629 : Sig := bin false w469 w11
def w1630 : Sig := bin false w498 w4
def w1631 : Sig := bin true w876 w2
def w1632 : Sig := bin true w876 w26
def w1633 : Sig := bin true w960 w2
def w1634 : Sig := bin true w1630 w3
def w1635 : Sig := bin false w424 w4
def w1636 : Sig := bin true w1635 w2
def w1637 : Sig := bin true w375 w26
def r8 : List Sig := [w0,w1,w2,w3,w4]

def tbl_0_0 : STree := L
lemma nolive_0_0 : ∀ v, MemSTree v tbl_0_0 → ∀ m ≤ 0, ¬ Live m 0 v.toFinset := fun _ h => False.elim h
def tbl_0_1 : STree := L
lemma nolive_0_1 : ∀ v, MemSTree v tbl_0_1 → ∀ m ≤ 0, ¬ Live m 1 v.toFinset := fun _ h => False.elim h
def tbl_1_0 : STree := L
lemma nolive_1_0 : ∀ v, MemSTree v tbl_1_0 → ∀ m ≤ 1, ¬ Live m 0 v.toFinset := fun _ h => False.elim h
def tbl_1_1 : STree := L
lemma nolive_1_1 : ∀ v, MemSTree v tbl_1_1 → ∀ m ≤ 1, ¬ Live m 1 v.toFinset := fun _ h => False.elim h
def tbl_2_0 : STree := (N [w84,w2,w530] (N [w306,w2,w320] (N [w306,w97,w29] L L) (N [w84,w97,w59] L L)) (N [w258,w18,w243] (N [w691,w18,w29] L L) (N [w0,w18,w1446] L L)))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_2_0 : checkSTree aut12.fn aut34.fn 1 0 tbl_1_0 tbl_1_0 tbl_2_0 = true := by decide +kernel
lemma nolive_2_0 : ∀ v, MemSTree v tbl_2_0 → ∀ m ≤ 2, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 1 0 tbl_2_0 tbl_1_0 tbl_1_0 nolive_1_0 nolive_1_0 chk_tbl_2_0
def tbl_2_1 : STree := L
lemma nolive_2_1 : ∀ v, MemSTree v tbl_2_1 → ∀ m ≤ 2, ¬ Live m 1 v.toFinset := fun _ h => False.elim h
def tbl_3_0 : STree := (N [w0,w18,w29,w251] (N [w84,w2,w59,w11] (N [w14,w16,w301,w2] (N [w10,w2,w199,w200] (N [w10,w375,w97,w4] (N [w1224,w0,w162,w29] L L) (N [w10,w97,w199,w4] L L)) (N [w62,w18,w199,w4] (N [w62,w375,w18,w4] L L) L)) (N [w306,w2,w29,w11] (N [w306,w97,w3,w4] (N [w14,w177,w92,w2] L L) L) (N [w84,w20,w2,w100] (N [w84,w20,w97,w4] L L) L))) (N [w258,w18,w64,w4] (N [w691,w18,w3,w4] (N [w91,w301,w2,w28] (N [w84,w2,w169,w29] L L) L) (N [w697,w310,w2,w4] (N [w691,w1,w2,w29] L L) L)) (N [w0,w18,w64,w259] (N [w317,w92,w2,w28] (N [w258,w1,w2,w243] L L) L) (N [w0,w18,w246,w67] (N [w0,w18,w254,w28] L L) L)))) (N [w0,w1,w1580,w29] (N [w0,w1,w1021,w29] (N [w0,w98,w207,w27] (N [w0,w92,w318,w28] (N [w0,w963,w72,w29] L L) (N [w0,w98,w72,w29] L L)) (N [w0,w1,w1539,w29] (N [w0,w1,w2,w1446] L L) L)) (N [w0,w1,w1631,w140] (N [w0,w1,w1632,w27] (N [w0,w1,w972,w243] L L) L) (N [w0,w1,w162,w29] (N [w0,w1,w162,w1447] L L) L))) (N [w0,w1,w207,w1633] (N [w0,w1,w1637,w27] (N [w0,w1,w1445,w27] (N [w0,w1,w72,w652] L L) L) (N [w0,w1,w207,w1636] (N [w0,w1,w207,w171] L L) L)) (N [w0,w1,w43,w243] (N [w0,w1,w529,w29] (N [w0,w1,w1634,w171] L L) L) (N [w19,w3,w128,w48] (N [w0,w161,w162,w29] L L) L)))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_3_0 : checkSTree aut12.fn aut34.fn 2 0 tbl_2_0 tbl_2_0 tbl_3_0 = true := by decide +kernel
lemma nolive_3_0 : ∀ v, MemSTree v tbl_3_0 → ∀ m ≤ 3, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 2 0 tbl_3_0 tbl_2_0 tbl_2_0 nolive_2_0 nolive_2_0 chk_tbl_3_0
def tbl_3_1 : STree := (N [w84,w2,w530] (N [w306,w2,w320] (N [w306,w97,w29] L L) (N [w84,w97,w59] L L)) (N [w258,w18,w243] (N [w691,w18,w29] L L) (N [w0,w18,w1446] L L)))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_3_1 : checkSTree aut12.fn aut34.fn 2 1 tbl_2_0 tbl_2_1 tbl_3_1 = true := by decide +kernel
lemma nolive_3_1 : ∀ v, MemSTree v tbl_3_1 → ∀ m ≤ 3, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 2 1 tbl_3_1 tbl_2_0 tbl_2_1 nolive_2_0 nolive_2_1 chk_tbl_3_1
def tbl_4_0LLL : STree := (N [w7,w12,w1,w153,w154] (N [w403,w0,w1,w2,w243] (N [w9,w0,w1,w207,w171] (N [w102,w1,w2,w3,w200] (N [w639,w0,w1,w162,w29] (N [w172,w0,w1,w207,w171] (N [w90,w0,w1,w162,w29] L L) (N [w217,w0,w1,w43,w140] L L)) (N [w102,w16,w1,w2,w60] (N [w102,w16,w1,w2,w470] L L) L)) (N [w108,w0,w1,w2,w259] (N [w108,w258,w1,w2,w4] (N [w361,w0,w2,w4,w41] L L) L) (N [w9,w0,w1,w162,w29] (N [w108,w0,w1,w4,w162] L L) L))) (N [w395,w0,w97,w3,w4] (N [w393,w375,w1,w2,w4] (N [w1531,w0,w1,w2,w270] (N [w9,w0,w1,w43,w140] L L) (N [w393,w44,w1,w2,w29] L L)) (N [w395,w0,w962,w3,w4] (N [w967,w14,w1,w2,w4] L L) L)) (N [w964,w0,w18,w3,w4] (N [w966,w0,w1,w2,w28] (N [w395,w0,w2,w99,w4] L L) L) (N [w975,w0,w1,w2,w29] (N [w68,w0,w1,w162,w29] L L) L)))) (N [w1035,w0,w1,w2,w29] (N [w451,w0,w2,w3,w100] (N [w1535,w0,w1,w2,w4] (N [w997,w0,w18,w19,w4] (N [w400,w62,w18,w3,w4] L L) (N [w997,w0,w1,w2,w4] L L)) (N [w451,w0,w97,w3,w4] (N [w1017,w0,w1109,w2,w4] L L) L)) (N [w416,w0,w1,w2,w29] (N [w1022,w0,w1,w2,w29] (N [w451,w2,w3,w4,w544] L L) L) (N [w413,w0,w1,w2,w140] (N [w416,w0,w1019,w2,w29] L L) L))) (N [w1099,w0,w1,w2,w59] (N [w114,w0,w1,w2,w243] (N [w114,w0,w1,w2,w140] (N [w114,w0,w1,w93,w27] L L) L) (N [w1541,w0,w1,w93,w4] (N [w114,w0,w1019,w2,w29] L L) L)) (N [w110,w62,w18,w3,w4] (N [w110,w12,w98,w3,w4] (N [w110,w10,w97,w3,w4] L L) L) (N [w7,w12,w98,w153,w4] (N [w1075,w0,w1,w2,w29] L L) L))))) (N [w454,w0,w1019,w2,w4] (N [w454,w12,w1,w4,w13] (N [w449,w16,w1,w2,w207] (N [w7,w0,w2,w161,w29] (N [w7,w0,w1,w207,w171] (N [w7,w0,w1,w162,w29] L L) (N [w7,w0,w1019,w2,w29] L L)) (N [w1542,w0,w1,w2,w4] (N [w7,w0,w2,w60,w169] L L) L)) (N [w449,w2,w515,w3,w4] (N [w449,w1,w2,w3,w100] (N [w449,w1,w97,w3,w4] L L) L) (N [w1547,w0,w1,w2,w4] (N [w1546,w0,w1,w2,w4] L L) L))) (N [w454,w0,w1,w97,w4] (N [w454,w0,w22,w2,w23] (N [w454,w0,w18,w19,w4] (N [w454,w16,w1,w2,w211] L L) L) (N [w454,w0,w1,w26,w171] (N [w454,w0,w98,w2,w4] L L) L)) (N [w454,w0,w1,w2,w4] (N [w454,w0,w1,w2,w154] (N [w454,w0,w1,w2,w100] L L) L) (N [w454,w0,w1,w2,w140] (N [w454,w0,w1,w2,w59] L L) L)))) (N [w1554,w0,w18,w3,w4] (N [w1115,w0,w1,w2,w207] (N [w1550,w0,w1,w2,w100] (N [w454,w1,w2,w4,w544] (N [w454,w0,w2,w515,w4] L L) (N [w1550,w0,w1,w97,w4] L L)) (N [w1548,w0,w1,w26,w3] (N [w1550,w0,w1,w2,w4] L L) L)) (N [w1552,w0,w1,w2,w4] (N [w54,w0,w1,w207,w171] (N [w1549,w0,w1,w2,w4] L L) L) (N [w1553,w0,w18,w3,w4] (N [w1551,w0,w1,w2,w28] L L) L))) (N [w460,w1,w2,w4,w188] (N [w1135,w0,w1,w2,w29] (N [w1557,w0,w18,w3,w4] (N [w1139,w0,w18,w3,w4] L L) L) (N [w460,w0,w1,w2,w59] (N [w460,w0,w1,w2,w189] L L) L)) (N [w1555,w1,w2,w3,w4] (N [w457,w1,w2,w3,w128] (N [w457,w62,w18,w3,w4] L L) L) (N [w1147,w1148,w1,w2,w4] (N [w1556,w0,w1,w2,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LLL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LLL = true := by decide +kernel
def tbl_4_0LLR : STree := (N [w1250,w0,w1,w2,w4] (N [w1224,w0,w2,w3,w4] (N [w499,w0,w1,w4,w162] (N [w1558,w0,w1,w2,w4] (N [w1148,w0,w18,w19,w4] (N [w1147,w1,w2,w4,w191] (N [w1147,w1,w2,w3,w4] L L) (N [w1147,w1,w2,w4,w60] L L)) (N [w1148,w1,w2,w4,w544] (N [w1148,w0,w1,w2,w4] L L) L)) (N [w118,w0,w2,w60,w23] (N [w118,w0,w2,w70,w29] (N [w1559,w1,w2,w3,w4] L L) L) (N [w5,w0,w1,w207,w171] (N [w5,w0,w1,w162,w29] L L) L))) (N [w40,w0,w1,w162,w29] (N [w494,w0,w2,w4,w137] (N [w494,w16,w0,w2,w60] (N [w1210,w0,w19,w3,w4] L L) L) (N [w494,w0,w531,w3,w4] (N [w494,w0,w2,w4,w60] L L) L)) (N [w1224,w1225,w0,w3,w4] (N [w1565,w0,w2,w3,w4] (N [w40,w0,w1,w207,w171] L L) L) (N [w1224,w0,w2,w28,w29] (N [w1224,w44,w0,w2,w29] L L) L)))) (N [w1233,w0,w1,w2,w29] (N [w1570,w0,w2,w3,w4] (N [w160,w0,w1,w162,w29] (N [w1566,w44,w0,w1,w2] (N [w1224,w0,w3,w4,w162] L L) (N [w1566,w0,w1,w2,w28] L L)) (N [w502,w0,w2,w3,w128] (N [w1567,w0,w1,w2,w4] L L) L)) (N [w1246,w0,w2,w4,w514] (N [w1246,w0,w2,w3,w4] (N [w1246,w1247,w0,w2,w4] L L) L) (N [w1573,w0,w2,w3,w4] (N [w1246,w0,w2,w4,w207] L L) L))) (N [w1247,w0,w1,w2,w4] (N [w505,w0,w2,w135,w4] (N [w505,w0,w1,w2,w140] (N [w505,w0,w1,w2,w516] L L) L) (N [w1569,w12,w1,w3,w4] (N [w1571,w0,w1,w2,w4] L L) L)) (N [w1574,w0,w18,w3,w4] (N [w1572,w0,w1,w2,w4] (N [w1247,w0,w2,w515,w4] L L) L) (N [w1250,w0,w18,w19,w4] (N [w1250,w1251,w0,w1,w2] L L) L))))) (N [w371,w0,w933,w3,w4] (N [w10,w2,w1540,w3,w4] (N [w10,w0,w97,w99,w4] (N [w1267,w0,w2,w4,w1285] (N [w1575,w0,w1,w2,w4] (N [w1250,w0,w1,w2,w128] L L) (N [w32,w19,w3,w4,w48] L L)) (N [w10,w375,w2,w4,w11] (N [w10,w14,w97,w3,w4] L L) L)) (N [w10,w0,w2,w99,w100] (N [w10,w0,w97,w3,w751] (N [w10,w0,w97,w3,w4] L L) L) (N [w10,w97,w3,w4,w48] (N [w10,w103,w97,w3,w4] L L) L))) (N [w10,w121,w3,w4,w48] (N [w10,w2,w3,w4,w48] (N [w10,w2,w153,w4,w11] (N [w10,w2,w199,w4,w48] L L) L) (N [w10,w2,w3,w763,w48] (N [w10,w2,w3,w4,w1313] L L) L)) (N [w750,w0,w97,w3,w4] (N [w427,w2,w3,w4,w48] (N [w427,w0,w97,w3,w4] L L) L) (N [w371,w0,w97,w3,w4] (N [w1513,w2,w3,w4,w48] L L) L)))) (N [w44,w0,w1,w2,w29] (N [w62,w0,w18,w3,w4] (N [w434,w2,w34,w3,w4] (N [w1577,w0,w1,w2,w4] (N [w371,w0,w2,w3,w100] L L) (N [w434,w1,w97,w3,w4] L L)) (N [w62,w375,w1,w2,w4] (N [w62,w14,w18,w3,w4] L L) L)) (N [w1007,w0,w18,w3,w4] (N [w62,w18,w3,w4,w48] (N [w62,w103,w18,w3,w4] L L) L) (N [w1303,w0,w18,w3,w4] (N [w1582,w0,w18,w3,w4] L L) L))) (N [w14,w16,w1,w2,w81] (N [w1605,w0,w1,w2,w29] (N [w1277,w0,w1,w2,w29] (N [w44,w0,w1,w162,w29] L L) L) (N [w174,w0,w1,w2,w29] (N [w1516,w0,w1,w2,w29] L L) L)) (N [w14,w177,w1,w2,w29] (N [w14,w960,w1,w2,w15] (N [w14,w1274,w1,w2,w29] L L) L) (N [w14,w0,w301,w2,w4] (N [w14,w0,w92,w2,w23] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LLR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LLR = true := by decide +kernel
def tbl_4_0LL : STree := N [w1147,w18,w19,w3,w4] tbl_4_0LLL tbl_4_0LLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0LLL chk_tbl_4_0LLR
def tbl_4_0LRL : STree := (N [w258,w1,w2,w64,w4] (N [w375,w0,w1,w2,w59] (N [w429,w0,w1,w2,w140] (N [w14,w0,w1,w43,w140] (N [w14,w0,w1,w2,w1184] (N [w14,w0,w1,w2,w189] (N [w14,w0,w1,w2,w469] L L) (N [w14,w0,w1,w2,w59] L L)) (N [w14,w0,w1,w162,w29] (N [w14,w0,w1,w2,w243] L L) L)) (N [w14,w1,w2,w4,w188] (N [w14,w363,w1,w2,w4] (N [w14,w874,w1,w2,w4] L L) L) (N [w429,w0,w1,w2,w59] (N [w1291,w0,w1,w2,w140] L L) L))) (N [w375,w0,w18,w19,w4] (N [w881,w0,w1,w2,w4] (N [w1583,w0,w1,w2,w4] (N [w1607,w1,w2,w3,w4] L L) L) (N [w1584,w0,w1,w2,w4] (N [w1587,w0,w1,w2,w4] L L) L)) (N [w375,w0,w934,w2,w4] (N [w375,w0,w98,w2,w4] (N [w375,w0,w22,w2,w23] L L) L) (N [w375,w0,w1,w2,w4] (N [w375,w0,w1,w2,w100] L L) L)))) (N [w84,w1519,w2,w3,w4] (N [w306,w2,w3,w4,w11] (N [w1112,w0,w1,w2,w4] (N [w1586,w0,w1,w2,w4] (N [w375,w0,w1,w4,w162] L L) (N [w1112,w0,w1,w2,w154] L L)) (N [w306,w0,w1,w2,w29] (N [w1588,w0,w1,w2,w4] L L) L)) (N [w84,w20,w2,w4,w11] (N [w84,w0,w1,w2,w59] (N [w84,w0,w92,w2,w4] L L) L) (N [w84,w1,w2,w3,w100] (N [w84,w1,w97,w3,w4] L L) L))) (N [w91,w1,w2,w3,w38] (N [w91,w301,w2,w3,w4] (N [w84,w2,w3,w4,w169] (N [w84,w2,w34,w3,w4] L L) L) (N [w91,w1,w2,w3,w772] (N [w91,w1,w2,w28,w81] L L) L)) (N [w697,w1,w2,w4,w207] (N [w697,w1,w2,w3,w4] (N [w691,w1,w2,w3,w4] L L) L) (N [w258,w86,w2,w3,w4] (N [w258,w18,w19,w3,w4] L L) L))))) (N [w0,w18,w958,w3,w4] (N [w317,w1,w2,w3,w4] (N [w1621,w1,w2,w3,w4] (N [w258,w1,w2,w404,w4] (N [w258,w1,w2,w3,w4] (N [w258,w1,w2,w3,w259] L L) (N [w258,w1,w2,w3,w730] L L)) (N [w258,w1,w1469,w3,w4] (N [w258,w1,w2,w4,w29] L L) L)) (N [w317,w1,w318,w3,w4] (N [w317,w92,w2,w3,w4] (N [w702,w1,w2,w3,w4] L L) L) (N [w317,w1,w2,w88,w4] (N [w317,w1,w2,w28,w29] L L) L))) (N [w0,w1585,w1,w2,w4] (N [w317,w335,w2,w3,w4] (N [w317,w1,w722,w3,w4] (N [w317,w1,w2,w3,w1455] L L) L) (N [w711,w1,w2,w3,w4] (N [w1625,w1,w2,w3,w4] L L) L)) (N [w0,w1589,w1,w2,w28] (N [w0,w880,w22,w2,w3] (N [w0,w1543,w1,w2,w4] L L) L) (N [w0,w18,w1,w207,w27] (N [w0,w18,w1,w72,w29] L L) L)))) (N [w0,w18,w19,w260,w4] (N [w0,w18,w1266,w3,w4] (N [w0,w18,w254,w3,w4] (N [w0,w18,w1592,w3,w4] (N [w0,w18,w64,w4,w65] L L) (N [w0,w18,w252,w3,w4] L L)) (N [w0,w18,w34,w3,w4] (N [w0,w18,w526,w3,w4] L L) L)) (N [w0,w18,w19,w28,w29] (N [w0,w18,w237,w3,w4] (N [w0,w18,w228,w3,w4] L L) L) (N [w0,w18,w19,w99,w4] (N [w0,w18,w19,w199,w4] L L) L))) (N [w0,w18,w19,w3,w763] (N [w0,w18,w19,w3,w730] (N [w0,w18,w19,w3,w4] (N [w0,w18,w19,w262,w4] L L) L) (N [w0,w18,w19,w3,w330] (N [w0,w18,w19,w3,w725] L L) L)) (N [w0,w18,w19,w3,w189] (N [w0,w18,w19,w3,w128] (N [w0,w18,w19,w3,w469] L L) L) (N [w0,w18,w19,w3,w243] (N [w0,w18,w19,w3,w59] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LRL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LRL = true := by decide +kernel
def tbl_4_0LRR : STree := (N [w0,w92,w2,w3,w484] (N [w0,w20,w2,w41,w59] (N [w0,w963,w3,w4,w72] (N [w0,w479,w33,w3,w4] (N [w0,w18,w3,w4,w251] (N [w0,w18,w1162,w3,w4] (N [w0,w18,w840,w3,w4] L L) (N [w0,w18,w480,w3,w4] L L)) (N [w0,w1470,w19,w3,w4] (N [w0,w1463,w19,w3,w4] L L) L)) (N [w0,w1599,w2,w3,w4] (N [w0,w381,w209,w3,w4] (N [w0,w381,w2,w4,w60] L L) L) (N [w0,w963,w2,w3,w4] (N [w0,w963,w2,w28,w29] L L) L))) (N [w0,w20,w1109,w2,w4] (N [w0,w1533,w19,w3,w4] (N [w0,w1532,w19,w3,w4] (N [w0,w1601,w2,w3,w4] L L) L) (N [w0,w1534,w33,w3,w4] (N [w0,w982,w19,w3,w4] L L) L)) (N [w0,w20,w2,w4,w41] (N [w0,w20,w2,w100,w21] (N [w0,w20,w97,w4,w21] L L) L) (N [w0,w20,w2,w4,w1285] (N [w0,w20,w2,w4,w1276] L L) L)))) (N [w0,w86,w2,w410,w4] (N [w0,w75,w97,w3,w4] (N [w0,w1423,w2,w4,w1165] (N [w0,w1524,w2,w4,w41] (N [w0,w481,w2,w4,w41] L L) (N [w0,w1423,w2,w4,w21] L L)) (N [w0,w1608,w2,w3,w4] (N [w0,w487,w2,w4,w36] L L) L)) (N [w0,w310,w2,w4,w220] (N [w0,w310,w2,w4,w21] (N [w0,w75,w2,w3,w100] L L) L) (N [w0,w86,w2,w3,w259] (N [w0,w311,w19,w3,w4] L L) L))) (N [w0,w92,w2,w28,w89] (N [w0,w86,w1521,w3,w4] (N [w0,w86,w2,w4,w60] (N [w0,w86,w2,w4,w36] L L) L) (N [w0,w92,w318,w3,w4] (N [w0,w86,w33,w3,w4] L L) L)) (N [w0,w92,w2,w3,w52] (N [w0,w92,w2,w3,w38] (N [w0,w92,w2,w3,w770] L L) L) (N [w0,w92,w2,w3,w23] (N [w0,w92,w2,w3,w169] L L) L))))) (N [w0,w98,w2,w3,w469] (N [w0,w98,w2,w576,w4] (N [w0,w98,w2,w28,w29] (N [w0,w668,w2,w3,w4] (N [w0,w92,w2,w70,w29] (N [w0,w92,w2,w123,w23] L L) (N [w0,w92,w2,w60,w23] L L)) (N [w0,w98,w97,w3,w4] (N [w0,w672,w2,w3,w4] L L) L)) (N [w0,w98,w2,w153,w154] (N [w0,w98,w2,w99,w4] (N [w0,w98,w2,w199,w4] L L) L) (N [w0,w98,w2,w153,w330] (N [w0,w98,w2,w153,w4] L L) L))) (N [w0,w98,w2,w3,w725] (N [w0,w98,w2,w1598,w4] (N [w0,w98,w2,w262,w4] (N [w0,w98,w2,w1597,w4] L L) L) (N [w0,w98,w2,w3,w738] (N [w0,w98,w2,w3,w4] L L) L)) (N [w0,w98,w2,w3,w330] (N [w0,w98,w2,w3,w741] (N [w0,w98,w2,w3,w748] L L) L) (N [w0,w98,w2,w3,w763] (N [w0,w98,w2,w3,w751] L L) L)))) (N [w0,w98,w56,w3,w4] (N [w0,w98,w467,w3,w4] (N [w0,w98,w2,w329,w330] (N [w0,w98,w2,w3,w59] (N [w0,w98,w2,w3,w556] L L) (N [w0,w98,w2,w3,w140] L L)) (N [w0,w98,w348,w3,w4] (N [w0,w98,w327,w3,w4] L L) L)) (N [w0,w98,w121,w3,w4] (N [w0,w98,w121,w153,w4] (N [w0,w98,w472,w3,w4] L L) L) (N [w0,w98,w133,w3,w4] (N [w0,w98,w121,w3,w330] L L) L))) (N [w0,w934,w2,w153,w4] (N [w0,w675,w2,w3,w4] (N [w0,w1612,w2,w3,w4] (N [w0,w98,w3,w4,w72] L L) L) (N [w0,w1617,w2,w3,w4] (N [w0,w1464,w2,w3,w4] L L) L)) (N [w0,w934,w2,w3,w4] (N [w0,w934,w2,w3,w154] (N [w0,w934,w2,w1598,w4] L L) L) (N [w0,w689,w2,w3,w4] (N [w0,w685,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LRR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LRR = true := by decide +kernel
def tbl_4_0LR : STree := N [w0,w18,w778,w3,w4] tbl_4_0LRL tbl_4_0LRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0LR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0LR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0LRL chk_tbl_4_0LRR
def tbl_4_0L : STree := N [w14,w0,w1,w2,w1153] tbl_4_0LL tbl_4_0LR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0L : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0L = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0LL chk_tbl_4_0LR
def tbl_4_0RLL : STree := (N [w0,w1,w2,w28,w988] (N [w0,w301,w2,w3,w717] (N [w0,w706,w2,w3,w4] (N [w0,w297,w2,w329,w4] (N [w0,w297,w2,w3,w4] (N [w0,w297,w2,w3,w154] (N [w0,w297,w2,w153,w4] L L) (N [w0,w297,w2,w3,w575] L L)) (N [w0,w297,w2,w3,w330] (N [w0,w297,w2,w3,w738] L L) L)) (N [w0,w1479,w2,w3,w4] (N [w0,w1618,w2,w3,w4] (N [w0,w297,w1480,w3,w4] L L) L) (N [w0,w1624,w2,w3,w4] (N [w0,w1488,w2,w3,w4] L L) L))) (N [w0,w319,w337,w3,w4] (N [w0,w319,w2,w3,w4] (N [w0,w319,w2,w222,w4] (N [w0,w319,w2,w28,w29] L L) L) (N [w0,w319,w2,w3,w59] (N [w0,w319,w2,w3,w723] L L) L)) (N [w0,w301,w2,w28,w29] (N [w0,w301,w302,w3,w4] (N [w0,w1626,w2,w3,w4] L L) L) (N [w0,w301,w2,w3,w4] (N [w0,w301,w2,w80,w4] L L) L)))) (N [w0,w1,w1603,w2,w4] (N [w0,w1,w1600,w2,w28] (N [w0,w301,w716,w3,w4] (N [w0,w301,w2,w3,w125] (N [w0,w301,w2,w3,w469] L L) (N [w0,w301,w2,w3,w59] L L)) (N [w0,w1627,w2,w3,w4] (N [w0,w709,w2,w3,w4] L L) L)) (N [w0,w1,w435,w2,w140] (N [w0,w1,w1378,w2,w29] (N [w0,w1,w1372,w2,w29] L L) L) (N [w0,w1,w1114,w2,w4] (N [w0,w1,w1602,w2,w4] L L) L))) (N [w0,w1,w2,w266,w280] (N [w0,w1,w1545,w2,w4] (N [w0,w1,w1019,w2,w29] (N [w0,w1,w1544,w2,w4] L L) L) (N [w0,w1,w2,w254,w28] (N [w0,w1,w2,w64,w259] L L) L)) (N [w0,w1,w2,w28,w280] (N [w0,w1,w2,w28,w320] (N [w0,w1,w2,w266,w29] L L) L) (N [w0,w1,w2,w28,w29] (N [w0,w1,w2,w28,w246] L L) L))))) (N [w0,w1,w2,w305,w29] (N [w0,w1,w2,w1422,w29] (N [w0,w1,w2,w1514,w29] (N [w0,w1,w2,w1402,w29] (N [w0,w1,w2,w1451,w29] (N [w0,w1,w2,w28,w761] L L) (N [w0,w1,w2,w1456,w29] L L)) (N [w0,w1,w2,w757,w29] (N [w0,w1,w2,w1402,w761] L L) L)) (N [w0,w1,w2,w1411,w29] (N [w0,w1,w2,w779,w29] (N [w0,w1,w2,w1515,w29] L L) L) (N [w0,w1,w2,w1010,w29] (N [w0,w1,w2,w443,w140] L L) L))) (N [w0,w1,w2,w1563,w29] (N [w0,w1,w2,w841,w29] (N [w0,w1,w2,w490,w29] (N [w0,w1,w2,w490,w45] L L) L) (N [w0,w1,w2,w1171,w29] (N [w0,w1,w2,w1609,w4] L L) L)) (N [w0,w1,w2,w285,w29] (N [w0,w1,w2,w1564,w29] (N [w0,w1,w2,w486,w29] L L) L) (N [w0,w1,w2,w80,w59] (N [w0,w1,w2,w80,w469] L L) L)))) (N [w0,w1,w2,w661,w4] (N [w0,w1,w2,w884,w29] (N [w0,w1,w2,w88,w140] (N [w0,w1,w2,w88,w1522] (N [w0,w1,w2,w312,w29] L L) (N [w0,w1,w2,w88,w45] L L)) (N [w0,w1,w2,w1437,w29] (N [w0,w1,w2,w88,w29] L L) L)) (N [w0,w1,w2,w199,w4] (N [w0,w1,w2,w199,w200] (N [w0,w1,w2,w1517,w29] L L) L) (N [w0,w1,w2,w658,w4] (N [w0,w1,w2,w199,w763] L L) L))) (N [w0,w1,w2,w99,w1082] (N [w0,w1,w2,w1610,w4] (N [w0,w1,w2,w678,w4] (N [w0,w1,w2,w665,w4] L L) L) (N [w0,w1,w2,w99,w298] (N [w0,w1,w2,w99,w100] L L) L)) (N [w0,w1,w2,w99,w1606] (N [w0,w1,w2,w99,w263] (N [w0,w1,w2,w99,w154] L L) L) (N [w0,w1,w2,w99,w1482] (N [w0,w1,w2,w99,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RLL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RLL = true := by decide +kernel
def tbl_4_0RLR : STree := (N [w0,w1,w2,w3,w1462] (N [w0,w1,w2,w260,w29] (N [w0,w1,w2,w299,w751] (N [w0,w1,w2,w99,w59] (N [w0,w1,w2,w99,w751] (N [w0,w1,w2,w99,w1498] (N [w0,w1,w2,w99,w330] L L) (N [w0,w1,w2,w99,w1489] L L)) (N [w0,w1,w2,w99,w469] (N [w0,w1,w2,w99,w1153] L L) L)) (N [w0,w1,w2,w1615,w4] (N [w0,w1,w2,w99,w140] (N [w0,w1,w2,w99,w557] L L) L) (N [w0,w1,w2,w299,w4] (N [w0,w1,w2,w682,w4] L L) L))) (N [w0,w1,w2,w1465,w4] (N [w0,w1,w2,w1081,w1082] (N [w0,w1,w2,w1613,w4] (N [w0,w1,w2,w299,w59] L L) L) (N [w0,w1,w2,w1620,w4] (N [w0,w1,w2,w1081,w4] L L) L)) (N [w0,w1,w2,w260,w406] (N [w0,w1,w2,w260,w4] (N [w0,w1,w2,w695,w4] L L) L) (N [w0,w1,w2,w260,w243] (N [w0,w1,w2,w260,w59] L L) L)))) (N [w0,w1,w2,w3,w1628] (N [w0,w1,w2,w700,w4] (N [w0,w1,w2,w262,w4] (N [w0,w1,w2,w1616,w4] (N [w0,w1,w2,w1622,w4] L L) (N [w0,w1,w2,w262,w263] L L)) (N [w0,w1,w2,w262,w330] (N [w0,w1,w2,w262,w725] L L) L)) (N [w0,w1,w2,w1619,w4] (N [w0,w1,w2,w935,w4] (N [w0,w1,w2,w1611,w4] L L) L) (N [w0,w1,w2,w1623,w4] (N [w0,w1,w2,w1481,w4] L L) L))) (N [w0,w1,w2,w3,w1467] (N [w0,w1,w2,w3,w1490] (N [w0,w1,w2,w3,w1483] (N [w0,w1,w2,w3,w1503] L L) L) (N [w0,w1,w2,w3,w1461] (N [w0,w1,w2,w3,w4] L L) L)) (N [w0,w1,w2,w3,w738] (N [w0,w1,w2,w3,w1475] (N [w0,w1,w2,w3,w730] L L) L) (N [w0,w1,w2,w3,w1495] (N [w0,w1,w2,w3,w1494] L L) L))))) (N [w0,w1,w2,w3,w128] (N [w0,w1,w2,w3,w763] (N [w0,w1,w2,w3,w741] (N [w0,w1,w2,w3,w1497] (N [w0,w1,w2,w3,w1472] (N [w0,w1,w2,w3,w725] L L) (N [w0,w1,w2,w3,w1492] L L)) (N [w0,w1,w2,w3,w748] (N [w0,w1,w2,w3,w1476] L L) L)) (N [w0,w1,w2,w3,w1509] (N [w0,w1,w2,w3,w330] (N [w0,w1,w2,w3,w1499] L L) L) (N [w0,w1,w2,w3,w1496] (N [w0,w1,w2,w3,w1512] L L) L))) (N [w0,w1,w2,w3,w1560] (N [w0,w1,w2,w3,w1001] (N [w0,w1,w2,w3,w1536] (N [w0,w1,w2,w3,w1527] L L) L) (N [w0,w1,w2,w3,w1562] (N [w0,w1,w2,w3,w1629] L L) L)) (N [w0,w1,w2,w3,w469] (N [w0,w1,w2,w3,w1561] (N [w0,w1,w2,w3,w1153] L L) L) (N [w0,w1,w2,w3,w511] (N [w0,w1,w2,w3,w1568] L L) L)))) (N [w0,w1,w2,w3,w1581] (N [w0,w1,w2,w3,w1591] (N [w0,w1,w2,w3,w523] (N [w0,w1,w2,w3,w1576] (N [w0,w1,w2,w3,w134] L L) (N [w0,w1,w2,w3,w519] L L)) (N [w0,w1,w2,w3,w1590] (N [w0,w1,w2,w3,w189] L L) L)) (N [w0,w1,w2,w3,w712] (N [w0,w1,w2,w3,w530] (N [w0,w1,w2,w3,w547] L L) L) (N [w0,w1,w2,w3,w556] (N [w0,w1,w2,w3,w558] L L) L))) (N [w0,w1,w2,w3,w1184] (N [w0,w1,w2,w3,w1593] (N [w0,w1,w2,w3,w1596] (N [w0,w1,w2,w3,w59] L L) L) (N [w0,w1,w2,w3,w1595] (N [w0,w1,w2,w3,w1504] L L) L)) (N [w0,w1,w2,w3,w587] (N [w0,w1,w2,w3,w562] (N [w0,w1,w2,w3,w1505] L L) L) (N [w0,w1,w2,w3,w1604] (N [w0,w1,w2,w3,w243] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RLR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RLR = true := by decide +kernel
def tbl_4_0RL : STree := N [w0,w1,w2,w99,w725] tbl_4_0RLL tbl_4_0RLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0RLL chk_tbl_4_0RLR
def tbl_4_0RRL : STree := (N [w0,w1,w2,w60,w140] (N [w0,w1,w2,w470,w125] (N [w0,w1,w2,w362,w59] (N [w0,w1,w2,w746,w330] (N [w0,w1,w2,w724,w725] (N [w0,w1,w2,w350,w59] (N [w0,w1,w2,w350,w469] L L) (N [w0,w1,w2,w344,w59] L L)) (N [w0,w1,w2,w747,w330] (N [w0,w1,w2,w747,w748] L L) L)) (N [w0,w1,w2,w329,w1596] (N [w0,w1,w2,w329,w59] (N [w0,w1,w2,w329,w330] L L) L) (N [w0,w1,w2,w762,w763] (N [w0,w1,w2,w329,w140] L L) L))) (N [w0,w1,w2,w1156,w476] (N [w0,w1,w2,w410,w59] (N [w0,w1,w2,w1005,w412] (N [w0,w1,w2,w109,w243] L L) L) (N [w0,w1,w2,w1190,w29] (N [w0,w1,w2,w1424,w29] L L) L)) (N [w0,w1,w2,w474,w59] (N [w0,w1,w2,w474,w469] (N [w0,w1,w2,w1156,w125] L L) L) (N [w0,w1,w2,w470,w469] (N [w0,w1,w2,w474,w140] L L) L)))) (N [w0,w1,w2,w50,w59] (N [w0,w1,w2,w142,w29] (N [w0,w1,w2,w123,w59] (N [w0,w1,w2,w470,w59] (N [w0,w1,w2,w470,w52] L L) (N [w0,w1,w2,w123,w189] L L)) (N [w0,w1,w2,w123,w243] (N [w0,w1,w2,w123,w1184] L L) L)) (N [w0,w1,w2,w36,w59] (N [w0,w1,w2,w137,w38] (N [w0,w1,w2,w127,w128] L L) L) (N [w0,w1,w2,w191,w52] (N [w0,w1,w2,w192,w29] L L) L))) (N [w0,w1,w2,w1194,w29] (N [w0,w1,w2,w70,w29] (N [w0,w1,w2,w161,w29] (N [w0,w1,w2,w571,w29] L L) L) (N [w0,w1,w2,w1394,w29] (N [w0,w1,w2,w1518,w29] L L) L)) (N [w0,w1,w2,w60,w169] (N [w0,w1,w2,w60,w59] (N [w0,w1,w2,w313,w29] L L) L) (N [w0,w1,w2,w60,w484] (N [w0,w1,w2,w60,w23] L L) L))))) (N [w0,w1,w744,w99,w4] (N [w0,w1,w716,w28,w29] (N [w0,w1,w1449,w3,w4] (N [w0,w1,w2,w21,w243] (N [w0,w1,w2,w1327,w484] (N [w0,w1,w2,w1327,w23] L L) (N [w0,w1,w2,w273,w29] L L)) (N [w0,w1,w2,w29,w251] (N [w0,w1,w2,w246,w67] L L) L)) (N [w0,w1,w722,w3,w4] (N [w0,w1,w722,w28,w29] (N [w0,w1,w1453,w3,w4] L L) L) (N [w0,w1,w1450,w3,w4] (N [w0,w1,w1460,w3,w4] L L) L))) (N [w0,w1,w735,w299,w4] (N [w0,w1,w337,w72,w29] (N [w0,w1,w1457,w3,w4] (N [w0,w1,w716,w3,w4] L L) L) (N [w0,w1,w735,w99,w4] (N [w0,w1,w1478,w3,w4] L L) L)) (N [w0,w1,w735,w3,w751] (N [w0,w1,w735,w3,w4] (N [w0,w1,w735,w3,w100] L L) L) (N [w0,w1,w1487,w3,w4] (N [w0,w1,w735,w1484,w4] L L) L)))) (N [w0,w1,w327,w99,w751] (N [w0,w1,w1485,w3,w59] (N [w0,w1,w744,w3,w751] (N [w0,w1,w744,w3,w4] (N [w0,w1,w744,w3,w100] L L) (N [w0,w1,w744,w3,w1489] L L)) (N [w0,w1,w1485,w3,w4] (N [w0,w1,w744,w756,w4] L L) L)) (N [w0,w1,w327,w28,w29] (N [w0,w1,w1502,w3,w4] (N [w0,w1,w1500,w3,w4] L L) L) (N [w0,w1,w327,w99,w4] (N [w0,w1,w327,w99,w100] L L) L))) (N [w0,w1,w327,w3,w725] (N [w0,w1,w327,w1597,w4] (N [w0,w1,w327,w153,w4] (N [w0,w1,w327,w299,w4] L L) L) (N [w0,w1,w327,w3,w4] (N [w0,w1,w327,w262,w4] L L) L)) (N [w0,w1,w327,w3,w751] (N [w0,w1,w327,w3,w1489] (N [w0,w1,w327,w3,w1498] L L) L) (N [w0,w1,w327,w3,w140] (N [w0,w1,w327,w3,w59] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RRL : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RRL = true := by decide +kernel
def tbl_4_0RRR : STree := (N [w0,w1,w3,w43,w140] (N [w0,w1,w972,w64,w4] (N [w0,w1,w366,w222,w4] (N [w0,w1,w348,w576,w4] (N [w0,w1,w728,w260,w4] (N [w0,w1,w1507,w3,w4] (N [w0,w1,w327,w756,w751] L L) (N [w0,w1,w1506,w3,w4] L L)) (N [w0,w1,w348,w153,w4] (N [w0,w1,w728,w3,w140] L L) L)) (N [w0,w1,w1530,w3,w27] (N [w0,w1,w121,w153,w154] (N [w0,w1,w348,w3,w140] L L) L) (N [w0,w1,w1528,w3,w4] (N [w0,w1,w1523,w3,w27] L L) L))) (N [w0,w1,w1539,w3,w4] (N [w0,w1,w107,w207,w27] (N [w0,w1,w107,w72,w29] (N [w0,w1,w366,w3,w140] L L) L) (N [w0,w1,w398,w72,w29] (N [w0,w1,w107,w25,w140] L L) L)) (N [w0,w1,w1021,w3,w1522] (N [w0,w1,w1021,w3,w4] (N [w0,w1,w1021,w28,w29] L L) L) (N [w0,w1,w1021,w29] (N [w0,w1,w1021,w3,w29] L L) L)))) (N [w0,w1,w521,w3,w4] (N [w0,w1,w513,w3,w4] (N [w0,w1,w402,w72,w29] (N [w0,w1,w972,w3,w140] (N [w0,w1,w972,w3,w1537] L L) (N [w0,w1,w972,w27,w29] L L)) (N [w0,w1,w64,w4,w43] (N [w0,w1,w402,w207,w27] L L) L)) (N [w0,w1,w133,w3,w134] (N [w0,w1,w133,w3,w4] (N [w0,w1,w133,w153,w4] L L) L) (N [w0,w1,w133,w4,w36] (N [w0,w1,w133,w3,w59] L L) L))) (N [w0,w1,w3,w4,w1580] (N [w0,w1,w222,w4,w43] (N [w0,w1,w28,w162,w29] (N [w0,w1,w33,w3,w128] L L) L) (N [w0,w1,w3,w4,w162] (N [w0,w1,w153,w4,w162] L L) L)) (N [w0,w1,w3,w45,w162] (N [w0,w1,w3,w516,w43] (N [w0,w1,w3,w4,w529] L L) L) (N [w0,w1,w3,w207,w171] (N [w0,w1,w3,w162,w29] L L) L))))) (N [w1473,w1,w2,w3,w4] (N [w719,w1,w2,w28,w29] (N [w0,w135,w3,w4,w43] (N [w0,w1,w207,w27,w13] (N [w0,w1,w72,w29,w13] (N [w0,w1,w162,w29] L L) (N [w0,w1,w207,w171] L L)) (N [w0,w715,w716,w3,w4] (N [w0,w1,w43,w27,w29] L L) L)) (N [w1448,w1,w2,w3,w4] (N [w0,w3,w4,w161,w162] (N [w0,w19,w3,w4,w164] L L) L) (N [w719,w319,w2,w3,w4] (N [w1454,w1,w2,w3,w4] L L) L))) (N [w727,w18,w19,w3,w4] (N [w1458,w1,w2,w3,w4] (N [w719,w721,w2,w3,w4] (N [w719,w1,w2,w3,w4] L L) L) (N [w1468,w1,w2,w3,w4] (N [w333,w301,w2,w3,w4] L L) L)) (N [w727,w1,w2,w729,w4] (N [w727,w1,w2,w3,w4] (N [w727,w1,w2,w260,w4] L L) L) (N [w1471,w1,w2,w3,w59] (N [w1471,w1,w2,w3,w4] L L) L)))) (N [w75,w2,w3,w4,w48] (N [w111,w98,w2,w153,w4] (N [w340,w579,w2,w3,w4] (N [w401,w1,w2,w262,w4] (N [w401,w1,w2,w99,w4] L L) (N [w340,w98,w2,w3,w4] L L)) (N [w340,w1,w2,w576,w4] (N [w340,w1,w2,w153,w4] L L) L)) (N [w357,w216,w2,w3,w4] (N [w1529,w1,w2,w3,w4] (N [w111,w1,w2,w153,w154] L L) L) (N [w18,w19,w3,w4,w188] (N [w363,w1,w2,w80,w4] L L) L))) (N [w1,w2,w3,w4,w549] (N [w1,w2,w99,w4,w188] (N [w1,w2,w199,w4,w188] (N [w98,w2,w3,w4,w188] L L) L) (N [w1,w2,w3,w4,w188] (N [w1,w2,w3,w4,w543] L L) L)) (N [w1,w2,w3,w188,w59] (N [w1,w2,w3,w188,w189] (N [w1,w2,w3,w125,w544] L L) L) (N [w1,w2,w3,w544,w52] (N [w1,w2,w3,w128,w48] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RRR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RRR = true := by decide +kernel
def tbl_4_0RR : STree := N [w0,w1,w327,w3,w1594] tbl_4_0RRL tbl_4_0RRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0RR : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0RR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0RRL chk_tbl_4_0RRR
def tbl_4_0R : STree := N [w0,w1,w2,w737,w330] tbl_4_0RL tbl_4_0RR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0R : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0R = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0RL chk_tbl_4_0RR
def tbl_4_0 : STree := N [w0,w689,w2,w4,w207] tbl_4_0L tbl_4_0R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_0 : checkSTree aut12.fn aut34.fn 3 0 tbl_3_0 tbl_3_0 tbl_4_0 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_4_0L chk_tbl_4_0R
lemma nolive_4_0 : ∀ v, MemSTree v tbl_4_0 → ∀ m ≤ 4, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 3 0 tbl_4_0 tbl_3_0 tbl_3_0 nolive_3_0 nolive_3_0 chk_tbl_4_0
def tbl_4_1 : STree := (N [w317,w92,w2,w28] (N [w84,w20,w2,w100] (N [w14,w177,w92,w2] (N [w62,w18,w199,w4] (N [w10,w2,w199,w200] (N [w10,w97,w199,w4] L L) L) (N [w14,w16,w301,w2] L L)) (N [w306,w2,w29,w11] (N [w306,w97,w3,w4] L L) (N [w84,w20,w97,w4] L L))) (N [w691,w1,w2,w29] (N [w91,w301,w2,w28] (N [w84,w2,w169,w29] (N [w84,w2,w59,w11] L L) L) (N [w691,w18,w3,w4] L L)) (N [w258,w18,w64,w4] (N [w697,w310,w2,w4] L L) (N [w258,w1,w2,w243] L L)))) (N [w0,w1,w162,w1447] (N [w0,w92,w318,w28] (N [w0,w18,w246,w67] (N [w0,w18,w254,w28] (N [w0,w18,w64,w259] L L) L) (N [w0,w18,w29,w251] L L)) (N [w0,w98,w207,w27] (N [w0,w98,w72,w29] L L) (N [w0,w1,w2,w1446] L L))) (N [w0,w1,w529,w29] (N [w0,w1,w1445,w27] (N [w0,w1,w72,w652] (N [w0,w1,w162,w29] L L) L) (N [w0,w1,w207,w171] L L)) (N [w0,w161,w162,w29] (N [w0,w1,w43,w243] L L) (N [w19,w3,w128,w48] L L)))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_4_1 : checkSTree aut12.fn aut34.fn 3 1 tbl_3_0 tbl_3_1 tbl_4_1 = true := by decide +kernel
lemma nolive_4_1 : ∀ v, MemSTree v tbl_4_1 → ∀ m ≤ 4, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 3 1 tbl_4_1 tbl_3_0 tbl_3_1 nolive_3_0 nolive_3_1 chk_tbl_4_1
def tbl_5_0LLLLL : STree := (N [w295,w0,w1,w2,w153,w4] (N [w261,w0,w1,w2,w99,w4] (N [w316,w0,w1,w2,w28,w29] (N [w300,w0,w1,w2,w3,w4] (N [w714,w0,w1,w2,w3,w4] (N [w708,w0,w1,w2,w3,w4] (N [w710,w0,w1,w2,w3,w4] L L) L) (N [w300,w0,w1,w2,w28,w29] (N [w300,w0,w301,w2,w3,w4] L L) L)) (N [w720,w0,w1,w2,w3,w4] (N [w718,w0,w1,w2,w3,w4] (N [w300,w0,w1,w716,w3,w4] L L) L) (N [w316,w0,w319,w2,w3,w4] (N [w316,w540,w1,w2,w3,w4] L L) L))) (N [w745,w0,w1,w2,w3,w4] (N [w316,w719,w1,w2,w3,w4] (N [w316,w0,w721,w2,w3,w4] (N [w316,w0,w1,w2,w3,w4] L L) L) (N [w701,w0,w1,w2,w3,w4] (N [w705,w0,w1,w2,w3,w4] L L) L)) (N [w261,w0,w18,w19,w3,w4] (N [w726,w0,w1,w2,w3,w4] (N [w699,w0,w1,w2,w3,w4] L L) L) (N [w261,w0,w98,w2,w3,w4] L L)))) (N [w257,w0,w1,w2,w729,w4] (N [w732,w0,w1,w2,w3,w4] (N [w261,w0,w1,w2,w3,w725] (N [w261,w0,w1,w2,w3,w4] (N [w261,w0,w1,w2,w262,w4] L L) L) (N [w731,w0,w1,w2,w3,w4] (N [w261,w0,w1,w327,w3,w4] L L) L)) (N [w257,w0,w1,w2,w260,w4] (N [w257,w0,w18,w19,w3,w4] (N [w257,w538,w1,w2,w3,w4] L L) L) (N [w257,w0,w1,w2,w3,w4] L L))) (N [w733,w0,w1,w2,w3,w4] (N [w696,w0,w1,w2,w3,w59] (N [w696,w0,w1,w2,w3,w4] (N [w257,w727,w1,w2,w3,w4] L L) L) (N [w690,w0,w1,w2,w3,w4] (N [w694,w0,w1,w2,w3,w4] L L) L)) (N [w295,w0,w98,w2,w3,w4] (N [w736,w0,w1,w2,w3,w4] (N [w742,w0,w1,w2,w3,w4] L L) L) (N [w295,w0,w579,w2,w3,w4] L L))))) (N [w765,w0,w1,w2,w3,w4] (N [w328,w0,w1,w2,w153,w4] (N [w295,w0,w734,w2,w3,w4] (N [w295,w0,w1,w2,w3,w4] (N [w295,w0,w1,w2,w3,w154] (N [w295,w0,w1,w2,w576,w4] L L) L) (N [w295,w0,w1,w2,w737,w4] (N [w295,w0,w1,w2,w3,w330] L L) L)) (N [w684,w0,w1,w2,w3,w4] (N [w687,w0,w1,w2,w3,w140] (N [w687,w0,w1,w2,w3,w4] L L) L) (N [w328,w0,w98,w2,w3,w4] L L))) (N [w328,w0,w740,w2,w3,w4] (N [w328,w0,w1,w2,w3,w741] (N [w328,w0,w1,w2,w3,w4] (N [w328,w0,w1,w2,w3,w154] L L) L) (N [w328,w0,w1,w2,w329,w4] (N [w328,w0,w1,w2,w3,w330] L L) L)) (N [w677,w0,w1,w2,w3,w4] (N [w680,w0,w1,w2,w3,w4] (N [w328,w0,w326,w2,w3,w4] L L) L) (N [w660,w0,w1,w2,w3,w4] L L)))) (N [w96,w0,w18,w19,w3,w4] (N [w325,w0,w326,w2,w3,w4] (N [w325,w0,w1,w2,w3,w4] (N [w325,w0,w1,w2,w153,w4] (N [w325,w0,w98,w2,w3,w4] L L) L) (N [w325,w0,w1,w2,w3,w330] (N [w325,w0,w1,w2,w3,w748] L L) L)) (N [w760,w0,w1,w2,w3,w4] (N [w674,w0,w1,w2,w3,w4] (N [w758,w0,w1,w2,w3,w4] L L) L) (N [w96,w12,w0,w98,w3,w4] L L))) (N [w96,w0,w1,w97,w3,w4] (N [w96,w0,w98,w2,w3,w330] (N [w96,w0,w98,w2,w3,w4] (N [w96,w0,w98,w2,w153,w4] L L) L) (N [w96,w0,w297,w2,w3,w4] (N [w96,w0,w98,w121,w3,w4] L L) L)) (N [w96,w0,w1,w2,w153,w154] (N [w96,w0,w1,w2,w99,w4] (N [w96,w0,w1,w2,w28,w29] L L) L) (N [w96,w0,w1,w2,w153,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLLL = true := by decide +kernel
def tbl_5_0LLLLR : STree := (N [w90,w0,w1,w2,w779,w29] (N [w198,w0,w1,w2,w3,w763] (N [w96,w0,w326,w2,w3,w4] (N [w96,w0,w1,w2,w3,w330] (N [w96,w0,w1,w2,w3,w4] (N [w96,w0,w1,w2,w262,w4] (N [w96,w0,w1,w2,w576,w4] L L) L) (N [w96,w0,w1,w2,w3,w741] (N [w96,w0,w1,w2,w3,w748] L L) L)) (N [w96,w0,w1,w2,w329,w330] (N [w96,w0,w1,w2,w3,w140] (N [w96,w0,w1,w2,w3,w59] L L) L) (N [w96,w0,w326,w2,w153,w4] (N [w96,w0,w740,w2,w3,w4] L L) L))) (N [w198,w10,w2,w3,w4,w48] (N [w667,w0,w1,w2,w3,w4] (N [w671,w0,w1,w2,w3,w4] (N [w96,w0,w326,w2,w3,w330] L L) L) (N [w656,w0,w1,w2,w3,w4] (N [w663,w0,w1,w2,w3,w4] L L) L)) (N [w198,w0,w1,w2,w199,w4] (N [w198,w0,w98,w2,w3,w4] (N [w198,w0,w18,w19,w3,w4] L L) L) (N [w198,w0,w1,w2,w3,w4] L L)))) (N [w332,w333,w1,w2,w3,w4] (N [w334,w0,w1,w2,w3,w59] (N [w334,w0,w92,w2,w3,w4] (N [w766,w0,w1,w2,w3,w4] (N [w768,w0,w1,w2,w3,w4] L L) L) (N [w334,w0,w1,w2,w3,w4] (N [w334,w0,w1,w2,w28,w29] L L) L)) (N [w332,w0,w1,w2,w28,w29] (N [w332,w91,w1,w2,w3,w4] (N [w334,w0,w335,w2,w3,w4] L L) L) (N [w332,w0,w1,w2,w3,w4] L L))) (N [w90,w0,w92,w2,w3,w23] (N [w90,w44,w0,w1,w2,w29] (N [w777,w0,w1,w2,w3,w4] (N [w780,w0,w1,w2,w3,w4] L L) L) (N [w90,w0,w18,w19,w3,w4] (N [w90,w317,w1,w2,w3,w4] L L) L)) (N [w90,w0,w301,w2,w3,w4] (N [w90,w0,w319,w2,w3,w4] (N [w90,w0,w98,w2,w3,w4] L L) L) (N [w90,w0,w1,w2,w28,w29] L L))))) (N [w343,w0,w1,w2,w3,w4] (N [w783,w0,w1,w2,w3,w4] (N [w654,w0,w1,w2,w3,w4] (N [w90,w0,w1,w2,w3,w4] (N [w90,w0,w1,w2,w99,w4] (N [w90,w0,w1,w2,w88,w29] L L) L) (N [w90,w0,w1,w2,w70,w29] (N [w90,w0,w1,w2,w3,w59] L L) L)) (N [w612,w0,w1,w2,w3,w4] (N [w612,w0,w1,w2,w153,w4] (N [w654,w0,w1,w2,w3,w243] L L) L) (N [w653,w0,w1,w2,w3,w4] L L))) (N [w341,w0,w221,w2,w3,w4] (N [w339,w0,w1,w2,w3,w4] (N [w339,w178,w1,w2,w3,w4] (N [w785,w0,w1,w2,w3,w4] L L) L) (N [w788,w0,w1,w2,w3,w4] (N [w339,w340,w1,w2,w3,w4] L L) L)) (N [w806,w0,w1,w2,w3,w4] (N [w341,w0,w342,w2,w3,w4] (N [w341,w0,w1,w2,w3,w4] L L) L) (N [w343,w0,w1,w2,w222,w4] L L)))) (N [w83,w0,w1,w93,w3,w27] (N [w83,w540,w1,w2,w3,w4] (N [w802,w0,w1,w2,w3,w4] (N [w343,w0,w1,w2,w344,w4] (N [w343,w0,w1,w2,w3,w140] L L) L) (N [w83,w538,w1,w2,w3,w4] (N [w804,w0,w1,w2,w3,w4] L L) L)) (N [w83,w0,w579,w2,w3,w4] (N [w83,w0,w98,w2,w3,w4] (N [w83,w0,w18,w19,w3,w4] L L) L) (N [w83,w0,w319,w2,w3,w4] L L))) (N [w83,w0,w1,w2,w576,w4] (N [w83,w0,w1,w2,w222,w29] (N [w83,w0,w1,w2,w28,w29] (N [w83,w0,w1,w97,w3,w4] L L) L) (N [w83,w0,w1,w2,w153,w4] (N [w83,w0,w1,w2,w99,w4] L L) L)) (N [w83,w0,w1,w2,w3,w154] (N [w83,w0,w1,w2,w3,w100] (N [w83,w0,w1,w2,w260,w4] L L) L) (N [w83,w0,w1,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLLR = true := by decide +kernel
def tbl_5_0LLLL : STree := N [w96,w0,w1,w2,w153,w330] tbl_5_0LLLLL tbl_5_0LLLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLLLL chk_tbl_5_0LLLLR
def tbl_5_0LLLRL : STree := (N [w345,w0,w216,w2,w3,w4] (N [w217,w14,w0,w1,w2,w140] (N [w573,w0,w1,w2,w3,w4] (N [w649,w0,w1,w2,w3,w4] (N [w83,w0,w1,w2,w4,w207] (N [w83,w0,w1,w2,w4,w60] (N [w83,w0,w1,w2,w3,w140] L L) L) (N [w651,w0,w1,w2,w3,w4] (N [w83,w0,w1,w2,w207,w27] L L) L)) (N [w610,w0,w1,w2,w3,w4] (N [w610,w0,w1,w2,w3,w100] (N [w812,w0,w1,w2,w3,w4] L L) L) (N [w573,w0,w1,w97,w3,w4] (N [w647,w0,w1,w2,w3,w4] L L) L))) (N [w643,w0,w1,w2,w3,w4] (N [w172,w0,w1,w26,w3,w171] (N [w645,w0,w1,w2,w3,w4] (N [w810,w0,w1,w2,w3,w4] L L) L) (N [w172,w0,w1,w2,w3,w4] (N [w172,w0,w1,w2,w3,w154] L L) L)) (N [w817,w0,w1,w2,w3,w4] (N [w815,w0,w1,w2,w3,w140] (N [w815,w0,w1,w2,w3,w4] L L) L) (N [w817,w0,w1,w2,w3,w140] L L)))) (N [w824,w0,w1,w2,w3,w4] (N [w195,w0,w18,w19,w3,w4] (N [w217,w0,w1,w2,w25,w140] (N [w217,w0,w1,w2,w3,w140] (N [w217,w0,w1,w2,w3,w4] L L) L) (N [w822,w0,w1,w2,w3,w4] (N [w820,w0,w1,w2,w3,w4] L L) L)) (N [w636,w0,w1,w2,w3,w4] (N [w638,w0,w1,w2,w3,w4] (N [w195,w0,w1,w2,w3,w4] L L) L) (N [w636,w0,w1,w2,w3,w189] L L))) (N [w639,w0,w1,w3,w4,w162] (N [w265,w0,w1,w2,w3,w4] (N [w265,w0,w1,w2,w28,w29] (N [w826,w0,w1,w2,w3,w4] L L) L) (N [w639,w0,w1,w2,w3,w4] (N [w265,w0,w1,w2,w72,w29] L L) L)) (N [w828,w0,w1,w2,w3,w4] (N [w635,w0,w1,w2,w3,w4] (N [w641,w0,w1,w2,w3,w4] L L) L) (N [w830,w0,w1,w2,w3,w4] L L))))) (N [w74,w0,w1,w2,w3,w59] (N [w74,w0,w18,w19,w3,w4] (N [w349,w0,w1,w2,w3,w4] (N [w839,w0,w1,w2,w3,w4] (N [w345,w0,w346,w2,w3,w4] (N [w345,w0,w1,w2,w3,w4] L L) L) (N [w349,w0,w1,w2,w80,w4] (N [w349,w14,w0,w1,w2,w4] L L) L)) (N [w842,w0,w1,w2,w3,w4] (N [w349,w0,w1,w2,w350,w4] (N [w349,w0,w1,w2,w3,w469] L L) L) (N [w74,w375,w0,w1,w2,w4] L L))) (N [w74,w0,w1,w2,w99,w4] (N [w74,w0,w579,w2,w3,w4] (N [w74,w0,w98,w2,w3,w4] (N [w74,w0,w22,w2,w3,w23] L L) L) (N [w74,w0,w1,w2,w28,w29] (N [w74,w0,w301,w2,w3,w4] L L) L)) (N [w74,w0,w1,w2,w3,w4] (N [w74,w0,w1,w2,w3,w100] (N [w74,w0,w1,w2,w299,w4] L L) L) (N [w74,w0,w1,w2,w3,w469] L L)))) (N [w627,w0,w1,w2,w3,w4] (N [w844,w0,w1,w2,w3,w4] (N [w846,w0,w1,w2,w3,w4] (N [w634,w0,w1,w2,w3,w4] (N [w74,w0,w1,w2,w4,w60] L L) L) (N [w630,w0,w1,w2,w3,w4] (N [w632,w0,w1,w2,w3,w4] L L) L)) (N [w212,w0,w1,w2,w3,w4] (N [w212,w0,w1,w2,w3,w154] (N [w629,w0,w1,w2,w3,w4] L L) L) (N [w212,w0,w1,w2,w4,w207] L L))) (N [w145,w0,w1,w2,w3,w4] (N [w168,w0,w1,w2,w3,w4] (N [w848,w0,w1,w2,w3,w4] (N [w627,w1,w2,w3,w4,w544] L L) L) (N [w853,w0,w1,w2,w3,w4] (N [w851,w0,w1,w2,w3,w4] L L) L)) (N [w621,w0,w1,w2,w3,w4] (N [w622,w0,w1,w2,w3,w516] (N [w622,w0,w1,w2,w3,w4] L L) L) (N [w621,w0,w1,w2,w3,w128] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLRL = true := by decide +kernel
def tbl_5_0LLLRR : STree := (N [w361,w0,w1,w2,w3,w4] (N [w102,w16,w1,w2,w3,w29] (N [w355,w0,w1,w2,w3,w4] (N [w618,w0,w1,w2,w3,w4] (N [w264,w0,w1,w2,w28,w29] (N [w855,w0,w1,w2,w3,w4] (N [w624,w0,w1,w2,w3,w4] L L) L) (N [w620,w0,w1,w2,w3,w4] (N [w264,w0,w1,w2,w3,w4] L L) L)) (N [w351,w0,w1,w2,w3,w4] (N [w859,w0,w1,w2,w3,w4] (N [w857,w0,w1,w2,w3,w4] L L) L) (N [w351,w357,w1,w2,w3,w4] (N [w351,w0,w352,w2,w3,w4] L L) L))) (N [w102,w375,w0,w1,w2,w4] (N [w866,w0,w1,w2,w3,w4] (N [w355,w363,w1,w2,w3,w4] (N [w355,w0,w1,w2,w356,w4] L L) L) (N [w102,w124,w16,w1,w2,w3] (N [w869,w0,w1,w2,w3,w4] L L) L)) (N [w102,w16,w1,w2,w3,w4] (N [w102,w16,w22,w1,w2,w3] (N [w102,w375,w103,w1,w2,w4] L L) L) (N [w102,w16,w1,w2,w3,w17] L L)))) (N [w102,w357,w1,w2,w3,w4] (N [w102,w0,w1,w2,w99,w4] (N [w102,w0,w18,w19,w3,w4] (N [w102,w91,w1,w2,w3,w4] (N [w102,w177,w1,w2,w3,w4] L L) L) (N [w102,w0,w1,w2,w28,w29] (N [w102,w0,w98,w2,w3,w4] L L) L)) (N [w102,w0,w1,w2,w3,w59] (N [w102,w0,w1,w2,w3,w4] (N [w102,w0,w1,w2,w3,w100] L L) L) (N [w102,w0,w1,w2,w4,w60] L L))) (N [w358,w0,w18,w19,w3,w4] (N [w102,w1,w2,w3,w4,w48] (N [w102,w103,w1,w2,w3,w4] (N [w102,w363,w1,w2,w3,w4] L L) L) (N [w872,w0,w1,w2,w3,w4] (N [w947,w0,w1,w2,w3,w4] L L) L)) (N [w361,w876,w0,w1,w2,w4] (N [w358,w0,w1,w359,w3,w4] (N [w358,w0,w1,w2,w3,w4] L L) L) (N [w361,w14,w0,w1,w2,w4] L L))))) (N [w104,w0,w98,w2,w3,w4] (N [w104,w876,w0,w1,w2,w4] (N [w889,w0,w1,w2,w3,w4] (N [w361,w0,w1,w2,w4,w21] (N [w361,w0,w1,w2,w362,w4] (N [w361,w0,w1,w2,w3,w59] L L) L) (N [w889,w0,w98,w2,w3,w4] (N [w361,w0,w364,w2,w3,w4] L L) L)) (N [w104,w877,w0,w22,w2,w3] (N [w885,w0,w1,w2,w3,w4] (N [w887,w0,w1,w2,w3,w4] L L) L) (N [w104,w876,w0,w22,w2,w4] L L))) (N [w104,w0,w22,w2,w3,w23] (N [w104,w16,w0,w22,w2,w3] (N [w104,w375,w0,w1,w2,w4] (N [w104,w881,w0,w1,w2,w4] L L) L) (N [w104,w0,w22,w2,w3,w4] (N [w104,w0,w18,w19,w3,w4] L L) L)) (N [w104,w0,w221,w2,w3,w4] (N [w104,w0,w216,w2,w3,w4] (N [w104,w0,w22,w2,w4,w60] L L) L) (N [w104,w0,w92,w2,w3,w4] L L)))) (N [w104,w0,w1,w2,w4,w60] (N [w104,w0,w1,w2,w3,w100] (N [w104,w0,w1,w2,w28,w29] (N [w104,w0,w1,w97,w3,w4] (N [w104,w0,w1,w26,w3,w27] L L) L) (N [w104,w0,w1,w2,w153,w4] (N [w104,w0,w1,w2,w99,w4] L L) L)) (N [w104,w0,w1,w2,w3,w59] (N [w104,w0,w1,w2,w3,w4] (N [w104,w0,w1,w2,w3,w154] L L) L) (N [w104,w0,w1,w2,w3,w140] L L))) (N [w104,w0,w2,w34,w3,w4] (N [w104,w0,w360,w2,w3,w4] (N [w104,w0,w352,w2,w3,w4] (N [w104,w0,w1,w2,w4,w207] L L) L) (N [w104,w0,w105,w2,w3,w4] (N [w104,w0,w364,w2,w3,w4] L L) L)) (N [w942,w0,w1,w2,w3,w4] (N [w942,w0,w1,w2,w3,w154] (N [w104,w0,w2,w3,w4,w41] L L) L) (N [w897,w0,w1,w2,w99,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLRR = true := by decide +kernel
def tbl_5_0LLLR : STree := N [w626,w0,w1,w2,w3,w4] tbl_5_0LLLRL tbl_5_0LLLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLLRL chk_tbl_5_0LLLRR
def tbl_5_0LLL : STree := N [w83,w0,w1,w2,w3,w59] tbl_5_0LLLL tbl_5_0LLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLLL chk_tbl_5_0LLLR
def tbl_5_0LLRLL : STree := (N [w385,w0,w18,w19,w3,w4] (N [w108,w0,w1,w2,w356,w4] (N [w108,w0,w22,w2,w3,w23] (N [w108,w386,w0,w1,w2,w4] (N [w108,w44,w0,w1,w2,w4] (N [w108,w399,w0,w1,w2,w28] (N [w895,w0,w1,w2,w3,w4] L L) L) (N [w108,w14,w363,w1,w2,w4] (N [w108,w14,w0,w1,w2,w4] L L) L)) (N [w108,w16,w1,w2,w3,w17] (N [w108,w368,w0,w1,w2,w4] (N [w108,w375,w0,w1,w2,w4] L L) L) (N [w108,w0,w18,w19,w3,w4] (N [w108,w84,w0,w1,w2,w4] L L) L))) (N [w108,w0,w1,w2,w99,w4] (N [w108,w0,w1,w2,w28,w29] (N [w108,w0,w1,w2,w28,w4] (N [w108,w0,w98,w2,w3,w4] L L) L) (N [w108,w0,w1,w2,w88,w4] (N [w108,w0,w1,w2,w80,w4] L L) L)) (N [w108,w0,w1,w2,w3,w59] (N [w108,w0,w1,w2,w3,w4] (N [w108,w0,w1,w2,w3,w100] L L) L) (N [w108,w0,w1,w2,w362,w4] L L)))) (N [w944,w0,w1,w2,w3,w154] (N [w108,w0,w1,w2,w4,w60] (N [w108,w0,w1,w2,w4,w36] (N [w108,w0,w1,w2,w87,w4] (N [w108,w0,w1,w2,w109,w4] L L) L) (N [w108,w0,w1,w2,w4,w70] (N [w108,w0,w1,w2,w4,w50] L L) L)) (N [w108,w0,w1,w2,w4,w384] (N [w108,w0,w1,w2,w4,w21] (N [w108,w0,w1,w2,w4,w41] L L) L) (N [w108,w0,w1,w2,w4,w65] L L))) (N [w392,w0,w1,w97,w3,w4] (N [w919,w0,w1,w2,w3,w4] (N [w931,w0,w1,w2,w3,w4] (N [w944,w0,w1,w2,w3,w4] L L) L) (N [w925,w0,w1,w2,w3,w4] (N [w929,w0,w1,w2,w3,w4] L L) L)) (N [w392,w0,w1,w2,w3,w4] (N [w392,w0,w1,w2,w3,w100] (N [w392,w0,w1,w2,w99,w4] L L) L) (N [w917,w0,w1,w2,w3,w4] L L))))) (N [w9,w538,w1,w2,w3,w4] (N [w9,w10,w2,w3,w4,w48] (N [w390,w14,w0,w1,w2,w4] (N [w927,w0,w1,w2,w3,w4] (N [w940,w0,w1,w2,w3,w4] (N [w385,w0,w1,w2,w3,w4] L L) L) (N [w391,w0,w1,w2,w3,w4] (N [w923,w0,w1,w2,w3,w4] L L) L)) (N [w938,w0,w1,w2,w3,w4] (N [w936,w0,w1,w2,w3,w4] (N [w390,w0,w1,w2,w3,w4] L L) L) (N [w9,w10,w0,w97,w3,w4] L L))) (N [w9,w375,w0,w1,w2,w4] (N [w9,w14,w0,w1,w2,w59] (N [w9,w44,w0,w1,w2,w29] (N [w9,w62,w0,w18,w3,w4] L L) L) (N [w9,w881,w0,w1,w2,w4] (N [w9,w14,w363,w1,w2,w4] L L) L)) (N [w9,w16,w1,w2,w3,w17] (N [w9,w16,w1,w2,w3,w289] (N [w9,w16,w0,w1,w2,w60] L L) L) (N [w9,w258,w1,w2,w3,w4] L L)))) (N [w9,w0,w98,w2,w3,w4] (N [w9,w0,w22,w2,w60,w23] (N [w9,w0,w20,w2,w4,w41] (N [w9,w0,w18,w34,w3,w4] (N [w9,w317,w1,w2,w3,w4] L L) L) (N [w9,w0,w22,w2,w3,w23] (N [w9,w0,w22,w2,w3,w169] L L) L)) (N [w9,w0,w98,w2,w153,w4] (N [w9,w0,w92,w2,w4,w21] (N [w9,w0,w92,w2,w3,w23] L L) L) (N [w9,w0,w98,w2,w3,w154] L L))) (N [w9,w0,w1,w2,w28,w29] (N [w9,w0,w579,w2,w3,w4] (N [w9,w0,w297,w2,w3,w4] (N [w9,w0,w934,w2,w3,w4] L L) L) (N [w9,w0,w301,w2,w3,w4] (N [w9,w0,w319,w2,w3,w4] L L) L)) (N [w9,w0,w1,w2,w99,w100] (N [w9,w0,w1,w2,w199,w4] (N [w9,w0,w1,w2,w88,w29] L L) L) (N [w9,w0,w1,w2,w99,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRLL = true := by decide +kernel
def tbl_5_0LLRLR : STree := (N [w271,w0,w1,w2,w270,w29] (N [w9,w0,w1,w2,w21,w59] (N [w9,w0,w1,w2,w3,w189] (N [w9,w0,w1,w2,w3,w298] (N [w9,w0,w1,w2,w935,w4] (N [w9,w0,w1,w2,w262,w4] (N [w9,w0,w1,w2,w260,w4] L L) L) (N [w9,w0,w1,w2,w3,w100] (N [w9,w0,w1,w2,w3,w200] L L) L)) (N [w9,w0,w1,w2,w3,w4] (N [w9,w0,w1,w2,w3,w263] (N [w9,w0,w1,w2,w3,w259] L L) L) (N [w9,w0,w1,w2,w3,w134] (N [w9,w0,w1,w2,w3,w128] L L) L))) (N [w9,w0,w1,w2,w4,w191] (N [w9,w0,w1,w2,w87,w29] (N [w9,w0,w1,w2,w3,w243] (N [w9,w0,w1,w2,w3,w59] L L) L) (N [w9,w0,w1,w2,w4,w137] (N [w9,w0,w1,w2,w4,w127] L L) L)) (N [w9,w0,w1,w2,w70,w29] (N [w9,w0,w1,w2,w4,w246] (N [w9,w0,w1,w2,w4,w60] L L) L) (N [w9,w0,w1,w2,w60,w23] L L)))) (N [w614,w0,w1,w2,w3,w4] (N [w616,w0,w1,w2,w3,w263] (N [w9,w0,w1,w3,w4,w162] (N [w9,w0,w1,w531,w3,w4] (N [w9,w0,w1,w133,w3,w4] L L) L) (N [w9,w1,w2,w3,w4,w544] (N [w9,w1,w2,w3,w4,w188] L L) L)) (N [w615,w0,w1,w2,w3,w4] (N [w615,w0,w1,w2,w3,w259] (N [w616,w0,w1,w2,w3,w4] L L) L) (N [w614,w0,w1,w2,w3,w575] L L))) (N [w275,w0,w1,w2,w3,w4] (N [w275,w0,w1,w2,w153,w154] (N [w275,w0,w98,w2,w3,w4] (N [w275,w0,w98,w2,w3,w154] L L) L) (N [w275,w0,w1,w2,w3,w154] (N [w275,w0,w1,w2,w153,w4] L L) L)) (N [w949,w0,w1,w2,w3,w4] (N [w608,w0,w1,w2,w3,w4] (N [w608,w0,w1,w2,w3,w200] L L) L) (N [w271,w0,w1,w2,w3,w4] L L))))) (N [w395,w0,w2,w3,w4,w11] (N [w393,w0,w1,w2,w28,w29] (N [w604,w0,w1,w2,w3,w4] (N [w605,w0,w1,w2,w3,w4] (N [w607,w0,w1,w2,w3,w4] (N [w271,w0,w1,w2,w4,w207] L L) L) (N [w268,w0,w1,w2,w3,w4] (N [w951,w0,w1,w2,w3,w4] L L) L)) (N [w393,w44,w1,w2,w3,w4] (N [w953,w0,w1,w2,w3,w4] (N [w602,w0,w1,w2,w3,w4] L L) L) (N [w393,w14,w1,w2,w3,w4] L L))) (N [w395,w0,w58,w2,w3,w4] (N [w967,w0,w1,w2,w3,w4] (N [w393,w394,w1,w2,w3,w4] (N [w393,w0,w1,w2,w3,w4] L L) L) (N [w395,w0,w18,w2,w3,w4] (N [w957,w0,w1,w2,w3,w4] L L) L)) (N [w395,w0,w1,w2,w3,w4] (N [w395,w0,w1,w2,w28,w29] (N [w395,w0,w20,w2,w3,w4] L L) L) (N [w395,w0,w396,w2,w3,w4] L L)))) (N [w68,w375,w0,w1,w2,w4] (N [w966,w0,w1,w2,w3,w4] (N [w966,w0,w1,w2,w28] (N [w966,w68,w0,w1,w2,w28] (N [w968,w0,w1,w2,w3,w4] L L) L) (N [w966,w0,w1,w2,w28,w29] (N [w966,w0,w1,w2,w28,w3] L L) L)) (N [w68,w44,w0,w1,w2,w29] (N [w964,w0,w1,w2,w3,w4] (N [w969,w0,w1,w2,w3,w4] L L) L) (N [w68,w14,w1,w2,w4,w15] L L))) (N [w68,w0,w1,w2,w99,w4] (N [w68,w0,w20,w2,w4,w21] (N [w68,w0,w963,w2,w3,w4] (N [w68,w0,w18,w19,w3,w4] L L) L) (N [w68,w0,w1,w2,w28,w29] (N [w68,w0,w98,w2,w3,w4] L L) L)) (N [w68,w0,w1,w2,w70,w29] (N [w68,w0,w1,w2,w3,w59] (N [w68,w0,w1,w2,w3,w4] L L) L) (N [w68,w0,w1,w3,w4,w162] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRLR = true := by decide +kernel
def tbl_5_0LLRL : STree := N [w9,w0,w1,w2,w299,w4] tbl_5_0LLRLL tbl_5_0LLRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLRLL chk_tbl_5_0LLRLR
def tbl_5_0LLRRL : STree := (N [w998,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w260,w4] (N [w400,w401,w1,w2,w3,w4] (N [w403,w0,w1,w2,w3,w4] (N [w973,w0,w1,w2,w3,w4] (N [w975,w0,w1,w2,w3,w4] (N [w600,w0,w1,w2,w3,w4] L L) L) (N [w403,w0,w1,w2,w64,w4] (N [w403,w0,w18,w19,w3,w4] L L) L)) (N [w400,w62,w1,w2,w3,w4] (N [w403,w0,w1,w2,w4,w29] (N [w403,w0,w1,w2,w404,w4] L L) L) (N [w400,w0,w1,w2,w3,w4] (N [w400,w0,w18,w19,w3,w4] L L) L))) (N [w61,w0,w18,w19,w3,w4] (N [w61,w10,w2,w3,w4,w11] (N [w987,w0,w1,w2,w3,w4] (N [w985,w0,w1,w2,w3,w4] L L) L) (N [w61,w258,w1,w2,w3,w4] (N [w61,w62,w0,w18,w3,w4] L L) L)) (N [w61,w0,w1,w2,w28,w29] (N [w61,w0,w98,w2,w3,w4] (N [w61,w0,w982,w19,w3,w4] L L) L) (N [w61,w0,w1,w2,w99,w4] L L)))) (N [w595,w0,w1,w2,w3,w4] (N [w989,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w3,w59] (N [w61,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w262,w4] L L) L) (N [w598,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w3,w243] L L) L)) (N [w141,w0,w98,w2,w3,w4] (N [w141,w0,w18,w33,w3,w4] (N [w597,w0,w1,w2,w3,w4] L L) L) (N [w141,w0,w1,w2,w3,w4] L L))) (N [w594,w0,w1,w531,w3,w4] (N [w210,w0,w1,w2,w3,w4] (N [w995,w0,w1,w2,w3,w4] (N [w993,w0,w1,w2,w3,w4] L L) L) (N [w594,w0,w1,w2,w3,w4] (N [w210,w0,w1,w2,w4,w60] L L) L)) (N [w591,w0,w1,w2,w3,w4] (N [w593,w0,w1,w2,w3,w4] (N [w592,w0,w1,w2,w3,w4] L L) L) (N [w589,w0,w1,w2,w3,w4] L L))))) (N [w407,w0,w419,w2,w3,w4] (N [w582,w0,w1,w2,w3,w4] (N [w242,w0,w18,w19,w3,w4] (N [w997,w0,w1,w2,w19,w4] (N [w997,w0,w1,w2,w66,w4] (N [w997,w242,w0,w1,w2,w4] L L) L) (N [w997,w0,w1,w2,w4] (N [w997,w0,w1,w2,w3,w4] L L) L)) (N [w586,w0,w1,w2,w3,w4] (N [w242,w0,w1,w2,w4,w246] (N [w242,w0,w1,w2,w3,w4] L L) L) (N [w584,w0,w1,w2,w3,w4] L L))) (N [w409,w0,w1,w2,w410,w4] (N [w409,w0,w1,w2,w3,w4] (N [w1002,w0,w1,w2,w3,w4] (N [w1004,w0,w1,w2,w3,w4] L L) L) (N [w409,w0,w1,w2,w3,w59] (N [w409,w0,w1,w2,w3,w1001] L L) L)) (N [w407,w0,w98,w2,w3,w4] (N [w407,w0,w18,w2,w3,w4] (N [w409,w0,w415,w2,w3,w4] L L) L) (N [w407,w0,w1,w2,w3,w4] L L)))) (N [w112,w0,w1,w2,w28,w29] (N [w112,w0,w18,w2,w3,w4] (N [w1013,w0,w1,w2,w3,w4] (N [w1011,w0,w1,w2,w3,w4] (N [w407,w0,w113,w2,w3,w4] L L) L) (N [w112,w12,w0,w18,w3,w4] (N [w112,w459,w0,w18,w3,w4] L L) L)) (N [w112,w0,w98,w2,w3,w4] (N [w112,w0,w86,w2,w3,w4] (N [w112,w0,w18,w19,w3,w4] L L) L) (N [w112,w0,w1,w97,w3,w4] L L))) (N [w112,w0,w1,w2,w3,w140] (N [w112,w0,w1,w2,w3,w4] (N [w112,w0,w1,w2,w153,w4] (N [w112,w0,w1,w2,w99,w4] L L) L) (N [w112,w0,w1,w2,w3,w59] (N [w112,w0,w1,w2,w3,w1001] L L) L)) (N [w112,w0,w113,w2,w3,w4] (N [w112,w0,w419,w2,w3,w4] (N [w112,w0,w415,w2,w3,w4] L L) L) (N [w112,w0,w2,w3,w4,w41] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRRL = true := by decide +kernel
def tbl_5_0LLRRR : STree := (N [w114,w0,w1,w24,w2,w140] (N [w416,w0,w1,w2,w29] (N [w451,w0,w2,w3,w4,w11] (N [w451,w0,w51,w2,w3,w4] (N [w1017,w454,w0,w1,w2,w4] (N [w1015,w0,w1,w2,w3,w4] (N [w1101,w0,w1,w2,w3,w4] L L) L) (N [w451,w454,w0,w1,w2,w4] (N [w1017,w0,w1,w2,w3,w4] L L) L)) (N [w451,w0,w1,w2,w3,w4] (N [w451,w0,w22,w2,w3,w4] (N [w451,w0,w18,w2,w3,w4] L L) L) (N [w451,w0,w452,w2,w3,w4] (N [w451,w0,w1,w2,w4,w207] L L) L))) (N [w416,w454,w0,w1,w2,w4] (N [w1022,w0,w1,w2,w3,w4] (N [w1130,w0,w1,w2,w3,w4] (N [w1116,w0,w1,w2,w3,w4] L L) L) (N [w416,w7,w0,w1,w2,w29] (N [w416,w114,w0,w1,w2,w29] L L) L)) (N [w416,w0,w1,w2,w3,w417] (N [w416,w0,w1,w2,w3,w4] (N [w416,w0,w1,w2,w28,w29] L L) L) (N [w416,w0,w1,w2,w3,w29] L L)))) (N [w1037,w0,w1,w2,w3,w4] (N [w413,w0,w1,w2,w115,w4] (N [w413,w0,w1,w2,w153,w4] (N [w413,w0,w1,w24,w2,w4] (N [w416,w0,w1019,w2,w3,w4] L L) L) (N [w413,w0,w1,w2,w420,w4] (N [w413,w0,w1,w2,w3,w4] L L) L)) (N [w1035,w0,w1,w2,w3,w4] (N [w1033,w0,w1,w2,w3,w4] (N [w413,w0,w1,w2,w4,w29] L L) L) (N [w1037,w0,w1,w2,w99,w4] L L))) (N [w114,w12,w1,w3,w4,w13] (N [w114,w1026,w0,w1,w24,w2] (N [w114,w7,w0,w1,w2,w140] (N [w114,w116,w0,w1,w2,w29] L L) L) (N [w114,w138,w0,w1,w2,w140] (N [w114,w1026,w0,w1,w2,w3] L L) L)) (N [w114,w0,w98,w2,w3,w4] (N [w114,w0,w18,w19,w3,w4] (N [w114,w16,w0,w1,w2,w29] L L) L) (N [w114,w0,w1,w24,w2,w4] L L))))) (N [w114,w0,w1,w2,w4,w140] (N [w114,w0,w1,w2,w3,w1001] (N [w114,w0,w1,w2,w99,w4] (N [w114,w0,w1,w2,w64,w4] (N [w114,w0,w1,w97,w3,w4] (N [w114,w0,w1,w93,w2,w4] L L) L) (N [w114,w0,w1,w2,w222,w4] (N [w114,w0,w1,w2,w28,w29] L L) L)) (N [w114,w0,w1,w2,w3,w154] (N [w114,w0,w1,w2,w3,w100] (N [w114,w0,w1,w2,w153,w4] L L) L) (N [w114,w0,w1,w2,w3,w4] L L))) (N [w114,w0,w1,w2,w115,w4] (N [w114,w0,w1,w2,w420,w4] (N [w114,w0,w1,w2,w3,w140] (N [w114,w0,w1,w2,w3,w59] L L) L) (N [w114,w0,w1,w2,w418,w4] (N [w114,w0,w1,w2,w410,w4] L L) L)) (N [w114,w0,w1,w2,w4,w60] (N [w114,w0,w1,w2,w4,w46] (N [w114,w0,w1,w2,w4,w36] L L) L) (N [w114,w0,w1,w2,w4,w207] L L)))) (N [w1045,w0,w1,w2,w3,w4] (N [w114,w0,w1019,w2,w3,w4] (N [w114,w0,w1,w2,w23,w29] (N [w114,w0,w1,w2,w4,w444] (N [w114,w0,w1,w2,w4,w29] L L) L) (N [w114,w0,w1,w2,w27,w29] (N [w114,w0,w1,w2,w140] L L) L)) (N [w1099,w0,w1,w2,w3,w4] (N [w1090,w0,w1,w2,w3,w4] (N [w1090,w0,w1,w97,w3,w4] L L) L) (N [w1043,w0,w1,w2,w3,w4] L L))) (N [w110,w62,w1,w2,w3,w4] (N [w110,w12,w18,w1,w3,w4] (N [w110,w10,w2,w3,w4,w11] (N [w110,w120,w12,w1,w3,w4] L L) L) (N [w110,w12,w1,w3,w4,w13] (N [w110,w12,w1,w2,w3,w4] L L) L)) (N [w110,w0,w98,w2,w3,w4] (N [w110,w0,w18,w19,w3,w4] (N [w110,w150,w1,w2,w3,w4] L L) L) (N [w110,w0,w1,w97,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRRR = true := by decide +kernel
def tbl_5_0LLRR : STree := N [w1095,w0,w1,w2,w3,w4] tbl_5_0LLRRL tbl_5_0LLRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLRRL chk_tbl_5_0LLRRR
def tbl_5_0LLR : STree := N [w600,w0,w1,w2,w153,w4] tbl_5_0LLRL tbl_5_0LLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLRL chk_tbl_5_0LLRR
def tbl_5_0LL : STree := N [w897,w0,w1,w2,w3,w4] tbl_5_0LLL tbl_5_0LLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LLL chk_tbl_5_0LLR
def tbl_5_0LRLLL : STree := (N [w7,w0,w18,w19,w3,w4] (N [w448,w0,w1,w2,w3,w4] (N [w1073,w0,w1,w2,w3,w4] (N [w110,w414,w1,w2,w3,w4] (N [w110,w0,w1,w2,w3,w4] (N [w110,w0,w1,w2,w153,w4] (N [w110,w0,w1,w2,w99,w4] L L) L) (N [w110,w0,w1,w2,w3,w140] (N [w110,w0,w1,w2,w3,w59] L L) L)) (N [w110,w1,w2,w3,w4,w55] (N [w110,w111,w1,w2,w3,w4] (N [w110,w408,w1,w2,w3,w4] L L) L) (N [w1069,w0,w1,w2,w3,w4] (N [w1067,w0,w1,w2,w3,w4] L L) L))) (N [w1077,w0,w1,w2,w4,w60] (N [w1075,w0,w1,w2,w3,w4] (N [w445,w0,w1,w2,w3,w4] (N [w1071,w0,w1,w2,w3,w4] L L) L) (N [w1077,w0,w1,w2,w3,w4] (N [w1079,w0,w1,w2,w3,w4] L L) L)) (N [w448,w0,w1,w97,w3,w4] (N [w446,w0,w1,w2,w4,w29] (N [w446,w0,w1,w2,w3,w4] L L) L) (N [w448,w0,w1,w2,w99,w4] L L)))) (N [w7,w12,w1,w3,w4,w48] (N [w7,w10,w0,w97,w3,w4] (N [w447,w0,w1,w2,w3,w4] (N [w447,w0,w1,w2,w28,w29] (N [w1083,w0,w1,w2,w3,w4] L L) L) (N [w1085,w0,w1,w2,w3,w4] (N [w1087,w0,w1,w2,w3,w4] L L) L)) (N [w7,w12,w98,w3,w4,w13] (N [w7,w12,w0,w98,w3,w4] (N [w7,w10,w2,w3,w4,w48] L L) L) (N [w7,w12,w1,w153,w4,w13] L L))) (N [w7,w258,w1,w2,w3,w4] (N [w7,w44,w0,w1,w2,w29] (N [w7,w62,w0,w18,w3,w4] (N [w7,w12,w1,w3,w4,w13] L L) L) (N [w7,w14,w0,w1,w2,w140] (N [w7,w14,w0,w1,w2,w59] L L) L)) (N [w7,w0,w18,w34,w3,w4] (N [w7,w540,w1,w2,w3,w4] (N [w7,w317,w1,w2,w3,w4] L L) L) (N [w7,w0,w18,w33,w3,w4] L L))))) (N [w7,w0,w1,w2,w153,w154] (N [w7,w0,w1,w97,w3,w4] (N [w7,w0,w319,w2,w3,w4] (N [w7,w0,w98,w2,w153,w4] (N [w7,w0,w92,w2,w3,w23] (N [w7,w0,w20,w2,w4,w41] L L) L) (N [w7,w0,w297,w2,w3,w4] (N [w7,w0,w98,w2,w3,w4] L L) L)) (N [w7,w0,w1,w93,w3,w27] (N [w7,w0,w1,w24,w4,w43] (N [w7,w0,w301,w2,w3,w4] L L) L) (N [w7,w0,w1,w97,w99,w4] L L))) (N [w7,w0,w1,w2,w199,w4] (N [w7,w0,w1,w302,w3,w4] (N [w7,w0,w1,w318,w3,w4] (N [w7,w0,w1,w296,w3,w4] L L) L) (N [w7,w0,w1,w2,w222,w29] (N [w7,w0,w1,w2,w88,w29] L L) L)) (N [w7,w0,w1,w2,w299,w4] (N [w7,w0,w1,w2,w99,w4] (N [w7,w0,w1,w2,w99,w100] L L) L) (N [w7,w0,w1,w2,w1081,w4] L L)))) (N [w7,w0,w1,w2,w3,w59] (N [w7,w0,w1,w2,w3,w1001] (N [w7,w0,w1,w2,w260,w4] (N [w7,w0,w1,w2,w576,w4] (N [w7,w0,w1,w2,w153,w4] L L) L) (N [w7,w0,w1,w2,w3,w4] (N [w7,w0,w1,w2,w262,w4] L L) L)) (N [w7,w0,w1,w2,w3,w516] (N [w7,w0,w1,w2,w3,w134] (N [w7,w0,w1,w2,w3,w128] L L) L) (N [w7,w0,w1,w2,w3,w189] L L))) (N [w7,w0,w1,w2,w207,w27] (N [w7,w0,w1,w2,w70,w29] (N [w7,w0,w1,w2,w3,w243] (N [w7,w0,w1,w2,w3,w140] L L) L) (N [w7,w0,w1,w2,w72,w29] (N [w7,w0,w1,w2,w60,w23] L L) L)) (N [w7,w0,w1019,w2,w3,w4] (N [w7,w0,w1,w3,w4,w162] (N [w7,w0,w1,w133,w3,w4] L L) L) (N [w7,w0,w2,w135,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLLL = true := by decide +kernel
def tbl_5_0LRLLR : STree := (N [w454,w131,w0,w1,w2,w4] (N [w567,w0,w1,w2,w3,w4] (N [w239,w0,w1,w2,w3,w4] (N [w578,w0,w1,w577,w3,w4] (N [w581,w0,w1,w2,w3,w4] (N [w581,w0,w1,w302,w3,w4] (N [w7,w1,w2,w3,w4,w188] L L) L) (N [w580,w0,w1,w2,w3,w4] (N [w580,w0,w1,w318,w3,w4] L L) L)) (N [w239,w0,w1,w97,w99,w4] (N [w239,w10,w0,w97,w3,w4] (N [w578,w0,w1,w2,w3,w4] L L) L) (N [w239,w0,w1,w2,w99,w4] (N [w239,w0,w1,w97,w3,w4] L L) L))) (N [w1097,w0,w1,w2,w3,w4] (N [w234,w0,w1,w2,w28,w29] (N [w234,w0,w1,w93,w3,w27] (N [w1093,w0,w1,w2,w3,w4] L L) L) (N [w234,w0,w1,w2,w3,w140] (N [w234,w0,w1,w2,w3,w4] L L) L)) (N [w568,w0,w1,w2,w3,w4] (N [w570,w0,w1,w2,w3,w4] (N [w231,w0,w1,w2,w3,w4] L L) L) (N [w568,w0,w1,w2,w3,w59] L L)))) (N [w449,w12,w1,w2,w3,w4] (N [w559,w0,w1,w2,w3,w4] (N [w566,w0,w1,w2,w3,w4] (N [w227,w0,w1,w2,w3,w4] (N [w1103,w0,w1,w2,w3,w4] L L) L) (N [w561,w0,w1,w2,w3,w4] (N [w564,w0,w1,w2,w3,w4] L L) L)) (N [w449,w454,w0,w1,w2,w4] (N [w1106,w0,w1,w2,w3,w4] (N [w1106,w454,w0,w1,w2,w4] L L) L) (N [w449,w131,w1,w2,w3,w4] L L))) (N [w449,w1,w2,w3,w4,w11] (N [w449,w0,w1,w2,w3,w4] (N [w449,w16,w1,w2,w3,w4] (N [w449,w16,w1,w26,w2,w3] L L) L) (N [w449,w450,w1,w2,w3,w4] (N [w449,w0,w1,w2,w4,w207] L L) L)) (N [w454,w201,w0,w1,w2,w4] (N [w454,w54,w0,w1,w2,w4] (N [w1119,w0,w1,w2,w3,w4] L L) L) (N [w454,w10,w0,w1,w2,w4] L L))))) (N [w454,w0,w1,w2,w4] (N [w454,w0,w1,w1109,w2,w4] (N [w454,w0,w450,w1,w2,w4] (N [w454,w16,w0,w1,w26,w2] (N [w454,w14,w0,w1,w2,w4] (N [w454,w12,w0,w1,w2,w4] L L) L) (N [w454,w0,w1108,w1,w2,w4] (N [w454,w16,w0,w1,w2,w4] L L) L)) (N [w454,w0,w20,w1,w2,w4] (N [w454,w0,w18,w1,w2,w4] (N [w454,w0,w51,w1,w2,w4] L L) L) (N [w454,w0,w22,w1,w2,w4] L L))) (N [w454,w0,w1,w2,w208,w4] (N [w454,w0,w1,w24,w2,w4] (N [w454,w0,w1,w71,w2,w4] (N [w454,w0,w1,w452,w2,w4] L L) L) (N [w454,w0,w1,w26,w2,w27] (N [w454,w0,w1,w26,w2,w4] L L) L)) (N [w454,w0,w1,w2,w3,w4] (N [w454,w0,w1,w2,w28,w4] (N [w454,w0,w1,w2,w19,w4] L L) L) (N [w454,w0,w1,w2,w455,w4] L L)))) (N [w454,w0,w1,w2,w4,w13] (N [w454,w0,w1,w2,w4,w25] (N [w454,w0,w1,w2,w4,w17] (N [w454,w0,w1,w2,w4,w211] (N [w454,w0,w1,w2,w4,w15] L L) L) (N [w454,w0,w1,w2,w4,w207] (N [w454,w0,w1,w2,w4,w21] L L) L)) (N [w454,w0,w1,w2,w4,w29] (N [w454,w0,w1,w2,w4,w27] (N [w454,w0,w1,w2,w4,w23] L L) L) (N [w454,w0,w1,w2,w4,w11] L L))) (N [w1127,w0,w1,w2,w3,w4] (N [w1115,w0,w1,w26,w2,w3] (N [w1123,w0,w1,w2,w3,w4] (N [w1122,w0,w1,w2,w3,w4] L L) L) (N [w1124,w0,w1,w2,w3,w4] (N [w1115,w0,w1,w2,w3,w4] L L) L)) (N [w1120,w0,w1,w2,w3,w4] (N [w1125,w0,w1,w2,w3,w4] (N [w1117,w0,w1,w2,w3,w4] L L) L) (N [w54,w12,w1,w3,w4,w13] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLLR = true := by decide +kernel
def tbl_5_0LRLL : STree := N [w7,w0,w2,w3,w4,w161] tbl_5_0LRLLL tbl_5_0LRLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRLLL chk_tbl_5_0LRLLR
def tbl_5_0LRLRL : STree := (N [w460,w0,w1,w2,w4,w15] (N [w54,w1,w2,w3,w4,w544] (N [w54,w0,w1,w2,w3,w100] (N [w54,w0,w1,w1114,w2,w4] (N [w54,w0,w18,w19,w3,w4] (N [w54,w16,w1,w2,w3,w211] (N [w54,w16,w0,w1,w2,w207] L L) L) (N [w54,w0,w98,w2,w3,w4] (N [w54,w0,w22,w2,w3,w23] L L) L)) (N [w54,w0,w1,w2,w28,w29] (N [w54,w0,w1,w97,w3,w4] (N [w54,w0,w1,w26,w3,w171] L L) L) (N [w54,w0,w1,w2,w153,w4] (N [w54,w0,w1,w2,w99,w4] L L) L))) (N [w54,w0,w1,w2,w4,w191] (N [w54,w0,w1,w2,w3,w59] (N [w54,w0,w1,w2,w3,w4] (N [w54,w0,w1,w2,w3,w154] L L) L) (N [w54,w0,w1,w2,w4,w514] (N [w54,w0,w1,w2,w3,w140] L L) L)) (N [w54,w0,w1,w2,w207,w27] (N [w54,w0,w1,w2,w4,w207] (N [w54,w0,w1,w2,w4,w60] L L) L) (N [w54,w0,w2,w515,w3,w4] L L)))) (N [w1139,w0,w18,w1,w3,w4] (N [w1128,w0,w1,w2,w3,w4] (N [w555,w0,w1,w2,w3,w4] (N [w555,w0,w1,w2,w3,w100] (N [w555,w0,w1,w97,w3,w4] L L) L) (N [w551,w0,w1,w2,w3,w4] (N [w553,w0,w1,w2,w3,w4] L L) L)) (N [w201,w0,w1,w2,w3,w140] (N [w201,w0,w1,w2,w3,w4] (N [w201,w0,w1,w2,w28,w29] L L) L) (N [w1139,w47,w0,w18,w3,w4] L L))) (N [w460,w0,w49,w1,w2,w4] (N [w1139,w0,w1,w2,w3,w4] (N [w1139,w0,w18,w3,w4] (N [w1139,w0,w18,w19,w3,w4] L L) L) (N [w1132,w0,w1,w2,w3,w4] (N [w1135,w0,w1,w2,w3,w4] L L) L)) (N [w460,w0,w1,w2,w3,w4] (N [w460,w0,w20,w1,w2,w4] (N [w460,w0,w18,w19,w3,w4] L L) L) (N [w460,w0,w1,w2,w461,w4] L L))))) (N [w47,w0,w1,w2,w3,w128] (N [w1146,w0,w1,w2,w3,w4] (N [w457,w0,w18,w19,w3,w4] (N [w457,w32,w1,w2,w3,w4] (N [w1143,w0,w1,w2,w3,w4] (N [w460,w0,w1,w2,w4,w29] L L) L) (N [w457,w10,w1,w2,w3,w4] (N [w457,w10,w18,w2,w3,w4] L L) L)) (N [w457,w1,w2,w3,w4,w15] (N [w457,w458,w1,w2,w3,w4] (N [w457,w0,w1,w2,w3,w4] L L) L) (N [w1141,w0,w1,w2,w3,w4] L L))) (N [w47,w0,w98,w2,w3,w4] (N [w47,w62,w0,w18,w3,w4] (N [w47,w10,w2,w3,w4,w48] (N [w1144,w0,w1,w2,w3,w4] L L) L) (N [w47,w0,w18,w19,w3,w4] (N [w47,w0,w18,w34,w3,w4] L L) L)) (N [w47,w0,w1,w2,w99,w4] (N [w47,w0,w1,w2,w199,w4] (N [w47,w0,w1,w2,w28,w29] L L) L) (N [w47,w0,w1,w2,w3,w4] L L)))) (N [w1147,w1,w2,w3,w4] (N [w1147,w187,w1,w2,w3,w4] (N [w47,w1,w2,w3,w4,w188] (N [w47,w0,w1,w2,w3,w59] (N [w47,w0,w1,w2,w3,w189] L L) L) (N [w546,w0,w1,w2,w3,w4] (N [w548,w0,w1,w2,w3,w4] L L) L)) (N [w1147,w18,w1,w2,w3,w4] (N [w1147,w51,w1,w2,w3,w4] (N [w1147,w0,w1,w2,w3,w4] L L) L) (N [w1147,w22,w1,w2,w3,w4] L L))) (N [w1148,w0,w1,w2,w4] (N [w1148,w0,w18,w1,w2,w4] (N [w1148,w0,w51,w1,w2,w4] (N [w1148,w187,w0,w1,w2,w4] L L) L) (N [w1148,w0,w1,w2,w3,w4] (N [w1148,w0,w22,w1,w2,w4] L L) L)) (N [w187,w0,w1,w2,w4,w191] (N [w187,w0,w1,w2,w3,w4] (N [w187,w0,w18,w19,w3,w4] L L) L) (N [w187,w0,w1,w2,w4,w60] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLRL = true := by decide +kernel
def tbl_5_0LRLRR : STree := (N [w118,w10,w0,w2,w3,w4] (N [w122,w0,w1,w2,w99,w4] (N [w464,w0,w1,w2,w3,w59] (N [w1154,w0,w1,w2,w3,w4] (N [w468,w0,w1,w2,w28,w29] (N [w1151,w0,w1,w2,w3,w4] (N [w542,w0,w1,w2,w3,w4] L L) L) (N [w468,w0,w1,w2,w3,w469] (N [w468,w0,w1,w2,w3,w4] L L) L)) (N [w464,w0,w1,w2,w3,w4] (N [w464,w0,w1,w2,w99,w4] (N [w464,w14,w0,w1,w2,w4] L L) L) (N [w464,w0,w1,w2,w3,w469] (N [w464,w0,w1,w2,w3,w1153] L L) L))) (N [w122,w14,w0,w1,w2,w469] (N [w1163,w0,w1,w2,w3,w4] (N [w464,w0,w1,w2,w123,w4] (N [w464,w0,w1,w2,w474,w4] L L) L) (N [w122,w14,w0,w1,w2,w4] (N [w1161,w0,w1,w2,w3,w4] L L) L)) (N [w122,w0,w1,w2,w28,w29] (N [w122,w0,w98,w2,w3,w4] (N [w122,w0,w18,w19,w3,w4] L L) L) (N [w122,w0,w1,w2,w80,w4] L L)))) (N [w122,w0,w1,w2,w4,w60] (N [w122,w0,w1,w2,w474,w4] (N [w122,w0,w1,w2,w3,w1153] (N [w122,w0,w1,w2,w3,w4] (N [w122,w0,w1,w2,w3,w100] L L) L) (N [w122,w0,w1,w2,w3,w59] (N [w122,w0,w1,w2,w3,w469] L L) L)) (N [w122,w0,w1,w2,w123,w469] (N [w122,w0,w1,w2,w123,w4] (N [w122,w0,w1,w2,w470,w4] L L) L) (N [w122,w0,w1,w2,w4,w50] L L))) (N [w471,w0,w1,w472,w3,w4] (N [w471,w0,w18,w19,w3,w4] (N [w471,w10,w0,w2,w3,w4] (N [w1206,w0,w1,w2,w3,w4] L L) L) (N [w471,w0,w1,w2,w3,w4] (N [w471,w0,w98,w2,w3,w4] L L) L)) (N [w1191,w0,w1,w2,w3,w4] (N [w1172,w0,w1,w2,w3,w4] (N [w471,w0,w1,w121,w3,w4] L L) L) (N [w1174,w0,w1,w2,w3,w4] L L))))) (N [w1195,w0,w1,w2,w4,w60] (N [w118,w0,w1,w2,w3,w469] (N [w118,w0,w1,w2,w28,w29] (N [w118,w0,w75,w2,w3,w4] (N [w118,w0,w20,w2,w4,w21] (N [w118,w0,w18,w19,w3,w4] L L) L) (N [w118,w0,w1,w97,w3,w4] (N [w118,w0,w98,w2,w3,w4] L L) L)) (N [w118,w0,w1,w2,w3,w4] (N [w118,w0,w1,w2,w153,w4] (N [w118,w0,w1,w2,w99,w4] L L) L) (N [w118,w0,w1,w2,w3,w1153] L L))) (N [w118,w0,w2,w57,w3,w4] (N [w118,w0,w465,w2,w3,w4] (N [w118,w0,w1,w2,w3,w140] (N [w118,w0,w1,w2,w3,w59] L L) L) (N [w118,w0,w119,w2,w3,w4] (N [w118,w0,w473,w2,w3,w4] L L) L)) (N [w1188,w0,w1,w2,w3,w4] (N [w1193,w0,w1,w2,w3,w4] (N [w118,w0,w2,w3,w4,w70] L L) L) (N [w1195,w0,w1,w2,w3,w4] L L)))) (N [w5,w10,w0,w97,w3,w4] (N [w493,w0,w1,w2,w28,w29] (N [w485,w0,w1,w2,w3,w4] (N [w485,w0,w18,w19,w3,w4] (N [w492,w0,w1,w2,w3,w4] L L) L) (N [w493,w14,w0,w1,w2,w4] (N [w1197,w0,w1,w2,w3,w4] L L) L)) (N [w493,w0,w1,w2,w3,w125] (N [w493,w0,w1,w2,w3,w469] (N [w493,w0,w1,w2,w3,w4] L L) L) (N [w1199,w0,w1,w2,w3,w4] L L))) (N [w5,w258,w1,w2,w3,w4] (N [w5,w44,w0,w1,w2,w29] (N [w5,w62,w0,w18,w3,w4] (N [w5,w10,w2,w3,w4,w48] L L) L) (N [w5,w14,w0,w1,w2,w59] (N [w5,w14,w0,w1,w2,w469] L L) L)) (N [w5,w0,w18,w480,w3,w4] (N [w5,w0,w18,w34,w3,w4] (N [w5,w317,w1,w2,w3,w4] L L) L) (N [w5,w0,w20,w2,w4,w41] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLRR = true := by decide +kernel
def tbl_5_0LRLR : STree := N [w187,w1,w2,w3,w4,w544] tbl_5_0LRLRL tbl_5_0LRLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRLRL chk_tbl_5_0LRLRR
def tbl_5_0LRL : STree := N [w54,w1112,w0,w1,w2,w4] tbl_5_0LRLL tbl_5_0LRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRLL chk_tbl_5_0LRLR
def tbl_5_0LRRLL : STree := (N [w1208,w0,w1,w2,w3,w4] (N [w5,w0,w1,w2,w3,w1184] (N [w5,w0,w1,w2,w99,w4] (N [w5,w0,w301,w2,w3,w4] (N [w5,w0,w98,w121,w3,w4] (N [w5,w0,w98,w2,w3,w4] (N [w5,w0,w98,w2,w153,w4] L L) L) (N [w5,w0,w319,w2,w3,w4] (N [w5,w0,w297,w2,w3,w4] L L) L)) (N [w5,w0,w1,w2,w88,w29] (N [w5,w0,w1,w2,w486,w29] (N [w5,w0,w1,w2,w490,w29] L L) L) (N [w5,w0,w1,w2,w99,w100] (N [w5,w0,w1,w2,w199,w4] L L) L))) (N [w5,w0,w1,w2,w3,w469] (N [w5,w0,w1,w2,w262,w4] (N [w5,w0,w1,w2,w260,w4] (N [w5,w0,w1,w2,w299,w4] L L) L) (N [w5,w0,w1,w2,w3,w1153] (N [w5,w0,w1,w2,w3,w4] L L) L)) (N [w5,w0,w1,w2,w3,w189] (N [w5,w0,w1,w2,w3,w134] (N [w5,w0,w1,w2,w3,w128] L L) L) (N [w5,w0,w1,w2,w3,w59] L L)))) (N [w539,w538,w1,w2,w3,w4] (N [w5,w0,w1,w133,w3,w4] (N [w5,w0,w1,w2,w123,w59] (N [w5,w0,w1,w2,w470,w125] (N [w5,w0,w1,w2,w3,w243] L L) L) (N [w5,w0,w1,w2,w60,w23] (N [w5,w0,w1,w2,w70,w29] L L) L)) (N [w541,w540,w1,w2,w3,w4] (N [w5,w1,w2,w3,w4,w188] (N [w5,w0,w1,w3,w4,w162] L L) L) (N [w541,w0,w1,w2,w3,w4] L L))) (N [w179,w0,w1,w2,w3,w4] (N [w183,w0,w1,w2,w28,w29] (N [w1202,w0,w1,w2,w3,w4] (N [w539,w0,w1,w2,w3,w4] L L) L) (N [w1204,w0,w1,w2,w3,w4] (N [w183,w0,w1,w2,w3,w4] L L) L)) (N [w533,w0,w1,w2,w3,w4] (N [w537,w0,w1,w2,w3,w140] (N [w537,w0,w1,w2,w3,w4] L L) L) (N [w535,w0,w1,w2,w3,w4] L L))))) (N [w1223,w0,w1,w2,w3,w4] (N [w494,w37,w0,w2,w3,w4] (N [w499,w0,w1,w2,w4,w21] (N [w499,w0,w1,w2,w28,w4] (N [w499,w14,w0,w1,w2,w4] (N [w499,w44,w0,w1,w2,w4] L L) L) (N [w499,w0,w1,w2,w500,w4] (N [w499,w0,w1,w2,w3,w4] L L) L)) (N [w1213,w0,w1,w2,w3,w4] (N [w1213,w16,w0,w1,w2,w3] (N [w1219,w0,w1,w2,w3,w4] L L) L) (N [w1210,w0,w1,w2,w3,w4] L L))) (N [w494,w0,w2,w19,w3,w4] (N [w494,w0,w22,w2,w3,w4] (N [w494,w16,w0,w22,w2,w3] (N [w494,w10,w0,w2,w3,w4] L L) L) (N [w494,w0,w495,w2,w3,w4] (N [w494,w0,w1,w2,w3,w4] L L) L)) (N [w1214,w16,w0,w1,w2,w3] (N [w1222,w0,w1,w2,w3,w4] (N [w494,w0,w2,w3,w4,w21] L L) L) (N [w1214,w0,w1,w2,w3,w4] L L)))) (N [w40,w0,w1,w2,w3,w100] (N [w40,w0,w18,w19,w3,w4] (N [w40,w44,w0,w1,w2,w29] (N [w1217,w0,w1,w2,w3,w4] (N [w1220,w0,w1,w2,w3,w4] L L) L) (N [w40,w16,w0,w1,w2,w60] (N [w40,w16,w0,w1,w2,w470] L L) L)) (N [w40,w0,w1,w2,w28,w29] (N [w40,w0,w98,w2,w3,w4] (N [w40,w0,w22,w2,w3,w169] L L) L) (N [w40,w0,w1,w2,w99,w4] L L))) (N [w40,w0,w1,w531,w3,w4] (N [w40,w0,w1,w2,w470,w4] (N [w40,w0,w1,w2,w3,w59] (N [w40,w0,w1,w2,w3,w4] L L) L) (N [w40,w0,w1,w2,w4,w60] (N [w40,w0,w1,w2,w4,w137] L L) L)) (N [w1224,w160,w0,w2,w3,w4] (N [w528,w0,w1,w2,w3,w4] (N [w40,w0,w1,w3,w4,w162] L L) L) (N [w1224,w44,w0,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRLL = true := by decide +kernel
def tbl_5_0LRRLR : STree := (N [w31,w12,w0,w98,w3,w4] (N [w1246,w132,w0,w2,w3,w4] (N [w525,w0,w1,w2,w3,w4] (N [w160,w0,w1,w2,w3,w4] (N [w1224,w0,w2,w3,w4] (N [w1224,w0,w2,w28,w3,w4] (N [w1224,w0,w1,w2,w3,w4] L L) L) (N [w160,w0,w1,w2,w28,w29] (N [w160,w44,w0,w1,w2,w29] L L) L)) (N [w155,w62,w0,w18,w3,w4] (N [w1228,w0,w1,w2,w3,w4] (N [w160,w0,w1,w3,w4,w162] L L) L) (N [w155,w0,w1,w2,w3,w4] (N [w155,w0,w18,w19,w3,w4] L L) L))) (N [w502,w0,w18,w2,w3,w4] (N [w502,w32,w0,w2,w3,w4] (N [w1230,w0,w1,w2,w3,w4] (N [w522,w0,w1,w2,w3,w4] L L) L) (N [w502,w12,w0,w18,w3,w4] (N [w502,w10,w0,w2,w3,w4] L L) L)) (N [w502,w0,w2,w3,w4,w21] (N [w502,w0,w503,w2,w3,w4] (N [w502,w0,w1,w2,w3,w4] L L) L) (N [w1237,w0,w1,w2,w3,w4] L L)))) (N [w505,w0,w1,w2,w3,w4] (N [w1246,w0,w2,w3,w4] (N [w1246,w16,w0,w2,w3,w4] (N [w1246,w12,w0,w2,w3,w4] (N [w1246,w131,w0,w2,w3,w4] L L) L) (N [w1246,w0,w26,w2,w3,w4] (N [w1246,w0,w1,w2,w3,w4] L L) L)) (N [w505,w14,w0,w1,w2,w4] (N [w505,w42,w0,w1,w2,w4] (N [w1233,w0,w1,w2,w3,w4] L L) L) (N [w505,w0,w1,w24,w2,w4] L L))) (N [w1245,w0,w1,w2,w3,w4] (N [w505,w0,w1,w2,w4,w29] (N [w505,w0,w1,w2,w4,w21] (N [w505,w0,w1,w2,w506,w4] L L) L) (N [w1242,w0,w1,w2,w3,w4] (N [w1239,w0,w1,w2,w3,w4] L L) L)) (N [w1235,w0,w1,w2,w3,w4] (N [w1235,w12,w0,w1,w3,w4] (N [w1240,w0,w1,w2,w3,w4] L L) L) (N [w1243,w0,w1,w2,w3,w4] L L))))) (N [w1247,w0,w1,w2,w3,w4] (N [w31,w0,w1,w2,w3,w516] (N [w31,w0,w1,w2,w28,w29] (N [w31,w0,w18,w19,w3,w4] (N [w31,w0,w18,w34,w3,w4] (N [w31,w12,w1,w3,w4,w48] L L) L) (N [w31,w0,w1,w97,w3,w4] (N [w31,w0,w98,w2,w3,w4] L L) L)) (N [w31,w0,w1,w2,w3,w4] (N [w31,w0,w1,w2,w153,w4] (N [w31,w0,w1,w2,w99,w4] L L) L) (N [w31,w0,w1,w2,w3,w128] L L))) (N [w1247,w132,w0,w1,w2,w4] (N [w31,w0,w2,w135,w3,w4] (N [w31,w0,w1,w2,w3,w140] (N [w31,w0,w1,w2,w3,w59] L L) L) (N [w518,w0,w1,w2,w3,w4] (N [w520,w0,w1,w2,w3,w4] L L) L)) (N [w1247,w16,w0,w1,w2,w4] (N [w1247,w12,w0,w1,w2,w4] (N [w1247,w131,w0,w1,w2,w4] L L) L) (N [w1247,w0,w1,w26,w2,w4] L L)))) (N [w1250,w0,w1,w2,w3,w4] (N [w512,w0,w1,w2,w3,w4] (N [w132,w0,w1,w2,w4,w514] (N [w132,w0,w1,w2,w3,w4] (N [w1247,w0,w1,w2,w4] L L) L) (N [w132,w0,w2,w515,w3,w4] (N [w132,w0,w1,w2,w4,w207] L L) L)) (N [w1250,w10,w0,w1,w2,w4] (N [w1250,w32,w0,w1,w2,w4] (N [w1250,w126,w0,w1,w2,w4] L L) L) (N [w1250,w0,w18,w1,w2,w4] L L))) (N [w129,w0,w1,w2,w3,w4] (N [w126,w0,w1,w2,w3,w4] (N [w126,w0,w18,w19,w3,w4] (N [w1250,w0,w1,w2,w4] L L) L) (N [w510,w0,w1,w2,w3,w4] (N [w126,w0,w1,w2,w3,w128] L L) L)) (N [w32,w0,w1,w2,w3,w128] (N [w32,w0,w1,w2,w3,w4] (N [w32,w0,w18,w19,w3,w4] L L) L) (N [w32,w0,w1,w33,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRLR = true := by decide +kernel
def tbl_5_0LRRL : STree := N [w1224,w14,w0,w2,w3,w4] tbl_5_0LRRLL tbl_5_0LRRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRRLL chk_tbl_5_0LRRLR
def tbl_5_0LRRRL : STree := (N [w10,w0,w1,w2,w99,w4] (N [w909,w0,w1,w2,w3,w4] (N [w35,w0,w2,w3,w4,w41] (N [w136,w0,w1,w2,w3,w4] (N [w1265,w0,w1,w2,w3,w4] (N [w1316,w0,w1,w2,w3,w4] (N [w1254,w0,w1,w2,w3,w4] L L) L) (N [w908,w0,w1,w2,w3,w4] (N [w1269,w0,w1,w2,w3,w4] L L) L)) (N [w35,w0,w1,w2,w3,w59] (N [w35,w0,w1,w2,w3,w134] (N [w35,w0,w1,w2,w3,w4] L L) L) (N [w35,w0,w1,w133,w3,w4] (N [w35,w0,w1,w2,w4,w36] L L) L))) (N [w1283,w0,w1,w2,w3,w4] (N [w1263,w0,w1,w2,w3,w4] (N [w1256,w0,w1,w2,w3,w4] (N [w1259,w0,w1,w2,w3,w4] L L) L) (N [w1257,w0,w1,w2,w3,w4] (N [w1333,w0,w1,w2,w3,w4] L L) L)) (N [w1286,w0,w1,w2,w3,w4] (N [w1267,w0,w1,w2,w3,w4] (N [w1267,w375,w0,w1,w2,w4] L L) L) (N [w1270,w0,w1,w2,w3,w4] L L)))) (N [w10,w0,w18,w121,w3,w4] (N [w10,w1258,w1,w2,w3,w4] (N [w10,w12,w0,w18,w3,w4] (N [w151,w0,w1,w2,w3,w4] (N [w147,w0,w1,w2,w3,w4] L L) L) (N [w10,w14,w2,w3,w4,w11] (N [w10,w1255,w1,w2,w3,w4] L L) L)) (N [w10,w91,w1,w2,w3,w4] (N [w10,w150,w1,w2,w3,w4] (N [w10,w375,w0,w1,w2,w4] L L) L) (N [w10,w0,w18,w2,w3,w4] L L))) (N [w10,w0,w86,w2,w3,w4] (N [w10,w0,w479,w2,w3,w4] (N [w10,w0,w18,w19,w3,w4] (N [w10,w0,w18,w33,w3,w4] L L) L) (N [w10,w0,w487,w2,w3,w4] (N [w10,w0,w381,w2,w3,w4] L L) L)) (N [w10,w0,w1,w97,w3,w4] (N [w10,w0,w98,w2,w3,w4] (N [w10,w0,w92,w2,w3,w4] L L) L) (N [w10,w0,w1,w2,w28,w29] L L))))) (N [w10,w0,w2,w34,w3,w4] (N [w10,w0,w1,w133,w3,w4] (N [w10,w0,w1,w2,w3,w128] (N [w10,w0,w1,w2,w3,w330] (N [w10,w0,w1,w2,w3,w4] (N [w10,w0,w1,w2,w153,w4] L L) L) (N [w10,w0,w1,w2,w3,w469] (N [w10,w0,w1,w2,w3,w751] L L) L)) (N [w10,w0,w1,w2,w3,w140] (N [w10,w0,w1,w2,w3,w59] (N [w10,w0,w1,w2,w3,w134] L L) L) (N [w10,w0,w1,w327,w3,w4] L L))) (N [w10,w0,w419,w2,w3,w4] (N [w10,w0,w342,w2,w3,w4] (N [w10,w0,w326,w2,w3,w4] (N [w10,w0,w335,w2,w3,w4] L L) L) (N [w10,w0,w415,w2,w3,w4] (N [w10,w0,w352,w2,w3,w4] L L) L)) (N [w10,w0,w97,w3,w4] (N [w10,w0,w97,w2,w3,w4] (N [w10,w0,w113,w2,w3,w4] L L) L) (N [w10,w0,w97,w3,w4,w11] L L)))) (N [w10,w357,w1,w2,w3,w4] (N [w10,w0,w2,w3,w751,w11] (N [w10,w0,w2,w3,w4,w48] (N [w10,w0,w2,w3,w4,w41] (N [w10,w0,w2,w99,w4,w11] L L) L) (N [w10,w0,w2,w3,w4,w428] (N [w10,w0,w2,w3,w4,w11] L L) L)) (N [w10,w340,w1,w2,w3,w4] (N [w10,w333,w1,w2,w3,w4] (N [w10,w0,w327,w3,w4,w11] L L) L) (N [w10,w424,w2,w3,w4,w11] L L))) (N [w10,w2,w3,w4,w11,w13] (N [w10,w1,w2,w3,w4,w48] (N [w10,w18,w2,w3,w4,w48] (N [w10,w103,w2,w3,w4,w11] L L) L) (N [w10,w2,w3,w4,w48] (N [w10,w2,w402,w3,w4,w11] L L) L)) (N [w773,w0,w1,w2,w3,w4] (N [w1345,w0,w1,w2,w3,w4] (N [w1287,w0,w1,w2,w3,w4] L L) L) (N [w1349,w0,w1,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRRL = true := by decide +kernel
def tbl_5_0LRRRR : STree := (N [w423,w0,w1,w2,w3,w4] (N [w371,w0,w1,w2,w3,w4] (N [w1363,w0,w1,w2,w3,w4] (N [w427,w0,w2,w3,w4,w11] (N [w427,w0,w18,w2,w3,w4] (N [w792,w0,w1,w2,w3,w4] (N [w1292,w0,w1,w2,w3,w4] L L) L) (N [w427,w0,w113,w2,w3,w4] (N [w427,w0,w1,w2,w3,w4] L L) L)) (N [w750,w0,w1,w2,w3,w4] (N [w749,w0,w1,w2,w3,w4] (N [w427,w0,w2,w3,w4,w428] L L) L) (N [w1361,w0,w1,w2,w3,w4] (N [w750,w0,w2,w3,w4,w11] L L) L))) (N [w1300,w0,w1,w2,w3,w4] (N [w380,w103,w1,w2,w3,w4] (N [w380,w0,w1,w2,w3,w4] (N [w380,w16,w1,w2,w3,w4] L L) L) (N [w1370,w0,w1,w2,w3,w4] (N [w793,w0,w1,w2,w3,w4] L L) L)) (N [w371,w0,w18,w2,w3,w4] (N [w371,w375,w0,w1,w2,w4] (N [w1301,w0,w1,w2,w3,w4] L L) L) (N [w371,w0,w22,w2,w3,w4] L L)))) (N [w1271,w0,w1,w2,w3,w4] (N [w878,w0,w1,w2,w3,w4] (N [w371,w0,w2,w3,w4,w372] (N [w371,w0,w2,w3,w4,w11] (N [w371,w0,w105,w2,w3,w4] L L) L) (N [w1305,w0,w1,w2,w3,w4] (N [w833,w0,w1,w2,w3,w4] L L) L)) (N [w1306,w0,w1,w2,w3,w4] (N [w367,w0,w1,w2,w3,w4] (N [w891,w0,w1,w2,w3,w4] L L) L) (N [w959,w0,w1,w2,w3,w4] L L))) (N [w434,w111,w1,w2,w3,w4] (N [w1056,w0,w1,w2,w3,w4] (N [w1374,w0,w1,w2,w3,w4] (N [w1273,w0,w1,w2,w3,w4] L L) L) (N [w434,w0,w1,w2,w3,w4] (N [w1376,w0,w1,w2,w3,w4] L L) L)) (N [w980,w0,w1,w2,w3,w4] (N [w434,w1,w2,w3,w4,w428] (N [w434,w1,w2,w3,w4,w11] L L) L) (N [w1027,w0,w1,w2,w3,w4] L L))))) (N [w44,w0,w1,w2,w29] (N [w62,w103,w1,w2,w3,w4] (N [w62,w0,w18,w1,w3,w4] (N [w156,w0,w1,w2,w3,w4] (N [w1110,w0,w1,w2,w3,w4] (N [w1383,w0,w1,w2,w3,w4] L L) L) (N [w62,w14,w1,w2,w3,w4] (N [w247,w0,w1,w2,w3,w4] L L) L)) (N [w62,w0,w1,w2,w3,w4] (N [w62,w0,w18,w3,w4] (N [w62,w0,w18,w19,w3,w4] L L) L) (N [w62,w0,w1,w402,w3,w4] L L))) (N [w44,w375,w0,w1,w2,w4] (N [w1303,w0,w1,w2,w3,w4] (N [w1007,w0,w1,w2,w3,w4] (N [w1388,w0,w1,w2,w3,w4] L L) L) (N [w44,w14,w0,w1,w2,w29] (N [w910,w0,w1,w2,w3,w4] L L) L)) (N [w44,w0,w1,w2,w3,w45] (N [w44,w0,w1,w2,w3,w4] (N [w44,w0,w1,w2,w28,w29] L L) L) (N [w44,w0,w1,w2,w3,w29] L L)))) (N [w14,w1274,w1,w2,w3,w4] (N [w1057,w0,w1,w2,w3,w4] (N [w1275,w0,w1,w2,w3,w4] (N [w1277,w0,w1,w2,w3,w4] (N [w44,w0,w1,w3,w4,w162] L L) L) (N [w1392,w0,w1,w2,w3,w4] (N [w1284,w0,w1,w2,w3,w4] L L) L)) (N [w14,w16,w0,w1,w2,w29] (N [w14,w375,w0,w1,w2,w4] (N [w174,w0,w1,w2,w3,w4] L L) L) (N [w14,w16,w1,w2,w3,w17] L L))) (N [w14,w0,w20,w1,w2,w4] (N [w14,w0,w363,w1,w2,w4] (N [w14,w177,w1,w2,w3,w4] (N [w14,w960,w0,w1,w2,w3] L L) L) (N [w14,w0,w18,w19,w3,w4] (N [w14,w0,w49,w1,w2,w4] L L) L)) (N [w14,w0,w481,w1,w2,w4] (N [w14,w0,w20,w2,w4,w41] (N [w14,w0,w20,w1,w2,w59] L L) L) (N [w14,w0,w383,w1,w2,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRRR = true := by decide +kernel
def tbl_5_0LRRR : STree := N [w1290,w0,w1,w2,w3,w4] tbl_5_0LRRRL tbl_5_0LRRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRRRL chk_tbl_5_0LRRRR
def tbl_5_0LRR : STree := N [w32,w1,w2,w3,w4,w48] tbl_5_0LRRL tbl_5_0LRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRRL chk_tbl_5_0LRRR
def tbl_5_0LR : STree := N [w5,w0,w92,w2,w3,w23] tbl_5_0LRL tbl_5_0LRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0LR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0LR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LRL chk_tbl_5_0LRR
def tbl_5_0L : STree := N [w110,w0,w1,w2,w28,w29] tbl_5_0LL tbl_5_0LR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0L : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0L = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0LL chk_tbl_5_0LR
def tbl_5_0RLLLL : STree := (N [w14,w0,w1,w133,w3,w4] (N [w14,w0,w1,w2,w418,w4] (N [w14,w0,w1,w2,w3,w4] (N [w14,w0,w1,w2,w64,w4] (N [w14,w0,w98,w2,w3,w4] (N [w14,w0,w92,w1,w2,w4] (N [w14,w0,w75,w1,w2,w4] L L) L) (N [w14,w0,w1,w433,w2,w4] (N [w14,w0,w1,w435,w2,w4] L L) L)) (N [w14,w0,w1,w2,w88,w4] (N [w14,w0,w1,w2,w490,w4] (N [w14,w0,w1,w2,w28,w29] L L) L) (N [w14,w0,w1,w2,w3,w100] (N [w14,w0,w1,w2,w99,w4] L L) L))) (N [w14,w0,w1,w2,w404,w4] (N [w14,w0,w1,w2,w3,w134] (N [w14,w0,w1,w2,w3,w469] (N [w14,w0,w1,w2,w3,w330] L L) L) (N [w14,w0,w1,w2,w344,w4] (N [w14,w0,w1,w2,w3,w59] L L) L)) (N [w14,w0,w1,w2,w420,w4] (N [w14,w0,w1,w2,w356,w4] (N [w14,w0,w1,w2,w329,w4] L L) L) (N [w14,w0,w1,w2,w410,w4] L L)))) (N [w14,w0,w1,w2,w4,w59] (N [w14,w0,w1,w2,w4,w46] (N [w14,w0,w1,w2,w470,w4] (N [w14,w0,w1,w2,w461,w4] (N [w14,w0,w1,w2,w115,w4] L L) L) (N [w14,w0,w1,w2,w4,w36] (N [w14,w0,w1,w2,w4,w469] L L) L)) (N [w14,w0,w1,w2,w4,w430] (N [w14,w0,w1,w2,w4,w15] (N [w14,w0,w1,w2,w4,w55] L L) L) (N [w14,w0,w1,w2,w4,w60] L L))) (N [w14,w0,w1,w2,w125,w29] (N [w14,w0,w1,w2,w4,w81] (N [w14,w0,w1,w2,w4,w444] (N [w14,w0,w1,w2,w4,w29] L L) L) (N [w14,w0,w1,w2,w469] (N [w14,w0,w1,w2,w338,w29] L L) L)) (N [w14,w0,w1,w2,w23,w29] (N [w14,w0,w1,w2,w59] (N [w14,w0,w1,w2,w501,w29] L L) L) (N [w14,w0,w1,w327,w3,w4] L L))))) (N [w429,w0,w1,w2,w4,w29] (N [w1399,w0,w1,w2,w3,w4] (N [w14,w103,w1,w2,w4,w15] (N [w14,w340,w1,w2,w3,w4] (N [w14,w401,w1,w2,w3,w4] (N [w14,w0,w1,w3,w4,w162] L L) L) (N [w14,w363,w1,w2,w4] (N [w14,w363,w1,w2,w3,w4] L L) L)) (N [w1294,w0,w1,w2,w3,w4] (N [w1397,w0,w1,w2,w3,w4] (N [w14,w369,w1,w2,w4,w15] L L) L) (N [w1289,w0,w1,w2,w3,w4] L L))) (N [w429,w0,w1,w24,w2,w4] (N [w1291,w0,w1,w2,w3,w4] (N [w1295,w0,w1,w2,w3,w4] (N [w981,w0,w1,w2,w3,w4] L L) L) (N [w429,w0,w20,w1,w2,w4] (N [w794,w0,w1,w2,w3,w4] L L) L)) (N [w429,w0,w1,w2,w4,w15] (N [w429,w0,w1,w2,w115,w4] (N [w429,w0,w1,w2,w3,w4] L L) L) (N [w429,w0,w1,w2,w4,w430] L L)))) (N [w441,w0,w1,w2,w3,w4] (N [w386,w103,w1,w2,w3,w4] (N [w1403,w0,w1,w2,w3,w4] (N [w752,w0,w1,w2,w3,w4] (N [w1298,w0,w1,w2,w3,w4] L L) L) (N [w386,w0,w1,w2,w4,w29] (N [w386,w0,w1,w2,w3,w4] L L) L)) (N [w1410,w0,w1,w2,w3,w4] (N [w774,w0,w1,w2,w4,w29] (N [w774,w0,w1,w2,w3,w4] L L) L) (N [w1412,w0,w1,w2,w3,w4] L L))) (N [w1417,w0,w1,w2,w3,w4] (N [w1029,w0,w1,w2,w3,w4] (N [w795,w0,w1,w2,w3,w4] (N [w441,w111,w1,w2,w3,w4] L L) L) (N [w426,w0,w1,w2,w3,w4] (N [w1008,w0,w1,w2,w3,w4] L L) L)) (N [w881,w0,w357,w1,w2,w4] (N [w1138,w0,w1,w2,w3,w4] (N [w1419,w0,w1,w2,w3,w4] L L) L) (N [w881,w0,w1,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLLL = true := by decide +kernel
def tbl_5_0RLLLR : STree := (N [w84,w1,w2,w3,w4,w11] (N [w375,w103,w1,w2,w4,w17] (N [w375,w0,w1,w2,w109,w4] (N [w375,w0,w20,w1,w2,w4] (N [w375,w0,w103,w1,w2,w4] (N [w375,w0,w363,w1,w2,w4] (N [w375,w368,w0,w1,w2,w4] L L) L) (N [w375,w0,w18,w1,w2,w4] (N [w375,w0,w394,w1,w2,w4] L L) L)) (N [w375,w0,w1,w2,w19,w4] (N [w375,w0,w1,w105,w2,w4] (N [w375,w0,w22,w1,w2,w4] L L) L) (N [w375,w0,w1,w2,w3,w4] (N [w375,w0,w1,w2,w28,w4] L L) L))) (N [w375,w0,w1,w2,w4,w21] (N [w375,w0,w1,w2,w4,w376] (N [w375,w0,w1,w2,w4,w15] (N [w375,w0,w1,w2,w4] L L) L) (N [w375,w0,w1,w2,w4,w1285] (N [w375,w0,w1,w2,w4,w17] L L) L)) (N [w375,w0,w1,w2,w4,w11] (N [w375,w0,w1,w2,w4,w29] (N [w375,w0,w1,w2,w4,w23] L L) L) (N [w375,w0,w1,w2,w4,w372] L L)))) (N [w835,w0,w1,w2,w4,w15] (N [w879,w0,w1,w2,w3,w4] (N [w1112,w0,w1,w26,w2,w4] (N [w1112,w0,w450,w1,w2,w4] (N [w834,w0,w1,w2,w3,w4] L L) L) (N [w1112,w0,w1,w2,w4] (N [w1112,w0,w1,w2,w3,w4] L L) L)) (N [w1111,w0,w1,w2,w3,w4] (N [w368,w0,w1,w2,w4,w29] (N [w368,w0,w1,w2,w3,w4] L L) L) (N [w835,w0,w1,w2,w3,w4] L L))) (N [w84,w0,w1,w2,w3,w4] (N [w309,w0,w1,w2,w3,w4] (N [w306,w0,w1,w2,w3,w4] (N [w303,w0,w1,w2,w3,w4] L L) L) (N [w84,w0,w20,w1,w2,w4] (N [w309,w0,w1,w2,w4,w60] L L) L)) (N [w84,w111,w1,w2,w3,w4] (N [w84,w0,w1,w2,w4,w29] (N [w84,w0,w1,w2,w425,w4] L L) L) (N [w84,w103,w1,w2,w3,w4] L L))))) (N [w317,w1,w2,w3,w4,w29] (N [w1440,w0,w1,w2,w3,w4] (N [w91,w0,w1,w2,w28,w29] (N [w1028,w0,w1,w2,w3,w4] (N [w1434,w0,w1,w2,w3,w4] (N [w1432,w0,w1,w2,w3,w4] L L) L) (N [w1058,w0,w1,w2,w3,w4] (N [w1296,w0,w1,w2,w3,w4] L L) L)) (N [w91,w1,w2,w3,w4,w15] (N [w91,w111,w1,w2,w3,w4] (N [w91,w0,w1,w2,w3,w4] L L) L) (N [w91,w1,w2,w3,w4,w81] L L))) (N [w258,w1,w2,w3,w4,w21] (N [w258,w0,w1,w2,w3,w4] (N [w1059,w0,w1,w2,w3,w4] (N [w1297,w0,w1,w2,w3,w4] L L) L) (N [w258,w1,w2,w3,w4] (N [w258,w1,w2,w19,w3,w4] L L) L)) (N [w317,w1,w2,w3,w4] (N [w317,w0,w1,w2,w3,w4] (N [w258,w1,w2,w3,w4,w65] L L) L) (N [w317,w1,w2,w3,w4,w21] L L)))) (N [w0,w787,w1,w2,w3,w4] (N [w0,w1023,w1,w2,w3,w4] (N [w0,w767,w1,w2,w3,w4] (N [w0,w719,w1,w2,w3,w4] (N [w317,w1,w2,w3,w4,w89] L L) L) (N [w0,w333,w1,w2,w3,w4] (N [w0,w333,w1,w2,w28,w29] L L) L)) (N [w0,w401,w18,w19,w3,w4] (N [w0,w974,w1,w2,w3,w4] (N [w0,w727,w1,w2,w3,w4] L L) L) (N [w0,w401,w1,w2,w3,w4] L L))) (N [w0,w414,w1,w2,w3,w4] (N [w0,w340,w1,w2,w3,w4] (N [w0,w790,w1,w2,w3,w4] (N [w0,w1003,w1,w2,w3,w4] L L) L) (N [w0,w816,w1,w2,w3,w140] (N [w0,w816,w1,w2,w3,w4] L L) L)) (N [w0,w1133,w1,w2,w3,w4] (N [w0,w821,w1,w2,w3,w4] (N [w0,w994,w1,w2,w3,w4] L L) L) (N [w0,w408,w1,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLLR = true := by decide +kernel
def tbl_5_0RLLL : STree := N [w881,w0,w1,w2,w4] tbl_5_0RLLLL tbl_5_0RLLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLLLL chk_tbl_5_0RLLLR
def tbl_5_0RLLRL : STree := (N [w0,w450,w1,w2,w3,w154] (N [w0,w892,w1,w2,w3,w4] (N [w0,w111,w1,w2,w3,w59] (N [w0,w111,w1,w2,w28,w29] (N [w0,w111,w18,w19,w3,w4] (N [w0,w1054,w1,w2,w3,w4] (N [w0,w825,w1,w2,w3,w4] L L) L) (N [w0,w111,w1,w97,w3,w4] (N [w0,w111,w98,w2,w3,w4] L L) L)) (N [w0,w111,w1,w2,w153,w4] (N [w0,w111,w1,w2,w1081,w4] (N [w0,w111,w1,w2,w99,w4] L L) L) (N [w0,w111,w1,w2,w3,w330] (N [w0,w111,w1,w2,w3,w4] L L) L))) (N [w0,w458,w98,w2,w3,w4] (N [w0,w1094,w1,w2,w3,w4] (N [w0,w111,w326,w2,w3,w4] (N [w0,w111,w1,w2,w3,w140] L L) L) (N [w0,w458,w18,w19,w3,w4] (N [w0,w1098,w1,w2,w3,w4] L L) L)) (N [w0,w911,w1,w2,w3,w4] (N [w0,w1304,w1,w2,w3,w4] (N [w0,w458,w1,w2,w3,w4] L L) L) (N [w0,w880,w1,w2,w3,w4] L L)))) (N [w0,w103,w1,w2,w28,w29] (N [w0,w904,w1,w2,w3,w4] (N [w0,w357,w1,w2,w3,w4] (N [w0,w874,w1,w2,w3,w4] (N [w0,w871,w1,w2,w3,w4] L L) L) (N [w0,w363,w1,w2,w3,w4] (N [w0,w902,w1,w2,w3,w4] L L) L)) (N [w0,w103,w98,w2,w3,w4] (N [w0,w103,w22,w2,w3,w23] (N [w0,w103,w18,w19,w3,w4] L L) L) (N [w0,w103,w934,w2,w3,w4] L L))) (N [w0,w103,w1,w2,w4,w60] (N [w0,w103,w1,w2,w3,w100] (N [w0,w103,w1,w2,w935,w4] (N [w0,w103,w1,w2,w99,w4] L L) L) (N [w0,w103,w1,w2,w3,w59] (N [w0,w103,w1,w2,w3,w4] L L) L)) (N [w0,w1016,w1,w2,w3,w4] (N [w0,w999,w1,w2,w3,w4] (N [w0,w1108,w1,w2,w3,w4] L L) L) (N [w0,w948,w1,w2,w3,w4] L L))))) (N [w0,w1309,w1,w2,w3,w4] (N [w0,w49,w1,w2,w3,w189] (N [w0,w394,w1,w2,w3,w4] (N [w0,w1149,w1,w2,w3,w4] (N [w0,w450,w1,w2,w4,w207] (N [w0,w450,w1,w2,w3,w4] L L) L) (N [w0,w394,w1,w2,w28,w29] (N [w0,w956,w1,w2,w3,w4] L L) L)) (N [w0,w49,w18,w19,w3,w4] (N [w0,w190,w1,w2,w3,w4] (N [w0,w1129,w1,w2,w3,w4] L L) L) (N [w0,w49,w1,w2,w3,w4] L L))) (N [w0,w1308,w1,w2,w3,w4] (N [w0,w49,w1,w2,w4,w50] (N [w0,w49,w1,w2,w123,w4] (N [w0,w49,w1,w2,w3,w59] L L) L) (N [w0,w1312,w1,w2,w3,w4] (N [w0,w1310,w1,w2,w3,w4] L L) L)) (N [w0,w1317,w1,w2,w3,w4] (N [w0,w1334,w1,w2,w3,w4] (N [w0,w1314,w1,w2,w3,w4] L L) L) (N [w0,w912,w1,w2,w3,w4] L L)))) (N [w0,w18,w75,w2,w3,w4] (N [w0,w18,w377,w19,w3,w4] (N [w0,w193,w1,w2,w3,w4] (N [w0,w1182,w1,w2,w3,w4] (N [w0,w1342,w1,w2,w3,w4] L L) L) (N [w0,w18,w477,w19,w3,w4] (N [w0,w196,w1,w2,w3,w4] L L) L)) (N [w0,w18,w20,w19,w3,w4] (N [w0,w18,w20,w2,w4,w21] (N [w0,w18,w982,w19,w3,w4] L L) L) (N [w0,w18,w442,w2,w3,w4] L L))) (N [w0,w18,w1,w2,w3,w4] (N [w0,w18,w1,w2,w28,w29] (N [w0,w18,w98,w2,w3,w4] (N [w0,w18,w92,w2,w3,w4] L L) L) (N [w0,w18,w1,w2,w99,w4] (N [w0,w18,w1,w2,w199,w4] L L) L)) (N [w0,w18,w1,w2,w3,w469] (N [w0,w18,w1,w2,w3,w763] (N [w0,w18,w1,w2,w3,w330] L L) L) (N [w0,w18,w1,w2,w3,w128] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLRL = true := by decide +kernel
def tbl_5_0RLLRR : STree := (N [w0,w1159,w1,w2,w3,w4] (N [w0,w18,w19,w382,w3,w4] (N [w0,w18,w1,w19,w3,w4] (N [w0,w18,w1,w472,w3,w4] (N [w0,w18,w1,w327,w3,w4] (N [w0,w18,w1,w337,w3,w4] (N [w0,w18,w1,w2,w3,w59] L L) L) (N [w0,w18,w1,w467,w3,w4] (N [w0,w18,w1,w348,w3,w4] L L) L)) (N [w0,w18,w1,w56,w3,w4] (N [w0,w18,w1,w359,w3,w4] (N [w0,w18,w1,w121,w3,w4] L L) L) (N [w0,w18,w1,w33,w3,w4] (N [w0,w18,w1,w34,w3,w4] L L) L))) (N [w0,w18,w105,w19,w3,w4] (N [w0,w18,w119,w121,w3,w4] (N [w0,w18,w1,w3,w4,w72] (N [w0,w18,w1,w480,w3,w4] L L) L) (N [w0,w18,w119,w480,w3,w4] (N [w0,w18,w119,w19,w3,w4] L L) L)) (N [w0,w18,w34,w3,w4] (N [w0,w18,w64,w19,w3,w4] (N [w0,w18,w113,w19,w3,w4] L L) L) (N [w0,w18,w19,w480,w3,w4] L L)))) (N [w0,w18,w19,w3,w4,w29] (N [w0,w18,w19,w3,w123,w4] (N [w0,w18,w19,w3,w109,w4] (N [w0,w18,w19,w3,w404,w4] (N [w0,w18,w19,w28,w3,w4] L L) L) (N [w0,w18,w19,w3,w461,w4] (N [w0,w18,w19,w3,w115,w4] L L) L)) (N [w0,w18,w19,w3,w4,w50] (N [w0,w18,w19,w3,w4,w15] (N [w0,w18,w19,w3,w4] L L) L) (N [w0,w18,w19,w3,w4,w21] L L))) (N [w0,w1346,w1,w2,w3,w4] (N [w0,w18,w19,w3,w4,w65] (N [w0,w18,w19,w3,w4,w11] (N [w0,w18,w19,w3,w4,w48] L L) L) (N [w0,w18,w480,w3,w4] (N [w0,w18,w19,w3,w4,w63] L L) L)) (N [w0,w1353,w1,w2,w3,w4] (N [w0,w1351,w1,w2,w3,w4] (N [w0,w775,w1,w2,w3,w4] L L) L) (N [w0,w836,w1,w2,w3,w4] L L))))) (N [w0,w963,w2,w398,w3,w4] (N [w0,w381,w105,w2,w3,w4] (N [w0,w477,w1,w2,w3,w4] (N [w0,w479,w2,w19,w3,w4] (N [w0,w479,w119,w2,w3,w4] (N [w0,w479,w1,w2,w3,w4] L L) L) (N [w0,w753,w1,w2,w3,w4] (N [w0,w479,w2,w480,w3,w4] L L) L)) (N [w0,w381,w22,w2,w3,w4] (N [w0,w1364,w1,w2,w3,w4] (N [w0,w1359,w1,w2,w3,w4] L L) L) (N [w0,w381,w1,w2,w3,w4] L L))) (N [w0,w862,w1,w2,w3,w4] (N [w0,w381,w2,w3,w4,w21] (N [w0,w381,w2,w382,w3,w4] (N [w0,w381,w2,w19,w3,w4] L L) L) (N [w0,w1368,w1,w2,w3,w4] (N [w0,w796,w1,w2,w3,w4] L L) L)) (N [w0,w1215,w1,w2,w3,w4] (N [w0,w377,w1,w2,w3,w4] (N [w0,w893,w1,w2,w3,w4] L L) L) (N [w0,w963,w1,w2,w3,w4] L L)))) (N [w0,w1321,w1,w2,w3,w4] (N [w0,w982,w19,w3,w4] (N [w0,w961,w1,w2,w3,w4] (N [w0,w963,w2,w3,w4] (N [w0,w963,w2,w28,w3,w4] L L) L) (N [w0,w982,w1,w19,w3,w4] (N [w0,w982,w1,w2,w3,w4] L L) L)) (N [w0,w58,w1,w2,w3,w59] (N [w0,w58,w1,w2,w3,w4] (N [w0,w58,w1,w2,w28,w29] L L) L) (N [w0,w1326,w1,w2,w3,w4] L L))) (N [w0,w213,w1,w2,w3,w4] (N [w0,w1344,w1,w2,w3,w4] (N [w0,w1323,w1,w2,w3,w4] (N [w0,w1393,w1,w2,w3,w4] L L) L) (N [w0,w1183,w1,w2,w3,w4] (N [w0,w1395,w1,w2,w3,w4] L L) L)) (N [w0,w223,w1,w2,w153,w4] (N [w0,w223,w98,w2,w3,w4] (N [w0,w218,w1,w2,w3,w4] L L) L) (N [w0,w223,w1,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLRR = true := by decide +kernel
def tbl_5_0RLLR : STree := N [w0,w18,w1,w2,w3,w189] tbl_5_0RLLRL tbl_5_0RLLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLLRL chk_tbl_5_0RLLRR
def tbl_5_0RLL : STree := N [w0,w1050,w1,w2,w3,w4] tbl_5_0RLLL tbl_5_0RLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLLL chk_tbl_5_0RLLR
def tbl_5_0RLRLL : STree := (N [w0,w20,w1,w327,w3,w4] (N [w0,w20,w1,w2,w3,w189] (N [w0,w20,w1,w2,w99,w4] (N [w0,w20,w1,w2,w1318,w4] (N [w0,w20,w221,w2,w3,w4] (N [w0,w20,w216,w2,w3,w4] (N [w0,w20,w1320,w2,w3,w4] L L) L) (N [w0,w20,w1,w97,w3,w4] (N [w0,w20,w98,w2,w3,w4] L L) L)) (N [w0,w20,w1,w2,w1322,w4] (N [w0,w20,w1,w2,w28,w29] (N [w0,w20,w1,w2,w1319,w3] L L) L) (N [w0,w20,w1,w2,w222,w4] (N [w0,w20,w1,w2,w80,w4] L L) L))) (N [w0,w20,w1,w2,w3,w751] (N [w0,w20,w1,w2,w3,w154] (N [w0,w20,w1,w2,w3,w100] (N [w0,w20,w1,w2,w153,w4] L L) L) (N [w0,w20,w1,w2,w3,w330] (N [w0,w20,w1,w2,w3,w4] L L) L)) (N [w0,w20,w1,w2,w3,w469] (N [w0,w20,w1,w2,w3,w1153] (N [w0,w20,w1,w2,w3,w1001] L L) L) (N [w0,w20,w1,w2,w3,w134] L L)))) (N [w0,w20,w1,w2,w470,w4] (N [w0,w20,w1,w2,w756,w4] (N [w0,w20,w1,w2,w350,w4] (N [w0,w20,w1,w2,w3,w140] (N [w0,w20,w1,w2,w3,w59] L L) L) (N [w0,w20,w1,w2,w329,w4] (N [w0,w20,w1,w2,w344,w4] L L) L)) (N [w0,w20,w1,w2,w474,w4] (N [w0,w20,w1,w2,w410,w4] (N [w0,w20,w1,w2,w362,w4] L L) L) (N [w0,w20,w1,w2,w1170,w4] L L))) (N [w0,w20,w1,w2,w4,w41] (N [w0,w20,w1,w2,w4,w36] (N [w0,w20,w1,w2,w123,w59] (N [w0,w20,w1,w2,w123,w4] L L) L) (N [w0,w20,w1,w2,w4,w60] (N [w0,w20,w1,w2,w4,w50] L L) L)) (N [w0,w20,w1,w2,w4,w207] (N [w0,w20,w1,w2,w4,w482] (N [w0,w20,w1,w2,w4,w21] L L) L) (N [w0,w20,w1,w2,w21,w59] L L))))) (N [w0,w837,w1,w2,w3,w4] (N [w0,w20,w2,w4,w41] (N [w0,w20,w105,w2,w4,w21] (N [w0,w20,w342,w2,w3,w4] (N [w0,w20,w326,w2,w3,w4] (N [w0,w20,w1,w133,w3,w4] L L) L) (N [w0,w20,w364,w2,w3,w4] (N [w0,w20,w346,w2,w3,w4] L L) L)) (N [w0,w20,w113,w2,w4,w21] (N [w0,w20,w415,w2,w3,w4] (N [w0,w20,w370,w2,w4,w21] L L) L) (N [w0,w20,w2,w3,w4,w41] L L))) (N [w0,w1347,w326,w2,w3,w4] (N [w0,w1398,w1,w2,w3,w4] (N [w0,w1396,w1,w2,w3,w4] (N [w0,w20,w2,w4,w21,w11] L L) L) (N [w0,w1347,w1,w2,w3,w4] (N [w0,w1355,w1,w2,w3,w4] L L) L)) (N [w0,w1356,w1,w2,w3,w4] (N [w0,w797,w1,w2,w3,w4] (N [w0,w1350,w1,w2,w3,w4] L L) L) (N [w0,w1352,w1,w2,w3,w4] L L)))) (N [w0,w1406,w1,w2,w3,w4] (N [w0,w1401,w1,w2,w3,w4] (N [w0,w481,w1,w2,w123,w4] (N [w0,w481,w1,w2,w3,w1184] (N [w0,w481,w1,w2,w3,w4] L L) L) (N [w0,w481,w1,w2,w4,w482] (N [w0,w481,w1,w2,w4,w21] L L) L)) (N [w0,w755,w1,w2,w3,w4] (N [w0,w754,w1,w2,w3,w4] (N [w0,w1401,w1,w2,w329,w4] L L) L) (N [w0,w1405,w1,w2,w3,w4] L L))) (N [w0,w383,w1,w2,w28,w4] (N [w0,w776,w1,w2,w3,w4] (N [w0,w387,w105,w2,w3,w4] (N [w0,w387,w1,w2,w3,w4] L L) L) (N [w0,w1362,w1,w2,w3,w4] (N [w0,w1360,w1,w2,w3,w4] L L) L)) (N [w0,w383,w1,w2,w4,w21] (N [w0,w383,w1,w2,w109,w4] (N [w0,w383,w1,w2,w3,w4] L L) L) (N [w0,w383,w1,w2,w4,w384] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRLL = true := by decide +kernel
def tbl_5_0RLRLR : STree := (N [w0,w308,w1,w2,w3,w4] (N [w0,w838,w1,w2,w3,w4] (N [w0,w1418,w1,w2,w3,w4] (N [w0,w378,w1,w2,w3,w59] (N [w0,w863,w1,w2,w3,w4] (N [w0,w1369,w1,w2,w3,w4] (N [w0,w799,w1,w2,w3,w4] L L) L) (N [w0,w378,w1,w2,w3,w4] (N [w0,w882,w1,w2,w3,w4] L L) L)) (N [w0,w442,w1,w2,w3,w4] (N [w0,w1413,w1,w2,w3,w4] (N [w0,w1408,w1,w2,w3,w4] L L) L) (N [w0,w798,w1,w2,w3,w4] (N [w0,w442,w113,w2,w3,w4] L L) L))) (N [w0,w487,w1,w2,w3,w4] (N [w0,w1421,w1,w2,w3,w4] (N [w0,w800,w1,w2,w4,w21] (N [w0,w800,w1,w2,w3,w4] L L) L) (N [w0,w1423,w1,w2,w470,w4] (N [w0,w1423,w1,w2,w3,w4] L L) L)) (N [w0,w487,w2,w3,w4,w482] (N [w0,w487,w2,w3,w4,w21] (N [w0,w487,w119,w2,w3,w4] L L) L) (N [w0,w1169,w1,w2,w3,w4] L L)))) (N [w0,w75,w1,w2,w3,w4] (N [w0,w1426,w1,w2,w3,w4] (N [w0,w478,w1,w2,w3,w59] (N [w0,w478,w1,w2,w3,w4] (N [w0,w1160,w1,w2,w3,w4] L L) L) (N [w0,w1216,w1,w2,w3,w4] (N [w0,w1425,w1,w2,w3,w4] L L) L)) (N [w0,w286,w1,w2,w3,w4] (N [w0,w284,w1,w2,w3,w4] (N [w0,w281,w1,w2,w3,w4] L L) L) (N [w0,w290,w1,w2,w3,w4] L L))) (N [w0,w1157,w1,w2,w3,w4] (N [w0,w75,w113,w2,w3,w4] (N [w0,w75,w105,w2,w3,w4] (N [w0,w75,w1,w2,w123,w4] L L) L) (N [w0,w1428,w1,w2,w3,w4] (N [w0,w75,w2,w3,w4,w11] L L) L)) (N [w0,w913,w1,w2,w3,w4] (N [w0,w1365,w1,w2,w3,w4] (N [w0,w1430,w1,w2,w3,w4] L L) L) (N [w0,w865,w1,w2,w3,w4] L L))))) (N [w0,w92,w113,w2,w3,w4] (N [w0,w1436,w1,w2,w3,w4] (N [w0,w86,w105,w2,w3,w4] (N [w0,w311,w1,w2,w3,w4] (N [w0,w310,w1,w2,w4,w207] (N [w0,w310,w1,w2,w3,w4] L L) L) (N [w0,w86,w119,w2,w3,w4] (N [w0,w86,w1,w2,w3,w4] L L) L)) (N [w0,w86,w2,w3,w4,w65] (N [w0,w86,w2,w3,w4,w21] (N [w0,w86,w2,w19,w3,w4] L L) L) (N [w0,w1433,w1,w2,w3,w4] L L))) (N [w0,w92,w1,w2,w3,w4] (N [w0,w1366,w1,w2,w3,w4] (N [w0,w1185,w1,w2,w3,w4] (N [w0,w1357,w1,w2,w3,w4] L L) L) (N [w0,w92,w1,w2,w28,w29] (N [w0,w914,w1,w2,w3,w4] L L) L)) (N [w0,w92,w1,w2,w3,w23] (N [w0,w92,w1,w2,w3,w59] (N [w0,w92,w1,w2,w3,w125] L L) L) (N [w0,w92,w119,w2,w3,w4] L L)))) (N [w0,w98,w1,w2,w3,w330] (N [w0,w1441,w1,w2,w3,w4] (N [w0,w92,w2,w3,w23] (N [w0,w92,w2,w3,w4,w89] (N [w0,w92,w2,w3,w4,w21] L L) L) (N [w0,w1438,w1,w2,w3,w4] (N [w0,w92,w2,w3,w23,w29] L L) L)) (N [w0,w98,w1,w2,w153,w4] (N [w0,w1186,w1,w2,w3,w4] (N [w0,w1358,w1,w2,w3,w4] L L) L) (N [w0,w98,w1,w2,w3,w4] L L))) (N [w0,w98,w113,w2,w3,w4] (N [w0,w98,w119,w2,w3,w4] (N [w0,w98,w326,w2,w3,w4] (N [w0,w98,w1,w121,w3,w4] L L) L) (N [w0,w98,w105,w2,w3,w4] (N [w0,w98,w915,w2,w3,w4] L L) L)) (N [w0,w98,w2,w402,w3,w4] (N [w0,w98,w2,w107,w3,w4] (N [w0,w98,w2,w121,w3,w4] L L) L) (N [w0,w98,w2,w504,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRLR = true := by decide +kernel
def tbl_5_0RLRL : STree := N [w0,w383,w1,w2,w4,w25] tbl_5_0RLRLL tbl_5_0RLRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLRLL chk_tbl_5_0RLRLR
def tbl_5_0RLRRL : STree := (N [w0,w301,w1,w2,w3,w4] (N [w0,w98,w2,w3,w4,w78] (N [w0,w98,w2,w3,w4] (N [w0,w98,w2,w3,w329,w4] (N [w0,w98,w2,w153,w3,w4] (N [w0,w98,w2,w28,w3,w4] (N [w0,w98,w2,w19,w3,w4] L L) L) (N [w0,w98,w2,w153,w4,w13] (N [w0,w98,w2,w153,w4] L L) L)) (N [w0,w98,w2,w3,w425,w4] (N [w0,w98,w2,w3,w115,w4] (N [w0,w98,w2,w3,w109,w4] L L) L) (N [w0,w98,w2,w3,w123,w4] (N [w0,w98,w2,w3,w1092,w4] L L) L))) (N [w0,w98,w2,w3,w4,w48] (N [w0,w98,w2,w3,w4,w21] (N [w0,w98,w2,w3,w4,w240] (N [w0,w98,w2,w3,w4,w15] L L) L) (N [w0,w98,w2,w3,w4,w29] (N [w0,w98,w2,w3,w4,w25] L L) L)) (N [w0,w98,w2,w3,w4,w1063] (N [w0,w98,w2,w3,w4,w13] (N [w0,w98,w2,w3,w4,w11] L L) L) (N [w0,w98,w2,w3,w4,w374] L L)))) (N [w0,w297,w1,w2,w3,w4] (N [w0,w934,w1,w2,w3,w4] (N [w0,w98,w2,w3,w330,w13] (N [w0,w98,w2,w3,w330] (N [w0,w98,w2,w3,w4,w63] L L) L) (N [w0,w98,w121,w3,w4,w13] (N [w0,w98,w121,w3,w4] L L) L)) (N [w0,w934,w2,w3,w4,w13] (N [w0,w934,w2,w3,w4] (N [w0,w934,w2,w107,w3,w4] L L) L) (N [w0,w934,w2,w3,w4,w374] L L))) (N [w0,w319,w1,w2,w3,w4] (N [w0,w297,w2,w3,w4,w25] (N [w0,w297,w2,w3,w4,w15] (N [w0,w297,w2,w3,w4] L L) L) (N [w0,w297,w2,w3,w4,w78] (N [w0,w297,w2,w3,w4,w13] L L) L)) (N [w0,w319,w2,w3,w4,w29] (N [w0,w319,w2,w3,w4,w25] (N [w0,w319,w2,w3,w4] L L) L) (N [w0,w319,w2,w3,w4,w94] L L))))) (N [w0,w1,w811,w2,w3,w4] (N [w0,w1,w1152,w2,w3,w4] (N [w0,w1,w715,w2,w3,w4] (N [w0,w301,w2,w3,w4,w29] (N [w0,w301,w2,w3,w4,w15] (N [w0,w301,w2,w3,w4] L L) L) (N [w0,w1,w721,w2,w3,w4] (N [w0,w301,w2,w3,w4,w81] L L) L)) (N [w0,w1,w335,w2,w28,w29] (N [w0,w1,w769,w2,w3,w4] (N [w0,w1,w771,w2,w3,w4] L L) L) (N [w0,w1,w335,w2,w3,w4] L L))) (N [w0,w1,w784,w2,w3,w4] (N [w0,w1,w326,w2,w153,w4] (N [w0,w1,w740,w2,w3,w4] (N [w0,w1,w734,w2,w3,w4] L L) L) (N [w0,w1,w326,w2,w3,w330] (N [w0,w1,w326,w2,w3,w4] L L) L)) (N [w0,w1,w818,w2,w3,w4] (N [w0,w1,w342,w2,w3,w4] (N [w0,w1,w791,w2,w3,w4] L L) L) (N [w0,w1,w818,w2,w3,w140] L L)))) (N [w0,w1,w1167,w2,w3,w4] (N [w0,w1,w849,w2,w3,w4] (N [w0,w1,w1155,w2,w3,w4] (N [w0,w1,w829,w2,w3,w4] (N [w0,w1,w827,w2,w3,w4] L L) L) (N [w0,w1,w346,w2,w3,w4] (N [w0,w1,w832,w2,w3,w4] L L) L)) (N [w0,w1,w845,w2,w3,w4] (N [w0,w1,w465,w2,w3,w469] (N [w0,w1,w465,w2,w3,w4] L L) L) (N [w0,w1,w852,w2,w3,w4] L L))) (N [w0,w1,w119,w2,w99,w4] (N [w0,w1,w856,w2,w3,w4] (N [w0,w1,w1177,w2,w3,w4] (N [w0,w1,w473,w2,w3,w4] L L) L) (N [w0,w1,w119,w2,w28,w29] (N [w0,w1,w1181,w2,w3,w4] L L) L)) (N [w0,w1,w119,w2,w3,w751] (N [w0,w1,w119,w2,w3,w4] (N [w0,w1,w119,w2,w153,w4] L L) L) (N [w0,w1,w119,w2,w3,w469] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRRL = true := by decide +kernel
def tbl_5_0RLRRR : STree := (N [w0,w1,w1060,w2,w3,w4] (N [w0,w1,w105,w2,w3,w100] (N [w0,w1,w352,w2,w3,w4] (N [w0,w1,w883,w2,w3,w4] (N [w0,w1,w119,w327,w3,w4] (N [w0,w1,w119,w2,w3,w140] (N [w0,w1,w119,w2,w3,w1184] L L) L) (N [w0,w1,w1205,w2,w3,w4] (N [w0,w1,w1203,w2,w3,w4] L L) L)) (N [w0,w1,w915,w2,w3,w4] (N [w0,w1,w1367,w2,w3,w4] (N [w0,w1,w894,w2,w3,w4] L L) L) (N [w0,w1,w861,w2,w3,w4] (N [w0,w1,w858,w2,w3,w4] L L) L))) (N [w0,w1,w906,w2,w3,w4] (N [w0,w1,w900,w2,w3,w4] (N [w0,w1,w360,w2,w3,w4] (N [w0,w1,w875,w2,w3,w4] L L) L) (N [w0,w1,w907,w2,w3,w4] (N [w0,w1,w364,w2,w3,w4] L L) L)) (N [w0,w1,w105,w2,w153,w4] (N [w0,w1,w105,w2,w99,w4] (N [w0,w1,w105,w2,w28,w29] L L) L) (N [w0,w1,w105,w2,w935,w4] L L)))) (N [w0,w1,w1211,w2,w3,w4] (N [w0,w1,w105,w2,w4,w207] (N [w0,w1,w105,w2,w3,w59] (N [w0,w1,w105,w2,w3,w4] (N [w0,w1,w105,w2,w3,w154] L L) L) (N [w0,w1,w105,w2,w4,w60] (N [w0,w1,w105,w2,w3,w140] L L) L)) (N [w0,w1,w943,w2,w3,w4] (N [w0,w1,w943,w2,w3,w154] (N [w0,w1,w1209,w2,w3,w4] L L) L) (N [w0,w1,w950,w2,w3,w4] L L))) (N [w0,w1,w396,w2,w28,w29] (N [w0,w1,w495,w2,w3,w4] (N [w0,w1,w495,w2,w3,w100] (N [w0,w1,w952,w2,w3,w4] L L) L) (N [w0,w1,w958,w2,w3,w4] (N [w0,w1,w954,w2,w3,w4] L L) L)) (N [w0,w1,w1372,w2,w3,w4] (N [w0,w1,w1226,w2,w3,w4] (N [w0,w1,w396,w2,w3,w4] L L) L) (N [w0,w1,w1375,w2,w3,w4] L L))))) (N [w0,w1,w1381,w2,w3,w4] (N [w0,w1,w1114,w2,w3,w4] (N [w0,w1,w435,w2,w4,w436] (N [w0,w1,w435,w2,w3,w4] (N [w0,w1,w1379,w2,w3,w4] (N [w0,w1,w1378,w2,w3,w4] L L) L) (N [w0,w1,w435,w2,w4,w21] (N [w0,w1,w435,w2,w115,w4] L L) L)) (N [w0,w1,w1382,w2,w3,w4] (N [w0,w1,w983,w2,w3,w4] (N [w0,w1,w435,w2,w4,w29] L L) L) (N [w0,w1,w1114,w452,w2,w4] L L))) (N [w0,w1,w1113,w2,w3,w4] (N [w0,w1,w1031,w2,w3,w4] (N [w0,w1,w1040,w2,w3,w4] (N [w0,w1,w1114,w2,w4] L L) L) (N [w0,w1,w433,w2,w3,w59] (N [w0,w1,w433,w2,w3,w4] L L) L)) (N [w0,w1,w1061,w2,w3,w4] (N [w0,w1,w1380,w2,w3,w4] (N [w0,w1,w1236,w2,w3,w4] L L) L) (N [w0,w1,w1030,w2,w3,w4] L L)))) (N [w0,w1,w113,w2,w99,w4] (N [w0,w1,w415,w2,w4,w29] (N [w0,w1,w1019,w2,w3,w4] (N [w0,w1,w1039,w2,w3,w4] (N [w0,w1,w1062,w2,w3,w4] L L) L) (N [w0,w1,w415,w2,w3,w4] (N [w0,w1,w1024,w2,w3,w4] L L) L)) (N [w0,w1,w1055,w2,w3,w4] (N [w0,w1,w1047,w2,w3,w4] (N [w0,w1,w419,w2,w3,w4] L L) L) (N [w0,w1,w113,w2,w28,w29] L L))) (N [w0,w1,w1096,w2,w3,w4] (N [w0,w1,w113,w2,w3,w4] (N [w0,w1,w113,w2,w153,w4] (N [w0,w1,w113,w2,w1081,w4] L L) L) (N [w0,w1,w113,w2,w3,w140] (N [w0,w1,w113,w2,w3,w59] L L) L)) (N [w0,w1,w503,w2,w3,w4] (N [w0,w1,w1102,w2,w3,w4] (N [w0,w1,w1232,w2,w3,w4] L L) L) (N [w0,w1,w1105,w2,w3,w4] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRRR = true := by decide +kernel
def tbl_5_0RLRR : STree := N [w0,w1,w119,w2,w3,w59] tbl_5_0RLRRL tbl_5_0RLRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLRRL chk_tbl_5_0RLRRR
def tbl_5_0RLR : STree := N [w0,w98,w2,w33,w3,w4] tbl_5_0RLRL tbl_5_0RLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLRL chk_tbl_5_0RLRR
def tbl_5_0RL : STree := N [w0,w20,w22,w2,w3,w23] tbl_5_0RLL tbl_5_0RLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RLL chk_tbl_5_0RLR
def tbl_5_0RRLLL : STree := (N [w0,w1,w2,w19,w262,w4] (N [w0,w1,w2,w252,w3,w4] (N [w0,w1,w2,w64,w123,w4] (N [w0,w1,w2,w248,w3,w4] (N [w0,w1,w1248,w2,w3,w4] (N [w0,w1,w452,w2,w4,w207] (N [w0,w1,w452,w2,w3,w4] L L) L) (N [w0,w1,w2,w245,w3,w4] (N [w0,w1,w1131,w2,w3,w4] L L) L)) (N [w0,w1,w2,w64,w3,w4] (N [w0,w1,w2,w64,w28,w4] (N [w0,w1,w2,w249,w3,w4] L L) L) (N [w0,w1,w2,w64,w109,w4] (N [w0,w1,w2,w64,w3,w243] L L) L))) (N [w0,w1,w2,w916,w3,w4] (N [w0,w1,w2,w1386,w3,w4] (N [w0,w1,w2,w64,w4,w65] (N [w0,w1,w2,w64,w4,w21] L L) L) (N [w0,w1,w2,w1384,w3,w4] (N [w0,w1,w2,w1389,w3,w4] L L) L)) (N [w0,w1,w2,w1187,w3,w4] (N [w0,w1,w2,w1385,w3,w4] (N [w0,w1,w2,w1009,w3,w4] L L) L) (N [w0,w1,w2,w139,w3,w4] L L)))) (N [w0,w1,w2,w1189,w3,w4] (N [w0,w1,w2,w1329,w3,w4] (N [w0,w1,w2,w135,w3,w4] (N [w0,w1,w2,w206,w3,w4] (N [w0,w1,w2,w204,w3,w4] L L) L) (N [w0,w1,w2,w57,w3,w140] (N [w0,w1,w2,w57,w3,w4] L L) L)) (N [w0,w1,w2,w918,w3,w4] (N [w0,w1,w2,w1332,w3,w4] (N [w0,w1,w2,w1325,w3,w4] L L) L) (N [w0,w1,w2,w1338,w3,w4] L L))) (N [w0,w1,w2,w920,w3,w4] (N [w0,w1,w2,w1262,w3,w4] (N [w0,w1,w2,w34,w3,w4] (N [w0,w1,w2,w254,w3,w4] L L) L) (N [w0,w1,w2,w228,w3,w4] (N [w0,w1,w2,w1266,w3,w4] L L) L)) (N [w0,w1,w2,w19,w99,w4] (N [w0,w1,w2,w19,w28,w29] (N [w0,w1,w2,w237,w3,w4] L L) L) (N [w0,w1,w2,w19,w260,w4] L L))))) (N [w0,w1,w2,w28,w99,w4] (N [w0,w1,w2,w480,w3,w4] (N [w0,w1,w2,w19,w3,w59] (N [w0,w1,w2,w19,w3,w725] (N [w0,w1,w2,w19,w3,w730] (N [w0,w1,w2,w19,w3,w4] L L) L) (N [w0,w1,w2,w19,w3,w469] (N [w0,w1,w2,w19,w3,w330] L L) L)) (N [w0,w1,w2,w840,w3,w4] (N [w0,w1,w2,w778,w3,w4] (N [w0,w1,w2,w19,w3,w243] L L) L) (N [w0,w1,w2,w1162,w3,w4] L L))) (N [w0,w1,w2,w266,w99,w4] (N [w0,w1,w2,w382,w3,w4] (N [w0,w1,w2,w896,w3,w4] (N [w0,w1,w2,w867,w3,w4] L L) L) (N [w0,w1,w2,w965,w3,w4] (N [w0,w1,w2,w1218,w3,w4] L L) L)) (N [w0,w1,w2,w28,w440,w29] (N [w0,w1,w2,w28,w779,w29] (N [w0,w1,w2,w266,w3,w4] L L) L) (N [w0,w1,w2,w28,w486,w29] L L)))) (N [w0,w1,w2,w28,w123,w29] (N [w0,w1,w2,w28,w3,w45] (N [w0,w1,w2,w28,w3,w330] (N [w0,w1,w2,w28,w3,w406] (N [w0,w1,w2,w28,w3,w4] L L) L) (N [w0,w1,w2,w28,w3,w469] (N [w0,w1,w2,w28,w3,w417] L L) L)) (N [w0,w1,w2,w28,w109,w29] (N [w0,w1,w2,w28,w3,w29] (N [w0,w1,w2,w28,w3,w59] L L) L) (N [w0,w1,w2,w28,w115,w29] L L))) (N [w0,w1,w2,w28,w29,w491] (N [w0,w1,w2,w28,w70,w29] (N [w0,w1,w2,w28,w15,w29] (N [w0,w1,w2,w28,w69,w29] L L) L) (N [w0,w1,w2,w28,w29] (N [w0,w1,w2,w28,w21,w29] L L) L)) (N [w0,w1,w2,w28,w29,w89] (N [w0,w1,w2,w28,w29,w11] (N [w0,w1,w2,w28,w29,w444] L L) L) (N [w0,w1,w2,w28,w29,w81] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLLL = true := by decide +kernel
def tbl_5_0RRLLR : STree := (N [w0,w1,w2,w1414,w3,w4] (N [w0,w1,w2,w490,w3,w29] (N [w0,w1,w2,w443,w4,w29] (N [w0,w1,w2,w779,w3,w29] (N [w0,w1,w2,w1402,w3,w330] (N [w0,w1,w2,w1402,w3,w4] (N [w0,w1,w2,w984,w3,w4] L L) L) (N [w0,w1,w2,w779,w3,w4] (N [w0,w1,w2,w757,w3,w4] L L) L)) (N [w0,w1,w2,w1411,w3,w4] (N [w0,w1,w2,w1409,w3,w4] (N [w0,w1,w2,w779,w29] L L) L) (N [w0,w1,w2,w443,w115,w4] (N [w0,w1,w2,w443,w3,w4] L L) L))) (N [w0,w1,w2,w440,w3,w4] (N [w0,w1,w2,w1420,w3,w4] (N [w0,w1,w2,w801,w3,w4] (N [w0,w1,w2,w443,w4,w444] L L) L) (N [w0,w1,w2,w1010,w3,w4] (N [w0,w1,w2,w1042,w3,w4] L L) L)) (N [w0,w1,w2,w490,w3,w4] (N [w0,w1,w2,w1422,w3,w4] (N [w0,w1,w2,w1140,w3,w4] L L) L) (N [w0,w1,w2,w490,w3,w469] L L)))) (N [w0,w1,w2,w486,w29] (N [w0,w1,w2,w841,w3,w4] (N [w0,w1,w2,w490,w4,w491] (N [w0,w1,w2,w490,w4,w29] (N [w0,w1,w2,w490,w123,w4] L L) L) (N [w0,w1,w2,w490,w29] (N [w0,w1,w2,w490,w125,w29] L L) L)) (N [w0,w1,w2,w486,w3,w4] (N [w0,w1,w2,w1171,w3,w4] (N [w0,w1,w2,w1427,w3,w4] L L) L) (N [w0,w1,w2,w486,w3,w29] L L))) (N [w0,w1,w2,w80,w4,w15] (N [w0,w1,w2,w291,w3,w4] (N [w0,w1,w2,w285,w3,w4] (N [w0,w1,w2,w1238,w3,w4] L L) L) (N [w0,w1,w2,w80,w115,w4] (N [w0,w1,w2,w80,w3,w4] L L) L)) (N [w0,w1,w2,w1431,w3,w4] (N [w0,w1,w2,w80,w4,w81] (N [w0,w1,w2,w80,w4,w29] L L) L) (N [w0,w1,w2,w868,w3,w4] L L))))) (N [w0,w1,w2,w99,w3,w751] (N [w0,w1,w2,w88,w4,w89] (N [w0,w1,w2,w88,w3,w29] (N [w0,w1,w2,w312,w3,w4] (N [w0,w1,w2,w305,w3,w4] (N [w0,w1,w2,w1064,w3,w4] L L) L) (N [w0,w1,w2,w88,w3,w59] (N [w0,w1,w2,w88,w3,w4] L L) L)) (N [w0,w1,w2,w88,w4,w21] (N [w0,w1,w2,w88,w123,w4] (N [w0,w1,w2,w88,w115,w4] L L) L) (N [w0,w1,w2,w88,w4,w29] L L))) (N [w0,w1,w2,w199,w3,w4] (N [w0,w1,w2,w1435,w3,w4] (N [w0,w1,w2,w88,w29] (N [w0,w1,w2,w88,w23,w29] L L) L) (N [w0,w1,w2,w884,w3,w4] (N [w0,w1,w2,w1437,w3,w4] L L) L)) (N [w0,w1,w2,w99,w3,w100] (N [w0,w1,w2,w199,w4,w48] (N [w0,w1,w2,w199,w4] L L) L) (N [w0,w1,w2,w99,w3,w4] L L)))) (N [w0,w1,w2,w99,w4,w751] (N [w0,w1,w2,w99,w425,w4] (N [w0,w1,w2,w99,w109,w4] (N [w0,w1,w2,w99,w921,w4] (N [w0,w1,w2,w99,w756,w4] L L) L) (N [w0,w1,w2,w99,w115,w4] (N [w0,w1,w2,w99,w1066,w4] L L) L)) (N [w0,w1,w2,w99,w100,w11] (N [w0,w1,w2,w99,w100] (N [w0,w1,w2,w99,w123,w4] L L) L) (N [w0,w1,w2,w99,w4] L L))) (N [w0,w1,w2,w99,w4,w55] (N [w0,w1,w2,w99,w4,w117] (N [w0,w1,w2,w99,w4,w946] (N [w0,w1,w2,w99,w4,w338] L L) L) (N [w0,w1,w2,w99,w4,w125] (N [w0,w1,w2,w99,w4,w439] L L) L)) (N [w0,w1,w2,w99,w4,w41] (N [w0,w1,w2,w99,w4,w17] (N [w0,w1,w2,w99,w4,w15] L L) L) (N [w0,w1,w2,w99,w4,w21] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLLR = true := by decide +kernel
def tbl_5_0RRLL : STree := N [w0,w1,w2,w1400,w3,w4] tbl_5_0RRLLL tbl_5_0RRLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRLLL chk_tbl_5_0RRLLR
def tbl_5_0RRLRL : STree := (N [w0,w1,w2,w3,w854,w4] (N [w0,w1,w2,w1081,w4] (N [w0,w1,w2,w99,w4,w101] (N [w0,w1,w2,w99,w4,w11] (N [w0,w1,w2,w99,w4,w27] (N [w0,w1,w2,w99,w4,w23] (N [w0,w1,w2,w99,w4,w25] L L) L) (N [w0,w1,w2,w99,w4,w29] (N [w0,w1,w2,w99,w4,w279] L L) L)) (N [w0,w1,w2,w99,w4,w76] (N [w0,w1,w2,w99,w4,w372] (N [w0,w1,w2,w99,w4,w428] L L) L) (N [w0,w1,w2,w99,w4,w922] (N [w0,w1,w2,w99,w4,w13] L L) L))) (N [w0,w1,w2,w299,w4,w17] (N [w0,w1,w2,w99,w751,w11] (N [w0,w1,w2,w99,w751] (N [w0,w1,w2,w99,w4,w63] L L) L) (N [w0,w1,w2,w299,w4] (N [w0,w1,w2,w299,w3,w4] L L) L)) (N [w0,w1,w2,w299,w4,w101] (N [w0,w1,w2,w299,w4,w11] (N [w0,w1,w2,w299,w4,w23] L L) L) (N [w0,w1,w2,w1081,w3,w4] L L)))) (N [w0,w1,w2,w935,w3,w4] (N [w0,w1,w2,w260,w4,w67] (N [w0,w1,w2,w260,w3,w4] (N [w0,w1,w2,w1081,w4,w428] (N [w0,w1,w2,w1081,w4,w11] L L) L) (N [w0,w1,w2,w260,w4,w23] (N [w0,w1,w2,w260,w4] L L) L)) (N [w0,w1,w2,w262,w4,w11] (N [w0,w1,w2,w262,w4] (N [w0,w1,w2,w262,w3,w4] L L) L) (N [w0,w1,w2,w262,w4,w63] L L))) (N [w0,w1,w2,w3,w831,w4] (N [w0,w1,w2,w935,w4,w372] (N [w0,w1,w2,w935,w4,w11] (N [w0,w1,w2,w935,w4] L L) L) (N [w0,w1,w2,w3,w737,w4] (N [w0,w1,w2,w3,w729,w4] L L) L)) (N [w0,w1,w2,w3,w789,w4] (N [w0,w1,w2,w3,w786,w4] (N [w0,w1,w2,w3,w350,w4] L L) L) (N [w0,w1,w2,w3,w344,w4] L L))))) (N [w0,w1,w2,w3,w903,w4] (N [w0,w1,w2,w3,w847,w4] (N [w0,w1,w2,w3,w996,w4] (N [w0,w1,w2,w3,w979,w4] (N [w0,w1,w2,w3,w724,w4] (N [w0,w1,w2,w3,w823,w4] L L) L) (N [w0,w1,w2,w3,w404,w4] (N [w0,w1,w2,w3,w976,w4] L L) L)) (N [w0,w1,w2,w3,w329,w4] (N [w0,w1,w2,w3,w746,w4] (N [w0,w1,w2,w3,w747,w4] L L) L) (N [w0,w1,w2,w3,w329,w330] L L))) (N [w0,w1,w2,w3,w873,w4] (N [w0,w1,w2,w3,w762,w4] (N [w0,w1,w2,w3,w990,w4] (N [w0,w1,w2,w3,w813,w4] L L) L) (N [w0,w1,w2,w3,w921,w4] (N [w0,w1,w2,w3,w1407,w4] L L) L)) (N [w0,w1,w2,w3,w356,w4] (N [w0,w1,w2,w3,w362,w4] (N [w0,w1,w2,w3,w860,w4] L L) L) (N [w0,w1,w2,w3,w901,w4] L L)))) (N [w0,w1,w2,w3,w420,w4] (N [w0,w1,w2,w3,w1065,w4] (N [w0,w1,w2,w3,w1000,w4] (N [w0,w1,w2,w3,w109,w59] (N [w0,w1,w2,w3,w109,w4] L L) L) (N [w0,w1,w2,w3,w1415,w4] (N [w0,w1,w2,w3,w945,w4] L L) L)) (N [w0,w1,w2,w3,w1006,w4] (N [w0,w1,w2,w3,w1041,w4] (N [w0,w1,w2,w3,w1032,w4] L L) L) (N [w0,w1,w2,w3,w1025,w4] L L))) (N [w0,w1,w2,w3,w418,w4] (N [w0,w1,w2,w3,w1005,w4] (N [w0,w1,w2,w3,w1066,w4] (N [w0,w1,w2,w3,w1416,w4] L L) L) (N [w0,w1,w2,w3,w1053,w4] (N [w0,w1,w2,w3,w410,w4] L L) L)) (N [w0,w1,w2,w3,w115,w4] (N [w0,w1,w2,w3,w1052,w4] (N [w0,w1,w2,w3,w1049,w4] L L) L) (N [w0,w1,w2,w3,w115,w59] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLRL = true := by decide +kernel
def tbl_5_0RRLRR : STree := (N [w0,w1,w2,w3,w4,w924] (N [w0,w1,w2,w3,w123,w469] (N [w0,w1,w2,w3,w1424,w4] (N [w0,w1,w2,w3,w455,w4] (N [w0,w1,w2,w3,w1091,w4] (N [w0,w1,w2,w3,w1100,w4] (N [w0,w1,w2,w3,w1104,w4] L L) L) (N [w0,w1,w2,w3,w1018,w4] (N [w0,w1,w2,w3,w1107,w4] L L) L)) (N [w0,w1,w2,w3,w461,w4] (N [w0,w1,w2,w3,w1136,w4] (N [w0,w1,w2,w3,w1137,w4] L L) L) (N [w0,w1,w2,w3,w1158,w4] (N [w0,w1,w2,w3,w1150,w4] L L) L))) (N [w0,w1,w2,w3,w1180,w4] (N [w0,w1,w2,w3,w1168,w4] (N [w0,w1,w2,w3,w1166,w4] (N [w0,w1,w2,w3,w1190,w4] L L) L) (N [w0,w1,w2,w3,w474,w4] (N [w0,w1,w2,w3,w1156,w4] L L) L)) (N [w0,w1,w2,w3,w1179,w4] (N [w0,w1,w2,w3,w470,w125] (N [w0,w1,w2,w3,w470,w4] L L) L) (N [w0,w1,w2,w3,w123,w4] L L)))) (N [w0,w1,w2,w3,w4] (N [w0,w1,w2,w3,w1231,w4] (N [w0,w1,w2,w3,w1229,w4] (N [w0,w1,w2,w3,w1207,w4] (N [w0,w1,w2,w3,w123,w59] L L) L) (N [w0,w1,w2,w3,w500,w4] (N [w0,w1,w2,w3,w1212,w4] L L) L)) (N [w0,w1,w2,w3,w1249,w4] (N [w0,w1,w2,w3,w506,w4] (N [w0,w1,w2,w3,w1234,w4] L L) L) (N [w0,w1,w2,w3,w1252,w4] L L))) (N [w0,w1,w2,w3,w4,w127] (N [w0,w1,w2,w3,w4,w69] (N [w0,w1,w2,w3,w4,w202] (N [w0,w1,w2,w3,w4,w142] L L) L) (N [w0,w1,w2,w3,w4,w1068] (N [w0,w1,w2,w3,w4,w1390] L L) L)) (N [w0,w1,w2,w3,w4,w1268] (N [w0,w1,w2,w3,w4,w36] (N [w0,w1,w2,w3,w4,w137] L L) L) (N [w0,w1,w2,w3,w4,w1264] L L))))) (N [w0,w1,w2,w3,w4,w886] (N [w0,w1,w2,w3,w4,w55] (N [w0,w1,w2,w3,w4,w46] (N [w0,w1,w2,w3,w4,w1070] (N [w0,w1,w2,w3,w4,w1260] (N [w0,w1,w2,w3,w4,w1272] L L) L) (N [w0,w1,w2,w3,w4,w292] (N [w0,w1,w2,w3,w4,w166] L L) L)) (N [w0,w1,w2,w3,w4,w1072] (N [w0,w1,w2,w3,w4,w1278] (N [w0,w1,w2,w3,w4,w1282] L L) L) (N [w0,w1,w2,w3,w4,w188] L L))) (N [w0,w1,w2,w3,w4,w1330] (N [w0,w1,w2,w3,w4,w1371] (N [w0,w1,w2,w3,w4,w272] (N [w0,w1,w2,w3,w4,w1328] L L) L) (N [w0,w1,w2,w3,w4,w244] (N [w0,w1,w2,w3,w4,w157] L L) L)) (N [w0,w1,w2,w3,w4,w15] (N [w0,w1,w2,w3,w4,w182] (N [w0,w1,w2,w3,w4,w926] L L) L) (N [w0,w1,w2,w3,w4,w803] L L)))) (N [w0,w1,w2,w3,w4,w191] (N [w0,w1,w2,w3,w4,w1034] (N [w0,w1,w2,w3,w4,w1335] (N [w0,w1,w2,w3,w4,w986] (N [w0,w1,w2,w3,w4,w376] L L) L) (N [w0,w1,w2,w3,w4,w1012] (N [w0,w1,w2,w3,w4,w1074] L L) L)) (N [w0,w1,w2,w3,w4,w1142] (N [w0,w1,w2,w3,w4,w1118] (N [w0,w1,w2,w3,w4,w430] L L) L) (N [w0,w1,w2,w3,w4,w192] L L))) (N [w0,w1,w2,w3,w4,w1192] (N [w0,w1,w2,w3,w4,w1315] (N [w0,w1,w2,w3,w4,w50] (N [w0,w1,w2,w3,w4,w164] L L) L) (N [w0,w1,w2,w3,w4,w1311] (N [w0,w1,w2,w3,w4,w928] L L) L)) (N [w0,w1,w2,w3,w4,w1391] (N [w0,w1,w2,w3,w4,w70] (N [w0,w1,w2,w3,w4,w161] L L) L) (N [w0,w1,w2,w3,w4,w1076] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLRR = true := by decide +kernel
def tbl_5_0RRLR : STree := N [w0,w1,w2,w3,w115,w140] tbl_5_0RRLRL tbl_5_0RRLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRLRL chk_tbl_5_0RRLRR
def tbl_5_0RRL : STree := N [w0,w1,w2,w99,w4,w277] tbl_5_0RRLL tbl_5_0RRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRLL chk_tbl_5_0RRLR
def tbl_5_0RRRLL : STree := (N [w0,w1,w2,w3,w4,w761] (N [w0,w1,w2,w3,w4,w229] (N [w0,w1,w2,w3,w4,w41] (N [w0,w1,w2,w3,w4,w1373] (N [w0,w1,w2,w3,w4,w60] (N [w0,w1,w2,w3,w4,w313] (N [w0,w1,w2,w3,w4,w1194] L L) L) (N [w0,w1,w2,w3,w4,w1337] (N [w0,w1,w2,w3,w4,w1340] L L) L)) (N [w0,w1,w2,w3,w4,w1196] (N [w0,w1,w2,w3,w4,w1327] (N [w0,w1,w2,w3,w4,w1078] L L) L) (N [w0,w1,w2,w3,w4,w240] (N [w0,w1,w2,w3,w4,w314] L L) L))) (N [w0,w1,w2,w3,w4,w273] (N [w0,w1,w2,w3,w4,w1276] (N [w0,w1,w2,w3,w4,w269] (N [w0,w1,w2,w3,w4,w1279] L L) L) (N [w0,w1,w2,w3,w4,w1080] (N [w0,w1,w2,w3,w4,w1280] L L) L)) (N [w0,w1,w2,w3,w4,w930] (N [w0,w1,w2,w3,w4,w1285] (N [w0,w1,w2,w3,w4,w278] L L) L) (N [w0,w1,w2,w3,w4,w233] L L)))) (N [w0,w1,w2,w3,w4,w1121] (N [w0,w1,w2,w3,w4,w384] (N [w0,w1,w2,w3,w4,w843] (N [w0,w1,w2,w3,w4,w805] (N [w0,w1,w2,w3,w4,w21] L L) L) (N [w0,w1,w2,w3,w4,w888] (N [w0,w1,w2,w3,w4,w870] L L) L)) (N [w0,w1,w2,w3,w4,w1036] (N [w0,w1,w2,w3,w4,w1044] (N [w0,w1,w2,w3,w4,w759] L L) L) (N [w0,w1,w2,w3,w4,w436] L L))) (N [w0,w1,w2,w3,w4,w320] (N [w0,w1,w2,w3,w4,w482] (N [w0,w1,w2,w3,w4,w1165] (N [w0,w1,w2,w3,w4,w1173] L L) L) (N [w0,w1,w2,w3,w4,w1241] (N [w0,w1,w2,w3,w4,w1221] L L) L)) (N [w0,w1,w2,w3,w4,w29] (N [w0,w1,w2,w3,w4,w246] (N [w0,w1,w2,w3,w4,w280] L L) L) (N [w0,w1,w2,w3,w4,w988] L L))))) (N [w0,w1,w2,w3,w4,w149] (N [w0,w1,w2,w3,w4,w932] (N [w0,w1,w2,w3,w4,w1244] (N [w0,w1,w2,w3,w4,w1046] (N [w0,w1,w2,w3,w4,w491] (N [w0,w1,w2,w3,w4,w1175] L L) L) (N [w0,w1,w2,w3,w4,w444] (N [w0,w1,w2,w3,w4,w1014] L L) L)) (N [w0,w1,w2,w3,w4,w1313] (N [w0,w1,w2,w3,w4,w48] (N [w0,w1,w2,w3,w4,w1145] L L) L) (N [w0,w1,w2,w3,w4,w232] L L))) (N [w0,w1,w2,w3,w4,w781] (N [w0,w1,w2,w3,w4,w184] (N [w0,w1,w2,w3,w4,w181] (N [w0,w1,w2,w3,w4,w194] L L) L) (N [w0,w1,w2,w3,w4,w11] (N [w0,w1,w2,w3,w4,w235] L L) L)) (N [w0,w1,w2,w3,w4,w1038] (N [w0,w1,w2,w3,w4,w807] (N [w0,w1,w2,w3,w4,w267] L L) L) (N [w0,w1,w2,w3,w4,w428] L L)))) (N [w0,w1,w2,w3,w4,w251] (N [w0,w1,w2,w3,w4,w215] (N [w0,w1,w2,w3,w4,w898] (N [w0,w1,w2,w3,w4,w225] (N [w0,w1,w2,w3,w4,w890] L L) L) (N [w0,w1,w2,w3,w4,w176] (N [w0,w1,w2,w3,w4,w372] L L) L)) (N [w0,w1,w2,w3,w4,w1126] (N [w0,w1,w2,w3,w4,w937] (N [w0,w1,w2,w3,w4,w76] L L) L) (N [w0,w1,w2,w3,w4,w1084] L L))) (N [w0,w1,w2,w3,w4,w63] (N [w0,w1,w2,w3,w4,w65] (N [w0,w1,w2,w3,w4,w220] (N [w0,w1,w2,w3,w4,w167] L L) L) (N [w0,w1,w2,w3,w4,w1198] (N [w0,w1,w2,w3,w4,w939] L L) L)) (N [w0,w1,w2,w3,w4,w970] (N [w0,w1,w2,w3,w4,w253] (N [w0,w1,w2,w3,w4,w941] L L) L) (N [w0,w1,w2,w3,w4,w197] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRLL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRLL = true := by decide +kernel
def tbl_5_0RRRLR : STree := (N [w0,w1,w2,w3,w330,w78] (N [w0,w1,w2,w3,w725,w11] (N [w0,w1,w2,w3,w738,w15] (N [w0,w1,w2,w3,w4,w293] (N [w0,w1,w2,w3,w4,w1200] (N [w0,w1,w2,w3,w4,w1086] (N [w0,w1,w2,w3,w4,w89] L L) L) (N [w0,w1,w2,w3,w4,w1088] (N [w0,w1,w2,w3,w4,w81] L L) L)) (N [w0,w1,w2,w3,w730,w21] (N [w0,w1,w2,w3,w730] (N [w0,w1,w2,w3,w4,w255] L L) L) (N [w0,w1,w2,w3,w738] (N [w0,w1,w2,w3,w730,w65] L L) L))) (N [w0,w1,w2,w3,w717,w81] (N [w0,w1,w2,w3,w738,w78] (N [w0,w1,w2,w3,w738,w13] (N [w0,w1,w2,w3,w738,w25] L L) L) (N [w0,w1,w2,w3,w717,w29] (N [w0,w1,w2,w3,w717,w17] L L) L)) (N [w0,w1,w2,w3,w723,w94] (N [w0,w1,w2,w3,w723,w29] (N [w0,w1,w2,w3,w723,w27] L L) L) (N [w0,w1,w2,w3,w725] L L)))) (N [w0,w1,w2,w3,w330,w432] (N [w0,w1,w2,w3,w741] (N [w0,w1,w2,w3,w406,w67] (N [w0,w1,w2,w3,w406,w23] (N [w0,w1,w2,w3,w725,w63] L L) L) (N [w0,w1,w2,w3,w748,w13] (N [w0,w1,w2,w3,w748] L L) L)) (N [w0,w1,w2,w3,w330,w15] (N [w0,w1,w2,w3,w330] (N [w0,w1,w2,w3,w741,w13] L L) L) (N [w0,w1,w2,w3,w330,w17] L L))) (N [w0,w1,w2,w3,w330,w739] (N [w0,w1,w2,w3,w330,w23] (N [w0,w1,w2,w3,w330,w25] (N [w0,w1,w2,w3,w330,w21] L L) L) (N [w0,w1,w2,w3,w330,w27] (N [w0,w1,w2,w3,w330,w1348] L L) L)) (N [w0,w1,w2,w3,w330,w11] (N [w0,w1,w2,w3,w330,w761] (N [w0,w1,w2,w3,w330,w29] L L) L) (N [w0,w1,w2,w3,w330,w13] L L))))) (N [w0,w1,w2,w3,w819,w140] (N [w0,w1,w2,w3,w1001] (N [w0,w1,w2,w3,w772,w29] (N [w0,w1,w2,w3,w763] (N [w0,w1,w2,w3,w330,w63] (N [w0,w1,w2,w3,w330,w241] L L) L) (N [w0,w1,w2,w3,w770,w29] (N [w0,w1,w2,w3,w763,w48] L L) L)) (N [w0,w1,w2,w3,w338,w29] (N [w0,w1,w2,w3,w338,w59] (N [w0,w1,w2,w3,w338,w45] L L) L) (N [w0,w1,w2,w3,w422,w27] L L))) (N [w0,w1,w2,w3,w117,w52] (N [w0,w1,w2,w3,w417,w23] (N [w0,w1,w2,w3,w412,w29] (N [w0,w1,w2,w3,w412,w27] L L) L) (N [w0,w1,w2,w3,w117,w144] (N [w0,w1,w2,w3,w417,w27] L L) L)) (N [w0,w1,w2,w3,w117,w171] (N [w0,w1,w2,w3,w117,w140] (N [w0,w1,w2,w3,w117,w59] L L) L) (N [w0,w1,w2,w3,w117,w27] L L)))) (N [w0,w1,w2,w3,w469,w1164] (N [w0,w1,w2,w3,w469,w125] (N [w0,w1,w2,w3,w476,w17] (N [w0,w1,w2,w3,w1153] (N [w0,w1,w2,w3,w463,w52] L L) L) (N [w0,w1,w2,w3,w469] (N [w0,w1,w2,w3,w476,w29] L L) L)) (N [w0,w1,w2,w3,w469,w21] (N [w0,w1,w2,w3,w469,w17] (N [w0,w1,w2,w3,w469,w15] L L) L) (N [w0,w1,w2,w3,w469,w23] L L))) (N [w0,w1,w2,w3,w125,w289] (N [w0,w1,w2,w3,w469,w81] (N [w0,w1,w2,w3,w469,w11] (N [w0,w1,w2,w3,w469,w29] L L) L) (N [w0,w1,w2,w3,w125,w45] (N [w0,w1,w2,w3,w125,w38] L L) L)) (N [w0,w1,w2,w3,w125,w59] (N [w0,w1,w2,w3,w125,w60] (N [w0,w1,w2,w3,w125,w17] L L) L) (N [w0,w1,w2,w3,w125,w29] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRLR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRLR = true := by decide +kernel
def tbl_5_0RRRL : STree := N [w0,w1,w2,w3,w4,w152] tbl_5_0RRRLL tbl_5_0RRRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRRLL chk_tbl_5_0RRRLR
def tbl_5_0RRRRL : STree := (N [w0,w1,w2,w123,w125,w29] (N [w0,w1,w2,w3,w59,w782] (N [w0,w1,w2,w3,w17,w59] (N [w0,w1,w2,w3,w128] (N [w0,w1,w2,w3,w509,w144] (N [w0,w1,w2,w3,w501,w29] (N [w0,w1,w2,w3,w501,w45] L L) L) (N [w0,w1,w2,w3,w15,w59] (N [w0,w1,w2,w3,w55,w59] L L) L)) (N [w0,w1,w2,w3,w38,w29] (N [w0,w1,w2,w3,w38,w27] (N [w0,w1,w2,w3,w134] L L) L) (N [w0,w1,w2,w3,w17,w52] (N [w0,w1,w2,w3,w45,w23] L L) L))) (N [w0,w1,w2,w3,w52,w29] (N [w0,w1,w2,w3,w21,w59] (N [w0,w1,w2,w3,w60,w23] (N [w0,w1,w2,w3,w70,w29] L L) L) (N [w0,w1,w2,w3,w189] (N [w0,w1,w2,w3,w21,w140] L L) L)) (N [w0,w1,w2,w3,w59,w1201] (N [w0,w1,w2,w3,w59,w1089] (N [w0,w1,w2,w3,w59] L L) L) (N [w0,w1,w2,w3,w59,w23] L L)))) (N [w0,w1,w2,w3,w23,w808] (N [w0,w1,w2,w3,w59,w214] (N [w0,w1,w2,w3,w59,w808] (N [w0,w1,w2,w3,w59,w29] (N [w0,w1,w2,w3,w59,w27] L L) L) (N [w0,w1,w2,w3,w59,w13] (N [w0,w1,w2,w3,w59,w11] L L) L)) (N [w0,w1,w2,w3,w169,w29] (N [w0,w1,w2,w3,w1184] (N [w0,w1,w2,w3,w59,w219] L L) L) (N [w0,w1,w2,w3,w23,w29] L L))) (N [w0,w1,w2,w329,w330] (N [w0,w1,w2,w3,w243] (N [w0,w1,w2,w3,w484,w29] (N [w0,w1,w2,w3,w782,w29] L L) L) (N [w0,w1,w2,w344,w27,w29] (N [w0,w1,w2,w3,w29,w67] L L) L)) (N [w0,w1,w2,w109,w23,w29] (N [w0,w1,w2,w109,w338,w29] (N [w0,w1,w2,w329,w330,w13] L L) L) (N [w0,w1,w2,w470,w125] L L))))) (N [w0,w1,w735,w3,w4,w101] (N [w0,w1,w716,w3,w4] (N [w0,w1,w2,w21,w27,w29] (N [w0,w1,w2,w70,w29] (N [w0,w1,w2,w123,w23,w29] (N [w0,w1,w2,w123,w59] L L) L) (N [w0,w1,w2,w21,w23,w29] (N [w0,w1,w2,w60,w23] L L) L)) (N [w0,w1,w722,w3,w4,w29] (N [w0,w1,w722,w3,w4,w21] (N [w0,w1,w722,w3,w4] L L) L) (N [w0,w1,w722,w3,w4,w89] L L))) (N [w0,w1,w337,w3,w27,w29] (N [w0,w1,w716,w3,w4,w81] (N [w0,w1,w716,w3,w4,w29] (N [w0,w1,w716,w3,w4,w15] L L) L) (N [w0,w1,w337,w3,w4,w94] (N [w0,w1,w337,w3,w4,w25] L L) L)) (N [w0,w1,w735,w3,w4,w23] (N [w0,w1,w735,w3,w4,w17] (N [w0,w1,w735,w3,w4] L L) L) (N [w0,w1,w735,w3,w4,w11] L L)))) (N [w0,w1,w327,w3,w4,w15] (N [w0,w1,w327,w99,w3,w4] (N [w0,w1,w327,w19,w3,w4] (N [w0,w1,w744,w3,w4,w11] (N [w0,w1,w744,w3,w4] L L) L) (N [w0,w1,w327,w28,w3,w4] (N [w0,w1,w327,w480,w3,w4] L L) L)) (N [w0,w1,w327,w3,w756,w4] (N [w0,w1,w327,w99,w4,w11] (N [w0,w1,w327,w99,w4] L L) L) (N [w0,w1,w327,w3,w4] L L))) (N [w0,w1,w327,w3,w4,w76] (N [w0,w1,w327,w3,w4,w1444] (N [w0,w1,w327,w3,w4,w25] (N [w0,w1,w327,w3,w4,w21] L L) L) (N [w0,w1,w327,w3,w4,w11] (N [w0,w1,w327,w3,w4,w29] L L) L)) (N [w0,w1,w327,w3,w4,w63] (N [w0,w1,w327,w3,w4,w1063] (N [w0,w1,w327,w3,w4,w13] L L) L) (N [w0,w1,w327,w3,w751] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRRL : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRRL = true := by decide +kernel
def tbl_5_0RRRRR : STree := (N [w0,w1,w3,w4,w72,w13] (N [w0,w1,w107,w3,w117,w27] (N [w0,w1,w121,w3,w4,w43] (N [w0,w1,w348,w3,w4,w241] (N [w0,w1,w728,w3,w4,w67] (N [w0,w1,w728,w3,w4,w27] (N [w0,w1,w728,w19,w3,w4] L L) L) (N [w0,w1,w348,w3,w4,w13] (N [w0,w1,w348,w3,w4,w27] L L) L)) (N [w0,w1,w121,w33,w3,w4] (N [w0,w1,w472,w3,w4,w13] (N [w0,w1,w467,w3,w4,w13] L L) L) (N [w0,w1,w121,w153,w4,w13] L L))) (N [w0,w1,w366,w3,w4,w27] (N [w0,w1,w121,w3,w330,w13] (N [w0,w1,w121,w3,w4,w13] (N [w0,w1,w121,w3,w4,w48] L L) L) (N [w0,w1,w359,w3,w4,w27] (N [w0,w1,w354,w3,w4,w27] L L) L)) (N [w0,w1,w107,w3,w4,w171] (N [w0,w1,w107,w3,w4,w72] (N [w0,w1,w107,w209,w3,w4] L L) L) (N [w0,w1,w107,w3,w4,w27] L L)))) (N [w0,w1,w402,w33,w3,w4] (N [w0,w1,w972,w19,w3,w4] (N [w0,w1,w398,w3,w4,w72] (N [w0,w1,w498,w3,w4,w171] (N [w0,w1,w107,w3,w27,w29] L L) L) (N [w0,w1,w1021,w3,w4] (N [w0,w1,w1021,w28,w3,w4] L L) L)) (N [w0,w1,w402,w56,w3,w4] (N [w0,w1,w978,w19,w3,w4] (N [w0,w1,w972,w3,w4,w27] L L) L) (N [w0,w1,w402,w34,w3,w4] L L))) (N [w0,w1,w56,w3,w4,w13] (N [w0,w1,w504,w33,w3,w4] (N [w0,w1,w402,w3,w4,w72] (N [w0,w1,w402,w19,w3,w4] L L) L) (N [w0,w1,w133,w3,w4] (N [w0,w1,w992,w209,w3,w4] L L) L)) (N [w0,w1,w28,w3,w4,w162] (N [w0,w1,w19,w3,w4,w43] (N [w0,w1,w33,w3,w4,w25] L L) L) (N [w0,w1,w3,w4,w162] L L))))) (N [w111,w1,w2,w153,w4,w13] (N [w727,w1,w2,w3,w4] (N [w719,w1,w2,w3,w4,w29] (N [w0,w113,w402,w19,w3,w4] (N [w0,w326,w121,w3,w4,w13] (N [w0,w1,w3,w4,w43,w27] L L) L) (N [w719,w1,w2,w3,w4,w25] (N [w719,w1,w2,w3,w4] L L) L)) (N [w333,w1,w2,w3,w4,w81] (N [w333,w1,w2,w3,w4,w15] (N [w719,w1,w2,w3,w4,w94] L L) L) (N [w727,w1,w2,w19,w3,w4] L L))) (N [w340,w1,w2,w3,w4,w13] (N [w401,w1,w2,w3,w4,w11] (N [w727,w1,w2,w3,w4,w67] (N [w727,w1,w2,w3,w4,w23] L L) L) (N [w340,w1,w2,w3,w4,w17] (N [w401,w1,w2,w3,w4,w63] L L) L)) (N [w408,w1,w2,w3,w4,w13] (N [w414,w1,w2,w3,w4,w13] (N [w340,w1,w2,w3,w4,w241] L L) L) (N [w111,w98,w2,w3,w4,w13] L L)))) (N [w103,w1,w2,w3,w4,w289] (N [w111,w326,w2,w3,w4,w13] (N [w111,w1,w2,w3,w4,w13] (N [w111,w1,w2,w3,w4,w48] (N [w111,w1,w2,w3,w4,w288] L L) L) (N [w111,w1,w121,w3,w4,w13] (N [w111,w1,w2,w3,w330,w13] L L) L)) (N [w363,w1,w2,w3,w4,w17] (N [w357,w1,w2,w3,w4,w17] (N [w458,w1,w2,w3,w4,w48] L L) L) (N [w103,w1,w2,w3,w4,w69] L L))) (N [w18,w1,w2,w3,w4,w188] (N [w450,w1,w2,w3,w4,w211] (N [w103,w1,w2,w3,w125,w17] (N [w103,w1,w2,w3,w4,w17] L L) L) (N [w49,w1,w2,w3,w4,w188] (N [w394,w1,w2,w3,w4,w69] L L) L)) (N [w1,w2,w3,w4,w55,w13] (N [w1,w2,w3,w4,w188] (N [w20,w1,w2,w3,w4,w188] L L) L) (N [w1,w2,w3,w4,w15,w48] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRRR = true := by decide +kernel
def tbl_5_0RRRR : STree := N [w0,w1,w327,w3,w751,w11] tbl_5_0RRRRL tbl_5_0RRRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRRRL chk_tbl_5_0RRRRR
def tbl_5_0RRR : STree := N [w0,w1,w2,w3,w125,w81] tbl_5_0RRRL tbl_5_0RRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RRR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRRL chk_tbl_5_0RRRR
def tbl_5_0RR : STree := N [w0,w1,w2,w3,w4,w1394] tbl_5_0RRL tbl_5_0RRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0RR : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0RR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RRL chk_tbl_5_0RRR
def tbl_5_0R : STree := N [w0,w1,w1109,w2,w3,w4] tbl_5_0RL tbl_5_0RR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0R : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0R = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0RL chk_tbl_5_0RR
def tbl_5_0 : STree := N [w14,w0,w442,w1,w2,w4] tbl_5_0L tbl_5_0R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_0 : checkSTree aut12.fn aut34.fn 4 0 tbl_4_0 tbl_4_0 tbl_5_0 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_0L chk_tbl_5_0R
lemma nolive_5_0 : ∀ v, MemSTree v tbl_5_0 → ∀ m ≤ 5, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 4 0 tbl_5_0 tbl_4_0 tbl_4_0 nolive_4_0 nolive_4_0 chk_tbl_5_0
def tbl_5_1L : STree := (N [w0,w18,w254,w3,w4] (N [w84,w0,w92,w2,w4] (N [w62,w1,w2,w262,w4] (N [w10,w97,w3,w4,w48] (N [w10,w0,w97,w3,w4] (N [w10,w14,w97,w3,w4] (N [w32,w19,w3,w4,w48] L L) (N [w10,w0,w97,w99,w4] L L)) (N [w10,w1,w97,w99,w4] (N [w10,w0,w2,w99,w100] L L) (N [w10,w1,w2,w99,w100] L L))) (N [w62,w14,w18,w3,w4] (N [w10,w2,w153,w4,w11] (N [w10,w2,w199,w4,w48] L L) (N [w10,w2,w3,w4,w48] L L)) (N [w62,w18,w3,w4,w48] (N [w62,w0,w18,w3,w4] L L) (N [w62,w1,w2,w99,w4] L L)))) (N [w14,w0,w1,w2,w189] (N [w14,w16,w1,w2,w81] (N [w44,w0,w1,w162,w29] (N [w44,w0,w1,w2,w29] L L) (N [w174,w0,w1,w2,w29] L L)) (N [w14,w0,w92,w2,w23] (N [w14,w177,w1,w2,w29] L L) (N [w14,w0,w301,w2,w4] L L))) (N [w14,w0,w1,w43,w140] (N [w14,w0,w1,w2,w243] (N [w14,w0,w1,w2,w59] L L) (N [w14,w0,w1,w162,w29] L L)) (N [w306,w0,w1,w2,w29] (N [w14,w1,w2,w4,w188] L L) (N [w306,w2,w3,w4,w11] L L))))) (N [w258,w86,w2,w3,w4] (N [w84,w2,w3,w4,w169] (N [w84,w1,w296,w3,w4] (N [w84,w20,w2,w4,w11] (N [w84,w0,w1,w2,w59] L L) (N [w84,w1,w97,w3,w4] L L)) (N [w84,w1,w2,w3,w298] (N [w84,w1,w2,w3,w100] L L) (N [w84,w2,w34,w3,w4] L L))) (N [w691,w1,w2,w3,w4] (N [w91,w1,w2,w28,w81] (N [w91,w301,w2,w3,w4] L L) (N [w91,w1,w2,w3,w38] L L)) (N [w697,w1,w2,w4,w207] (N [w697,w1,w2,w3,w4] L L) (N [w258,w18,w19,w3,w4] L L)))) (N [w317,w1,w2,w28,w29] (N [w258,w1,w2,w4,w29] (N [w258,w1,w2,w3,w259] (N [w258,w1,w2,w64,w4] L L) (N [w258,w1,w2,w3,w4] L L)) (N [w317,w92,w2,w3,w4] (N [w702,w1,w2,w3,w4] L L) (N [w317,w1,w318,w3,w4] L L))) (N [w0,w18,w1,w72,w29] (N [w317,w1,w2,w3,w4] (N [w317,w1,w2,w88,w4] L L) (N [w711,w1,w2,w3,w4] L L)) (N [w0,w18,w64,w4,w65] (N [w0,w18,w1,w207,w27] L L) (N [w0,w18,w252,w3,w4] L L)))))) (N [w0,w92,w2,w28,w89] (N [w0,w20,w97,w4,w21] (N [w0,w18,w19,w260,w4] (N [w0,w18,w237,w3,w4] (N [w0,w18,w34,w3,w4] (N [w0,w18,w526,w3,w4] L L) (N [w0,w18,w228,w3,w4] L L)) (N [w0,w18,w19,w199,w4] (N [w0,w18,w19,w28,w29] L L) (N [w0,w18,w19,w99,w4] L L))) (N [w0,w18,w19,w3,w189] (N [w0,w18,w19,w3,w4] (N [w0,w18,w19,w262,w4] L L) (N [w0,w18,w19,w3,w128] L L)) (N [w0,w18,w19,w3,w243] (N [w0,w18,w19,w3,w59] L L) (N [w0,w18,w3,w4,w251] L L)))) (N [w0,w310,w2,w4,w21] (N [w0,w75,w97,w3,w4] (N [w0,w20,w2,w4,w41] (N [w0,w20,w2,w100,w21] L L) (N [w0,w20,w2,w41,w59] L L)) (N [w0,w75,w2,w3,w100] (N [w0,w75,w296,w3,w4] L L) (N [w0,w75,w2,w3,w298] L L))) (N [w0,w86,w2,w4,w36] (N [w0,w311,w19,w3,w4] (N [w0,w310,w2,w4,w220] L L) (N [w0,w86,w2,w3,w259] L L)) (N [w0,w86,w33,w3,w4] (N [w0,w86,w2,w4,w60] L L) (N [w0,w92,w318,w3,w4] L L))))) (N [w0,w98,w2,w262,w4] (N [w0,w672,w2,w3,w4] (N [w0,w92,w2,w3,w23] (N [w0,w92,w2,w3,w52] (N [w0,w92,w2,w3,w38] L L) (N [w0,w92,w2,w3,w169] L L)) (N [w0,w92,w2,w60,w23] (N [w0,w92,w2,w70,w29] L L) (N [w0,w668,w2,w3,w4] L L))) (N [w0,w98,w2,w99,w4] (N [w0,w98,w2,w28,w29] (N [w0,w98,w97,w3,w4] L L) (N [w0,w98,w2,w199,w4] L L)) (N [w0,w98,w2,w153,w4] (N [w0,w98,w2,w153,w154] L L) (N [w0,w98,w2,w576,w4] L L)))) (N [w0,w675,w2,w3,w4] (N [w0,w98,w2,w3,w140] (N [w0,w98,w2,w3,w556] (N [w0,w98,w2,w3,w4] L L) (N [w0,w98,w2,w3,w59] L L)) (N [w0,w98,w56,w3,w4] (N [w0,w98,w133,w3,w4] L L) (N [w0,w98,w3,w4,w72] L L))) (N [w0,w297,w2,w153,w4] (N [w0,w689,w2,w3,w4] (N [w0,w685,w2,w3,w4] L L) (N [w0,w689,w2,w4,w207] L L)) (N [w0,w297,w2,w3,w575] (N [w0,w297,w2,w3,w154] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_1L : checkSTree aut12.fn aut34.fn 4 1 tbl_4_0 tbl_4_1 tbl_5_1L = true := by decide +kernel
def tbl_5_1R : STree := (N [w0,w1,w2,w3,w562] (N [w0,w1,w2,w678,w4] (N [w0,w1,w2,w28,w320] (N [w0,w301,w2,w80,w4] (N [w0,w319,w2,w3,w4] (N [w0,w319,w2,w28,w29] (N [w0,w706,w2,w3,w4] L L) (N [w0,w319,w2,w222,w4] L L)) (N [w0,w301,w302,w3,w4] (N [w0,w319,w2,w3,w59] L L) (N [w0,w301,w2,w28,w29] L L))) (N [w0,w1,w2,w64,w259] (N [w0,w301,w2,w3,w59] (N [w0,w301,w2,w3,w4] L L) (N [w0,w709,w2,w3,w4] L L)) (N [w0,w1,w2,w266,w280] (N [w0,w1,w2,w254,w28] L L) (N [w0,w1,w2,w266,w29] L L)))) (N [w0,w1,w2,w88,w45] (N [w0,w1,w2,w285,w29] (N [w0,w1,w2,w28,w246] (N [w0,w1,w2,w28,w280] L L) (N [w0,w1,w2,w28,w29] L L)) (N [w0,w1,w2,w305,w29] (N [w0,w1,w2,w80,w59] L L) (N [w0,w1,w2,w312,w29] L L))) (N [w0,w1,w2,w199,w4] (N [w0,w1,w2,w88,w29] (N [w0,w1,w2,w88,w140] L L) (N [w0,w1,w2,w199,w200] L L)) (N [w0,w1,w2,w661,w4] (N [w0,w1,w2,w658,w4] L L) (N [w0,w1,w2,w665,w4] L L))))) (N [w0,w1,w2,w260,w29] (N [w0,w1,w2,w99,w140] (N [w0,w1,w2,w99,w263] (N [w0,w1,w2,w99,w298] (N [w0,w1,w2,w99,w100] L L) (N [w0,w1,w2,w99,w154] L L)) (N [w0,w1,w2,w99,w59] (N [w0,w1,w2,w99,w4] L L) (N [w0,w1,w2,w99,w557] L L))) (N [w0,w1,w2,w695,w4] (N [w0,w1,w2,w299,w4] (N [w0,w1,w2,w682,w4] L L) (N [w0,w1,w2,w299,w59] L L)) (N [w0,w1,w2,w260,w59] (N [w0,w1,w2,w260,w4] L L) (N [w0,w1,w2,w260,w243] L L)))) (N [w0,w1,w2,w3,w523] (N [w0,w1,w2,w3,w511] (N [w0,w1,w2,w262,w4] (N [w0,w1,w2,w262,w263] L L) (N [w0,w1,w2,w700,w4] L L)) (N [w0,w1,w2,w3,w134] (N [w0,w1,w2,w3,w128] L L) (N [w0,w1,w2,w3,w519] L L))) (N [w0,w1,w2,w3,w712] (N [w0,w1,w2,w3,w547] (N [w0,w1,w2,w3,w189] L L) (N [w0,w1,w2,w3,w530] L L)) (N [w0,w1,w2,w3,w556] (N [w0,w1,w2,w3,w558] L L) (N [w0,w1,w2,w3,w59] L L)))))) (N [w0,w1,w222,w4,w43] (N [w0,w1,w2,w60,w23] (N [w0,w1,w2,w191,w52] (N [w0,w1,w2,w127,w128] (N [w0,w1,w2,w3,w243] (N [w0,w1,w2,w3,w587] L L) (N [w0,w1,w2,w142,w29] L L)) (N [w0,w1,w2,w36,w59] (N [w0,w1,w2,w137,w38] L L) (N [w0,w1,w2,w192,w29] L L))) (N [w0,w1,w2,w70,w29] (N [w0,w1,w2,w571,w29] (N [w0,w1,w2,w50,w59] L L) (N [w0,w1,w2,w161,w29] L L)) (N [w0,w1,w2,w60,w59] (N [w0,w1,w2,w313,w29] L L) (N [w0,w1,w2,w60,w169] L L)))) (N [w0,w1,w133,w153,w4] (N [w0,w1,w2,w246,w67] (N [w0,w1,w2,w273,w29] (N [w0,w1,w2,w60,w140] L L) (N [w0,w1,w2,w21,w243] L L)) (N [w0,w1,w64,w4,w43] (N [w0,w1,w2,w29,w251] L L) (N [w0,w1,w513,w3,w4] L L))) (N [w0,w1,w133,w4,w36] (N [w0,w1,w133,w3,w134] (N [w0,w1,w133,w3,w4] L L) (N [w0,w1,w133,w3,w59] L L)) (N [w0,w1,w33,w3,w128] (N [w0,w1,w521,w3,w4] L L) (N [w0,w1,w28,w162,w29] L L))))) (N [w0,w3,w4,w161,w162] (N [w0,w1,w3,w43,w140] (N [w0,w1,w3,w516,w43] (N [w0,w1,w3,w4,w162] (N [w0,w1,w153,w4,w162] L L) (N [w0,w1,w3,w4,w529] L L)) (N [w0,w1,w3,w162,w29] (N [w0,w1,w3,w45,w162] L L) (N [w0,w1,w3,w207,w171] L L))) (N [w0,w1,w207,w27,w13] (N [w0,w1,w72,w29,w13] (N [w0,w1,w162,w29] L L) (N [w0,w1,w207,w171] L L)) (N [w0,w135,w3,w4,w43] (N [w0,w1,w43,w27,w29] L L) (N [w0,w19,w3,w4,w164] L L)))) (N [w1,w2,w3,w4,w549] (N [w1,w2,w199,w4,w188] (N [w75,w2,w3,w4,w48] (N [w18,w19,w3,w4,w188] L L) (N [w98,w2,w3,w4,w188] L L)) (N [w1,w2,w3,w4,w543] (N [w1,w2,w99,w4,w188] L L) (N [w1,w2,w3,w4,w188] L L))) (N [w1,w2,w3,w544,w52] (N [w1,w2,w3,w188,w59] (N [w1,w2,w3,w188,w189] L L) (N [w1,w2,w3,w128,w48] L L)) (N [w1,w56,w3,w4,w188] (N [w1,w133,w3,w4,w55] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_1R : checkSTree aut12.fn aut34.fn 4 1 tbl_4_0 tbl_4_1 tbl_5_1R = true := by decide +kernel
def tbl_5_1 : STree := N [w0,w297,w2,w3,w4] tbl_5_1L tbl_5_1R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_5_1 : checkSTree aut12.fn aut34.fn 4 1 tbl_4_0 tbl_4_1 tbl_5_1 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_5_1L chk_tbl_5_1R
lemma nolive_5_1 : ∀ v, MemSTree v tbl_5_1 → ∀ m ≤ 5, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 4 1 tbl_5_1 tbl_4_0 tbl_4_1 nolive_4_0 nolive_4_1 chk_tbl_5_1
def tbl_6_0LLLL : STree := (N [w96,w0,w1,w2,w3,w4,w29] (N [w325,w96,w0,w1,w2,w3,w4] (N [w257,w0,w1,w2,w19,w3,w4] (N [w316,w0,w1,w2,w3,w4,w29] (N [w300,w0,w1,w2,w3,w4,w81] (N [w300,w0,w1,w2,w3,w4,w15] (N [w300,w0,w1,w2,w3,w4] L L) (N [w300,w0,w1,w2,w3,w4,w29] L L)) (N [w316,w0,w1,w2,w3,w4,w25] (N [w316,w0,w1,w2,w3,w4] L L) L)) (N [w261,w0,w1,w2,w3,w4] (N [w261,w0,w1,w2,w19,w3,w4] (N [w316,w0,w1,w2,w3,w4,w94] L L) L) (N [w261,w0,w1,w2,w3,w4,w63] (N [w261,w0,w1,w2,w3,w4,w11] L L) L))) (N [w295,w0,w1,w2,w3,w4,w27] (N [w257,w0,w1,w2,w3,w4,w67] (N [w257,w0,w1,w2,w3,w4,w23] (N [w257,w0,w1,w2,w3,w4] L L) L) (N [w295,w0,w1,w2,w3,w4,w17] (N [w295,w0,w1,w2,w3,w4] L L) L)) (N [w328,w96,w0,w1,w2,w3,w4] (N [w295,w0,w1,w2,w3,w4,w241] (N [w295,w0,w1,w2,w3,w4,w13] L L) L) (N [w328,w0,w1,w2,w3,w4,w13] (N [w328,w0,w1,w2,w3,w4] L L) L)))) (N [w96,w0,w1,w326,w2,w3,w4] (N [w96,w0,w111,w1,w2,w3,w4] (N [w96,w12,w0,w1,w2,w3,w4] (N [w325,w0,w1,w2,w3,w4,w13] (N [w325,w0,w1,w2,w3,w4] L L) (N [w96,w10,w0,w1,w2,w3,w4] L L)) (N [w96,w14,w0,w1,w2,w3,w4] (N [w96,w12,w0,w1,w3,w4,w13] L L) L)) (N [w96,w0,w98,w1,w2,w3,w4] (N [w96,w0,w20,w1,w2,w3,w4] (N [w96,w0,w18,w1,w2,w3,w4] L L) L) (N [w96,w0,w98,w2,w3,w4,w13] (N [w96,w0,w98,w2,w3,w4] L L) L))) (N [w96,w0,w1,w2,w153,w4] (N [w96,w0,w1,w2,w19,w3,w4] (N [w96,w0,w1,w2,w121,w3,w4] (N [w96,w0,w1,w24,w2,w3,w4] L L) L) (N [w96,w0,w1,w2,w153,w3,w4] (N [w96,w0,w1,w2,w28,w3,w4] L L) L)) (N [w96,w0,w1,w2,w3,w4,w15] (N [w96,w0,w1,w2,w3,w329,w4] (N [w96,w0,w1,w2,w153,w4,w13] L L) L) (N [w96,w0,w1,w2,w3,w4,w25] (N [w96,w0,w1,w2,w3,w4,w21] L L) L))))) (N [w90,w0,w18,w1,w2,w3,w4] (N [w198,w0,w1,w2,w3,w4,w48] (N [w96,w0,w1,w121,w3,w4,w13] (N [w96,w0,w1,w2,w3,w4,w63] (N [w96,w0,w1,w2,w3,w4,w13] (N [w96,w0,w1,w2,w3,w4,w11] L L) (N [w96,w0,w1,w2,w3,w4,w78] L L)) (N [w96,w0,w1,w2,w3,w330,w13] (N [w96,w0,w1,w2,w3,w330] L L) L)) (N [w96,w111,w1,w2,w3,w4,w13] (N [w96,w0,w326,w2,w3,w4,w13] (N [w96,w0,w326,w2,w3,w4] L L) L) (N [w198,w0,w1,w2,w3,w4] (N [w198,w0,w18,w1,w2,w3,w4] L L) L))) (N [w332,w0,w1,w2,w3,w4,w29] (N [w334,w0,w1,w2,w3,w4,w29] (N [w334,w0,w1,w2,w3,w4] (N [w334,w90,w0,w1,w2,w3,w4] L L) L) (N [w332,w0,w1,w2,w3,w4] (N [w332,w90,w0,w1,w2,w3,w4] L L) L)) (N [w90,w14,w0,w1,w2,w4,w29] (N [w90,w14,w0,w1,w2,w3,w4] (N [w90,w10,w0,w1,w2,w3,w4] L L) L) (N [w90,w0,w333,w1,w2,w3,w4] (N [w90,w91,w0,w1,w2,w3,w4] L L) L)))) (N [w90,w0,w1,w2,w3,w4,w11] (N [w90,w0,w1,w2,w28,w3,w29] (N [w90,w0,w1,w335,w2,w3,w4] (N [w90,w0,w92,w1,w2,w3,w4] (N [w90,w0,w20,w1,w2,w3,w4] L L) L) (N [w90,w0,w1,w2,w28,w3,w4] (N [w90,w0,w1,w2,w19,w3,w4] L L) L)) (N [w90,w0,w1,w2,w3,w4,w15] (N [w90,w0,w1,w2,w3,w109,w4] (N [w90,w0,w1,w2,w28,w29] L L) L) (N [w90,w0,w1,w2,w3,w4,w29] (N [w90,w0,w1,w2,w3,w4,w21] L L) L))) (N [w339,w0,w1,w2,w3,w4] (N [w90,w0,w1,w2,w3,w338,w29] (N [w90,w0,w1,w2,w3,w4,w81] (N [w90,w0,w1,w2,w3,w4,w89] L L) L) (N [w339,w83,w0,w1,w2,w3,w4] (N [w90,w0,w1,w2,w3,w23,w29] L L) L)) (N [w341,w0,w1,w2,w3,w4] (N [w341,w83,w0,w1,w2,w3,w4] (N [w339,w0,w1,w2,w3,w4,w27] L L) L) (N [w343,w83,w0,w1,w2,w3,w4] (N [w341,w0,w1,w2,w3,w4,w27] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLLL = true := by decide +kernel
def tbl_6_0LLLR : STree := (N [w265,w0,w1,w2,w3,w4] (N [w83,w0,w1,w2,w3,w4,w25] (N [w83,w0,w1,w24,w2,w3,w4] (N [w83,w0,w340,w1,w2,w3,w4] (N [w83,w14,w0,w1,w2,w3,w4] (N [w83,w10,w0,w1,w2,w3,w4] (N [w343,w0,w1,w2,w3,w4,w27] L L) (N [w83,w12,w0,w1,w2,w3,w4] L L)) (N [w83,w178,w0,w1,w2,w3,w4] (N [w83,w16,w0,w1,w2,w3,w4] L L) L)) (N [w83,w0,w22,w1,w2,w3,w4] (N [w83,w0,w20,w1,w2,w3,w4] (N [w83,w0,w18,w1,w2,w3,w4] L L) L) (N [w83,w0,w1,w342,w2,w3,w4] (N [w83,w0,w221,w1,w2,w3,w4] L L) L))) (N [w83,w0,w1,w2,w222,w3,w4] (N [w83,w0,w1,w2,w107,w3,w4] (N [w83,w0,w1,w26,w2,w3,w27] (N [w83,w0,w1,w26,w2,w3,w4] L L) L) (N [w83,w0,w1,w2,w28,w3,w4] (N [w83,w0,w1,w2,w19,w3,w4] L L) L)) (N [w83,w0,w1,w2,w3,w4,w15] (N [w83,w0,w1,w2,w3,w4,w117] (N [w83,w0,w1,w2,w3,w344,w4] L L) L) (N [w83,w0,w1,w2,w3,w4,w21] (N [w83,w0,w1,w2,w3,w4,w17] L L) L)))) (N [w172,w16,w0,w1,w2,w3,w4] (N [w83,w0,w1,w2,w3,w4,w241] (N [w83,w0,w1,w2,w3,w4,w29] (N [w83,w0,w1,w2,w3,w4,w27] (N [w83,w0,w1,w2,w3,w4,w23] L L) L) (N [w83,w0,w1,w2,w3,w4,w13] (N [w83,w0,w1,w2,w3,w4,w11] L L) L)) (N [w83,w0,w1,w2,w3,w117,w27] (N [w83,w0,w1,w2,w3,w4,w94] (N [w83,w0,w1,w2,w3,w4,w67] L L) L) (N [w83,w0,w1,w107,w3,w4,w27] (N [w83,w0,w1,w2,w3,w27,w29] L L) L))) (N [w217,w0,w1,w2,w3,w4,w140] (N [w217,w0,w1,w24,w2,w3,w4] (N [w172,w0,w1,w2,w3,w4,w171] (N [w172,w0,w1,w2,w3,w4] L L) L) (N [w217,w0,w1,w2,w3,w4] (N [w217,w0,w1,w24,w2,w3,w140] L L) L)) (N [w195,w0,w1,w2,w3,w4] (N [w195,w0,w18,w1,w2,w3,w4] (N [w217,w0,w1,w2,w3,w140] L L) L) (N [w265,w0,w1,w2,w28,w3,w4] (N [w195,w0,w1,w2,w3,w4,w52] L L) L))))) (N [w74,w0,w1,w2,w3,w4,w21] (N [w74,w0,w18,w1,w2,w3,w4] (N [w349,w0,w1,w2,w3,w4,w17] (N [w345,w0,w1,w2,w3,w4,w17] (N [w345,w74,w0,w1,w2,w3,w4] (N [w265,w0,w1,w2,w3,w4,w72] L L) (N [w345,w0,w1,w2,w3,w4] L L)) (N [w349,w0,w1,w2,w3,w4] (N [w349,w74,w0,w1,w2,w3,w4] L L) L)) (N [w74,w16,w0,w1,w2,w3,w4] (N [w74,w14,w0,w1,w2,w3,w4] (N [w74,w10,w0,w1,w2,w3,w4] L L) L) (N [w74,w0,w103,w1,w2,w3,w4] (N [w74,w16,w0,w1,w2,w3,w17] L L) L))) (N [w74,w0,w1,w2,w28,w3,w4] (N [w74,w0,w216,w1,w2,w3,w4] (N [w74,w0,w22,w1,w2,w3,w4] (N [w74,w0,w20,w1,w2,w3,w4] L L) L) (N [w74,w0,w1,w2,w19,w3,w4] (N [w74,w0,w1,w346,w2,w3,w4] L L) L)) (N [w74,w0,w1,w2,w3,w4,w125] (N [w74,w0,w1,w2,w3,w350,w4] (N [w74,w0,w1,w2,w80,w3,w4] L L) L) (N [w74,w0,w1,w2,w3,w4,w17] (N [w74,w0,w1,w2,w3,w4,w15] L L) L)))) (N [w168,w0,w1,w2,w3,w4] (N [w74,w0,w1,w2,w3,w125,w17] (N [w74,w0,w1,w2,w3,w4,w11] (N [w74,w0,w1,w2,w3,w4,w29] (N [w74,w0,w1,w2,w3,w4,w23] L L) L) (N [w74,w0,w1,w2,w3,w4,w81] (N [w74,w0,w1,w2,w3,w4,w101] L L) L)) (N [w212,w0,w1,w2,w3,w4] (N [w212,w0,w1,w26,w2,w3,w4] (N [w74,w103,w1,w2,w3,w4,w17] L L) L) (N [w168,w14,w0,w1,w2,w3,w4] (N [w212,w0,w1,w2,w3,w4,w211] L L) L))) (N [w264,w0,w1,w2,w3,w4] (N [w145,w0,w1,w2,w3,w4] (N [w145,w12,w0,w1,w2,w3,w4] (N [w168,w0,w1,w2,w3,w4,w45] L L) L) (N [w264,w0,w1,w2,w28,w3,w4] (N [w145,w0,w1,w2,w3,w4,w144] L L) L)) (N [w351,w104,w0,w1,w2,w3,w4] (N [w351,w102,w0,w1,w2,w3,w4] (N [w264,w0,w1,w2,w3,w4,w69] L L) L) (N [w351,w10,w0,w1,w2,w3,w4] (N [w351,w9,w0,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLLR = true := by decide +kernel
def tbl_6_0LLL : STree := N [w343,w0,w1,w2,w3,w4] tbl_6_0LLLL tbl_6_0LLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LLLL chk_tbl_6_0LLLR
def tbl_6_0LLRL : STree := (N [w104,w165,w0,w1,w2,w3,w4] (N [w102,w0,w1,w2,w3,w356,w4] (N [w102,w10,w0,w1,w2,w3,w4] (N [w102,w108,w0,w1,w2,w3,w4] (N [w355,w14,w0,w1,w2,w3,w4] (N [w355,w108,w0,w1,w2,w3,w4] (N [w355,w102,w0,w1,w2,w3,w4] L L) (N [w355,w9,w0,w1,w2,w3,w4] L L)) (N [w102,w104,w0,w1,w2,w3,w4] (N [w355,w0,w1,w2,w3,w4] L L) L)) (N [w102,w9,w103,w1,w2,w3,w4] (N [w102,w9,w0,w1,w2,w3,w4] (N [w102,w9,w16,w1,w2,w3,w4] L L) L) (N [w102,w40,w0,w1,w2,w3,w4] (N [w102,w40,w16,w1,w2,w3,w4] L L) L))) (N [w102,w0,w20,w1,w2,w3,w4] (N [w102,w16,w1,w2,w3,w4] (N [w102,w16,w0,w1,w2,w3,w4] (N [w102,w14,w0,w1,w2,w3,w4] L L) L) (N [w102,w0,w18,w1,w2,w3,w4] (N [w102,w0,w103,w1,w2,w3,w4] L L) L)) (N [w102,w0,w1,w105,w2,w3,w4] (N [w102,w0,w1,w352,w2,w3,w4] (N [w102,w0,w22,w1,w2,w3,w4] L L) L) (N [w102,w0,w1,w2,w28,w3,w4] (N [w102,w0,w1,w2,w19,w3,w4] L L) L)))) (N [w358,w0,w1,w2,w3,w4] (N [w102,w0,w1,w2,w3,w4,w29] (N [w102,w0,w1,w2,w3,w4,w17] (N [w102,w0,w1,w2,w3,w4] (N [w102,w0,w1,w2,w3,w109,w4] L L) (N [w102,w0,w1,w2,w3,w4,w15] L L)) (N [w102,w0,w1,w2,w3,w4,w23] (N [w102,w0,w1,w2,w3,w4,w21] L L) L)) (N [w358,w104,w0,w1,w2,w3,w4] (N [w102,w103,w1,w2,w3,w4] (N [w102,w0,w1,w2,w3,w4,w11] L L) L) (N [w358,w0,w18,w1,w2,w3,w4] (N [w358,w9,w0,w1,w2,w3,w4] L L) L))) (N [w104,w106,w0,w1,w2,w3,w4] (N [w361,w9,w0,w1,w2,w3,w4] (N [w361,w108,w0,w1,w2,w3,w4] (N [w361,w104,w0,w1,w2,w3,w4] L L) L) (N [w361,w0,w1,w2,w3,w4] (N [w361,w0,w20,w1,w2,w3,w4] L L) L)) (N [w104,w9,w0,w1,w2,w3,w4] (N [w104,w9,w0,w22,w2,w3,w4] (N [w104,w108,w0,w1,w2,w3,w4] L L) L) (N [w104,w165,w0,w22,w2,w3,w4] (N [w104,w9,w0,w105,w2,w3,w4] L L) L))))) (N [w104,w0,w1,w2,w3,w4,w23] (N [w104,w0,w1,w26,w2,w3,w4] (N [w104,w0,w18,w1,w2,w3,w4] (N [w104,w16,w0,w1,w2,w3,w4] (N [w104,w12,w0,w1,w2,w3,w4] (N [w104,w10,w0,w1,w2,w3,w4] L L) (N [w104,w14,w0,w1,w2,w3,w4] L L)) (N [w104,w0,w103,w1,w2,w3,w4] (N [w104,w0,w357,w1,w2,w3,w4] L L) L)) (N [w104,w0,w22,w2,w3,w4] (N [w104,w0,w22,w1,w2,w3,w4] (N [w104,w0,w20,w1,w2,w3,w4] L L) L) (N [w104,w0,w1,w24,w2,w3,w4] (N [w104,w0,w1,w105,w2,w3,w4] L L) L))) (N [w104,w0,w1,w2,w3,w109,w4] (N [w104,w0,w1,w2,w19,w3,w4] (N [w104,w0,w1,w2,w107,w3,w4] (N [w104,w0,w1,w2,w359,w3,w4] L L) L) (N [w104,w0,w1,w2,w3,w362,w4] (N [w104,w0,w1,w2,w28,w3,w4] L L) L)) (N [w104,w0,w1,w2,w3,w4,w17] (N [w104,w0,w1,w2,w3,w4,w15] (N [w104,w0,w1,w2,w3,w4] L L) L) (N [w104,w0,w1,w2,w3,w4,w25] (N [w104,w0,w1,w2,w3,w4,w21] L L) L)))) (N [w108,w68,w0,w1,w2,w3,w4] (N [w108,w9,w14,w0,w1,w2,w4] (N [w104,w0,w1,w2,w3,w4,w11] (N [w104,w0,w1,w2,w3,w4,w29] (N [w104,w0,w1,w2,w3,w4,w27] L L) L) (N [w104,w0,w105,w2,w3,w4] (N [w104,w0,w1,w2,w3,w4,w13] L L) L)) (N [w108,w9,w0,w1,w2,w109,w4] (N [w108,w9,w0,w1,w2,w3,w4] (N [w108,w9,w0,w1,w2,w28,w4] L L) L) (N [w108,w68,w0,w1,w2,w28,w4] (N [w108,w9,w0,w1,w2,w4,w21] L L) L))) (N [w108,w0,w103,w1,w2,w3,w4] (N [w108,w14,w0,w1,w2,w4] (N [w108,w14,w0,w1,w2,w3,w4] (N [w108,w10,w0,w1,w2,w3,w4] L L) L) (N [w108,w0,w363,w1,w2,w3,w4] (N [w108,w16,w0,w1,w2,w3,w4] L L) L)) (N [w108,w0,w22,w1,w2,w3,w4] (N [w108,w0,w20,w1,w2,w3,w4] (N [w108,w0,w18,w1,w2,w3,w4] L L) L) (N [w108,w0,w1,w105,w2,w3,w4] (N [w108,w0,w1,w364,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLRL = true := by decide +kernel
def tbl_6_0LLRR : STree := (N [w9,w84,w0,w1,w2,w3,w4] (N [w9,w32,w0,w1,w2,w3,w4] (N [w392,w9,w0,w1,w2,w3,w4] (N [w108,w0,w1,w2,w3,w4,w21] (N [w108,w0,w1,w2,w3,w4] (N [w108,w0,w1,w2,w28,w4] (N [w108,w0,w1,w2,w28,w3,w4] L L) (N [w108,w0,w1,w2,w3,w109,w4] L L)) (N [w108,w0,w1,w2,w3,w4,w17] (N [w108,w0,w1,w2,w3,w4,w15] L L) L)) (N [w108,w0,w1,w2,w3,w4,w11] (N [w108,w0,w1,w2,w3,w4,w29] (N [w108,w0,w1,w2,w3,w4,w23] L L) L) (N [w108,w0,w1,w2,w4,w21] (N [w108,w0,w1,w2,w109,w4] L L) L))) (N [w391,w9,w0,w1,w2,w3,w4] (N [w385,w9,w0,w1,w2,w3,w4] (N [w392,w0,w1,w2,w3,w4,w11] (N [w392,w0,w1,w2,w3,w4] L L) L) (N [w385,w0,w1,w2,w3,w4] (N [w385,w0,w1,w2,w19,w3,w4] L L) L)) (N [w390,w9,w0,w1,w2,w3,w4] (N [w391,w0,w1,w2,w3,w4,w21] (N [w391,w0,w1,w2,w3,w4] L L) L) (N [w390,w0,w1,w2,w3,w4,w15] (N [w390,w0,w1,w2,w3,w4] L L) L)))) (N [w9,w14,w0,w1,w2,w4,w29] (N [w9,w371,w0,w1,w2,w3,w4] (N [w9,w10,w0,w18,w2,w3,w4] (N [w9,w37,w0,w1,w2,w3,w4] (N [w9,w35,w0,w1,w2,w3,w4] L L) L) (N [w9,w380,w0,w1,w2,w3,w4] (N [w9,w10,w0,w2,w3,w4,w11] L L) L)) (N [w9,w44,w0,w1,w2,w3,w4] (N [w9,w62,w0,w1,w2,w3,w4] (N [w9,w367,w0,w1,w2,w3,w4] L L) L) (N [w9,w14,w0,w1,w2,w4,w15] (N [w9,w14,w0,w20,w1,w2,w4] L L) L))) (N [w9,w16,w0,w22,w1,w2,w3] (N [w9,w375,w0,w1,w2,w3,w4] (N [w9,w375,w0,w103,w1,w2,w4] (N [w9,w386,w0,w1,w2,w3,w4] L L) L) (N [w9,w368,w0,w1,w2,w3,w4] (N [w9,w375,w0,w1,w2,w4] L L) L)) (N [w9,w16,w0,w1,w2,w3,w29] (N [w9,w16,w0,w1,w2,w3,w17] (N [w9,w16,w0,w1,w2,w3,w4] L L) L) (N [w9,w16,w1,w2,w3,w17] (N [w9,w16,w1,w2,w3,w4,w17] L L) L))))) (N [w9,w0,w86,w1,w2,w3,w4] (N [w9,w0,w20,w1,w2,w3,w59] (N [w9,w0,w51,w1,w2,w3,w4] (N [w9,w0,w363,w1,w2,w3,w4] (N [w9,w91,w0,w1,w2,w3,w4] (N [w9,w177,w0,w1,w2,w3,w4] L L) (N [w9,w0,w357,w1,w2,w3,w4] L L)) (N [w9,w0,w49,w1,w2,w3,w4] (N [w9,w0,w103,w1,w2,w3,w4] L L) L)) (N [w9,w0,w381,w1,w2,w3,w4] (N [w9,w0,w18,w19,w3,w4] (N [w9,w0,w18,w1,w19,w3,w4] L L) L) (N [w9,w0,w58,w1,w2,w3,w4] (N [w9,w0,w377,w1,w2,w3,w4] L L) L))) (N [w9,w0,w22,w1,w2,w3,w23] (N [w9,w0,w383,w1,w2,w3,w4] (N [w9,w0,w387,w1,w2,w3,w4] (N [w9,w0,w20,w1,w2,w4,w21] L L) L) (N [w9,w0,w22,w1,w2,w3,w4] (N [w9,w0,w378,w1,w2,w3,w4] L L) L)) (N [w9,w0,w22,w2,w3,w23] (N [w9,w0,w22,w2,w3,w4,w23] (N [w9,w0,w22,w1,w2,w4,w60] L L) L) (N [w9,w0,w216,w1,w2,w3,w4] (N [w9,w0,w75,w1,w2,w3,w4] L L) L)))) (N [w9,w0,w1,w2,w57,w3,w4] (N [w9,w0,w1,w352,w2,w3,w4] (N [w9,w0,w98,w1,w2,w3,w4] (N [w9,w0,w92,w1,w2,w3,w4] (N [w9,w0,w221,w1,w2,w3,w4] L L) L) (N [w9,w0,w98,w2,w3,w4,w13] (N [w9,w0,w98,w2,w3,w4] L L) L)) (N [w9,w0,w1,w105,w2,w3,w4] (N [w9,w0,w1,w364,w2,w3,w4] (N [w9,w0,w1,w360,w2,w3,w4] L L) L) (N [w9,w0,w1,w2,w66,w3,w4] (N [w9,w0,w1,w2,w64,w3,w4] L L) L))) (N [w9,w0,w1,w2,w28,w4,w29] (N [w9,w0,w1,w2,w382,w3,w4] (N [w9,w0,w1,w2,w34,w3,w4] (N [w9,w0,w1,w2,w208,w3,w4] L L) L) (N [w9,w0,w1,w2,w28,w3,w29] (N [w9,w0,w1,w2,w28,w3,w4] L L) L)) (N [w9,w0,w1,w2,w88,w3,w4] (N [w9,w0,w1,w2,w80,w3,w4] (N [w9,w0,w1,w2,w28,w29] L L) L) (N [w9,w0,w1,w2,w99,w4] (N [w9,w0,w1,w2,w99,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLRR = true := by decide +kernel
def tbl_6_0LLR : STree := N [w108,w0,w1,w2,w19,w3,w4] tbl_6_0LLRL tbl_6_0LLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LLRL chk_tbl_6_0LLRR
def tbl_6_0LL : STree := N [w351,w0,w1,w2,w3,w4] tbl_6_0LLL tbl_6_0LLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LLL chk_tbl_6_0LLR
def tbl_6_0LRLL : STree := (N [w271,w0,w1,w2,w3,w4] (N [w9,w0,w1,w2,w3,w4,w169] (N [w9,w0,w1,w2,w3,w4,w376] (N [w9,w0,w1,w2,w3,w100,w4] (N [w9,w0,w1,w2,w3,w79,w4] (N [w9,w0,w1,w2,w3,w356,w4] (N [w9,w0,w1,w2,w3,w362,w4] L L) (N [w9,w0,w1,w2,w3,w109,w4] L L)) (N [w9,w0,w1,w2,w3,w100] (N [w9,w0,w1,w2,w3,w87,w4] L L) L)) (N [w9,w0,w1,w2,w3,w4,w36] (N [w9,w0,w1,w2,w3,w4,w69] (N [w9,w0,w1,w2,w3,w100,w11] L L) L) (N [w9,w0,w1,w2,w3,w4,w55] (N [w9,w0,w1,w2,w3,w4,w46] L L) L))) (N [w9,w0,w1,w2,w3,w4,w70] (N [w9,w0,w1,w2,w3,w4,w289] (N [w9,w0,w1,w2,w3,w4,w45] (N [w9,w0,w1,w2,w3,w4,w38] L L) L) (N [w9,w0,w1,w2,w3,w4,w50] (N [w9,w0,w1,w2,w3,w4,w17] L L) L)) (N [w9,w0,w1,w2,w3,w4,w384] (N [w9,w0,w1,w2,w3,w4,w41] (N [w9,w0,w1,w2,w3,w4,w60] L L) L) (N [w9,w0,w1,w2,w3,w4,w59] (N [w9,w0,w1,w2,w3,w4,w52] L L) L)))) (N [w9,w0,w1,w2,w3,w23,w29] (N [w9,w0,w1,w2,w3,w4,w65] (N [w9,w0,w1,w2,w3,w4,w372] (N [w9,w0,w1,w2,w3,w4,w29] (N [w9,w0,w1,w2,w3,w4,w23] L L) (N [w9,w0,w1,w2,w3,w4,w48] L L)) (N [w9,w0,w1,w2,w3,w4,w101] (N [w9,w0,w1,w2,w3,w4,w76] L L) L)) (N [w9,w0,w1,w2,w3,w4,w89] (N [w9,w0,w1,w2,w3,w4,w63] (N [w9,w0,w1,w2,w3,w4,w67] L L) L) (N [w9,w0,w1,w2,w3,w59] (N [w9,w0,w1,w2,w3,w4,w81] L L) L))) (N [w275,w0,w1,w2,w3,w154] (N [w9,w0,w1,w2,w4,w21,w29] (N [w9,w0,w1,w2,w4,w60] (N [w9,w0,w1,w2,w109,w4,w29] L L) L) (N [w9,w103,w1,w2,w3,w4,w17] (N [w9,w0,w1,w107,w3,w4,w27] L L) L)) (N [w275,w0,w1,w2,w3,w4] (N [w275,w0,w1,w2,w3,w154,w13] (N [w275,w0,w1,w2,w3,w154,w4] L L) L) (N [w271,w0,w1,w2,w3,w270,w4] (N [w275,w0,w1,w2,w3,w4,w13] L L) L))))) (N [w68,w0,w1,w2,w3,w4,w70] (N [w68,w14,w0,w1,w2,w3,w4] (N [w393,w0,w1,w2,w3,w4] (N [w268,w0,w1,w2,w3,w4,w15] (N [w268,w0,w1,w2,w3,w79,w4] (N [w271,w0,w1,w2,w3,w4,w25] L L) (N [w268,w0,w1,w2,w3,w4] L L)) (N [w393,w0,w1,w2,w28,w3,w4] (N [w393,w68,w0,w1,w2,w3,w4] L L) L)) (N [w395,w0,w1,w2,w3,w4] (N [w395,w0,w1,w2,w28,w3,w4] (N [w395,w68,w0,w1,w2,w3,w4] L L) L) (N [w68,w44,w0,w1,w2,w3,w4] (N [w68,w10,w0,w1,w2,w3,w4] L L) L))) (N [w68,w0,w1,w2,w19,w3,w4] (N [w68,w0,w58,w1,w2,w3,w4] (N [w68,w0,w18,w1,w2,w3,w4] (N [w68,w0,w394,w1,w2,w3,w4] L L) L) (N [w68,w0,w1,w396,w2,w3,w4] (N [w68,w0,w20,w1,w2,w3,w4] L L) L)) (N [w68,w0,w1,w2,w28,w29] (N [w68,w0,w1,w2,w28,w3,w29] (N [w68,w0,w1,w2,w28,w3,w4] L L) L) (N [w68,w0,w1,w2,w3,w4,w15] (N [w68,w0,w1,w2,w3,w4,w69] L L) L)))) (N [w61,w14,w0,w1,w2,w3,w4] (N [w403,w0,w1,w2,w3,w4] (N [w68,w0,w1,w2,w3,w4,w11] (N [w68,w0,w1,w2,w3,w4,w29] (N [w68,w0,w1,w2,w3,w4,w21] L L) L) (N [w403,w0,w1,w2,w19,w3,w4] (N [w403,w61,w0,w1,w2,w3,w4] L L) L)) (N [w400,w0,w1,w2,w3,w4] (N [w400,w0,w1,w2,w19,w3,w4] (N [w400,w61,w0,w1,w2,w3,w4] L L) L) (N [w61,w62,w0,w1,w2,w3,w4] (N [w61,w10,w0,w1,w2,w3,w4] L L) L))) (N [w61,w0,w1,w113,w2,w3,w4] (N [w61,w0,w18,w1,w19,w3,w4] (N [w61,w0,w18,w1,w2,w3,w4] (N [w61,w0,w401,w1,w2,w3,w4] L L) L) (N [w61,w0,w20,w1,w2,w3,w4] (N [w61,w0,w18,w19,w3,w4] L L) L)) (N [w61,w0,w1,w2,w28,w3,w4] (N [w61,w0,w1,w2,w19,w3,w4] (N [w61,w0,w1,w2,w64,w3,w4] L L) L) (N [w61,w0,w1,w2,w3,w4,w15] (N [w61,w0,w1,w2,w3,w404,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRLL = true := by decide +kernel
def tbl_6_0LRLR : STree := (N [w112,w0,w1,w2,w3,w4,w25] (N [w112,w114,w0,w1,w2,w3,w4] (N [w242,w0,w1,w2,w19,w3,w4] (N [w141,w0,w1,w2,w33,w3,w4] (N [w61,w0,w1,w2,w3,w4,w63] (N [w61,w0,w1,w2,w3,w4,w11] (N [w61,w0,w1,w2,w3,w4,w29] L L) (N [w61,w0,w1,w2,w3,w4,w65] L L)) (N [w141,w10,w0,w1,w2,w3,w4] (N [w61,w0,w1,w402,w19,w3,w4] L L) L)) (N [w210,w0,w1,w2,w209,w3,w4] (N [w210,w0,w22,w1,w2,w3,w4] (N [w141,w0,w1,w2,w3,w4] L L) L) (N [w242,w0,w1,w2,w66,w3,w4] (N [w210,w0,w1,w2,w3,w4] L L) L))) (N [w409,w0,w1,w2,w3,w4] (N [w409,w114,w0,w1,w2,w3,w4] (N [w409,w112,w0,w1,w2,w3,w4] (N [w242,w0,w1,w2,w3,w4] L L) L) (N [w409,w0,w20,w1,w2,w3,w4] (N [w409,w7,w0,w1,w2,w3,w4] L L) L)) (N [w407,w7,w0,w1,w2,w3,w4] (N [w407,w110,w0,w1,w2,w3,w4] (N [w407,w112,w0,w1,w2,w3,w4] L L) L) (N [w407,w0,w1,w2,w3,w4] (N [w407,w10,w0,w1,w2,w3,w4] L L) L)))) (N [w112,w0,w18,w1,w2,w3,w4] (N [w112,w47,w0,w1,w2,w3,w4] (N [w112,w7,w0,w1,w2,w3,w4] (N [w112,w7,w0,w18,w2,w3,w4] (N [w112,w110,w0,w1,w2,w3,w4] L L) L) (N [w112,w47,w0,w18,w2,w3,w4] (N [w112,w7,w0,w113,w2,w3,w4] L L) L)) (N [w112,w14,w0,w1,w2,w3,w4] (N [w112,w12,w0,w1,w2,w3,w4] (N [w112,w10,w0,w1,w2,w3,w4] L L) L) (N [w112,w0,w111,w1,w2,w3,w4] (N [w112,w0,w408,w1,w2,w3,w4] L L) L))) (N [w112,w0,w1,w2,w28,w3,w4] (N [w112,w0,w1,w113,w2,w3,w4] (N [w112,w0,w20,w1,w2,w3,w4] (N [w112,w0,w18,w2,w3,w4] L L) L) (N [w112,w0,w1,w2,w19,w3,w4] (N [w112,w0,w1,w24,w2,w3,w4] L L) L)) (N [w112,w0,w1,w2,w3,w4] (N [w112,w0,w1,w2,w3,w115,w4] (N [w112,w0,w1,w2,w3,w410,w4] L L) L) (N [w112,w0,w1,w2,w3,w4,w21] (N [w112,w0,w1,w2,w3,w4,w15] L L) L))))) (N [w114,w10,w0,w1,w2,w3,w4] (N [w413,w110,w0,w1,w2,w3,w4] (N [w451,w0,w1,w2,w3,w4] (N [w112,w0,w113,w2,w3,w4] (N [w112,w0,w1,w2,w3,w4,w11] (N [w112,w0,w1,w2,w3,w4,w29] L L) (N [w112,w0,w1,w2,w3,w4,w13] L L)) (N [w451,w0,w1,w26,w2,w3,w4] (N [w451,w54,w0,w1,w2,w3,w4] L L) L)) (N [w416,w0,w1,w2,w28,w3,w4] (N [w416,w7,w0,w1,w2,w3,w4] (N [w416,w114,w0,w1,w2,w3,w4] L L) L) (N [w413,w114,w0,w1,w2,w3,w4] (N [w416,w0,w1,w2,w3,w4] L L) L))) (N [w114,w7,w0,w1,w24,w2,w4] (N [w413,w0,w1,w2,w3,w4] (N [w413,w14,w0,w1,w2,w3,w4] (N [w413,w7,w0,w1,w2,w3,w4] L L) L) (N [w114,w110,w0,w1,w2,w3,w4] (N [w114,w116,w0,w1,w2,w3,w4] L L) L)) (N [w114,w7,w0,w1,w2,w4,w29] (N [w114,w7,w0,w1,w2,w115,w4] (N [w114,w7,w0,w1,w2,w3,w4] L L) L) (N [w114,w138,w0,w1,w2,w3,w4] (N [w114,w138,w0,w1,w24,w2,w4] L L) L)))) (N [w114,w0,w1,w24,w2,w4] (N [w114,w0,w18,w1,w2,w3,w4] (N [w114,w16,w0,w1,w2,w3,w4] (N [w114,w14,w0,w1,w2,w3,w4] (N [w114,w12,w0,w1,w2,w3,w4] L L) L) (N [w114,w0,w111,w1,w2,w3,w4] (N [w114,w0,w414,w1,w2,w3,w4] L L) L)) (N [w114,w0,w1,w415,w2,w3,w4] (N [w114,w0,w22,w1,w2,w3,w4] (N [w114,w0,w20,w1,w2,w3,w4] L L) L) (N [w114,w0,w1,w24,w2,w3,w4] (N [w114,w0,w1,w113,w2,w3,w4] L L) L))) (N [w114,w0,w1,w2,w3,w4,w417] (N [w114,w0,w1,w2,w28,w3,w4] (N [w114,w0,w1,w2,w19,w3,w4] (N [w114,w0,w1,w26,w2,w3,w4] L L) L) (N [w114,w0,w1,w2,w3,w4] (N [w114,w0,w1,w2,w3,w115,w4] L L) L)) (N [w114,w0,w1,w2,w3,w4,w17] (N [w114,w0,w1,w2,w3,w4,w15] (N [w114,w0,w1,w2,w3,w4,w117] L L) L) (N [w114,w0,w1,w2,w3,w4,w25] (N [w114,w0,w1,w2,w3,w4,w21] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRLR = true := by decide +kernel
def tbl_6_0LRL : STree := N [w61,w0,w1,w2,w3,w4,w21] tbl_6_0LRLL tbl_6_0LRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LRLL chk_tbl_6_0LRLR
def tbl_6_0LRRL : STree := (N [w7,w10,w0,w113,w2,w3,w4] (N [w110,w0,w1,w2,w3,w115,w4] (N [w110,w12,w0,w1,w2,w3,w4] (N [w110,w7,w12,w1,w2,w3,w4] (N [w114,w0,w1,w2,w3,w4,w13] (N [w114,w0,w1,w2,w3,w4,w29] (N [w114,w0,w1,w2,w3,w4,w27] L L) (N [w114,w0,w1,w2,w3,w4,w11] L L)) (N [w114,w0,w1,w2,w4,w29] (N [w114,w0,w1,w2,w115,w4] L L) L)) (N [w110,w31,w12,w1,w2,w3,w4] (N [w110,w7,w111,w1,w2,w3,w4] (N [w110,w7,w0,w1,w2,w3,w4] L L) L) (N [w110,w10,w0,w1,w2,w3,w4] (N [w110,w31,w0,w1,w2,w3,w4] L L) L))) (N [w110,w0,w1,w419,w2,w3,w4] (N [w110,w0,w111,w1,w2,w3,w4] (N [w110,w14,w0,w1,w2,w3,w4] (N [w110,w12,w1,w2,w3,w4] L L) L) (N [w110,w0,w20,w1,w2,w3,w4] (N [w110,w0,w18,w1,w2,w3,w4] L L) L)) (N [w110,w0,w1,w2,w19,w3,w4] (N [w110,w0,w1,w24,w2,w3,w4] (N [w110,w0,w1,w113,w2,w3,w4] L L) L) (N [w110,w0,w1,w2,w3,w420,w4] (N [w110,w0,w1,w2,w28,w3,w4] L L) L)))) (N [w446,w7,w0,w1,w2,w3,w4] (N [w110,w0,w1,w2,w3,w4,w11] (N [w110,w0,w1,w2,w3,w4,w21] (N [w110,w0,w1,w2,w3,w4,w15] (N [w110,w0,w1,w2,w3,w4] L L) L) (N [w110,w0,w1,w2,w3,w4,w29] (N [w110,w0,w1,w2,w3,w4,w25] L L) L)) (N [w445,w7,w0,w1,w2,w3,w4] (N [w110,w111,w1,w2,w3,w4] (N [w110,w0,w1,w2,w3,w4,w13] L L) L) (N [w445,w0,w1,w2,w3,w4,w15] (N [w445,w0,w1,w2,w3,w4] L L) L))) (N [w447,w7,w0,w1,w2,w3,w4] (N [w448,w7,w0,w1,w2,w3,w4] (N [w446,w0,w1,w2,w3,w4,w21] (N [w446,w0,w1,w2,w3,w4] L L) L) (N [w448,w0,w1,w2,w3,w4,w11] (N [w448,w0,w1,w2,w3,w4] L L) L)) (N [w7,w32,w0,w1,w2,w3,w4] (N [w447,w0,w1,w2,w3,w4,w29] (N [w447,w0,w1,w2,w3,w4] L L) L) (N [w7,w10,w0,w18,w2,w3,w4] (N [w7,w35,w0,w1,w2,w3,w4] L L) L))))) (N [w7,w0,w408,w1,w2,w3,w4] (N [w7,w14,w0,w20,w1,w2,w4] (N [w7,w12,w0,w1,w2,w3,w4] (N [w7,w423,w0,w1,w2,w3,w4] (N [w7,w427,w0,w1,w2,w3,w4] (N [w7,w10,w0,w2,w3,w4,w11] L L) (N [w7,w434,w0,w1,w2,w3,w4] L L)) (N [w7,w12,w0,w18,w1,w3,w4] (N [w7,w42,w0,w1,w2,w3,w4] L L) L)) (N [w7,w12,w1,w3,w4,w13] (N [w7,w12,w1,w2,w3,w4,w13] (N [w7,w12,w0,w1,w3,w4,w13] L L) L) (N [w7,w44,w0,w1,w2,w3,w4] (N [w7,w62,w0,w1,w2,w3,w4] L L) L))) (N [w7,w441,w0,w1,w2,w3,w4] (N [w7,w14,w0,w1,w2,w4,w15] (N [w7,w14,w0,w1,w2,w115,w4] (N [w7,w14,w0,w1,w24,w2,w4] L L) L) (N [w7,w429,w0,w1,w2,w3,w4] (N [w7,w14,w0,w1,w2,w4,w29] L L) L)) (N [w7,w150,w0,w1,w2,w3,w4] (N [w7,w84,w0,w1,w2,w3,w4] (N [w7,w426,w0,w1,w2,w3,w4] L L) L) (N [w7,w0,w414,w1,w2,w3,w4] (N [w7,w91,w0,w1,w2,w3,w4] L L) L)))) (N [w7,w0,w86,w1,w2,w3,w4] (N [w7,w0,w18,w19,w3,w4] (N [w7,w0,w18,w1,w2,w3,w4] (N [w7,w0,w49,w1,w2,w3,w4] (N [w7,w0,w111,w1,w2,w3,w4] L L) L) (N [w7,w0,w18,w2,w19,w3,w4] (N [w7,w0,w18,w1,w19,w3,w4] L L) L)) (N [w7,w0,w20,w1,w2,w4,w21] (N [w7,w0,w20,w1,w2,w3,w59] (N [w7,w0,w58,w1,w2,w3,w4] L L) L) (N [w7,w0,w75,w1,w2,w3,w4] (N [w7,w0,w442,w1,w2,w3,w4] L L) L))) (N [w7,w0,w1,w433,w2,w3,w4] (N [w7,w0,w98,w2,w3,w4] (N [w7,w0,w98,w1,w2,w3,w4] (N [w7,w0,w92,w1,w2,w3,w4] L L) L) (N [w7,w0,w1,w435,w2,w3,w4] (N [w7,w0,w98,w2,w3,w4,w13] L L) L)) (N [w7,w0,w1,w113,w2,w3,w4] (N [w7,w0,w1,w419,w2,w3,w4] (N [w7,w0,w1,w415,w2,w3,w4] L L) L) (N [w7,w0,w1,w24,w2,w3,w4] (N [w7,w0,w1,w71,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRRL = true := by decide +kernel
def tbl_6_0LRRR : STree := (N [w7,w0,w1,w2,w3,w4,w428] (N [w7,w0,w1,w2,w153,w4] (N [w7,w0,w1,w2,w19,w3,w4] (N [w7,w0,w1,w97,w3,w4,w11] (N [w7,w0,w1,w93,w2,w3,w4] (N [w7,w0,w1,w77,w2,w3,w4] (N [w7,w0,w1,w24,w2,w4,w25] L L) (N [w7,w0,w1,w85,w2,w3,w4] L L)) (N [w7,w0,w1,w97,w3,w4] (N [w7,w0,w1,w97,w2,w3,w4] L L) L)) (N [w7,w0,w1,w2,w56,w3,w4] (N [w7,w0,w1,w2,w57,w3,w4] (N [w7,w0,w1,w2,w64,w3,w4] L L) L) (N [w7,w0,w1,w2,w33,w3,w4] (N [w7,w0,w1,w2,w34,w3,w4] L L) L))) (N [w7,w0,w1,w2,w88,w3,w4] (N [w7,w0,w1,w2,w443,w3,w4] (N [w7,w0,w1,w2,w28,w29] (N [w7,w0,w1,w2,w28,w3,w29] L L) L) (N [w7,w0,w1,w2,w80,w3,w4] (N [w7,w0,w1,w2,w440,w3,w4] L L) L)) (N [w7,w0,w1,w2,w99,w4] (N [w7,w0,w1,w2,w99,w3,w4] (N [w7,w0,w1,w2,w222,w3,w4] L L) L) (N [w7,w0,w1,w2,w153,w3,w4] (N [w7,w0,w1,w2,w99,w4,w11] L L) L)))) (N [w7,w0,w1,w2,w3,w4,w430] (N [w7,w0,w1,w2,w3,w4,w69] (N [w7,w0,w1,w2,w3,w410,w4] (N [w7,w0,w1,w2,w3,w420,w4] (N [w7,w0,w1,w2,w153,w4,w13] L L) L) (N [w7,w0,w1,w2,w3,w115,w4] (N [w7,w0,w1,w2,w3,w418,w4] L L) L)) (N [w7,w0,w1,w2,w3,w4,w46] (N [w7,w0,w1,w2,w3,w4,w143] (N [w7,w0,w1,w2,w3,w4,w36] L L) L) (N [w7,w0,w1,w2,w3,w4,w288] (N [w7,w0,w1,w2,w3,w4,w55] L L) L))) (N [w7,w0,w1,w2,w3,w4,w72] (N [w7,w0,w1,w2,w3,w4,w60] (N [w7,w0,w1,w2,w3,w4,w70] (N [w7,w0,w1,w2,w3,w4,w50] L L) L) (N [w7,w0,w1,w2,w3,w4,w436] (N [w7,w0,w1,w2,w3,w4,w41] L L) L)) (N [w7,w0,w1,w2,w3,w4,w25] (N [w7,w0,w1,w2,w3,w4,w43] (N [w7,w0,w1,w2,w3,w4,w207] L L) L) (N [w7,w0,w1,w2,w3,w4,w48] (N [w7,w0,w1,w2,w3,w4,w444] L L) L))))) (N [w231,w0,w1,w2,w3,w4] (N [w7,w0,w1,w2,w3,w27,w29] (N [w7,w0,w1,w2,w3,w4,w94] (N [w7,w0,w1,w2,w3,w4,w65] (N [w7,w0,w1,w2,w3,w4,w13] (N [w7,w0,w1,w2,w3,w4,w76] L L) (N [w7,w0,w1,w2,w3,w4,w78] L L)) (N [w7,w0,w1,w2,w3,w4,w89] (N [w7,w0,w1,w2,w3,w4,w63] L L) L)) (N [w7,w0,w1,w2,w3,w59] (N [w7,w0,w1,w2,w3,w117,w27] (N [w7,w0,w1,w2,w3,w4,w81] L L) L) (N [w7,w0,w1,w2,w3,w140] (N [w7,w0,w1,w2,w3,w23,w29] L L) L))) (N [w239,w0,w1,w2,w3,w4] (N [w239,w0,w1,w97,w2,w3,w4] (N [w7,w111,w1,w2,w3,w4,w13] (N [w7,w0,w113,w2,w19,w3,w4] L L) L) (N [w239,w0,w1,w97,w3,w4,w11] (N [w239,w0,w1,w97,w3,w4] L L) L)) (N [w234,w0,w1,w2,w3,w4] (N [w234,w0,w1,w93,w2,w3,w4] (N [w239,w0,w1,w2,w3,w4,w11] L L) L) (N [w231,w0,w1,w230,w2,w3,w4] (N [w234,w0,w1,w2,w3,w4,w29] L L) L)))) (N [w454,w0,w1,w26,w2,w4] (N [w449,w0,w1,w26,w2,w3,w4] (N [w227,w0,w1,w2,w3,w4] (N [w227,w0,w1,w226,w2,w3,w4] (N [w231,w0,w1,w2,w3,w4,w23] L L) L) (N [w449,w54,w0,w1,w2,w3,w4] (N [w227,w0,w1,w2,w3,w4,w17] L L) L)) (N [w454,w54,w0,w1,w2,w3,w4] (N [w454,w54,w0,w1,w26,w2,w4] (N [w449,w0,w1,w2,w3,w4] L L) L) (N [w454,w0,w1,w26,w2,w3,w4] (N [w454,w54,w0,w1,w2,w4] L L) L))) (N [w54,w14,w0,w1,w2,w3,w4] (N [w54,w10,w0,w1,w2,w3,w4] (N [w454,w0,w1,w2,w4] (N [w454,w0,w1,w2,w3,w4] L L) L) (N [w54,w12,w0,w1,w2,w3,w4] (N [w54,w131,w0,w1,w2,w3,w4] L L) L)) (N [w54,w0,w450,w1,w2,w3,w4] (N [w54,w16,w0,w1,w2,w3,w4] (N [w54,w16,w0,w1,w26,w2,w3] L L) L) (N [w54,w0,w18,w1,w2,w3,w4] (N [w54,w0,w51,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRRR = true := by decide +kernel
def tbl_6_0LRR : STree := N [w7,w0,w1,w24,w2,w3,w140] tbl_6_0LRRL tbl_6_0LRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LRRL chk_tbl_6_0LRRR
def tbl_6_0LR : STree := N [w114,w0,w1,w2,w3,w4,w23] tbl_6_0LRL tbl_6_0LRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0LR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0LR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LRL chk_tbl_6_0LRR
def tbl_6_0L : STree := N [w9,w0,w1,w2,w99,w4,w11] tbl_6_0LL tbl_6_0LR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0L : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0L = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0LL chk_tbl_6_0LR
def tbl_6_0RLLL : STree := (N [w47,w0,w1,w2,w3,w4,w29] (N [w201,w0,w1,w24,w2,w3,w4] (N [w54,w0,w1,w2,w3,w4,w211] (N [w54,w0,w1,w26,w2,w4,w207] (N [w54,w0,w1,w24,w2,w3,w4] (N [w54,w0,w1,w452,w2,w3,w4] (N [w54,w0,w22,w1,w2,w3,w4] L L) (N [w54,w0,w1,w71,w2,w3,w4] L L)) (N [w54,w0,w1,w26,w2,w3,w27] (N [w54,w0,w1,w26,w2,w3,w4] L L) L)) (N [w54,w0,w1,w2,w28,w3,w4] (N [w54,w0,w1,w2,w19,w3,w4] (N [w54,w0,w1,w2,w208,w3,w4] L L) L) (N [w54,w0,w1,w2,w3,w4,w15] (N [w54,w0,w1,w2,w3,w455,w4] L L) L))) (N [w54,w0,w1,w2,w3,w4,w27] (N [w54,w0,w1,w2,w3,w4,w207] (N [w54,w0,w1,w2,w3,w4,w21] (N [w54,w0,w1,w2,w3,w4,w17] L L) L) (N [w54,w0,w1,w2,w3,w4,w23] (N [w54,w0,w1,w2,w3,w4,w25] L L) L)) (N [w54,w0,w1,w2,w3,w4,w13] (N [w54,w0,w1,w2,w3,w4,w11] (N [w54,w0,w1,w2,w3,w4,w29] L L) L) (N [w201,w0,w1,w71,w2,w3,w4] (N [w54,w0,w1,w2,w4,w207] L L) L)))) (N [w47,w0,w458,w1,w2,w3,w4] (N [w457,w0,w18,w1,w2,w3,w4] (N [w460,w0,w18,w1,w2,w3,w4] (N [w201,w0,w1,w2,w3,w4] (N [w201,w0,w1,w2,w28,w3,w4] L L) (N [w460,w47,w0,w1,w2,w3,w4] L L)) (N [w457,w47,w0,w1,w2,w3,w4] (N [w460,w0,w1,w2,w3,w4] L L) L)) (N [w47,w10,w0,w18,w2,w3,w4] (N [w47,w32,w0,w1,w2,w3,w4] (N [w457,w0,w1,w2,w3,w4] L L) L) (N [w47,w14,w0,w1,w2,w3,w4] (N [w47,w10,w0,w1,w2,w3,w4] L L) L))) (N [w47,w0,w1,w2,w19,w3,w4] (N [w47,w0,w18,w1,w19,w3,w4] (N [w47,w0,w18,w1,w2,w3,w4] (N [w47,w0,w49,w1,w2,w3,w4] L L) L) (N [w47,w0,w20,w1,w2,w3,w4] (N [w47,w0,w18,w19,w3,w4] L L) L)) (N [w47,w0,w1,w2,w3,w4,w15] (N [w47,w0,w1,w2,w3,w461,w4] (N [w47,w0,w1,w2,w28,w3,w4] L L) L) (N [w47,w0,w1,w2,w3,w4,w21] (N [w47,w0,w1,w2,w3,w4,w50] L L) L))))) (N [w122,w14,w0,w1,w2,w3,w4] (N [w464,w5,w0,w1,w2,w3,w4] (N [w468,w122,w0,w1,w2,w3,w4] (N [w187,w0,w18,w1,w2,w3,w4] (N [w47,w0,w1,w2,w3,w4,w11] (N [w47,w0,w1,w2,w3,w4,w48] L L) (N [w187,w0,w51,w1,w2,w3,w4] L L)) (N [w187,w0,w1,w2,w3,w4] (N [w187,w0,w22,w1,w2,w3,w4] L L) L)) (N [w468,w0,w1,w2,w3,w4] (N [w468,w0,w1,w2,w28,w3,w4] (N [w468,w5,w0,w1,w2,w3,w4] L L) L) (N [w464,w118,w0,w1,w2,w3,w4] (N [w464,w122,w0,w1,w2,w3,w4] L L) L))) (N [w122,w5,w0,w1,w2,w3,w4] (N [w122,w124,w0,w1,w2,w3,w4] (N [w464,w0,w1,w2,w3,w4] (N [w464,w0,w20,w1,w2,w3,w4] L L) L) (N [w122,w5,w14,w0,w1,w2,w4] (N [w122,w118,w0,w1,w2,w3,w4] L L) L)) (N [w122,w39,w14,w0,w1,w2,w4] (N [w122,w5,w0,w1,w2,w123,w4] (N [w122,w5,w0,w1,w2,w3,w469] L L) L) (N [w122,w10,w0,w1,w2,w3,w4] (N [w122,w39,w0,w1,w2,w3,w4] L L) L)))) (N [w122,w0,w1,w2,w3,w4,w469] (N [w122,w0,w1,w465,w2,w3,w4] (N [w122,w0,w18,w1,w2,w3,w4] (N [w122,w16,w0,w1,w2,w3,w4] (N [w122,w14,w0,w1,w2,w4] L L) L) (N [w122,w0,w22,w1,w2,w3,w4] (N [w122,w0,w20,w1,w2,w3,w4] L L) L)) (N [w122,w0,w1,w2,w28,w3,w4] (N [w122,w0,w1,w2,w19,w3,w4] (N [w122,w0,w1,w119,w2,w3,w4] L L) L) (N [w122,w0,w1,w2,w3,w4] (N [w122,w0,w1,w2,w3,w123,w4] L L) L))) (N [w122,w0,w1,w2,w3,w4,w29] (N [w122,w0,w1,w2,w3,w4,w17] (N [w122,w0,w1,w2,w3,w4,w15] (N [w122,w0,w1,w2,w3,w4,w125] L L) L) (N [w122,w0,w1,w2,w3,w4,w23] (N [w122,w0,w1,w2,w3,w4,w21] L L) L)) (N [w122,w0,w1,w2,w123,w4] (N [w122,w0,w1,w2,w3,w469] (N [w122,w0,w1,w2,w3,w4,w11] L L) L) (N [w471,w5,w0,w1,w2,w3,w4] (N [w471,w118,w0,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLLL = true := by decide +kernel
def tbl_6_0RLLR : STree := (N [w5,w14,w0,w1,w2,w4,w29] (N [w118,w0,w1,w2,w3,w4,w25] (N [w118,w0,w20,w1,w2,w3,w4] (N [w118,w30,w0,w1,w2,w3,w4] (N [w118,w5,w0,w1,w2,w3,w4] (N [w118,w120,w0,w1,w2,w3,w4] (N [w471,w0,w1,w2,w3,w4] L L) (N [w118,w5,w10,w0,w2,w3,w4] L L)) (N [w118,w30,w10,w0,w2,w3,w4] (N [w118,w5,w0,w119,w2,w3,w4] L L) L)) (N [w118,w12,w0,w1,w2,w3,w4] (N [w118,w10,w0,w2,w3,w4] (N [w118,w10,w0,w1,w2,w3,w4] L L) L) (N [w118,w0,w18,w1,w2,w3,w4] (N [w118,w14,w0,w1,w2,w3,w4] L L) L))) (N [w118,w0,w1,w2,w28,w3,w4] (N [w118,w0,w1,w2,w472,w3,w4] (N [w118,w0,w1,w24,w2,w3,w4] (N [w118,w0,w1,w119,w2,w3,w4] L L) L) (N [w118,w0,w1,w2,w19,w3,w4] (N [w118,w0,w1,w2,w121,w3,w4] L L) L)) (N [w118,w0,w1,w2,w3,w4] (N [w118,w0,w1,w2,w3,w123,w4] (N [w118,w0,w1,w2,w3,w474,w4] L L) L) (N [w118,w0,w1,w2,w3,w4,w21] (N [w118,w0,w1,w2,w3,w4,w15] L L) L)))) (N [w493,w0,w1,w2,w3,w4] (N [w492,w0,w1,w2,w3,w4] (N [w118,w0,w1,w2,w3,w4,w13] (N [w118,w0,w1,w2,w3,w4,w11] (N [w118,w0,w1,w2,w3,w4,w29] L L) L) (N [w492,w5,w0,w1,w2,w3,w4] (N [w118,w0,w119,w2,w3,w4] L L) L)) (N [w485,w0,w1,w2,w19,w3,w4] (N [w485,w5,w0,w1,w2,w3,w4] (N [w492,w0,w1,w2,w3,w4,w21] L L) L) (N [w493,w5,w0,w1,w2,w3,w4] (N [w485,w0,w1,w2,w3,w4] L L) L))) (N [w5,w10,w0,w2,w3,w4,w11] (N [w5,w35,w0,w1,w2,w3,w4] (N [w5,w32,w0,w1,w2,w3,w4] (N [w493,w0,w1,w2,w3,w4,w29] L L) L) (N [w5,w10,w0,w1,w2,w3,w4] (N [w5,w10,w0,w18,w2,w3,w4] L L) L)) (N [w5,w14,w0,w20,w1,w2,w4] (N [w5,w44,w0,w1,w2,w3,w4] (N [w5,w62,w0,w1,w2,w3,w4] L L) L) (N [w5,w14,w0,w1,w2,w4,w15] (N [w5,w14,w0,w1,w2,w3,w4] L L) L))))) (N [w5,w0,w1,w2,w64,w3,w4] (N [w5,w0,w481,w1,w2,w3,w4] (N [w5,w0,w479,w1,w2,w3,w4] (N [w5,w0,w18,w1,w121,w3,w4] (N [w5,w91,w0,w1,w2,w3,w4] (N [w5,w84,w0,w1,w2,w3,w4] L L) (N [w5,w0,w49,w1,w2,w3,w4] L L)) (N [w5,w0,w18,w19,w3,w4] (N [w5,w0,w18,w1,w19,w3,w4] L L) L)) (N [w5,w0,w20,w1,w2,w3,w59] (N [w5,w0,w58,w1,w2,w3,w4] (N [w5,w0,w477,w1,w2,w3,w4] L L) L) (N [w5,w0,w20,w1,w2,w4,w21] (N [w5,w0,w20,w1,w2,w123,w4] L L) L))) (N [w5,w0,w98,w1,w2,w3,w4] (N [w5,w0,w75,w1,w2,w3,w4] (N [w5,w0,w478,w1,w2,w3,w4] (N [w5,w0,w487,w1,w2,w3,w4] L L) L) (N [w5,w0,w92,w1,w2,w3,w4] (N [w5,w0,w86,w1,w2,w3,w4] L L) L)) (N [w5,w0,w1,w465,w2,w3,w4] (N [w5,w0,w98,w2,w3,w4,w13] (N [w5,w0,w98,w2,w3,w4] L L) L) (N [w5,w0,w1,w119,w2,w3,w4] (N [w5,w0,w1,w473,w2,w3,w4] L L) L)))) (N [w5,w0,w1,w2,w99,w4,w11] (N [w5,w0,w1,w2,w490,w3,w4] (N [w5,w0,w1,w2,w480,w3,w4] (N [w5,w0,w1,w2,w34,w3,w4] (N [w5,w0,w1,w2,w57,w3,w4] L L) L) (N [w5,w0,w1,w2,w28,w29] (N [w5,w0,w1,w2,w28,w3,w29] L L) L)) (N [w5,w0,w1,w2,w88,w3,w4] (N [w5,w0,w1,w2,w80,w3,w4] (N [w5,w0,w1,w2,w486,w3,w4] L L) L) (N [w5,w0,w1,w2,w99,w4] (N [w5,w0,w1,w2,w99,w3,w4] L L) L))) (N [w5,w0,w1,w2,w3,w4,w46] (N [w5,w0,w1,w2,w3,w123,w4] (N [w5,w0,w1,w2,w3,w470,w4] (N [w5,w0,w1,w2,w3,w474,w4] L L) L) (N [w5,w0,w1,w2,w3,w4,w36] (N [w5,w0,w1,w2,w3,w4,w69] L L) L)) (N [w5,w0,w1,w2,w3,w4,w50] (N [w5,w0,w1,w2,w3,w4,w15] (N [w5,w0,w1,w2,w3,w4,w55] L L) L) (N [w5,w0,w1,w2,w3,w4,w60] (N [w5,w0,w1,w2,w3,w4,w70] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLLR = true := by decide +kernel
def tbl_6_0RLL : STree := N [w471,w0,w18,w1,w2,w3,w4] tbl_6_0RLLL tbl_6_0RLLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RLLL chk_tbl_6_0RLLR
def tbl_6_0RLRL : STree := (N [w40,w0,w1,w2,w3,w4,w29] (N [w494,w40,w0,w1,w2,w3,w4] (N [w5,w0,w1,w2,w3,w59] (N [w5,w0,w1,w2,w3,w4,w63] (N [w5,w0,w1,w2,w3,w4,w11] (N [w5,w0,w1,w2,w3,w4,w491] (N [w5,w0,w1,w2,w3,w4,w482] L L) (N [w5,w0,w1,w2,w3,w4,w48] L L)) (N [w5,w0,w1,w2,w3,w4,w65] (N [w5,w0,w1,w2,w3,w4,w76] L L) L)) (N [w5,w0,w1,w2,w3,w469] (N [w5,w0,w1,w2,w3,w4,w81] (N [w5,w0,w1,w2,w3,w4,w89] L L) L) (N [w5,w0,w1,w2,w3,w125,w29] (N [w5,w0,w1,w2,w3,w125,w17] L L) L))) (N [w179,w178,w0,w1,w2,w3,w4] (N [w183,w91,w0,w1,w2,w3,w4] (N [w5,w0,w1,w121,w3,w4,w13] (N [w5,w0,w1,w2,w3,w23,w29] L L) L) (N [w183,w0,w1,w2,w3,w4,w29] (N [w183,w0,w1,w2,w3,w4] L L) L)) (N [w499,w40,w0,w1,w2,w3,w4] (N [w179,w0,w1,w2,w3,w4,w27] (N [w179,w0,w1,w2,w3,w4] L L) L) (N [w499,w0,w1,w2,w3,w4] (N [w499,w16,w0,w1,w2,w3,w4] L L) L)))) (N [w40,w0,w20,w1,w2,w3,w4] (N [w40,w14,w0,w1,w2,w3,w4] (N [w40,w37,w0,w1,w2,w3,w4] (N [w494,w0,w1,w2,w3,w4] (N [w494,w16,w0,w1,w2,w3,w4] L L) L) (N [w40,w44,w0,w1,w2,w3,w4] (N [w40,w10,w0,w1,w2,w3,w4] L L) L)) (N [w40,w16,w0,w1,w2,w3,w17] (N [w40,w16,w0,w1,w2,w3,w4] (N [w40,w16,w0,w22,w1,w2,w3] L L) L) (N [w40,w0,w18,w1,w2,w3,w4] (N [w40,w16,w0,w1,w2,w3,w29] L L) L))) (N [w40,w0,w1,w2,w3,w4,w46] (N [w40,w0,w1,w2,w19,w3,w4] (N [w40,w0,w1,w495,w2,w3,w4] (N [w40,w0,w22,w1,w2,w3,w4] L L) L) (N [w40,w0,w1,w2,w3,w500,w4] (N [w40,w0,w1,w2,w28,w3,w4] L L) L)) (N [w40,w0,w1,w2,w3,w4,w21] (N [w40,w0,w1,w2,w3,w4,w17] (N [w40,w0,w1,w2,w3,w4,w15] L L) L) (N [w40,w0,w1,w2,w3,w4,w23] (N [w40,w0,w1,w2,w3,w4,w169] L L) L))))) (N [w31,w0,w1,w24,w2,w3,w4] (N [w505,w12,w0,w1,w2,w3,w4] (N [w155,w0,w1,w2,w19,w3,w4] (N [w160,w0,w1,w2,w28,w3,w4] (N [w160,w44,w0,w1,w2,w3,w4] (N [w40,w0,w1,w2,w3,w4,w11] L L) (N [w160,w14,w0,w1,w2,w3,w4] L L)) (N [w155,w62,w0,w1,w2,w3,w4] (N [w160,w0,w1,w2,w3,w4] L L) L)) (N [w502,w12,w0,w1,w2,w3,w4] (N [w502,w31,w0,w1,w2,w3,w4] (N [w155,w0,w1,w2,w3,w4] L L) L) (N [w505,w31,w0,w1,w2,w3,w4] (N [w502,w0,w1,w2,w3,w4] L L) L))) (N [w31,w12,w0,w1,w2,w3,w4] (N [w31,w10,w0,w1,w2,w3,w4] (N [w31,w32,w0,w1,w2,w3,w4] (N [w505,w0,w1,w2,w3,w4] L L) L) (N [w31,w12,w0,w18,w1,w3,w4] (N [w31,w42,w0,w1,w2,w3,w4] L L) L)) (N [w31,w0,w18,w1,w2,w3,w4] (N [w31,w14,w0,w1,w2,w3,w4] (N [w31,w12,w0,w1,w3,w4,w13] L L) L) (N [w31,w0,w1,w503,w2,w3,w4] (N [w31,w0,w20,w1,w2,w3,w4] L L) L)))) (N [w132,w131,w0,w1,w2,w3,w4] (N [w31,w0,w1,w2,w3,w4,w15] (N [w31,w0,w1,w2,w28,w3,w4] (N [w31,w0,w1,w2,w19,w3,w4] (N [w31,w0,w1,w2,w34,w3,w4] L L) L) (N [w31,w0,w1,w2,w3,w4,w143] (N [w31,w0,w1,w2,w3,w506,w4] L L) L)) (N [w31,w0,w1,w2,w3,w4,w29] (N [w31,w0,w1,w2,w3,w4,w25] (N [w31,w0,w1,w2,w3,w4,w21] L L) L) (N [w31,w0,w1,w2,w3,w4,w13] (N [w31,w0,w1,w2,w3,w4,w11] L L) L))) (N [w126,w10,w0,w1,w2,w3,w4] (N [w132,w0,w1,w26,w2,w3,w4] (N [w132,w16,w0,w1,w2,w3,w4] (N [w132,w12,w0,w1,w2,w3,w4] L L) L) (N [w126,w32,w0,w1,w2,w3,w4] (N [w132,w0,w1,w2,w3,w4] L L) L)) (N [w32,w10,w0,w1,w2,w3,w4] (N [w126,w0,w1,w2,w3,w4] (N [w126,w0,w18,w1,w2,w3,w4] L L) L) (N [w32,w0,w1,w2,w3,w4] (N [w32,w0,w18,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLRL = true := by decide +kernel
def tbl_6_0RLRR : STree := (N [w423,w0,w1,w2,w3,w4] (N [w10,w0,w1,w2,w3,w109,w4] (N [w10,w0,w20,w1,w2,w3,w4] (N [w10,w14,w0,w1,w2,w3,w4] (N [w10,w367,w0,w1,w2,w3,w4] (N [w35,w0,w20,w1,w2,w3,w4] (N [w35,w14,w0,w1,w2,w3,w4] L L) (N [w35,w0,w1,w2,w3,w4] L L)) (N [w10,w12,w0,w1,w2,w3,w4] (N [w10,w423,w0,w1,w2,w3,w4] L L) L)) (N [w10,w0,w103,w1,w2,w3,w4] (N [w10,w0,w424,w1,w2,w3,w4] (N [w10,w0,w111,w1,w2,w3,w4] L L) L) (N [w10,w0,w18,w2,w3,w4] (N [w10,w0,w18,w1,w2,w3,w4] L L) L))) (N [w10,w0,w1,w2,w107,w3,w4] (N [w10,w0,w1,w113,w2,w3,w4] (N [w10,w0,w1,w105,w2,w3,w4] (N [w10,w0,w1,w119,w2,w3,w4] L L) L) (N [w10,w0,w1,w2,w121,w3,w4] (N [w10,w0,w1,w24,w2,w3,w4] L L) L)) (N [w10,w0,w1,w2,w33,w3,w4] (N [w10,w0,w1,w2,w504,w3,w4] (N [w10,w0,w1,w2,w402,w3,w4] L L) L) (N [w10,w0,w1,w2,w28,w3,w4] (N [w10,w0,w1,w2,w19,w3,w4] L L) L)))) (N [w10,w0,w1,w2,w3,w4,w13] (N [w10,w0,w1,w2,w3,w4,w36] (N [w10,w0,w1,w2,w3,w123,w4] (N [w10,w0,w1,w2,w3,w425,w4] (N [w10,w0,w1,w2,w3,w115,w4] L L) L) (N [w10,w0,w1,w2,w3,w4] (N [w10,w0,w1,w2,w3,w507,w4] L L) L)) (N [w10,w0,w1,w2,w3,w4,w25] (N [w10,w0,w1,w2,w3,w4,w21] (N [w10,w0,w1,w2,w3,w4,w15] L L) L) (N [w10,w0,w1,w2,w3,w4,w11] (N [w10,w0,w1,w2,w3,w4,w29] L L) L))) (N [w380,w0,w1,w2,w3,w4] (N [w427,w0,w111,w1,w2,w3,w4] (N [w10,w0,w2,w3,w4,w11] (N [w10,w0,w113,w2,w3,w4] L L) L) (N [w380,w0,w1,w105,w2,w3,w4] (N [w427,w0,w1,w2,w3,w4] L L) L)) (N [w367,w0,w1,w2,w3,w4] (N [w371,w0,w1,w2,w3,w4] (N [w371,w0,w103,w1,w2,w3,w4] L L) L) (N [w434,w0,w1,w2,w3,w4] (N [w434,w0,w1,w113,w2,w3,w4] L L) L))))) (N [w14,w0,w1,w2,w3,w123,w4] (N [w14,w0,w20,w1,w2,w3,w4] (N [w14,w368,w0,w1,w2,w3,w4] (N [w44,w0,w1,w2,w28,w3,w4] (N [w62,w0,w1,w2,w3,w4] (N [w62,w0,w1,w2,w19,w3,w4] L L) (N [w44,w14,w0,w1,w2,w3,w4] L L)) (N [w14,w426,w0,w1,w2,w3,w4] (N [w44,w0,w1,w2,w3,w4] L L) L)) (N [w14,w0,w103,w1,w2,w3,w4] (N [w14,w0,w111,w1,w2,w3,w4] (N [w14,w16,w0,w1,w2,w3,w4] L L) L) (N [w14,w0,w18,w1,w2,w3,w4] (N [w14,w0,w369,w1,w2,w3,w4] L L) L))) (N [w14,w0,w1,w496,w2,w3,w4] (N [w14,w0,w1,w119,w2,w3,w4] (N [w14,w0,w22,w1,w2,w3,w4] (N [w14,w0,w20,w1,w2,w4] L L) L) (N [w14,w0,w1,w370,w2,w3,w4] (N [w14,w0,w1,w105,w2,w3,w4] L L) L)) (N [w14,w0,w1,w2,w28,w3,w4] (N [w14,w0,w1,w2,w19,w3,w4] (N [w14,w0,w1,w113,w2,w3,w4] L L) L) (N [w14,w0,w1,w2,w3,w115,w4] (N [w14,w0,w1,w2,w3,w109,w4] L L) L)))) (N [w14,w0,w1,w2,w3,w4,w29] (N [w14,w0,w1,w2,w3,w4,w15] (N [w14,w0,w1,w2,w3,w4,w117] (N [w14,w0,w1,w2,w3,w4,w338] (N [w14,w0,w1,w2,w3,w4] L L) L) (N [w14,w0,w1,w2,w3,w4,w501] (N [w14,w0,w1,w2,w3,w4,w125] L L) L)) (N [w14,w0,w1,w2,w3,w4,w41] (N [w14,w0,w1,w2,w3,w4,w17] (N [w14,w0,w1,w2,w3,w4,w45] L L) L) (N [w14,w0,w1,w2,w3,w4,w23] (N [w14,w0,w1,w2,w3,w4,w21] L L) L))) (N [w429,w0,w1,w2,w3,w4] (N [w14,w0,w1,w2,w4,w15] (N [w14,w0,w1,w2,w115,w4] (N [w14,w0,w1,w2,w3,w4,w11] L L) L) (N [w429,w0,w111,w1,w2,w3,w4] (N [w14,w0,w1,w2,w4,w29] L L) L)) (N [w441,w0,w1,w2,w3,w115,w4] (N [w386,w0,w1,w2,w3,w4] (N [w386,w0,w1,w2,w3,w109,w4] L L) L) (N [w426,w0,w1,w2,w3,w4] (N [w441,w0,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLRR = true := by decide +kernel
def tbl_6_0RLR : STree := N [w35,w10,w0,w1,w2,w3,w4] tbl_6_0RLRL tbl_6_0RLRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RLR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RLRL chk_tbl_6_0RLRR
def tbl_6_0RL : STree := N [w5,w0,w1,w2,w3,w4,w41] tbl_6_0RLL tbl_6_0RLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RLL chk_tbl_6_0RLR
def tbl_6_0RRLL : STree := (N [w0,w103,w1,w2,w3,w4,w29] (N [w0,w111,w1,w2,w3,w4,w15] (N [w0,w340,w1,w2,w3,w4] (N [w91,w0,w1,w2,w3,w4] (N [w368,w0,w1,w2,w3,w4] (N [w375,w0,w1,w2,w3,w4] (N [w375,w0,w103,w1,w2,w4] L L) (N [w375,w0,w1,w2,w4] L L)) (N [w84,w0,w1,w2,w3,w4,w21] (N [w84,w0,w1,w2,w3,w4] L L) L)) (N [w0,w333,w1,w2,w3,w4,w29] (N [w0,w333,w1,w2,w3,w4] (N [w91,w0,w1,w2,w3,w4,w29] L L) L) (N [w0,w401,w1,w2,w3,w4] (N [w0,w401,w1,w2,w19,w3,w4] L L) L))) (N [w0,w111,w1,w113,w2,w3,w4] (N [w0,w408,w1,w2,w3,w4] (N [w0,w414,w1,w2,w3,w4] (N [w0,w340,w1,w2,w3,w4,w27] L L) L) (N [w0,w111,w20,w1,w2,w3,w4] (N [w0,w111,w18,w1,w2,w3,w4] L L) L)) (N [w0,w111,w1,w2,w28,w3,w4] (N [w0,w111,w1,w2,w19,w3,w4] (N [w0,w111,w1,w24,w2,w3,w4] L L) L) (N [w0,w111,w1,w2,w3,w4] (N [w0,w111,w1,w2,w3,w115,w4] L L) L)))) (N [w0,w103,w20,w1,w2,w3,w4] (N [w0,w111,w1,w2,w3,w4,w13] (N [w0,w111,w1,w2,w3,w4,w29] (N [w0,w111,w1,w2,w3,w4,w21] (N [w0,w111,w1,w2,w3,w4,w430] L L) (N [w0,w111,w1,w2,w3,w4,w25] L L)) (N [w0,w111,w1,w2,w3,w4,w428] (N [w0,w111,w1,w2,w3,w4,w11] L L) L)) (N [w0,w357,w1,w2,w3,w4] (N [w0,w458,w1,w2,w3,w4] (N [w0,w458,w18,w1,w2,w3,w4] L L) L) (N [w0,w103,w18,w1,w2,w3,w4] (N [w0,w363,w1,w2,w3,w4] L L) L))) (N [w0,w103,w1,w2,w3,w4] (N [w0,w103,w1,w2,w19,w3,w4] (N [w0,w103,w1,w105,w2,w3,w4] (N [w0,w103,w22,w1,w2,w3,w4] L L) L) (N [w0,w103,w1,w2,w3,w109,w4] (N [w0,w103,w1,w2,w28,w3,w4] L L) L)) (N [w0,w103,w1,w2,w3,w4,w17] (N [w0,w103,w1,w2,w3,w4,w376] (N [w0,w103,w1,w2,w3,w4,w15] L L) L) (N [w0,w103,w1,w2,w3,w4,w23] (N [w0,w103,w1,w2,w3,w4,w21] L L) L))))) (N [w0,w18,w1,w2,w3,w4,w21] (N [w0,w18,w1,w119,w2,w3,w4] (N [w0,w49,w18,w1,w2,w3,w4] (N [w0,w450,w1,w2,w3,w4] (N [w0,w103,w1,w2,w3,w4,w372] (N [w0,w103,w1,w2,w3,w4,w11] L L) (N [w0,w450,w1,w26,w2,w3,w4] L L)) (N [w0,w394,w1,w2,w3,w4] (N [w0,w394,w1,w2,w28,w3,w4] L L) L)) (N [w0,w18,w477,w1,w2,w3,w4] (N [w0,w49,w1,w2,w3,w4] (N [w0,w49,w20,w1,w2,w3,w4] L L) L) (N [w0,w18,w20,w1,w2,w3,w4] (N [w0,w18,w377,w1,w2,w3,w4] L L) L))) (N [w0,w18,w1,w2,w3,w115,w4] (N [w0,w18,w1,w2,w19,w3,w4] (N [w0,w18,w1,w113,w2,w3,w4] (N [w0,w18,w1,w105,w2,w3,w4] L L) L) (N [w0,w18,w1,w2,w3,w109,w4] (N [w0,w18,w1,w2,w28,w3,w4] L L) L)) (N [w0,w18,w1,w2,w3,w4] (N [w0,w18,w1,w2,w3,w123,w4] (N [w0,w18,w1,w2,w3,w461,w4] L L) L) (N [w0,w18,w1,w2,w3,w4,w50] (N [w0,w18,w1,w2,w3,w4,w15] L L) L)))) (N [w0,w377,w1,w2,w3,w4] (N [w0,w18,w19,w3,w4] (N [w0,w18,w1,w2,w3,w4,w11] (N [w0,w18,w1,w2,w3,w4,w48] (N [w0,w18,w1,w2,w3,w4,w29] L L) L) (N [w0,w18,w1,w19,w3,w4] (N [w0,w18,w1,w121,w3,w4] L L) L)) (N [w0,w477,w1,w2,w3,w4] (N [w0,w479,w1,w2,w3,w4] (N [w0,w479,w1,w2,w121,w3,w4] L L) L) (N [w0,w381,w1,w2,w3,w4] (N [w0,w381,w1,w2,w107,w3,w4] L L) L))) (N [w0,w20,w22,w1,w2,w3,w4] (N [w0,w58,w1,w2,w3,w4] (N [w0,w58,w1,w2,w28,w3,w4] (N [w0,w58,w20,w1,w2,w3,w4] L L) L) (N [w0,w20,w478,w1,w2,w3,w4] (N [w0,w20,w378,w1,w2,w3,w4] L L) L)) (N [w0,w20,w1,w370,w2,w3,w4] (N [w0,w20,w1,w105,w2,w3,w4] (N [w0,w20,w1,w119,w2,w3,w4] L L) L) (N [w0,w20,w1,w113,w2,w3,w4] (N [w0,w20,w1,w433,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRLL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRLL = true := by decide +kernel
def tbl_6_0RRLR : STree := (N [w0,w86,w1,w2,w3,w4,w25] (N [w0,w20,w1,w2,w3,w4,w59] (N [w0,w20,w1,w2,w3,w123,w4] (N [w0,w20,w1,w2,w56,w3,w4] (N [w0,w20,w1,w2,w379,w3,w4] (N [w0,w20,w1,w2,w121,w3,w4] (N [w0,w20,w1,w26,w2,w3,w4] L L) (N [w0,w20,w1,w2,w107,w3,w4] L L)) (N [w0,w20,w1,w2,w453,w3,w4] (N [w0,w20,w1,w2,w402,w3,w4] L L) L)) (N [w0,w20,w1,w2,w3,w109,w4] (N [w0,w20,w1,w2,w28,w3,w4] (N [w0,w20,w1,w2,w19,w3,w4] L L) L) (N [w0,w20,w1,w2,w3,w425,w4] (N [w0,w20,w1,w2,w3,w115,w4] L L) L))) (N [w0,w20,w1,w2,w3,w4,w125] (N [w0,w20,w1,w2,w3,w4,w117] (N [w0,w20,w1,w2,w3,w4,w338] (N [w0,w20,w1,w2,w3,w4] L L) L) (N [w0,w20,w1,w2,w3,w4,w456] (N [w0,w20,w1,w2,w3,w4,w439] L L) L)) (N [w0,w20,w1,w2,w3,w4,w17] (N [w0,w20,w1,w2,w3,w4,w15] (N [w0,w20,w1,w2,w3,w4,w55] L L) L) (N [w0,w20,w1,w2,w3,w4,w25] (N [w0,w20,w1,w2,w3,w4,w21] L L) L)))) (N [w0,w387,w1,w2,w3,w4] (N [w0,w20,w1,w2,w3,w59] (N [w0,w20,w1,w2,w3,w4,w29] (N [w0,w20,w1,w2,w3,w4,w27] (N [w0,w20,w1,w2,w3,w4,w23] L L) L) (N [w0,w20,w1,w2,w3,w4,w13] (N [w0,w20,w1,w2,w3,w4,w11] L L) L)) (N [w0,w481,w1,w119,w2,w3,w4] (N [w0,w20,w1,w2,w4,w21] (N [w0,w20,w1,w2,w123,w4] L L) L) (N [w0,w387,w1,w2,w3,w109,w4] (N [w0,w481,w1,w2,w3,w4] L L) L))) (N [w0,w487,w1,w2,w3,w123,w4] (N [w0,w378,w1,w2,w3,w4] (N [w0,w383,w1,w2,w3,w4] (N [w0,w383,w1,w105,w2,w3,w4] L L) L) (N [w0,w442,w1,w2,w3,w4] (N [w0,w442,w1,w2,w3,w115,w4] L L) L)) (N [w0,w75,w1,w2,w3,w4] (N [w0,w478,w1,w2,w3,w4] (N [w0,w487,w1,w2,w3,w4] L L) L) (N [w0,w86,w1,w2,w3,w4] (N [w0,w75,w1,w2,w3,w4,w15] L L) L))))) (N [w0,w1,w119,w2,w3,w4,w482] (N [w0,w1,w346,w2,w3,w4] (N [w0,w1,w335,w2,w3,w4] (N [w0,w98,w1,w2,w3,w4,w13] (N [w0,w92,w1,w2,w3,w4,w29] (N [w0,w92,w1,w2,w3,w4] L L) (N [w0,w98,w1,w2,w3,w4] L L)) (N [w0,w98,w2,w3,w4,w13] (N [w0,w98,w2,w3,w4] L L) L)) (N [w0,w1,w326,w2,w3,w4,w13] (N [w0,w1,w326,w2,w3,w4] (N [w0,w1,w335,w2,w3,w4,w29] L L) L) (N [w0,w1,w342,w2,w3,w4,w27] (N [w0,w1,w342,w2,w3,w4] L L) L))) (N [w0,w1,w119,w2,w480,w3,w4] (N [w0,w1,w473,w2,w3,w4] (N [w0,w1,w465,w2,w3,w4] (N [w0,w1,w346,w2,w3,w4,w17] L L) L) (N [w0,w1,w119,w2,w19,w3,w4] (N [w0,w1,w119,w2,w121,w3,w4] L L) L)) (N [w0,w1,w119,w2,w3,w4] (N [w0,w1,w119,w2,w3,w123,w4] (N [w0,w1,w119,w2,w28,w3,w4] L L) L) (N [w0,w1,w119,w2,w3,w4,w21] (N [w0,w1,w119,w2,w3,w4,w15] L L) L)))) (N [w0,w1,w105,w2,w3,w109,w4] (N [w0,w1,w360,w2,w3,w4] (N [w0,w1,w119,w2,w3,w4,w11] (N [w0,w1,w119,w2,w3,w4,w29] (N [w0,w1,w119,w2,w3,w4,w25] L L) L) (N [w0,w1,w352,w2,w3,w4] (N [w0,w1,w119,w2,w3,w4,w13] L L) L)) (N [w0,w1,w105,w2,w19,w3,w4] (N [w0,w1,w105,w2,w107,w3,w4] (N [w0,w1,w364,w2,w3,w4] L L) L) (N [w0,w1,w105,w2,w28,w3,w4] (N [w0,w1,w105,w2,w382,w3,w4] L L) L))) (N [w0,w1,w105,w2,w3,w4,w25] (N [w0,w1,w105,w2,w3,w4,w17] (N [w0,w1,w105,w2,w3,w4,w15] (N [w0,w1,w105,w2,w3,w4] L L) L) (N [w0,w1,w105,w2,w3,w4,w384] (N [w0,w1,w105,w2,w3,w4,w21] L L) L)) (N [w0,w1,w105,w2,w3,w4,w29] (N [w0,w1,w105,w2,w3,w4,w27] (N [w0,w1,w105,w2,w3,w4,w23] L L) L) (N [w0,w1,w105,w2,w3,w4,w372] (N [w0,w1,w105,w2,w3,w4,w11] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRLR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRLR = true := by decide +kernel
def tbl_6_0RRL : STree := N [w0,w20,w1,w24,w2,w3,w4] tbl_6_0RRLL tbl_6_0RRLR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRL = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RRLL chk_tbl_6_0RRLR
def tbl_6_0RRRL : STree := (N [w0,w1,w2,w28,w3,w4,w69] (N [w0,w1,w2,w57,w3,w4] (N [w0,w1,w113,w2,w3,w4,w15] (N [w0,w1,w415,w2,w3,w4] (N [w0,w1,w435,w113,w2,w3,w4] (N [w0,w1,w396,w2,w28,w3,w4] (N [w0,w1,w495,w2,w3,w4] L L) (N [w0,w1,w396,w2,w3,w4] L L)) (N [w0,w1,w433,w2,w3,w4] (N [w0,w1,w435,w2,w3,w4] L L) L)) (N [w0,w1,w113,w2,w28,w3,w4] (N [w0,w1,w113,w2,w19,w3,w4] (N [w0,w1,w419,w2,w3,w4] L L) L) (N [w0,w1,w113,w2,w3,w4] (N [w0,w1,w113,w2,w3,w115,w4] L L) L))) (N [w0,w1,w113,w2,w3,w4,w428] (N [w0,w1,w113,w2,w3,w4,w25] (N [w0,w1,w113,w2,w3,w4,w436] (N [w0,w1,w113,w2,w3,w4,w21] L L) L) (N [w0,w1,w113,w2,w3,w4,w11] (N [w0,w1,w113,w2,w3,w4,w29] L L) L)) (N [w0,w1,w452,w2,w3,w4] (N [w0,w1,w503,w2,w3,w4] (N [w0,w1,w113,w2,w3,w4,w13] L L) L) (N [w0,w1,w2,w64,w3,w4] (N [w0,w1,w2,w64,w19,w3,w4] L L) L)))) (N [w0,w1,w2,w19,w3,w4,w29] (N [w0,w1,w2,w19,w3,w109,w4] (N [w0,w1,w2,w19,w382,w3,w4] (N [w0,w1,w2,w19,w480,w3,w4] (N [w0,w1,w2,w34,w3,w4] L L) L) (N [w0,w1,w2,w19,w3,w404,w4] (N [w0,w1,w2,w19,w28,w3,w4] L L) L)) (N [w0,w1,w2,w19,w3,w4] (N [w0,w1,w2,w19,w3,w123,w4] (N [w0,w1,w2,w19,w3,w115,w4] L L) L) (N [w0,w1,w2,w19,w3,w4,w21] (N [w0,w1,w2,w19,w3,w4,w15] L L) L))) (N [w0,w1,w2,w28,w440,w3,w4] (N [w0,w1,w2,w19,w3,w4,w63] (N [w0,w1,w2,w19,w3,w4,w65] (N [w0,w1,w2,w19,w3,w4,w11] L L) L) (N [w0,w1,w2,w382,w3,w4] (N [w0,w1,w2,w480,w3,w4] L L) L)) (N [w0,w1,w2,w28,w3,w115,w4] (N [w0,w1,w2,w28,w3,w109,w4] (N [w0,w1,w2,w28,w486,w3,w4] L L) L) (N [w0,w1,w2,w28,w3,w4] (N [w0,w1,w2,w28,w3,w123,w4] L L) L))))) (N [w0,w1,w2,w3,w344,w4,w27] (N [w0,w1,w2,w486,w3,w4] (N [w0,w1,w2,w28,w29] (N [w0,w1,w2,w28,w3,w4,w29] (N [w0,w1,w2,w28,w3,w4,w70] (N [w0,w1,w2,w28,w3,w4,w15] L L) (N [w0,w1,w2,w28,w3,w4,w21] L L)) (N [w0,w1,w2,w28,w3,w29] (N [w0,w1,w2,w28,w3,w4,w11] L L) L)) (N [w0,w1,w2,w440,w3,w4] (N [w0,w1,w2,w443,w3,w4,w117] (N [w0,w1,w2,w443,w3,w4] L L) L) (N [w0,w1,w2,w490,w3,w4,w125] (N [w0,w1,w2,w490,w3,w4] L L) L))) (N [w0,w1,w2,w99,w3,w4,w11] (N [w0,w1,w2,w88,w3,w4] (N [w0,w1,w2,w80,w3,w4,w17] (N [w0,w1,w2,w80,w3,w4] L L) L) (N [w0,w1,w2,w99,w3,w4] (N [w0,w1,w2,w88,w3,w4,w23] L L) L)) (N [w0,w1,w2,w3,w350,w4] (N [w0,w1,w2,w99,w4,w11] (N [w0,w1,w2,w99,w4] L L) L) (N [w0,w1,w2,w3,w344,w4] (N [w0,w1,w2,w3,w350,w4,w17] L L) L)))) (N [w0,w1,w2,w3,w109,w4,w23] (N [w0,w1,w2,w3,w109,w4] (N [w0,w1,w2,w3,w329,w4,w13] (N [w0,w1,w2,w3,w329,w4] (N [w0,w1,w2,w3,w404,w4] L L) L) (N [w0,w1,w2,w3,w356,w4] (N [w0,w1,w2,w3,w362,w4] L L) L)) (N [w0,w1,w2,w3,w109,w4,w17] (N [w0,w1,w2,w3,w109,w4,w376] (N [w0,w1,w2,w3,w109,w4,w15] L L) L) (N [w0,w1,w2,w3,w109,w4,w384] (N [w0,w1,w2,w3,w109,w4,w21] L L) L))) (N [w0,w1,w2,w3,w115,w4] (N [w0,w1,w2,w3,w420,w4] (N [w0,w1,w2,w3,w109,w4,w11] (N [w0,w1,w2,w3,w109,w4,w29] L L) L) (N [w0,w1,w2,w3,w418,w4] (N [w0,w1,w2,w3,w410,w4] L L) L)) (N [w0,w1,w2,w3,w115,w4,w430] (N [w0,w1,w2,w3,w115,w4,w15] (N [w0,w1,w2,w3,w115,w4,w117] L L) L) (N [w0,w1,w2,w3,w115,w4,w21] (N [w0,w1,w2,w3,w115,w4,w17] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRRL : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRRL = true := by decide +kernel
def tbl_6_0RRRR : STree := (N [w0,w1,w2,w3,w4,w21,w23] (N [w0,w1,w2,w3,w4,w36] (N [w0,w1,w2,w3,w123,w4,w125] (N [w0,w1,w2,w3,w115,w4,w13] (N [w0,w1,w2,w3,w115,w4,w29] (N [w0,w1,w2,w3,w115,w4,w23] (N [w0,w1,w2,w3,w115,w4,w25] L L) (N [w0,w1,w2,w3,w115,w4,w27] L L)) (N [w0,w1,w2,w3,w115,w4,w11] (N [w0,w1,w2,w3,w115,w4,w444] L L) L)) (N [w0,w1,w2,w3,w474,w4] (N [w0,w1,w2,w3,w461,w4] (N [w0,w1,w2,w3,w455,w4] L L) L) (N [w0,w1,w2,w3,w123,w4] (N [w0,w1,w2,w3,w470,w4] L L) L))) (N [w0,w1,w2,w3,w123,w4,w29] (N [w0,w1,w2,w3,w123,w4,w21] (N [w0,w1,w2,w3,w123,w4,w17] (N [w0,w1,w2,w3,w123,w4,w15] L L) L) (N [w0,w1,w2,w3,w123,w4,w23] (N [w0,w1,w2,w3,w123,w4,w482] L L) L)) (N [w0,w1,w2,w3,w500,w4] (N [w0,w1,w2,w3,w123,w4,w11] (N [w0,w1,w2,w3,w123,w4,w491] L L) L) (N [w0,w1,w2,w3,w4,w69] (N [w0,w1,w2,w3,w506,w4] L L) L)))) (N [w0,w1,w2,w3,w4,w15,w81] (N [w0,w1,w2,w3,w4,w15,w17] (N [w0,w1,w2,w3,w4,w15] (N [w0,w1,w2,w3,w4,w55] (N [w0,w1,w2,w3,w4,w46] L L) L) (N [w0,w1,w2,w3,w4,w15,w430] (N [w0,w1,w2,w3,w4,w15,w376] L L) L)) (N [w0,w1,w2,w3,w4,w15,w29] (N [w0,w1,w2,w3,w4,w15,w23] (N [w0,w1,w2,w3,w4,w15,w21] L L) L) (N [w0,w1,w2,w3,w4,w15,w76] (N [w0,w1,w2,w3,w4,w15,w11] L L) L))) (N [w0,w1,w2,w3,w4,w41] (N [w0,w1,w2,w3,w4,w50] (N [w0,w1,w2,w3,w4,w430] (N [w0,w1,w2,w3,w4,w376] L L) L) (N [w0,w1,w2,w3,w4,w60] (N [w0,w1,w2,w3,w4,w70] L L) L)) (N [w0,w1,w2,w3,w4,w21,w436] (N [w0,w1,w2,w3,w4,w21,w384] (N [w0,w1,w2,w3,w4,w21] L L) L) (N [w0,w1,w2,w3,w4,w21,w25] (N [w0,w1,w2,w3,w4,w21,w482] L L) L))))) (N [w0,w1,w2,w3,w4,w11,w63] (N [w0,w1,w2,w3,w4,w29,w444] (N [w0,w1,w2,w3,w4,w21,w89] (N [w0,w1,w2,w3,w4,w21,w76] (N [w0,w1,w2,w3,w4,w21,w29] (N [w0,w1,w2,w3,w4,w21,w27] L L) (N [w0,w1,w2,w3,w4,w21,w11] L L)) (N [w0,w1,w2,w3,w4,w21,w65] (N [w0,w1,w2,w3,w4,w21,w13] L L) L)) (N [w0,w1,w2,w3,w4,w482] (N [w0,w1,w2,w3,w4,w436] (N [w0,w1,w2,w3,w4,w384] L L) L) (N [w0,w1,w2,w3,w4,w29,w491] (N [w0,w1,w2,w3,w4,w29] L L) L))) (N [w0,w1,w2,w3,w4,w48] (N [w0,w1,w2,w3,w4,w29,w81] (N [w0,w1,w2,w3,w4,w29,w89] (N [w0,w1,w2,w3,w4,w29,w11] L L) L) (N [w0,w1,w2,w3,w4,w444] (N [w0,w1,w2,w3,w4,w491] L L) L)) (N [w0,w1,w2,w3,w4,w11,w372] (N [w0,w1,w2,w3,w4,w11,w428] (N [w0,w1,w2,w3,w4,w11] L L) L) (N [w0,w1,w2,w3,w4,w11,w13] (N [w0,w1,w2,w3,w4,w11,w76] L L) L)))) (N [w0,w1,w2,w3,w469] (N [w0,w1,w2,w3,w4,w89] (N [w0,w1,w2,w3,w4,w76] (N [w0,w1,w2,w3,w4,w372] (N [w0,w1,w2,w3,w4,w428] L L) L) (N [w0,w1,w2,w3,w4,w63] (N [w0,w1,w2,w3,w4,w65] L L) L)) (N [w0,w1,w2,w3,w330,w13] (N [w0,w1,w2,w3,w330] (N [w0,w1,w2,w3,w4,w81] L L) L) (N [w0,w1,w2,w3,w117,w27] (N [w0,w1,w2,w3,w338,w29] L L) L))) (N [w0,w1,w327,w3,w4,w11] (N [w0,w1,w2,w3,w59] (N [w0,w1,w2,w3,w125,w29] (N [w0,w1,w2,w3,w125,w17] L L) L) (N [w0,w1,w327,w3,w4] (N [w0,w1,w2,w3,w23,w29] L L) L)) (N [w0,w1,w402,w19,w3,w4] (N [w0,w1,w107,w3,w4,w27] (N [w0,w1,w121,w3,w4,w13] L L) L) (N [w103,w1,w2,w3,w4,w17] (N [w111,w1,w2,w3,w4,w13] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRRR = true := by decide +kernel
def tbl_6_0RRR : STree := N [w0,w1,w2,w3,w115,w4,w436] tbl_6_0RRRL tbl_6_0RRRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RRR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RRR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RRRL chk_tbl_6_0RRRR
def tbl_6_0RR : STree := N [w0,w1,w105,w2,w3,w4,w13] tbl_6_0RRL tbl_6_0RRR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0RR : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0RR = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RRL chk_tbl_6_0RRR
def tbl_6_0R : STree := N [w375,w0,w103,w1,w2,w3,w4] tbl_6_0RL tbl_6_0RR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0R : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0R = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0RL chk_tbl_6_0RR
def tbl_6_0 : STree := N [w54,w0,w20,w1,w2,w3,w4] tbl_6_0L tbl_6_0R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_0 : checkSTree aut12.fn aut34.fn 5 0 tbl_5_0 tbl_5_0 tbl_6_0 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_0L chk_tbl_6_0R
lemma nolive_6_0 : ∀ v, MemSTree v tbl_6_0 → ∀ m ≤ 6, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 5 0 tbl_6_0 tbl_5_0 tbl_5_0 nolive_5_0 nolive_5_0 chk_tbl_6_0
def tbl_6_1LL : STree := (N [w62,w0,w1,w2,w3,w4] (N [w10,w0,w1,w2,w153,w4] (N [w147,w0,w1,w2,w3,w4] (N [w35,w0,w1,w2,w3,w4] (N [w32,w0,w1,w2,w3,w128] (N [w32,w0,w18,w19,w3,w4] (N [w129,w0,w1,w2,w3,w4] L L) (N [w32,w0,w1,w2,w3,w4] L L)) (N [w32,w1,w2,w3,w4,w48] (N [w32,w0,w1,w33,w3,w4] L L) (N [w136,w0,w1,w2,w3,w4] L L))) (N [w35,w0,w1,w133,w3,w4] (N [w35,w0,w1,w2,w3,w59] (N [w35,w0,w1,w2,w3,w134] L L) (N [w35,w0,w1,w2,w4,w36] L L)) (N [w35,w1,w2,w3,w4,w55] (N [w35,w0,w2,w3,w4,w41] L L) L))) (N [w10,w0,w18,w19,w3,w4] (N [w10,w150,w1,w2,w3,w4] (N [w10,w12,w0,w18,w3,w4] (N [w151,w0,w1,w2,w3,w4] L L) (N [w10,w14,w2,w3,w4,w11] L L)) (N [w10,w0,w18,w33,w3,w4] (N [w10,w91,w1,w2,w3,w4] L L) L)) (N [w10,w0,w1,w97,w3,w4] (N [w10,w0,w92,w2,w3,w4] (N [w10,w0,w86,w2,w3,w4] L L) (N [w10,w0,w98,w2,w3,w4] L L)) (N [w10,w0,w1,w2,w99,w4] (N [w10,w0,w1,w2,w28,w29] L L) L)))) (N [w10,w20,w2,w3,w4,w11] (N [w10,w0,w97,w3,w4] (N [w10,w0,w1,w2,w3,w59] (N [w10,w0,w1,w2,w3,w128] (N [w10,w0,w1,w2,w3,w4] L L) (N [w10,w0,w1,w2,w3,w134] L L)) (N [w10,w0,w1,w133,w3,w4] (N [w10,w0,w1,w2,w3,w140] L L) (N [w10,w0,w97,w2,w3,w4] L L))) (N [w10,w0,w2,w3,w4,w41] (N [w10,w0,w2,w34,w3,w4] (N [w10,w0,w97,w3,w4,w11] L L) (N [w10,w0,w2,w99,w4,w11] L L)) (N [w10,w18,w2,w3,w4,w48] (N [w10,w0,w2,w3,w4,w48] L L) L))) (N [w10,w2,w3,w4,w11,w13] (N [w10,w1,w2,w3,w4,w48] (N [w10,w1,w2,w99,w4,w11] (N [w10,w1,w97,w3,w4,w11] L L) (N [w10,w1,w2,w3,w4,w55] L L)) (N [w10,w2,w3,w4,w48] (N [w10,w2,w19,w3,w4,w11] L L) L)) (N [w62,w0,w18,w1,w3,w4] (N [w247,w0,w1,w2,w3,w4] (N [w156,w0,w1,w2,w3,w4] L L) (N [w62,w14,w1,w2,w3,w4] L L)) (N [w62,w0,w18,w3,w4] (N [w62,w0,w18,w19,w3,w4] L L) L))))) (N [w14,w0,w1,w2,w3,w59] (N [w14,w0,w49,w1,w2,w4] (N [w44,w0,w1,w2,w29] (N [w44,w0,w1,w2,w28,w29] (N [w62,w1,w2,w3,w4,w63] (N [w62,w1,w2,w3,w4,w11] L L) (N [w44,w14,w0,w1,w2,w29] L L)) (N [w44,w0,w1,w2,w3,w45] (N [w44,w0,w1,w2,w3,w4] L L) (N [w44,w0,w1,w2,w3,w29] L L))) (N [w14,w16,w0,w1,w2,w29] (N [w44,w1,w2,w3,w4,w69] (N [w44,w0,w1,w3,w4,w162] L L) (N [w174,w0,w1,w2,w3,w4] L L)) (N [w14,w177,w1,w2,w3,w4] (N [w14,w16,w1,w2,w3,w17] L L) L))) (N [w14,w0,w1,w2,w64,w4] (N [w14,w0,w75,w1,w2,w4] (N [w14,w0,w20,w1,w2,w59] (N [w14,w0,w18,w19,w3,w4] L L) (N [w14,w0,w20,w2,w4,w41] L L)) (N [w14,w0,w98,w2,w3,w4] (N [w14,w0,w92,w1,w2,w4] L L) L)) (N [w14,w0,w1,w2,w3,w100] (N [w14,w0,w1,w2,w88,w4] (N [w14,w0,w1,w2,w28,w29] L L) (N [w14,w0,w1,w2,w99,w4] L L)) (N [w14,w0,w1,w2,w3,w134] (N [w14,w0,w1,w2,w3,w4] L L) L)))) (N [w14,w1,w2,w3,w4,w55] (N [w14,w0,w1,w2,w59] (N [w14,w0,w1,w2,w4,w60] (N [w14,w0,w1,w2,w4,w46] (N [w14,w0,w1,w2,w4,w36] L L) (N [w14,w0,w1,w2,w4,w55] L L)) (N [w14,w0,w1,w2,w4,w29] (N [w14,w0,w1,w2,w4,w59] L L) (N [w14,w0,w1,w2,w4,w81] L L))) (N [w14,w20,w1,w2,w4,w55] (N [w14,w0,w1,w133,w3,w4] (N [w14,w0,w1,w2,w23,w29] L L) (N [w14,w0,w1,w3,w4,w162] L L)) (N [w14,w1,w2,w3,w4,w69] (N [w14,w1,w2,w28,w4,w15] L L) L))) (N [w84,w0,w1,w2,w4,w29] (N [w309,w0,w1,w2,w4,w60] (N [w306,w0,w1,w2,w3,w4] (N [w303,w0,w1,w2,w3,w4] L L) (N [w309,w0,w1,w2,w3,w4] L L)) (N [w84,w0,w1,w2,w3,w4] (N [w84,w0,w20,w1,w2,w4] L L) L)) (N [w91,w0,w1,w2,w28,w29] (N [w84,w1,w2,w3,w4,w11] (N [w84,w1,w2,w3,w4,w15] L L) (N [w84,w1,w2,w3,w4,w76] L L)) (N [w91,w1,w2,w3,w4,w15] (N [w91,w0,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1LL : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1LL = true := by decide +kernel
def tbl_6_1LR : STree := (N [w0,w20,w221,w2,w3,w4] (N [w0,w18,w1,w2,w3,w128] (N [w0,w49,w1,w2,w3,w59] (N [w317,w1,w2,w3,w4,w21] (N [w258,w1,w2,w3,w4,w21] (N [w258,w1,w2,w19,w3,w4] (N [w258,w0,w1,w2,w3,w4] L L) (N [w258,w1,w2,w3,w4] L L)) (N [w317,w0,w1,w2,w3,w4] (N [w258,w1,w2,w3,w4,w65] L L) (N [w317,w1,w2,w3,w4] L L))) (N [w0,w49,w18,w19,w3,w4] (N [w317,w1,w2,w3,w4,w89] (N [w317,w1,w2,w3,w4,w29] L L) (N [w0,w190,w1,w2,w3,w4] L L)) (N [w0,w49,w1,w2,w3,w189] (N [w0,w49,w1,w2,w3,w4] L L) L))) (N [w0,w18,w75,w2,w3,w4] (N [w0,w196,w1,w2,w3,w4] (N [w0,w49,w1,w56,w3,w4] (N [w0,w49,w1,w2,w4,w50] L L) (N [w0,w193,w1,w2,w3,w4] L L)) (N [w0,w18,w20,w19,w3,w4] (N [w0,w18,w20,w2,w4,w21] L L) L)) (N [w0,w18,w1,w2,w199,w4] (N [w0,w18,w98,w2,w3,w4] (N [w0,w18,w92,w2,w3,w4] L L) (N [w0,w18,w1,w2,w28,w29] L L)) (N [w0,w18,w1,w2,w3,w4] (N [w0,w18,w1,w2,w99,w4] L L) L)))) (N [w0,w18,w19,w3,w4,w11] (N [w0,w18,w34,w3,w4] (N [w0,w18,w1,w34,w3,w4] (N [w0,w18,w1,w2,w3,w59] (N [w0,w18,w1,w2,w3,w189] L L) (N [w0,w18,w1,w56,w3,w4] L L)) (N [w0,w18,w1,w3,w4,w72] (N [w0,w18,w1,w33,w3,w4] L L) (N [w0,w18,w64,w19,w3,w4] L L))) (N [w0,w18,w19,w3,w4,w21] (N [w0,w18,w19,w3,w4,w15] (N [w0,w18,w19,w28,w3,w4] L L) (N [w0,w18,w19,w3,w4,w50] L L)) (N [w0,w18,w19,w3,w4,w48] (N [w0,w18,w19,w3,w4,w29] L L) L))) (N [w0,w213,w1,w2,w3,w4] (N [w0,w58,w1,w2,w3,w4] (N [w0,w18,w19,w3,w4,w63] (N [w0,w18,w19,w3,w4,w65] L L) (N [w0,w58,w1,w2,w28,w29] L L)) (N [w0,w58,w2,w3,w4,w70] (N [w0,w58,w1,w2,w3,w59] L L) L)) (N [w0,w223,w1,w2,w3,w4] (N [w0,w223,w98,w2,w3,w4] (N [w0,w218,w1,w2,w3,w4] L L) (N [w0,w223,w1,w2,w153,w4] L L)) (N [w0,w20,w216,w2,w3,w4] (N [w0,w20,w22,w2,w3,w23] L L) L))))) (N [w0,w20,w2,w4,w41] (N [w0,w20,w1,w2,w3,w140] (N [w0,w20,w1,w2,w153,w4] (N [w0,w20,w1,w2,w28,w29] (N [w0,w20,w1,w24,w4,w25] (N [w0,w20,w98,w2,w3,w4] L L) (N [w0,w20,w1,w97,w3,w4] L L)) (N [w0,w20,w1,w2,w222,w4] (N [w0,w20,w1,w2,w80,w4] L L) (N [w0,w20,w1,w2,w99,w4] L L))) (N [w0,w20,w1,w2,w3,w134] (N [w0,w20,w1,w2,w3,w154] (N [w0,w20,w1,w2,w3,w100] L L) (N [w0,w20,w1,w2,w3,w4] L L)) (N [w0,w20,w1,w2,w3,w59] (N [w0,w20,w1,w2,w3,w189] L L) L))) (N [w0,w20,w1,w133,w3,w4] (N [w0,w20,w1,w2,w4,w41] (N [w0,w20,w1,w2,w4,w50] (N [w0,w20,w1,w2,w4,w36] L L) (N [w0,w20,w1,w2,w4,w60] L L)) (N [w0,w20,w1,w2,w21,w59] (N [w0,w20,w1,w2,w4,w207] L L) L)) (N [w0,w20,w2,w3,w4,w41] (N [w0,w20,w2,w28,w4,w21] (N [w0,w20,w2,w57,w3,w4] L L) (N [w0,w20,w2,w3,w4,w70] L L)) (N [w0,w20,w2,w4,w15,w21] (N [w0,w20,w2,w3,w21,w59] L L) L)))) (N [w0,w86,w2,w19,w3,w4] (N [w0,w75,w2,w3,w4,w11] (N [w0,w286,w1,w2,w3,w4] (N [w0,w281,w1,w2,w3,w4] (N [w0,w20,w2,w4,w21,w11] L L) (N [w0,w284,w1,w2,w3,w4] L L)) (N [w0,w75,w1,w2,w3,w4] (N [w0,w290,w1,w2,w3,w4] L L) (N [w0,w75,w2,w3,w4,w21] L L))) (N [w0,w310,w1,w2,w4,w207] (N [w0,w308,w1,w2,w3,w4] (N [w0,w75,w2,w3,w4,w76] L L) (N [w0,w310,w1,w2,w3,w4] L L)) (N [w0,w86,w1,w2,w3,w4] (N [w0,w311,w1,w2,w3,w4] L L) L))) (N [w0,w92,w2,w3,w4,w21] (N [w0,w92,w1,w2,w3,w4] (N [w0,w86,w2,w3,w4,w65] (N [w0,w86,w2,w3,w4,w21] L L) (N [w0,w92,w1,w2,w28,w29] L L)) (N [w0,w92,w1,w2,w3,w23] (N [w0,w92,w1,w2,w3,w59] L L) L)) (N [w0,w98,w1,w2,w153,w4] (N [w0,w92,w2,w3,w23] (N [w0,w92,w2,w3,w4,w89] L L) (N [w0,w92,w2,w3,w23,w29] L L)) (N [w0,w98,w2,w33,w3,w4] (N [w0,w98,w1,w2,w3,w4] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1LR : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1LR = true := by decide +kernel
def tbl_6_1L : STree := N [w91,w1,w2,w3,w4,w81] tbl_6_1LL tbl_6_1LR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1L : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1L = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_1LL chk_tbl_6_1LR
def tbl_6_1RL : STree := (N [w0,w1,w2,w266,w99,w4] (N [w0,w301,w2,w3,w4,w15] (N [w0,w98,w2,w3,w4,w63] (N [w0,w98,w2,w3,w4,w21] (N [w0,w98,w2,w153,w4,w13] (N [w0,w98,w2,w153,w3,w4] (N [w0,w98,w2,w28,w3,w4] L L) (N [w0,w98,w2,w153,w4] L L)) (N [w0,w98,w2,w3,w4,w15] (N [w0,w98,w2,w3,w4] L L) (N [w0,w98,w2,w3,w4,w240] L L))) (N [w0,w98,w2,w3,w4,w11] (N [w0,w98,w2,w3,w4,w29] (N [w0,w98,w2,w3,w4,w25] L L) (N [w0,w98,w2,w3,w4,w48] L L)) (N [w0,w98,w2,w3,w4,w78] (N [w0,w98,w2,w3,w4,w13] L L) L))) (N [w0,w319,w1,w2,w3,w4] (N [w0,w297,w2,w3,w4,w25] (N [w0,w297,w2,w3,w4] (N [w0,w297,w1,w2,w3,w4] L L) (N [w0,w297,w2,w3,w4,w15] L L)) (N [w0,w297,w2,w3,w4,w78] (N [w0,w297,w2,w3,w4,w13] L L) L)) (N [w0,w319,w2,w3,w4,w94] (N [w0,w319,w2,w3,w4,w25] (N [w0,w319,w2,w3,w4] L L) (N [w0,w319,w2,w3,w4,w29] L L)) (N [w0,w301,w2,w3,w4] (N [w0,w301,w1,w2,w3,w4] L L) L)))) (N [w0,w1,w2,w135,w3,w4] (N [w0,w1,w2,w64,w3,w243] (N [w0,w1,w2,w248,w3,w4] (N [w0,w301,w2,w3,w4,w81] (N [w0,w301,w2,w3,w4,w29] L L) (N [w0,w1,w2,w245,w3,w4] L L)) (N [w0,w1,w2,w64,w28,w4] (N [w0,w1,w2,w249,w3,w4] L L) (N [w0,w1,w2,w64,w3,w4] L L))) (N [w0,w1,w2,w252,w3,w4] (N [w0,w1,w2,w64,w4,w65] (N [w0,w1,w2,w64,w4,w21] L L) (N [w0,w1,w2,w139,w3,w4] L L)) (N [w0,w1,w2,w206,w3,w4] (N [w0,w1,w2,w204,w3,w4] L L) L))) (N [w0,w1,w2,w19,w28,w29] (N [w0,w1,w2,w34,w3,w4] (N [w0,w1,w2,w57,w3,w140] (N [w0,w1,w2,w57,w3,w4] L L) (N [w0,w1,w2,w254,w3,w4] L L)) (N [w0,w1,w2,w237,w3,w4] (N [w0,w1,w2,w228,w3,w4] L L) L)) (N [w0,w1,w2,w19,w3,w4] (N [w0,w1,w2,w19,w260,w4] (N [w0,w1,w2,w19,w99,w4] L L) (N [w0,w1,w2,w19,w262,w4] L L)) (N [w0,w1,w2,w19,w3,w243] (N [w0,w1,w2,w19,w3,w59] L L) L))))) (N [w0,w1,w2,w199,w3,w4] (N [w0,w1,w2,w80,w3,w4] (N [w0,w1,w2,w28,w70,w29] (N [w0,w1,w2,w28,w3,w45] (N [w0,w1,w2,w28,w99,w4] (N [w0,w1,w2,w266,w3,w4] L L) (N [w0,w1,w2,w28,w3,w4] L L)) (N [w0,w1,w2,w28,w69,w29] (N [w0,w1,w2,w28,w3,w59] L L) (N [w0,w1,w2,w28,w15,w29] L L))) (N [w0,w1,w2,w28,w29,w81] (N [w0,w1,w2,w28,w29,w11] (N [w0,w1,w2,w28,w21,w29] L L) (N [w0,w1,w2,w28,w29,w89] L L)) (N [w0,w1,w2,w291,w3,w4] (N [w0,w1,w2,w285,w3,w4] L L) L))) (N [w0,w1,w2,w88,w3,w59] (N [w0,w1,w2,w305,w3,w4] (N [w0,w1,w2,w80,w4,w29] (N [w0,w1,w2,w80,w4,w15] L L) (N [w0,w1,w2,w80,w4,w81] L L)) (N [w0,w1,w2,w88,w3,w4] (N [w0,w1,w2,w312,w3,w4] L L) L)) (N [w0,w1,w2,w88,w4,w89] (N [w0,w1,w2,w88,w4,w21] (N [w0,w1,w2,w88,w3,w29] L L) (N [w0,w1,w2,w88,w4,w29] L L)) (N [w0,w1,w2,w88,w29] (N [w0,w1,w2,w88,w23,w29] L L) L)))) (N [w0,w1,w2,w99,w4,w23] (N [w0,w1,w2,w99,w4,w55] (N [w0,w1,w2,w99,w3,w4] (N [w0,w1,w2,w199,w4,w48] (N [w0,w1,w2,w199,w4] L L) (N [w0,w1,w2,w99,w3,w100] L L)) (N [w0,w1,w2,w99,w100,w11] (N [w0,w1,w2,w99,w100] L L) (N [w0,w1,w2,w99,w4] L L))) (N [w0,w1,w2,w99,w4,w21] (N [w0,w1,w2,w99,w4,w17] (N [w0,w1,w2,w99,w4,w15] L L) (N [w0,w1,w2,w99,w4,w41] L L)) (N [w0,w1,w2,w99,w4,w25] (N [w0,w1,w2,w99,w4,w277] L L) L))) (N [w0,w1,w2,w99,w4,w101] (N [w0,w1,w2,w99,w4,w11] (N [w0,w1,w2,w99,w4,w279] (N [w0,w1,w2,w99,w4,w27] L L) (N [w0,w1,w2,w99,w4,w29] L L)) (N [w0,w1,w2,w99,w4,w13] (N [w0,w1,w2,w99,w4,w76] L L) L)) (N [w0,w1,w2,w299,w4,w17] (N [w0,w1,w2,w299,w3,w4] (N [w0,w1,w2,w99,w4,w63] L L) (N [w0,w1,w2,w299,w4] L L)) (N [w0,w1,w2,w299,w4,w11] (N [w0,w1,w2,w299,w4,w23] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1RL : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1RL = true := by decide +kernel
def tbl_6_1RR : STree := (N [w0,w1,w2,w3,w4,w76] (N [w0,w1,w2,w3,w4,w161] (N [w0,w1,w2,w3,w4,w166] (N [w0,w1,w2,w262,w4,w63] (N [w0,w1,w2,w260,w4,w67] (N [w0,w1,w2,w260,w4] (N [w0,w1,w2,w260,w3,w4] L L) (N [w0,w1,w2,w260,w4,w23] L L)) (N [w0,w1,w2,w262,w4] (N [w0,w1,w2,w262,w3,w4] L L) (N [w0,w1,w2,w262,w4,w11] L L))) (N [w0,w1,w2,w3,w4,w127] (N [w0,w1,w2,w3,w4,w202] (N [w0,w1,w2,w3,w4,w142] L L) (N [w0,w1,w2,w3,w4,w69] L L)) (N [w0,w1,w2,w3,w4,w36] (N [w0,w1,w2,w3,w4,w137] L L) L))) (N [w0,w1,w2,w3,w4,w244] (N [w0,w1,w2,w3,w4,w55] (N [w0,w1,w2,w3,w4,w46] (N [w0,w1,w2,w3,w4,w292] L L) (N [w0,w1,w2,w3,w4,w188] L L)) (N [w0,w1,w2,w3,w4,w157] (N [w0,w1,w2,w3,w4,w272] L L) L)) (N [w0,w1,w2,w3,w4,w191] (N [w0,w1,w2,w3,w4,w15] (N [w0,w1,w2,w3,w4,w182] L L) (N [w0,w1,w2,w3,w4,w192] L L)) (N [w0,w1,w2,w3,w4,w50] (N [w0,w1,w2,w3,w4,w164] L L) L)))) (N [w0,w1,w2,w3,w4,w246] (N [w0,w1,w2,w3,w4,w273] (N [w0,w1,w2,w3,w4,w314] (N [w0,w1,w2,w3,w4,w313] (N [w0,w1,w2,w3,w4,w70] L L) (N [w0,w1,w2,w3,w4,w60] L L)) (N [w0,w1,w2,w3,w4,w41] (N [w0,w1,w2,w3,w4,w240] L L) (N [w0,w1,w2,w3,w4,w269] L L))) (N [w0,w1,w2,w3,w4,w21] (N [w0,w1,w2,w3,w4,w233] (N [w0,w1,w2,w3,w4,w278] L L) (N [w0,w1,w2,w3,w4,w229] L L)) (N [w0,w1,w2,w3,w4,w280] (N [w0,w1,w2,w3,w4,w320] L L) L))) (N [w0,w1,w2,w3,w4,w235] (N [w0,w1,w2,w3,w4,w194] (N [w0,w1,w2,w3,w4,w48] (N [w0,w1,w2,w3,w4,w29] L L) (N [w0,w1,w2,w3,w4,w232] L L)) (N [w0,w1,w2,w3,w4,w184] (N [w0,w1,w2,w3,w4,w181] L L) L)) (N [w0,w1,w2,w3,w4,w225] (N [w0,w1,w2,w3,w4,w267] (N [w0,w1,w2,w3,w4,w11] L L) (N [w0,w1,w2,w3,w4,w149] L L)) (N [w0,w1,w2,w3,w4,w215] (N [w0,w1,w2,w3,w4,w176] L L) L))))) (N [w0,w1,w2,w3,w59,w23] (N [w0,w1,w2,w3,w128] (N [w0,w1,w2,w3,w4,w152] (N [w0,w1,w2,w3,w4,w65] (N [w0,w1,w2,w3,w4,w167] (N [w0,w1,w2,w3,w4,w251] L L) (N [w0,w1,w2,w3,w4,w220] L L)) (N [w0,w1,w2,w3,w4,w253] (N [w0,w1,w2,w3,w4,w63] L L) (N [w0,w1,w2,w3,w4,w197] L L))) (N [w0,w1,w2,w3,w4,w255] (N [w0,w1,w2,w3,w4,w81] (N [w0,w1,w2,w3,w4,w89] L L) (N [w0,w1,w2,w3,w4,w293] L L)) (N [w0,w1,w2,w3,w15,w59] (N [w0,w1,w2,w3,w55,w59] L L) L))) (N [w0,w1,w2,w3,w70,w29] (N [w0,w1,w2,w3,w45,w23] (N [w0,w1,w2,w3,w38,w27] (N [w0,w1,w2,w3,w134] L L) (N [w0,w1,w2,w3,w38,w29] L L)) (N [w0,w1,w2,w3,w17,w59] (N [w0,w1,w2,w3,w17,w52] L L) L)) (N [w0,w1,w2,w3,w189] (N [w0,w1,w2,w3,w21,w59] (N [w0,w1,w2,w3,w60,w23] L L) (N [w0,w1,w2,w3,w21,w140] L L)) (N [w0,w1,w2,w3,w59] (N [w0,w1,w2,w3,w52,w29] L L) L)))) (N [w0,w1,w133,w3,w4] (N [w0,w1,w2,w3,w169,w29] (N [w0,w1,w2,w3,w59,w13] (N [w0,w1,w2,w3,w59,w29] (N [w0,w1,w2,w3,w59,w27] L L) (N [w0,w1,w2,w3,w59,w11] L L)) (N [w0,w1,w2,w3,w59,w219] (N [w0,w1,w2,w3,w59,w214] L L) L)) (N [w0,w1,w2,w60,w23] (N [w0,w1,w2,w3,w29,w67] (N [w0,w1,w2,w3,w243] L L) (N [w0,w1,w2,w70,w29] L L)) (N [w0,w1,w2,w21,w27,w29] (N [w0,w1,w2,w21,w23,w29] L L) L))) (N [w0,w1,w3,w4,w43,w27] (N [w0,w1,w28,w3,w4,w162] (N [w0,w1,w33,w3,w4,w25] (N [w0,w1,w56,w3,w4,w13] L L) (N [w0,w1,w19,w3,w4,w43] L L)) (N [w0,w1,w3,w4,w72,w13] (N [w0,w1,w3,w4,w162] L L) L)) (N [w1,w2,w3,w4,w188] (N [w18,w1,w2,w3,w4,w188] (N [w49,w1,w2,w3,w4,w188] L L) (N [w20,w1,w2,w3,w4,w188] L L)) (N [w1,w2,w3,w4,w15,w48] (N [w1,w2,w3,w4,w55,w13] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1RR : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1RR = true := by decide +kernel
def tbl_6_1R : STree := N [w0,w1,w2,w299,w4,w101] tbl_6_1RL tbl_6_1RR
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1R : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1R = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_1RL chk_tbl_6_1RR
def tbl_6_1 : STree := N [w0,w98,w2,w19,w3,w4] tbl_6_1L tbl_6_1R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_6_1 : checkSTree aut12.fn aut34.fn 5 1 tbl_5_0 tbl_5_1 tbl_6_1 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_6_1L chk_tbl_6_1R
lemma nolive_6_1 : ∀ v, MemSTree v tbl_6_1 → ∀ m ≤ 6, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 5 1 tbl_6_1 tbl_5_0 tbl_5_1 nolive_5_0 nolive_5_1 chk_tbl_6_1
def tbl_7_0 : STree := (N [w7,w0,w1,w2,w28,w3,w4] (N [w9,w0,w1,w2,w3,w4,w15] (N [w108,w9,w0,w1,w2,w3,w4] (N [w74,w0,w1,w2,w3,w4] (N [w90,w0,w1,w2,w3,w4,w29] (N [w96,w0,w1,w2,w3,w4,w13] (N [w96,w0,w1,w2,w3,w4] L L) (N [w90,w0,w1,w2,w3,w4] L L)) (N [w83,w0,w1,w2,w3,w4,w27] (N [w83,w0,w1,w2,w3,w4] L L) L)) (N [w102,w0,w1,w2,w3,w4] (N [w102,w9,w0,w1,w2,w3,w4] (N [w74,w0,w1,w2,w3,w4,w17] L L) L) (N [w104,w0,w1,w2,w3,w4] (N [w104,w9,w0,w1,w2,w3,w4] L L) L))) (N [w9,w0,w20,w1,w2,w3,w4] (N [w9,w16,w0,w1,w2,w3,w4] (N [w9,w10,w0,w1,w2,w3,w4] (N [w108,w0,w1,w2,w3,w4] L L) (N [w9,w14,w0,w1,w2,w3,w4] L L)) (N [w9,w0,w18,w1,w2,w3,w4] (N [w9,w0,w103,w1,w2,w3,w4] L L) L)) (N [w9,w0,w1,w2,w19,w3,w4] (N [w9,w0,w1,w105,w2,w3,w4] (N [w9,w0,w22,w1,w2,w3,w4] L L) L) (N [w9,w0,w1,w2,w3,w109,w4] (N [w9,w0,w1,w2,w28,w3,w4] L L) L)))) (N [w114,w0,w1,w2,w3,w4] (N [w68,w0,w1,w2,w3,w4] (N [w9,w0,w1,w2,w3,w4,w29] (N [w9,w0,w1,w2,w3,w4,w21] (N [w9,w0,w1,w2,w3,w4,w17] L L) (N [w9,w0,w1,w2,w3,w4,w23] L L)) (N [w68,w0,w1,w2,w28,w3,w4] (N [w9,w0,w1,w2,w3,w4,w11] L L) L)) (N [w112,w7,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w3,w4] (N [w61,w0,w1,w2,w19,w3,w4] L L) L) (N [w114,w7,w0,w1,w2,w3,w4] (N [w112,w0,w1,w2,w3,w4] L L) L))) (N [w7,w0,w111,w1,w2,w3,w4] (N [w7,w10,w0,w1,w2,w3,w4] (N [w110,w0,w1,w2,w3,w4] (N [w110,w7,w0,w1,w2,w3,w4] L L) L) (N [w7,w14,w0,w1,w2,w3,w4] (N [w7,w12,w0,w1,w2,w3,w4] L L) L)) (N [w7,w0,w1,w113,w2,w3,w4] (N [w7,w0,w20,w1,w2,w3,w4] (N [w7,w0,w18,w1,w2,w3,w4] L L) L) (N [w7,w0,w1,w2,w19,w3,w4] (N [w7,w0,w1,w24,w2,w3,w4] L L) L))))) (N [w5,w0,w1,w2,w3,w4,w21] (N [w122,w0,w1,w2,w3,w4] (N [w7,w0,w1,w2,w3,w4,w13] (N [w7,w0,w1,w2,w3,w4,w25] (N [w7,w0,w1,w2,w3,w4,w15] (N [w7,w0,w1,w2,w3,w115,w4] L L) (N [w7,w0,w1,w2,w3,w4,w21] L L)) (N [w7,w0,w1,w2,w3,w4,w11] (N [w7,w0,w1,w2,w3,w4,w29] L L) L)) (N [w47,w0,w18,w1,w2,w3,w4] (N [w54,w0,w1,w2,w3,w4] (N [w54,w0,w1,w26,w2,w3,w4] L L) L) (N [w122,w5,w0,w1,w2,w3,w4] (N [w47,w0,w1,w2,w3,w4] L L) L))) (N [w5,w0,w20,w1,w2,w3,w4] (N [w5,w10,w0,w1,w2,w3,w4] (N [w118,w0,w1,w2,w3,w4] (N [w118,w5,w0,w1,w2,w3,w4] L L) L) (N [w5,w0,w18,w1,w2,w3,w4] (N [w5,w14,w0,w1,w2,w3,w4] L L) L)) (N [w5,w0,w1,w2,w28,w3,w4] (N [w5,w0,w1,w2,w19,w3,w4] (N [w5,w0,w1,w119,w2,w3,w4] L L) L) (N [w5,w0,w1,w2,w3,w4,w15] (N [w5,w0,w1,w2,w3,w123,w4] L L) L)))) (N [w0,w1,w119,w2,w3,w4] (N [w10,w0,w1,w2,w3,w4] (N [w40,w0,w1,w2,w3,w4] (N [w5,w0,w1,w2,w3,w4,w11] (N [w5,w0,w1,w2,w3,w4,w29] L L) (N [w40,w16,w0,w1,w2,w3,w4] L L)) (N [w31,w0,w1,w2,w3,w4] (N [w31,w12,w0,w1,w2,w3,w4] L L) L)) (N [w0,w103,w1,w2,w3,w4] (N [w0,w111,w1,w2,w3,w4] (N [w14,w0,w1,w2,w3,w4] L L) L) (N [w0,w20,w1,w2,w3,w4] (N [w0,w18,w1,w2,w3,w4] L L) L))) (N [w0,w1,w2,w3,w115,w4] (N [w0,w1,w2,w19,w3,w4] (N [w0,w1,w113,w2,w3,w4] (N [w0,w1,w105,w2,w3,w4] L L) L) (N [w0,w1,w2,w3,w109,w4] (N [w0,w1,w2,w28,w3,w4] L L) L)) (N [w0,w1,w2,w3,w4,w21] (N [w0,w1,w2,w3,w4,w15] (N [w0,w1,w2,w3,w123,w4] L L) L) (N [w0,w1,w2,w3,w4,w11] (N [w0,w1,w2,w3,w4,w29] L L) L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_7_0 : checkSTree aut12.fn aut34.fn 6 0 tbl_6_0 tbl_6_0 tbl_7_0 = true := by decide +kernel
lemma nolive_7_0 : ∀ v, MemSTree v tbl_7_0 → ∀ m ≤ 7, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 6 0 tbl_7_0 tbl_6_0 tbl_6_0 nolive_6_0 nolive_6_0 chk_tbl_7_0
def tbl_7_1L : STree := (N [w14,w0,w1,w2,w3,w4,w21] (N [w10,w0,w1,w2,w3,w4,w29] (N [w10,w0,w18,w2,w3,w4] (N [w35,w0,w20,w1,w2,w3,w4] (N [w32,w0,w1,w2,w3,w4] (N [w32,w0,w18,w1,w2,w3,w4] (N [w32,w10,w0,w1,w2,w3,w4] L L) L) (N [w35,w14,w0,w1,w2,w3,w4] (N [w35,w10,w0,w1,w2,w3,w4] L L) L)) (N [w10,w14,w0,w1,w2,w3,w4] (N [w10,w12,w0,w1,w2,w3,w4] (N [w35,w0,w1,w2,w3,w4] L L) L) (N [w10,w0,w18,w1,w2,w3,w4] L L))) (N [w10,w0,w1,w2,w28,w3,w4] (N [w10,w0,w1,w2,w33,w3,w4] (N [w10,w0,w1,w24,w2,w3,w4] (N [w10,w0,w20,w1,w2,w3,w4] L L) L) (N [w10,w0,w1,w2,w19,w3,w4] L L)) (N [w10,w0,w1,w2,w3,w4,w21] (N [w10,w0,w1,w2,w3,w4,w15] (N [w10,w0,w1,w2,w3,w4,w36] L L) L) (N [w10,w0,w1,w2,w3,w4,w25] L L)))) (N [w14,w0,w18,w1,w2,w3,w4] (N [w62,w0,w1,w2,w3,w4] (N [w10,w0,w2,w3,w4,w11] (N [w10,w0,w1,w2,w3,w4,w13] (N [w10,w0,w1,w2,w3,w4,w11] L L) L) (N [w62,w0,w1,w2,w19,w3,w4] (N [w10,w1,w2,w3,w4,w11] L L) L)) (N [w44,w0,w1,w2,w3,w4] (N [w44,w0,w1,w2,w28,w3,w4] (N [w44,w14,w0,w1,w2,w3,w4] L L) L) (N [w14,w16,w0,w1,w2,w3,w4] L L))) (N [w14,w0,w1,w2,w28,w3,w4] (N [w14,w0,w22,w1,w2,w3,w4] (N [w14,w0,w20,w1,w2,w4] (N [w14,w0,w20,w1,w2,w3,w4] L L) L) (N [w14,w0,w1,w2,w19,w3,w4] L L)) (N [w14,w0,w1,w2,w3,w4,w17] (N [w14,w0,w1,w2,w3,w4,w45] (N [w14,w0,w1,w2,w3,w4,w15] L L) L) (N [w14,w0,w1,w2,w3,w4,w41] L L))))) (N [w0,w18,w1,w2,w3,w4,w48] (N [w0,w49,w18,w1,w2,w3,w4] (N [w14,w1,w2,w3,w4,w15] (N [w14,w0,w1,w2,w3,w4,w11] (N [w14,w0,w1,w2,w3,w4,w29] (N [w14,w0,w1,w2,w3,w4,w23] L L) L) (N [w14,w0,w1,w2,w4,w29] (N [w14,w0,w1,w2,w4,w15] L L) L)) (N [w91,w0,w1,w2,w3,w4] (N [w84,w0,w1,w2,w3,w4,w21] (N [w84,w0,w1,w2,w3,w4] L L) L) (N [w91,w0,w1,w2,w3,w4,w29] L L))) (N [w0,w18,w1,w2,w28,w3,w4] (N [w0,w18,w20,w1,w2,w3,w4] (N [w0,w49,w1,w2,w3,w4] (N [w0,w49,w20,w1,w2,w3,w4] L L) L) (N [w0,w18,w1,w2,w19,w3,w4] L L)) (N [w0,w18,w1,w2,w3,w4,w21] (N [w0,w18,w1,w2,w3,w4,w50] (N [w0,w18,w1,w2,w3,w4,w15] L L) L) (N [w0,w18,w1,w2,w3,w4,w29] L L)))) (N [w0,w20,w1,w2,w56,w3,w4] (N [w0,w58,w1,w2,w28,w3,w4] (N [w0,w18,w19,w3,w4] (N [w0,w18,w1,w19,w3,w4] (N [w0,w18,w1,w2,w3,w4,w11] L L) L) (N [w0,w58,w20,w1,w2,w3,w4] L L)) (N [w0,w20,w1,w24,w2,w3,w4] (N [w0,w20,w22,w1,w2,w3,w4] (N [w0,w58,w1,w2,w3,w4] L L) L) (N [w0,w20,w1,w26,w2,w3,w4] L L))) (N [w0,w20,w1,w2,w3,w4,w17] (N [w0,w20,w1,w2,w3,w4,w55] (N [w0,w20,w1,w2,w28,w3,w4] (N [w0,w20,w1,w2,w19,w3,w4] L L) L) (N [w0,w20,w1,w2,w3,w4,w15] L L)) (N [w0,w20,w1,w2,w3,w4,w59] (N [w0,w20,w1,w2,w3,w4,w25] (N [w0,w20,w1,w2,w3,w4,w21] L L) L) (N [w0,w20,w1,w2,w3,w4,w23] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_7_1L : checkSTree aut12.fn aut34.fn 6 1 tbl_6_0 tbl_6_1 tbl_7_1L = true := by decide +kernel
def tbl_7_1R : STree := (N [w0,w1,w2,w99,w3,w4,w11] (N [w0,w1,w2,w19,w28,w3,w4] (N [w0,w92,w1,w2,w3,w4] (N [w0,w20,w2,w3,w4,w21] (N [w0,w20,w1,w2,w3,w4,w13] (N [w0,w20,w1,w2,w3,w4,w11] (N [w0,w20,w1,w2,w3,w4,w29] L L) L) (N [w0,w20,w1,w2,w4,w21] (N [w0,w20,w1,w2,w3,w59] L L) L)) (N [w0,w86,w1,w2,w3,w4] (N [w0,w75,w1,w2,w3,w4,w15] (N [w0,w75,w1,w2,w3,w4] L L) L) (N [w0,w86,w1,w2,w3,w4,w25] L L))) (N [w0,w98,w2,w3,w4,w13] (N [w0,w98,w1,w2,w3,w4,w13] (N [w0,w98,w1,w2,w3,w4] (N [w0,w92,w1,w2,w3,w4,w29] L L) L) (N [w0,w98,w2,w3,w4] L L)) (N [w0,w1,w2,w57,w3,w4] (N [w0,w1,w2,w64,w3,w4] (N [w0,w1,w2,w64,w19,w3,w4] L L) L) (N [w0,w1,w2,w34,w3,w4] L L)))) (N [w0,w1,w2,w28,w3,w4,w21] (N [w0,w1,w2,w19,w3,w4,w65] (N [w0,w1,w2,w19,w3,w4,w29] (N [w0,w1,w2,w19,w3,w4,w21] (N [w0,w1,w2,w19,w3,w4,w15] L L) L) (N [w0,w1,w2,w19,w3,w4,w11] L L)) (N [w0,w1,w2,w28,w3,w4,w15] (N [w0,w1,w2,w28,w3,w4,w69] (N [w0,w1,w2,w19,w3,w4,w63] L L) L) (N [w0,w1,w2,w28,w3,w4,w70] L L))) (N [w0,w1,w2,w80,w3,w4] (N [w0,w1,w2,w28,w3,w29] (N [w0,w1,w2,w28,w3,w4,w11] (N [w0,w1,w2,w28,w3,w4,w29] L L) L) (N [w0,w1,w2,w28,w29] L L)) (N [w0,w1,w2,w88,w3,w4,w23] (N [w0,w1,w2,w88,w3,w4] (N [w0,w1,w2,w80,w3,w4,w17] L L) L) (N [w0,w1,w2,w99,w3,w4] L L))))) (N [w0,w1,w2,w3,w4,w21,w29] (N [w0,w1,w2,w3,w4,w15,w11] (N [w0,w1,w2,w3,w4,w55] (N [w0,w1,w2,w3,w4,w69] (N [w0,w1,w2,w99,w4,w11] (N [w0,w1,w2,w99,w4] L L) L) (N [w0,w1,w2,w3,w4,w46] (N [w0,w1,w2,w3,w4,w36] L L) L)) (N [w0,w1,w2,w3,w4,w15,w23] (N [w0,w1,w2,w3,w4,w15,w21] (N [w0,w1,w2,w3,w4,w15,w17] L L) L) (N [w0,w1,w2,w3,w4,w15,w29] L L))) (N [w0,w1,w2,w3,w4,w60] (N [w0,w1,w2,w3,w4,w50] (N [w0,w1,w2,w3,w4,w15,w81] (N [w0,w1,w2,w3,w4,w15,w76] L L) L) (N [w0,w1,w2,w3,w4,w70] L L)) (N [w0,w1,w2,w3,w4,w21,w23] (N [w0,w1,w2,w3,w4,w21,w25] (N [w0,w1,w2,w3,w4,w41] L L) L) (N [w0,w1,w2,w3,w4,w21,w27] L L)))) (N [w0,w1,w2,w3,w4,w11,w76] (N [w0,w1,w2,w3,w4,w21,w89] (N [w0,w1,w2,w3,w4,w21,w13] (N [w0,w1,w2,w3,w4,w21,w76] (N [w0,w1,w2,w3,w4,w21,w11] L L) L) (N [w0,w1,w2,w3,w4,w21,w65] L L)) (N [w0,w1,w2,w3,w4,w29,w81] (N [w0,w1,w2,w3,w4,w29,w89] (N [w0,w1,w2,w3,w4,w29,w11] L L) L) (N [w0,w1,w2,w3,w4,w48] L L))) (N [w0,w1,w2,w3,w4,w63] (N [w0,w1,w2,w3,w4,w76] (N [w0,w1,w2,w3,w4,w11,w63] (N [w0,w1,w2,w3,w4,w11,w13] L L) L) (N [w0,w1,w2,w3,w4,w65] L L)) (N [w0,w1,w2,w3,w59] (N [w0,w1,w2,w3,w4,w81] (N [w0,w1,w2,w3,w4,w89] L L) L) (N [w0,w1,w2,w3,w23,w29] L L))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_7_1R : checkSTree aut12.fn aut34.fn 6 1 tbl_6_0 tbl_6_1 tbl_7_1R = true := by decide +kernel
def tbl_7_1 : STree := N [w0,w20,w1,w2,w3,w4,w27] tbl_7_1L tbl_7_1R
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_7_1 : checkSTree aut12.fn aut34.fn 6 1 tbl_6_0 tbl_6_1 tbl_7_1 = true :=
  checkSTree_node (by decide +kernel) chk_tbl_7_1L chk_tbl_7_1R
lemma nolive_7_1 : ∀ v, MemSTree v tbl_7_1 → ∀ m ≤ 7, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 6 1 tbl_7_1 tbl_6_0 tbl_6_1 nolive_6_0 nolive_6_1 chk_tbl_7_1
def tbl_8_0 : STree := (N [w5,w0,w1,w2,w3,w4] (N [w7,w0,w1,w2,w3,w4] (N [w9,w0,w1,w2,w3,w4] L L) L) (N [w0,w1,w2,w3,w4] L L))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_8_0 : checkSTree aut12.fn aut34.fn 7 0 tbl_7_0 tbl_7_0 tbl_8_0 = true := by decide +kernel
lemma nolive_8_0 : ∀ v, MemSTree v tbl_8_0 → ∀ m ≤ 8, ¬ Live m 0 v.toFinset :=
  layer_step_sound aut12 aut34 7 0 tbl_8_0 tbl_7_0 tbl_7_0 nolive_7_0 nolive_7_0 chk_tbl_8_0
def tbl_8_1 : STree := (N [w0,w1,w2,w28,w3,w4] (N [w0,w18,w1,w2,w3,w4] (N [w14,w0,w1,w2,w3,w4] (N [w10,w0,w1,w2,w3,w4] L L) L) (N [w0,w1,w2,w19,w3,w4] (N [w0,w20,w1,w2,w3,w4] L L) L)) (N [w0,w1,w2,w3,w4,w29] (N [w0,w1,w2,w3,w4,w21] (N [w0,w1,w2,w3,w4,w15] L L) L) (N [w0,w1,w2,w3,w4,w11] L L)))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_8_1 : checkSTree aut12.fn aut34.fn 7 1 tbl_7_0 tbl_7_1 tbl_8_1 = true := by decide +kernel
lemma nolive_8_1 : ∀ v, MemSTree v tbl_8_1 → ∀ m ≤ 8, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 7 1 tbl_8_1 tbl_7_0 tbl_7_1 nolive_7_0 nolive_7_1 chk_tbl_8_1
def tbl_9_0 : STree := L
lemma nolive_9_0 : ∀ v, MemSTree v tbl_9_0 → ∀ m ≤ 9, ¬ Live m 0 v.toFinset := fun _ h => False.elim h
def tbl_9_1 : STree := (N [w0,w1,w2,w3,w4] L L)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma chk_tbl_9_1 : checkSTree aut12.fn aut34.fn 8 1 tbl_8_0 tbl_8_1 tbl_9_1 = true := by decide +kernel
lemma nolive_9_1 : ∀ v, MemSTree v tbl_9_1 → ∀ m ≤ 9, ¬ Live m 1 v.toFinset :=
  layer_step_sound aut12 aut34 8 1 tbl_9_1 tbl_8_0 tbl_8_1 nolive_8_0 nolive_8_1 chk_tbl_9_1
lemma r8_in_8_0 : inTbl aut12.fn aut34.fn tbl_8_0 r8 = true := by decide +kernel
lemma r8_in_9_1 : inTbl aut12.fn aut34.fn tbl_9_1 r8 = true := by decide +kernel

lemma no8_0 : ∀ k ≤ 8, ¬ Live k 0 r8.toFinset := by
  intro k hk hl
  obtain ⟨v, A, hmv, hA⟩ := inTbl_sound aut12 aut34 tbl_8_0 r8 r8_in_8_0
  exact nolive_8_0 v hmv k hk (hA.symm ▸ live_aut A hl)

lemma no8_1 : ∀ k ≤ 9, ¬ Live k 1 r8.toFinset := by
  intro k hk hl
  obtain ⟨v, A, hmv, hA⟩ := inTbl_sound aut12 aut34 tbl_9_1 r8 r8_in_9_1
  exact nolive_9_1 v hmv k hk (hA.symm ▸ live_aut A hl)

lemma upper8 : ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length = 10 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8e880 x :=
  ⟨[⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.and,[6,8]⟩,⟨.or,[9,7]⟩,⟨.and,[0,10]⟩,⟨.or,[0,8]⟩,⟨.and,[5,12]⟩,⟨.or,[11,13]⟩], 14, by simp, rfl, by decide +kernel⟩

lemma fn8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = evalT 0xeae8e880 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = evalT 0xeae8e880 x :=
  replace_from_nolive 0xeae8e880 10 r8 rfl (by decide +kernel) (by decide +kernel) no8_0 no8_1 upper8 gs o h hn he

end PEqualNP.Outside.L_meta_1427_aux

theorem PEqualNP.Outside.L_meta_1427 : ∀ T ∈ ({0xeae8e800, 0xe8e8e888, 0xeaa8a8a8, 0xeaa8e888, 0xeaaac888, 0xeaaae880, 0xeac8e888, 0xeac8e8c0, 0xeae8e880, 0xeae8ea00} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1427_aux.fn0
  · exact PEqualNP.Outside.L_meta_1427_aux.fn1
  · exact PEqualNP.Outside.L_meta_1427_aux.fn2
  · exact PEqualNP.Outside.L_meta_1427_aux.fn3
  · exact PEqualNP.Outside.L_meta_1427_aux.fn4
  · exact PEqualNP.Outside.L_meta_1427_aux.fn5
  · exact PEqualNP.Outside.L_meta_1427_aux.fn6
  · exact PEqualNP.Outside.L_meta_1427_aux.fn7
  · exact PEqualNP.Outside.L_meta_1427_aux.fn8
  · exact PEqualNP.Outside.L_meta_1427_aux.fn9
