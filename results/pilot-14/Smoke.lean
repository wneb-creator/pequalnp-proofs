import SlimCompact1007
import Batteries.Tactic.OpenPrivate

export private
  PEqualNP.Outside.L_meta_670_aux.Base1007.bin_comm
  PEqualNP.Outside.L_meta_670_aux.Base1007.target_proper
  PEqualNP.Outside.L_meta_670_aux.Base1007.live_proper
  PEqualNP.Outside.L_meta_670_aux.Base1007.bin_laws
  PEqualNP.Outside.L_meta_670_aux.Base1007.neg_laws
  PEqualNP.Outside.L_meta_670_aux.Base1007.operand_cases
  PEqualNP.Outside.L_meta_670_aux.Base1007.bin_rep
  PEqualNP.Outside.L_meta_670_aux.Base1007.gate_rep
  PEqualNP.Outside.L_meta_670_aux.Base1007.pull_gate
  from SlimCompact1007

-- LiveSearch414
namespace PEqualNP.Outside.L_meta_670_aux.LiveCheck

abbrev B := BitVec 414
abbrev Sig := B × B
def top : B := BitVec.allOnes 414
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



def raw0 : Sig := (0x4c10398cc00b18000008400003f18000988903a6401040001075b00018486cd19e4a0000071cffffc40001ffffb0001c0007fff, 0x4c10098c400b1a91000854880131a910888901a6401055081014b542080024508e4aa88000044a88855100951135440d5102a22)
def raw1 : Sig := (0x210a52610c0402000032180002c860000f8000c38766180006249c00018b19302607ffffd9a932000180006400040001ffffffff, 0x210a52610804024086321a0462486408c300004081661a0866249482190108100201104398a9130461a08c2608c48231208d411c)
def raw2 : Sig := (0x1c01f2583c0000c0e00004f180000e41030c788020000038e7fffe4c61c23878c00021ce3c00020000780007fffe7fff8000, 0x40052583c1850c0e0c284b181850c410100288020c280080130a44c21c23828c62821422c62820c5058c50131444c5218a0)
def raw3 : Sig := (0x600607e0080c000000300000701fffff00e1c0f8007c00007c0f80000707e03c07f00003e0fc00003ffff800007ffff80000000, 0x600002a0080c001a203000d2000281a600e140f8007c0192340f80648105e01405700d10a0dc00d20c1a5001a46069981a40348)
def raw4 : Sig := (0x380c7f80031f000000fc000007fe000000701ff000f8000007ff0000007f8003ff8000003ff0000003fffffffff8000000000000, 0x380c7f00031f005244fc029247ec052480700be000f802a244be00a8906f8002b700152235f00152432a4a76a4a0a9202a485490)
def raw5 : Sig := (0xf800003e0000000fffffff8000000007fe00000fffffff8000000007ffffc000000003ffffffffc0000000000000000000000, 0x3e000006657280370000006c053200000aa680370000000d87ffdb8000000333fffba0370006c0006c001b0006c00d8)
def raw6 : Sig := (0x3ff0000003ffffffff00000000000000007fffffff00000000000000007fffffffffffffc0000000000000000000000000000000, 0xe50000003e9d4837800001b80000037007fffbf7e0000338000000ce07ef7effdfee1bc0000001b8003700037000dc0037006e0)
def raw7 : Sig := (0x3ffffffffc0000000000000000000000007fffffffffffffffffffffff8000000000000000000000000000000000000000000000, 0x3ffffbffac0000638000031c00000638002cdeffd755973c07f7fecf01800000000019c00000019c003380033800ce0033806700)
def raw8 : Sig := (0x3fffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000, 0x31afffd5fc162b7c00a8d7e007ffd7c00f800000000003c0000000f00000000000001e00000001e0003c0003c000f0003c007800)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
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
  by_cases hi : i < 414
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 414 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 414
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 414 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 414 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 414)] <;> simp [hi]
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

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
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
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
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
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 414).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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

def sample (s : Bool) (i : Fin 414) (j : Fin 9) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
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

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
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

lemma circuit_live (C : Circuit) (hc : C.size ≤ 15)
    (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ k ≤ 15, ∃ t ≤ 7, Live k t raw.toFinset := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  subst S
  have sz := live_size ht
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length = 9 := rfl
  change C.gates.length ≤ 15 at hc
  exact ⟨k,hk.trans hc,t,by omega,ht⟩


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
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]]

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  (tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
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
  rcases h with ⟨⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨h1,h2⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
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
  exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
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
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    apply Bool.or_eq_true_iff.mpr
    left
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf ht (by simpa only [bin_comm d b a] using ih)
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
  cases h with
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
    refine ⟨by simp, unary_found hv he (by omega) hf tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
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

end PEqualNP.Outside.L_meta_670_aux.LiveCheck

-- CompactSymmetry414
namespace PEqualNP.Outside.L_meta_670_aux.LiveCheck



def symKeys : Fin 12 → Nat := ![
  0x33b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200,
  0x22d0884c0e05107ebf9f6fc59a75508f472d94379b9dd1649c4dab55c954b24d2976b65b6d56b53a9b18d567e01958ac5bdda6d467336fd7fbe5f5dac864afd7ac5622e986c25f31d82c6602f176b99bcd8f07723114e6328dc6a326d360782c140d86822190c0543a170e04c241007ce8fa59abd5a6b343b1108730979c4e430188a04c2d16088562a138bc522e128904621a7d3a9a6b356760f0680c01ff987d3e5f10c85c2b379c8ac520b04cd666271288e5b2f94cac3e1d0db92c5609a4cab1569248a42d2a5522350a8345225108742209188645a05007f3f2d568a04fa7af170b8abd3097bbdbedcaa54dd6cf68af572c963b0d82bb5bb357ecb5aacd8ab0a351639b4d9c9e25ecf5696170cf278b319791bdde9d8eb5c2df1ad86bb5b2588c3bd1e6d16860f0981c13c1deeec863dd4e16fb9dcce572381d2e374389bcdd6e36e727c3d960af55aa4ccea42a8cb65c701007e994b8c45cd20702830160a048181c0806810060200802707a3c9589c4c29948a250269549e5425928924823d4ea532989d074381f8f87a3c1c90476401b8d86a3419d42572c91482512792c92432a91ca63f1e8ec9a386f3752a833fa3d1a8943a052685489f4f68b3c9d984be6632990c66034188ce5e2e970b65a,
  0x2190a85e3b1ad86cb69acd781c099ccf66e6b33138944603007fe0f0985c360704f0793c5deee65b316ca19d1f4b2b45aa813c9f9cce0f67c3c9e8ac572c1409e4d25120a2552a138a64b24930a447572b52c954a24e612f399c8e231180c8542913890462b178b8502d12898582210ddedf6e552a558ab492452151a84ae592d9749247218f4764b2a94c8a511f9049e4d1c381bcdc1f1045a1308c662f14f76ab51a79dcde722b1482c120f06c9e4b1388c3bd9eaf479b49a2d0883f9fafc7ddfefd80bedf1dac96432984c15f2ed86c7633017ec55e2f588ba5ce5b2f98ca6561f0e86be9f2f8c86471f7abdba9d8eb7238dc0dd72ba5d0e270b9dbcdf73371b6b75c5e6e774592cd389b4ed5ead359a4de6c763c1dc884323116f172b85c55eb1582612e9a4cd56a953a94ce65313a9d0843c1d8e46c3d20900743f1b8d4703e1a0ceed6cb6daad6a7532a11e8ea7d3a9b1b8d464d66a369b03c180b85424190e8702c1b0985034110803eeb67b45a6c15faed66c366b2d7ac95aae58eb762ac28d44a5522350e8642201108c45a15148141a25047f3f52a994ba1d0a813da25269141a3cfa7f46a2cf277178c1a4c66230174c86833984cc5e2f994b85b2d0241006018281c0d038300805058040400,
  0x2190a85ad942a05a2d53c9fcd666df77b740e0501803fe271288a592aae56a512692562ad229054aab1d8d9d4e670d96d361acd73e964f67c2b960ac793d1409a4f25120a24e26154a64b24950a447c2e1b0784c0e0a612fa8cb65d2b96542492191c7a3b259148255288fca64f268e33d9ccd6632de4f1783bddc73190c46072388a84e291208c5628130bc5a25170b04421380803e6e37e77379cbcdcee972bc5c2e31684c220f0682c122b1459a75649c4dac5609a4cabd3097cc65b2f94cadb2db76b55aed367b45d6c15dafd66c35eae56ecd64ad596c762ac3f9fb107e3edf4f97c43e1d0d47aa11ca653a354aa443a110c8044215068246229028b449fcfca251e33178ac4e4f1187c94de6d359a55ead33aad526531a9d49aaf76a34da4f67ab45a0f4799e0ee46229d888433a908e83c1c8ec6c3d1d0e0823f1b8d4803e1a0cf017fbf5f6f97bbd647218f8dc6a334fa75363117a652e9543a050a7b44a0cfe93479f5228d459e4ed94c9643b584be60aed86bf5eb1d8abc6331180ba5cae16eec75ba9c8e071b75cae16fba5cede74399c4dc6d878da6c0c0542e120c858281d0d84c381a088401e6a359a412060400c14070283818040682c04010018cc0622e990c25f34198bc673296cb85a,
  0x33b9ccdde6f172ba5cee370c7636733a9c64f2589c461f198bc5556a957ab54ea5339acd265319b4df3599bbdbedd97cb6632b94bb5d6db6cb459ed36bb559ac965b1d8ac35ead582bb5cadd7eb358c260f0d85c1606a350984b2572e96cbe552894c9e4d259147e49219048e3d1d8e643238fbd5eeff7ec05f6f94fa5532974ea6d268f48a351689419f50e813fa14f6793b8dc5e31198d432170a5b2d568a050a7d3d168ac520b0483c1a1308592bd66b15827136984ba7534996c369b2d76b1f0f67d3d1e4ac582b964aa532a148a24e25924a04d2613c944823bd9eaf77a3cda4d168355a8d33a9d8e8773c1088843208fc803e1e8e86e351e0e4703b1b0d066452344e251180c0e00ff812a952ac55ab95a924b25522904a24e1f1087435f4fe7ebe5f0fc7da9d4ca3512a14aa447a351c8c4522d128842a050e8441a090c803f9f9e0f278bbddccb663399ecd381bcdc73391c43e20188c0642f168b8582b140945427130a4482311085d4ec75bb5d2e774399cae16f391c0df71b75c4dc6dadd70c9643298ec56331186bf5e3097cbd60aed80ba5c9a4d66a34198ce6532184bc633017cc45d2e16cb46c368781c0c0682c1407020240c050400c020200074361c0d0642c130c054281709040220f,
  0x22d0884e31aaf7c562da6d45b284fb3a2cacd3ab24e26ef373ba1e0ef379b1188a769acd08843ab55e070267b399afd7f441f6fcc032afd7f64325db7cbeafd8abd622e986c75e30982c6602f976b94aa595aae49a50e632980c06271394bc502d130b0442b1789454291709c482310a3d508e5329ed96dbb5aad71b0f1b4d91a8c85836140d044321d098602e1c0a848200fa79a8d74da7432170ac7369b2d8c6b5dad9d83c1a0b048ac53379cc4b4b26f67ae230ed168649e8f3502d5689f4f1f0f7392c15cac7a3cce09c5326148a25525924a04f2a134944823ac561724d2655e984bde2e1713accc8554aa9d265311d0fc703e1e9046e351e0ec80391b0d06752a9c0600ff89e6a2511ccb3196f278e170cf0c1e11deeec0e09f5987cbe21f96cbc3a1b94cadeef4b85be45d8ebc83ab1ee173b7dcce574b79c8e374389c0dd6e36d24ac55a4520a9555beef6e380803f5196cb8dc6f95cb2a122944824f259547e492394c863d1d934711aa5525a50a8a41a25108c40a1d0c8b42201047f3f2894767b45d6bd64ae58ec366ad582bf65aed66b762ac1a63117038300a0b050380809040340c0301004014ba6528c2662f994c8682f18cc46730174b65c2d5068f3fa3512933ea1d0a91409ecf28b3b,
  0x22d148ac4e1f1088c4a1b0ebcde2ed77baac95eb358ac16cb55a29d4caa54a8d44a8562ad4aa456abb2792c86471ef57b3dde6f4783a9e2f275bb1daee77b85c0de6eb71cae46fba5d0e37139dccdbaa556ad57a954e9f4aa8d2e994da754283409f4f67944a1cfe9348a151e8d459d9d4ec743b9e0f87b3e9e8f270349acd46f37184c05e2e970c8632f9a0ce6233194b65a399b0da7139677379ccd65b2f98cce532b0c82c120f0684c22170a80bea06fe7ec01fef97c409f8fbb95cee970b8db2db6fb3da2d36ab5dbabd5dad566c360ae56ecd65afd92c762ac27136a04c25d3a9a4ca853e9e47a491a954b239229042a1102804421d06824622d0c8a449fcfc934a6271187c663b178ac6deaf77fbf6130780c3616fb7cc1605a4d868b41aada6cb51a6d76b32d98b75c33992c867b299abf5f2f176c3612f58ec660b018ac45d2e667359a4ca63369bce675388dc5e3130964ae331a974b65f2290c7e3d2592482552991ca24f268ec7084442195874391b8d87a3c1c104803b1f8f86a34199148c582b9649c4d25928a25026154a84f299489248238783e20038180803050240a0e06820180b008080030188c82c150984832180a07438170d8682011078a04e25120ac5426178b8522d160884621,
  0x33b0683c05f5987fc01f0f9c635700cf65625a5937b3d71cda6cdeef4cc65ae16f91793c5d8ebc3615669d47aa11cb058dc9329a4923556ac52296d29048a310c81401fd108745a15068441229127e3b9e26d372291a361e399b0db198d0c83a170984820190c0702c140a86c3411079d66642aa554f87b9c960ae7034c622e200f83810040180814090681c0a060602c0200a8d2e992e96c5a130881bf9fb10813f1f70c82c122b14cde72170a89c3f3596cbc4a230e86e6729957be2f14d469dfefcce64b21db7dbe3358ec15e2ed86c2633017ebd5f31588ba5ce230ed868b4324f479e35aed6c83c1d584c1e3ddeee74b8dbcdd72b91d0e270b7dc0e773371b782c0ac9389bbcadae77450a994f6cb6a552d7656abad56b49a515ea04c25ef0b55a5c2e29f4f2a554a251dbecf68bbdd6dd66afd6ab361b0596bd5caed6ec963b1560ed359a1108756ab9f67459a79a8d730180c69b4e389ca5e2f14894482b150b85026138b4582211884e93298958823b1b8d87a3c200e870391f8f86a3419d4aa67a3cce0aa4f25928a2502a138984d29948924823d28dc6f34188bc5d3218cce612f980cc652d970b52c95d4293429f4f68943a45067f40a3d1a79459dcaa471f8f496492991482432893c9a3b1c,
  0x22d148ae4f24f77abd9e6f4592bcec753a5e6f0b65aad166b15855aaf54aad4aa67d3e1ecf4793c1de270fc83c1d511894421b0ec8e3de2f2773bddaeb76385bce06eb71cae973b91d0e37137dccdb552a54ea651a8a9f4a381bcdc6b351a4c25e30174b86434198c6673117cca5b2d5deed75572b558ab542954951a85369d4ba65067d409ecf28949a3d0e91429fd1a8b3b399c8e26d364320b04c4e230ed869345a19dcde72170a84c220f06c7637198bc5369b2d76b355a8d35027136984bcd66933994c4ac442190874371c8d87a411f8d478401d8e07c3419dcee972b85c5429f4f27534999d4e671379b164b0572712c9a4a28954a649281509e4c291208e4622e6b2d9781c05fcfd7d613077fbf5eaf6ce65b3192c85bae33398ca65605007fbf1f6f97c61b0b82c0e02fb7c67b3594bf5e2f976c363b1584c660b017ac45d2e6df6cb6d9ed0964aa491e8d984b2571b8bc6062300f8803c0702018060a07030120d04014160101002dd6ab5da6bd5aaed66c366b2582cb5fae58eb762ac2512691482390a8142201108c4521d168641a25047f3f4be5d2d9147e431e92caa512494c8e412793476391a8c8c8502513890562f168a85c29130b04622108582615090643a1b0c0702e140d044200f,
  0x33b0683acd3b72582c5329ac4b4a667521631ab8e6d36726f67acda6e773c1148d393e1ecb057aad5202fa47a491aff80661f0f95423956ac48246d2a452a310286401fd10854521d06844122d127e6632ef77a5c2de361e380803f188b9a41c040400c040a0383012050303416010033f00cac2e19e4f1c8bb1d67319466346c3687426170904032160d86028150e068220fa8cb65d4ca5c320b045927136a057a612f1684c22170acde722b145b286f373ba2d5689f4f5e2e1716c6230ed1684d668762210cad32989d082371d8d87a3a1f8d478381c9007c3419e2f14f76a34f1ad76b649e8f39d1f4b357ab4e0f4792a92c9e4a28938a649281309a54291208f53a940dfcfdcd44f2d9787a552d6cb6a994f6f54aaacf685128e05107e3ef331288e532b0e86ab55c934a5dad56bbbdbaeb66ad57eb361af592c15caed6ecb63b15619d7fbf3259183c23c320ea980c0634f351ae572c371be94682f188ba6430998c65f3019cca5b2e1699b7dbe3b58ebc60aed86bf62b097abe6331180ba5ce0704ef7763dd2de71b75cae173b91bee074399c4dc6dcbce272178945224158a05a2a1309c5c2c1108c434ea6d42551f91c7a4b2294492412194c9e3b268e5267d429ed128347a1cfe8148a3516793b,
  0x2190482e25a4d8c3e21a0d189c3de19075405f5037f3f73596cbb2d997abdadd70cebfdf992c8c1e1164af3a9d8e89b4e2812e989990a693521910ad31990f080381f0d07a411d8e86e3f1a8e46c335329d52aa5128ce069a79a8d66e37d28c6672f994b66434188c25e33180ba5c2d23d248d4aa5ad96db7d9ed11b0f07c41178c0241a0505804140e0401c080c0300c0400980c0632b9645a2b14c9bd9eaf7c93d1e79d83c1a130885c2b379cc63571cda6ce2f14d469e35aed68844a230e86bc9e391763addaef7763dc8e86fb99cae971b89c2de73b81badc6dc01ff987cbe204fc7de67299567e019585c3336fb7c613197ac461b1d82c05faf18abe5dae97381c12cd62b05b5e56ab4bc1dcf07c3dd52aa7dab55cf479a954d3b724d2654373ba27d3d70b8cda6e45234e4b0579d16670502a130a4512a93c9c4b299249a4a2411d50ac55a9548ad575daef75399b0db51a5d30e272a6d3aa143a44fe8d44a4d0a833ea3d027b3ca2ced1c91485a50e8b41a25108c43215028a42201047f3f24d296ab5dbac165ae58ec366afd7ab564aed66b762ac0ca331a0c070281a0c8742e160986c2a12080441f2d974bc542e130b0562f148a04a2d13890442310c92532093c9655239147e51218f4764d1c,
  0x2190482ac95ea04da712e9880be9248f46c4e1f9acb65e06fe7eaa554a653a89476fb65b6cf684b25712d23accc8587c4361a0d13b1d2693598cc8ac43220f070401f0d07a3a1c9046e3f1a8ec6c33bd5ed96cc5bae0e0698dc5e301f1007812050682c020a038181c0406020060200641e0eac260eff7e67325914fa51b8de6a3598cbe673296cc861301a0bc6631174b85a984b25631186760f0659ac561724ea6933168ac53379c85c2a1308bcde16cb55a5cee970b8a853e9ecc401fef97c2b156a852a92d291482390e8345a25108542209188145219007f3f44a2310874373394cac09f8fbbbddaeaae56dbad56bb0572cb63b0d7abb5bb356ac95facd8ab09449e4decf5c7631b4d96ad52aa7c3d9dcf1399b4dcb0572291b24f77a3cf1b8bc535dacd469d5aaf52a99f4f4799d4e0b25026150a45127134aa4b299249e4a2411f22f278bb1d786c2e019ecaa8d2e9873361b65d2d8cc6864180a07034190b0543a130d85c24100883f1eef773b5c8df74399cae1703a5bce771b75c4dc6de0b037dbe33584bd6331186bf5f31d78c560aed80ba5cd429b4ea1cfe9146a250681499f51e853d9e516767238cbe492094c9e4b2290caa3f2891c7a4d1d8e0a84c2e160ac5027178945a291208c4421]

def inverseAuto : Fin 12 → Fin 12 := ![0, 1, 2, 8, 4, 11, 6, 7, 3, 9, 10, 5]

def index (key : Nat) (j : Fin 414) : Fin 414 := Fin.ofNat 414 ((key >>> (9 * j.val)) &&& 511)

def reindex (f : Fin 414 → Fin 414) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 414 → Fin 414) (a : B) (j : Nat) (hj : j < 414) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 414 → Fin 414) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 414 → Fin 414) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 414 → Fin 414) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

def symmetrySelector (g : Fin 12) : Fin 414 → Fin 414 := index (symKeys g)

def inverseSelector (g : Fin 12) : Fin 414 → Fin 414 := symmetrySelector (inverseAuto g)

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_0 : ∀ j : Fin 414,
    inverseSelector 0 (symmetrySelector 0 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_1 : ∀ j : Fin 414,
    inverseSelector 1 (symmetrySelector 1 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_2 : ∀ j : Fin 414,
    inverseSelector 2 (symmetrySelector 2 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_3 : ∀ j : Fin 414,
    inverseSelector 3 (symmetrySelector 3 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_4 : ∀ j : Fin 414,
    inverseSelector 4 (symmetrySelector 4 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_5 : ∀ j : Fin 414,
    inverseSelector 5 (symmetrySelector 5 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_6 : ∀ j : Fin 414,
    inverseSelector 6 (symmetrySelector 6 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_7 : ∀ j : Fin 414,
    inverseSelector 7 (symmetrySelector 7 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_8 : ∀ j : Fin 414,
    inverseSelector 8 (symmetrySelector 8 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_9 : ∀ j : Fin 414,
    inverseSelector 9 (symmetrySelector 9 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_10 : ∀ j : Fin 414,
    inverseSelector 10 (symmetrySelector 10 j) = j := by decide +kernel

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse_11 : ∀ j : Fin 414,
    inverseSelector 11 (symmetrySelector 11 j) = j := by decide +kernel

lemma symmetry_left_inverse (g : Fin 12) (j : Fin 414) :
    inverseSelector g (symmetrySelector g j) = j := by
  fin_cases g
  · exact symmetry_left_inverse_0 j
  · exact symmetry_left_inverse_1 j
  · exact symmetry_left_inverse_2 j
  · exact symmetry_left_inverse_3 j
  · exact symmetry_left_inverse_4 j
  · exact symmetry_left_inverse_5 j
  · exact symmetry_left_inverse_6 j
  · exact symmetry_left_inverse_7 j
  · exact symmetry_left_inverse_8 j
  · exact symmetry_left_inverse_9 j
  · exact symmetry_left_inverse_10 j
  · exact symmetry_left_inverse_11 j

lemma reindex_injective {s inv : Fin 414 → Fin 414} (h : Function.LeftInverse inv s) :
    Function.Injective (reindex s) := by
  have hs := Finite.surjective_of_injective h.injective
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨x,hx⟩ := hs ⟨j,hj⟩
  have c := congrArg (fun a : B => a.getLsbD x.val) eq
  simpa only [reindex_bit _ _ _ x.isLt, Fin.eta, hx] using c

def action (g : Fin 12) (a : Sig) : Sig :=
  (reindex (symmetrySelector g) a.1, reindex (symmetrySelector g) a.2)

lemma action_neg (g : Fin 12) (a : Sig) : action g (neg a) = neg (action g a) := by
  simp [action, neg, reindex_not]

lemma action_bin (g : Fin 12) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := by
  cases d <;> simp [action, bin, reindex_and, reindex_or]

lemma action_zero (g : Fin 12) : action g zero = zero :=
  Prod.ext (reindex_zero _) (reindex_zero _)

lemma action_one (g : Fin 12) : action g one = one :=
  Prod.ext (reindex_top _) (reindex_top _)

lemma action_target (g : Fin 12) : action g target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma action_injective (g : Fin 12) : Function.Injective (action g) := by
  intro a b eq
  have hi := reindex_injective (symmetry_left_inverse g)
  have hf : reindex (symmetrySelector g) a.1 = reindex (symmetrySelector g) b.1 :=
    congrArg (fun x : Sig => x.1) eq
  have hs : reindex (symmetrySelector g) a.2 = reindex (symmetrySelector g) b.2 :=
    congrArg (fun x : Sig => x.2) eq
  exact Prod.ext (hi hf) (hi hs)

lemma action_proper (g : Fin 12) (a : Sig) (h : proper a) : proper (action g a) := by
  constructor
  · intro h0
    exact h.1 ((action_injective g) (h0.trans (action_zero g).symm))
  · intro h1
    exact h.2 ((action_injective g) (h1.trans (action_one g).symm))

lemma live_action {k t : Nat} {S : Finset Sig} (h : Live k t S) (g : Fin 12) :
    Live k t (S.image (action g)) := by
  induction h with
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
    have hne : bin d (action g a) (action g b) ∉
        insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← Finset.image_insert, ← Finset.image_insert, ← action_bin]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Live.binary (action_proper _ _ ha) (action_proper _ _ hb)
      (fun e => hab ((action_injective g) e)) hne ih

lemma rotate_impossible {k t : Nat} {w z : List Sig} (g : Fin 12)
    (hp : (w.map (action g)).Perm z) (hn : Impossible k t z) : Impossible k t w := by
  intro m hm h
  apply hn m hm
  suffices hi : z.toFinset = w.toFinset.image (action g) by rw [hi]; exact live_action h g
  ext a
  simp only [List.mem_toFinset, hp.mem_iff.symm, List.mem_map, Finset.mem_image]

def rawPermCodes : Fin 12 → Nat := ![0x876543210, 0x267143850, 0x374268501, 0x547068321, 0x846375012, 0x64175832, 0x567840123, 0x176240583, 0x364872105, 0x146072385, 0x74561238, 0x247361058]

def rawSym (g : Fin 12) (i : Fin 9) : Fin 9 :=
  Fin.ofNat 9 ((rawPermCodes g >>> (4*i.val)) &&& 15)

def rawImage (g : Fin 12) (i : Fin 9) : Sig := raw.getD (rawSym g i).val zero

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_0 : ∀ i : Fin 9,
    rawImage 0 i = action 0 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_1 : ∀ i : Fin 9,
    rawImage 1 i = action 1 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_2 : ∀ i : Fin 9,
    rawImage 2 i = action 2 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_3 : ∀ i : Fin 9,
    rawImage 3 i = action 3 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_4 : ∀ i : Fin 9,
    rawImage 4 i = action 4 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_5 : ∀ i : Fin 9,
    rawImage 5 i = action 5 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_6 : ∀ i : Fin 9,
    rawImage 6 i = action 6 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_7 : ∀ i : Fin 9,
    rawImage 7 i = action 7 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_8 : ∀ i : Fin 9,
    rawImage 8 i = action 8 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_9 : ∀ i : Fin 9,
    rawImage 9 i = action 9 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_10 : ∀ i : Fin 9,
    rawImage 10 i = action 10 (raw.getD i.val zero) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq_11 : ∀ i : Fin 9,
    rawImage 11 i = action 11 (raw.getD i.val zero) := by decide +kernel

lemma rawImage_eq (g : Fin 12) (i : Fin 9) :
    rawImage g i = action g (raw.getD i.val zero) := by
  fin_cases g
  · exact rawImage_eq_0 i
  · exact rawImage_eq_1 i
  · exact rawImage_eq_2 i
  · exact rawImage_eq_3 i
  · exact rawImage_eq_4 i
  · exact rawImage_eq_5 i
  · exact rawImage_eq_6 i
  · exact rawImage_eq_7 i
  · exact rawImage_eq_8 i
  · exact rawImage_eq_9 i
  · exact rawImage_eq_10 i
  · exact rawImage_eq_11 i

lemma rawSym_bijective : ∀ g : Fin 12, Function.Bijective (rawSym g) := by decide

def pairReps : List (Fin 9 × Fin 9) := [(0,1), (0,2), (0,3), (0,4), (0,6), (4,6)]

set_option maxRecDepth 10000 in
lemma pair_orbits : ∀ i j : Fin 9, i ≠ j → ∃ g : Fin 12,
    (rawSym g i, rawSym g j) ∈ pairReps ∨ (rawSym g j, rawSym g i) ∈ pairReps := by
  decide +kernel

lemma unary_orbits : ∀ i : Fin 9, ∃ g : Fin 12, rawSym g i = 0 ∨ rawSym g i = 4 := by
  decide
def recipeFuel : Nat := 31

def recipeStep (rho : Fin 9 → Sig) (op : Nat) (w : List Sig) : List Sig :=
  if op ≤ 9 then rho (Fin.ofNat 9 (op-1)) :: w
  else match w with
  | [] => []
  | a :: t =>
    if op = 10 then neg a :: t
    else match t with
    | [] => []
    | b :: r => bin (decide (op = 12)) a b :: r

def recipeRun (rho : Fin 9 → Sig) : Nat → Nat → List Sig → List Sig
  | 0, _, w => w
  | n+1, code, w =>
    if code = 0 then w else
      recipeRun rho n (code >>> 4) (recipeStep rho (code &&& 15) w)

lemma recipeStep_map (g : Fin 12) (rho : Fin 9 → Sig) (op : Nat) (w : List Sig) :
    (recipeStep rho op w).map (action g) =
      recipeStep (action g ∘ rho) op (w.map (action g)) := by
  unfold recipeStep
  by_cases h : op ≤ 9
  · simp [h, Function.comp_def]
  · simp only [ite_eq_right h]
    cases w with
    | nil => rfl
    | cons a w =>
      by_cases hi : op = 10
      · simp [hi, action_neg]
      · simp only [ite_eq_right hi, List.map_cons]
        cases w <;> simp [action_bin]

lemma recipeRun_map (g : Fin 12) (rho : Fin 9 → Sig) (n code : Nat) (w : List Sig) :
    (recipeRun rho n code w).map (action g) =
      recipeRun (action g ∘ rho) n code (w.map (action g)) := by
  induction n generalizing code w with
  | zero => rfl
  | succ n ih =>
    by_cases h : code = 0 <;> simp only [recipeRun, h, ite_true, ite_false]
    rw [ih, recipeStep_map]

def recipeValue (rho : Fin 9 → Sig) (code : Nat) : Sig :=
  (recipeRun rho recipeFuel code []).headD zero

lemma recipeValue_action (g : Fin 12) (rho : Fin 9 → Sig) (code : Nat) :
    recipeValue (action g ∘ rho) code = action g (recipeValue rho code) := by
  have h := recipeRun_map g rho recipeFuel code []
  simp only [List.map_nil] at h
  unfold recipeValue
  rw [← h]
  cases recipeRun rho recipeFuel code [] <;> simp [action_zero]

def sourceSignals (i : Fin 9) : Sig := raw.getD i.val zero

lemma sourceSignals_image (g : Fin 12) : rawImage g = action g ∘ sourceSignals := by
  funext i
  exact rawImage_eq g i

def recipeAction (hint : Sig → Nat) (g : Fin 12) (a : Sig) : Sig :=
  let code := hint a
  if recipeValue sourceSignals code == a then recipeValue (rawImage g) code
  else action g a

lemma recipeAction_eq (hint : Sig → Nat) (g : Fin 12) : recipeAction hint g = action g := by
  funext a
  simp only [recipeAction]
  split
  · rename_i h
    rw [sourceSignals_image, recipeValue_action, beq_iff_eq.mp h]
  · rfl

lemma rotate_recipe_impossible {k t : Nat} {w z : List Sig} (hint : Sig → Nat)
    (g : Fin 12) (hp : (w.map (recipeAction hint g)).Perm z)
    (hn : Impossible k t z) : Impossible k t w := by
  rw [recipeAction_eq] at hp
  exact rotate_impossible g hp hn

end PEqualNP.Outside.L_meta_670_aux.LiveCheck

-- ProjectionCore
namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007

variable {p : LiveCheck.Sig → Base1007.Sig}

def Feasible (p : LiveCheck.Sig → Base1007.Sig) (q : Nat)
    (S : Finset LiveCheck.Sig) : Prop :=
  ∃ m ≤ q, ∃ t T, Base1007.Live m t T ∧ T ⊆ S.image p

lemma feasible_mono {k k' : Nat} {S : Finset LiveCheck.Sig}
    (h : Feasible p k S) (hk : k ≤ k') : Feasible p k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hk, t, T, hl, hs⟩

lemma old_neg_rep (w : List Base1007.Sig) (a : Base1007.Sig) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases (Or.inl ha : represented w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

lemma feasible_pull {q : Nat} {S S' : Finset LiveCheck.Sig} {g : LiveCheck.Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image p).toList (p g) ∨ witness (S.image p).toList (p g))
    (h : Feasible p q S') : Feasible p (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image p).toList ++ [p g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma feasible_free {q : Nat} {S S' : Finset LiveCheck.Sig} {g : LiveCheck.Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image p).toList (p g))
    (h : Feasible p q S') : Feasible p q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb

lemma pull_unary (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    {q : Nat} {a : LiveCheck.Sig} {U : Finset LiveCheck.Sig}
    (h : Feasible p q (insert (LiveCheck.neg a) U)) :
    Feasible p (q+1) (insert a U) := by
  apply feasible_pull (g := LiveCheck.neg a)
    (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [pn]
  exact old_neg_rep _ _ (by simp)

lemma pull_binary (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {q : Nat} {a b : LiveCheck.Sig} {d : Bool} {U : Finset LiveCheck.Sig}
    (h : Feasible p q (insert (LiveCheck.bin d a b) U)) :
    Feasible p (q+1) (insert a (insert b U)) := by
  apply feasible_pull (g := LiveCheck.bin d a b)
    (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [pb]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma free_unary (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    {q : Nat} {a : LiveCheck.Sig} {U : Finset LiveCheck.Sig}
    (ha : ¬ proper (p a))
    (h : Feasible p q (insert (LiveCheck.neg a) U)) :
    Feasible p q (insert a U) := by
  apply feasible_free (g := LiveCheck.neg a)
    (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rcases operand_cases (Or.inr ha : represented [] (p a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2 (by rw [pn,hz,neg_laws.1]))
  · exact Or.inr (fun hp => hp.1 (by rw [pn,ho,neg_laws.2]))
  · simp at hm

lemma free_binary_left (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {q : Nat} {a b : LiveCheck.Sig} {d : Bool} {U : Finset LiveCheck.Sig}
    (ha : ¬ proper (p a))
    (h : Feasible p q (insert (LiveCheck.bin d a b) U)) :
    Feasible p q (insert a (insert b U)) := by
  apply feasible_free (g := LiveCheck.bin d a b)
    (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [pb, bin_comm]
  rcases operand_cases (Or.inr ha : represented [] (p a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.1 (bin_laws _).2.2.1)
    · rw [(bin_laws _).2.1]
      exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws _).1]
      exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2 (bin_laws _).2.2.2.1)
  · simp at hm

lemma free_binary_right (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {q : Nat} {a b : LiveCheck.Sig} {d : Bool} {U : Finset LiveCheck.Sig}
    (hb : ¬ proper (p b))
    (h : Feasible p q (insert (LiveCheck.bin d a b) U)) :
    Feasible p q (insert a (insert b U)) := by
  rw [LiveCheck.bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left pb hb h

lemma feasible_live (pt : p LiveCheck.target = target)
    (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {k t : Nat} {S : Finset LiveCheck.Sig} (h : LiveCheck.Live k t S) :
    Feasible p k S := by
  induction h with
  | stop =>
    refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩
    simp [pt]
  | unary _ _ _ ih => exact pull_unary pn ih
  | binary _ _ _ _ _ ih => exact pull_binary pb ih

end PEqualNP.Outside.L_meta_670_aux.Projection

-- ProjectionCount
namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007

variable {p : LiveCheck.Sig → Base1007.Sig}

def constantSignals (p : LiveCheck.Sig → Base1007.Sig) (S : Finset LiveCheck.Sig) :
    Finset LiveCheck.Sig := S.filter (fun a => p a = zero ∨ p a = one)

def constantCount (p : LiveCheck.Sig → Base1007.Sig) (S : Finset LiveCheck.Sig) : Nat :=
  (constantSignals p S).card

lemma constantCount_mono {S T : Finset LiveCheck.Sig} (h : S ⊆ T) :
    constantCount p S ≤ constantCount p T := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ h

lemma constantCount_insert_le (a : LiveCheck.Sig) (S : Finset LiveCheck.Sig) :
    constantCount p (insert a S) ≤ constantCount p S + 1 := by
  unfold constantCount constantSignals
  by_cases h : p a = zero ∨ p a = one
  · simpa [Finset.filter_insert, h] using Finset.card_insert_le a
      (S.filter (fun a => p a = zero ∨ p a = one))
  · simp [Finset.filter_insert, h]

lemma constantCount_insert_proper {a : LiveCheck.Sig} (S : Finset LiveCheck.Sig)
    (ha : proper (p a)) : constantCount p (insert a S) = constantCount p S := by
  simp [constantCount, constantSignals, Finset.filter_insert, ha.1, ha.2]

lemma constantCount_insert_constant {a : LiveCheck.Sig} {S : Finset LiveCheck.Sig}
    (ha : a ∉ S) (hc : ¬ proper (p a)) :
    constantCount p (insert a S) = constantCount p S + 1 := by
  have hconst : p a = zero ∨ p a = one := by simpa only [proper, not_and_or, not_not] using hc
  simp [constantCount, constantSignals, Finset.filter_insert, hconst, ha]

lemma projected_bin_constant (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {a b : LiveCheck.Sig} {d : Bool} (ha : ¬ proper (p a)) (hb : ¬ proper (p b)) :
    ¬ proper (p (LiveCheck.bin d a b)) := by
  have ha' : p a = zero ∨ p a = one := by simpa only [proper, not_and_or, not_not] using ha
  have hb' : p b = zero ∨ p b = one := by simpa only [proper, not_and_or, not_not] using hb
  rw [pb]
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
    rw [ha', hb'] <;> cases d <;> simp [proper, bin, zero, one, top]

lemma count_binary_step
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {a b : LiveCheck.Sig} {d : Bool} {U : Finset LiveCheck.Sig}
    (hf : LiveCheck.bin d a b ∉ U) :
    constantCount p (insert a (insert b U)) ≤
      constantCount p (insert (LiveCheck.bin d a b) U) + 1 := by
  have htail : constantCount p U ≤ constantCount p (insert (LiveCheck.bin d a b) U) :=
    constantCount_mono (Finset.subset_insert _ _)
  by_cases ha : proper (p a)
  · rw [constantCount_insert_proper _ ha]
    exact (constantCount_insert_le b U).trans (by omega)
  · by_cases hb : proper (p b)
    · rw [Finset.insert_comm, constantCount_insert_proper _ hb]
      exact (constantCount_insert_le a U).trans (by omega)
    · rw [constantCount_insert_constant hf (projected_bin_constant pb ha hb)]
      have h1 := constantCount_insert_le (p := p) a (insert b U)
      have h2 := constantCount_insert_le (p := p) b U
      omega

lemma feasible_count (pt : p LiveCheck.target = target)
    (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {k t : Nat} {S : Finset LiveCheck.Sig} (h : LiveCheck.Live k t S) :
    ∃ q, q + constantCount p S ≤ k ∧ Feasible p q S := by
  induction h with
  | stop =>
    refine ⟨0, ?_, feasible_live pt pn pb LiveCheck.Live.stop⟩
    have hp : proper (p LiveCheck.target) := pt ▸ target_proper
    simp [constantCount, constantSignals, hp.1, hp.2]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨q, hq, hfeas⟩ := ih
    have htail : constantCount p U ≤ constantCount p (insert (LiveCheck.neg a) U) :=
      constantCount_mono (Finset.subset_insert _ _)
    by_cases hp : proper (p a)
    · refine ⟨q+1, ?_, pull_unary pn hfeas⟩
      rw [constantCount_insert_proper _ hp]
      omega
    · refine ⟨q, ?_, free_unary pn hp hfeas⟩
      have hs := constantCount_insert_le (p := p) a U
      omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    obtain ⟨q, hq, hfeas⟩ := ih
    have hfU : LiveCheck.bin d a b ∉ U :=
      fun hu => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have hstep := count_binary_step pb hfU
    by_cases hpa : proper (p a)
    · by_cases hpb : proper (p b)
      · refine ⟨q+1, ?_, pull_binary pb hfeas⟩
        rw [constantCount_insert_proper _ hpa, constantCount_insert_proper _ hpb]
        have htail : constantCount p U ≤ constantCount p (insert (LiveCheck.bin d a b) U) :=
          constantCount_mono (Finset.subset_insert _ _)
        omega
      · exact ⟨q, by omega, free_binary_right pb hpb hfeas⟩
    · exact ⟨q, by omega, free_binary_left pb hpa hfeas⟩

end PEqualNP.Outside.L_meta_670_aux.Projection

-- PrefixExtraction
namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007 PEqualNP.CircuitLowerBounds

lemma old_extract_from (gs : List Gate) (w : List Base1007.Sig)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {k t : Nat} {S : Finset Base1007.Sig} (h : Base1007.Live k t S)
    (hout : ∀ a ∈ S, a ∈ Base1007.execute gs w) :
    ∃ m t' T, m ≤ k + gs.length ∧ Base1007.Live m t' T ∧ ∀ a ∈ T, a ∈ w := by
  induction gs generalizing w k t S with
  | nil => exact ⟨k,t,S,by simp,h,by simpa [Base1007.execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨m,u,T,hm,hl,hs⟩ := ih (w++[Base1007.gv w g])
      (fun a ha => legal a (by simp [ha])) h hout
    obtain ⟨m',u',T',hm',hl',hs'⟩ := Base1007.pull_gate hl
      (Base1007.gate_rep w g (legal g (by simp))) hs
    exact ⟨m',u',T',by simp; omega,hl',hs'⟩

end PEqualNP.Outside.L_meta_670_aux.Projection

-- GeneralPrefix
namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007 PEqualNP.CircuitLowerBounds

lemma prefix_pull_from {p : LiveCheck.Sig → Base1007.Sig}
    (initial : List Base1007.Sig) (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {q : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]))
    (hf : Feasible p q S) :
    ∃ m ≤ q + gs.length, ∃ t T, Base1007.Live m t T ∧ T ⊆ initial.toFinset := by
  obtain ⟨m,hm,t,T,hl,hT⟩ := hf
  have hsub : ∀ a ∈ T,
      a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]) := by
    intro a ha
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (hT ha)
    subst a
    exact hcover b hb (Base1007.live_proper hl _ ha)
  obtain ⟨m',t',T',hm',hl',hT'⟩ :=
    old_extract_from gs (initial ++ [Base1007.zero, Base1007.one]) legal hl hsub
  refine ⟨m',by omega,t',T',hl',?_⟩
  intro a ha
  have hm := hT' a ha
  have hp := Base1007.live_proper hl' a ha
  apply List.mem_toFinset.mpr
  simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, hp.1, hp.2, or_false] using hm

lemma exclude_by_prefix_from {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (initial : List Base1007.Sig) (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {k t budget : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]))
    (hbase : ∀ m ≤ budget, ∀ u T, T ⊆ initial.toFinset → ¬ Base1007.Live m u T)
    (hcost : gs.length + k ≤ budget + constantCount p S) :
    ¬ LiveCheck.Live k t S := by
  intro h
  obtain ⟨q,hq,hf⟩ := feasible_count pt pn pb h
  obtain ⟨m,hm,u,T,hl,hT⟩ := prefix_pull_from initial gs legal hcover hf
  exact hbase m (by omega) u T hT hl

end PEqualNP.Outside.L_meta_670_aux.Projection

-- ConcreteProjection
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionData

open PEqualNP.Outside.L_meta_670_aux

def posKeys : Fin 3 → Nat := ![0xcd6673196cb6532991c863f0b85c1e0f0381c05fafd7cbe5eaf577bb5d6df6eb65b2d56ab4d9ecf58ac562b158ac562b158ac562b151a853e9b4da5d2e953b9dcee773b9dcee773b9dcee773097cb65b2b95c72391c8e472391c8e472391c8e46e33198bc5e271188c421f0d86c0e05017fbfdfafd7dbedf4f87c3c5e2f0773b9daeb75ba9b6db6db6db6db6db6db6db6db6d9ece66b2d96ca6432172b95cae572b95cae572b95cae56eb756ab556ab54aa550a65329148a2512552a9349a49209047a391a7e3f1f8fc7e3f1f8fc7e3f1f8fc73389c4e06e371b0d86a351a4b45a2d168b45a2d168b45a2d16864301808442211088442211088442211087c3e1e0783c1e0f0783c1e0f0783c1e0f000000000000000000000000000,
  0xc7635b0d96cb59acce67b370783c2e170381783c5e2ee7732d973a3e96673383d9ecf2792b15cae472391c8e472391c8e472391c8f30979cce271180c06421108844221108844221108844351a84ae572d96c72391c8e472391c8e472391c8e1c0dc6e0f87f198ac53ddaad369e4f2589c3e1deaf579bcda4d0685fafd80be5f1dac86432972b95cae572b95cae572b95cae72191c7deaf4ea75badb6db6db6db6db6db6db6db6db6d6eb7ab55a69349b4d8ec773b90c864522d52a952a94ce63313a9d08433198cc6633198cc6633198cc674fa6d3637198c9a8d46c360781e0f0783c1e0f0783c1e0f0783e954ba5cee773b9dcee773b9dcee773b9dc5e2e692d168b45a2d168b45a2d168b45a000000000000000000000000000,
  0xbcde2e573b9dc2e1399d4e2a954ab55aa55299cd2693198cda6d77b7dbaed75b65b2cf67b4daad558ac562b158ac562b158ac562b151a84c2572b96cb65f1c8e472391c8e472391c8e472394fa552e974da6cee773b9dcee773b9dcee773b9dc6e2f178cc656cb45a281429e4f2c95eb3582c1369b4ba5d3a994c9ecf67d3c9e4ac572b9648e472391c8e472391c8e472391cea763a1dcee422190c6633198cc6633198cc6633198cc8a4554aa556ab56ab524954aa41209349a994ca2512a148a447a351c7e3f1f8fc7e3f1f8fc7e3f1f8fc70371b8e6713887c3e30180c8422110884422110884422110884d26a35168b45a2d168b45a2d168b45a2d1b0d81e0000000000000000000000000000783c1e0f0783c1e0f0783c1e0f]

def negKeys : Fin 3 → Nat := ![0x4c02f60d7d5f5f37b06df6f60806b2efacdbd834177d8d5ec1a0653a8d249105816348e8c45d1b7b0682e4c09040194e054100c00033782e346b8c1a62f7b0682e4c09040194e0501970000b8d46041170fdec1a0b9302410065381406230002e35188c45c13000329df4f951826000980021f4057ca39f4f95c02006cb669bcd6b834adef60d0582410c00329c0a032e00010cb6682196b85b87af60d0582410c00329c0a030880170b70329c0c03032494ea702a8cd2a346a480a9147249222002a391b7b0682c12080329c0a82018080003379ac066f0f9acd26b0f1a6f60d05824100653814065c00800401f0f5ec1a0b048200ca70280c4611000803e1ebd8341609040194e05018440400bd8341609040194e05018080200,
  0x7621960869335a2cb04335960d045ed9b7d6582006cd37b2c100c3b112673201810de740f88084cb0400c460e06830ec041a82c000b8d00cde6b0f87840cb0400c460e06830ec040584400033787e2e208c32c1003118381a0c3b01017260000cde1f0f8801d88061d9a4d12203b100ec4035a404689d1a4d15b834177bbec68d6b70f2e19608018381ac0061d8080b088001b7bbe836f6b75c1a59608018381ac0061d8080b2e0016eb8061d8180b064ccec76021103c44214cc09323a4ce6517021d084cb0400c1c0d061d8083505804000b8d1ac171a8c1ac3c6b348799608018381a0c3b0101611010022f1834b2c10030703418760202e4c5c0045e306965820060e06830ec0405970020065820060e06830ec04058040400,
  0x3abe660c4e4c93133064ca6604061da64749983017328bccc1806492454ea3058162e8d8c4691d330602e4c070201924054100c00033782e2e1f8c08235330602e4c070201924050188c000b8bc60d31a35ccc180b9301c080649014065c0002e2f188c4680eaf0324938984881d5e075781138054c23538982101006763a1bc3e4210112660c0581c0835032480a031180008763a010ec422207a660c0581c0835032480a03008008444032480c030329d249202a4440914729c0aa346a9d466902a351d330602c0e04032480a820180800033787c066f3587c401f0f082660c0581c080649014062308800d26b0f4cc180b038100c920280cb801001a4d61e998301607020192405018040400998301607020192405018082200]

def selectBits {w v : Nat} (f : Fin v → Fin w) (x : BitVec w) : BitVec v :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma select_bit {w v : Nat} (f : Fin v → Fin w) (a : BitVec w) (j : Nat) (hj : j < v) :
    (selectBits f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [selectBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma select_and {w v : Nat} (f : Fin v → Fin w) (a b : BitVec w) :
    selectBits f (a &&& b) = selectBits f a &&& selectBits f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, select_bit _ _ _ hj]

lemma select_or {w v : Nat} (f : Fin v → Fin w) (a b : BitVec w) :
    selectBits f (a ||| b) = selectBits f a ||| selectBits f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, select_bit _ _ _ hj]

lemma select_not {w v : Nat} (f : Fin v → Fin w) (a : BitVec w) :
    selectBits f (~~~a) = ~~~selectBits f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, select_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma select_zero {w v : Nat} (f : Fin v → Fin w) : selectBits f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [select_bit _ _ _ hj]
  simp

lemma select_top {w v : Nat} (f : Fin v → Fin w) :
    selectBits f (BitVec.allOnes w) = BitVec.allOnes v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [select_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

def selector (key : Nat) (j : Fin 252) : Fin 414 := Fin.ofNat 414 ((key >>> (9*j.val)) &&& 511)

def project (i : Fin 3) (a : LiveCheck.Sig) : Base1007.Sig :=
  (selectBits (selector (posKeys i)) a.1, selectBits (selector (negKeys i)) a.2)

lemma project_neg (i : Fin 3) (a : LiveCheck.Sig) :
    project i (LiveCheck.neg a) = Base1007.neg (project i a) := by
  simp [project, LiveCheck.neg, Base1007.neg, select_not]

lemma project_bin (i : Fin 3) (b : Bool) (a c : LiveCheck.Sig) :
    project i (LiveCheck.bin b a c) = Base1007.bin b (project i a) (project i c) := by
  cases b <;> simp [project, LiveCheck.bin, Base1007.bin, select_and, select_or]

lemma project_target (i : Fin 3) : project i LiveCheck.target = Base1007.target := by
  exact Prod.ext (select_top (selector (posKeys i))) (select_zero (selector (negKeys i)))

lemma project_zero (i : Fin 3) : project i LiveCheck.zero = Base1007.zero := by
  exact Prod.ext (select_zero (selector (posKeys i))) (select_zero (selector (negKeys i)))

lemma project_one (i : Fin 3) : project i LiveCheck.one = Base1007.one := by
  exact Prod.ext (select_top (selector (posKeys i))) (select_top (selector (negKeys i)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_0 : project 0 LiveCheck.raw0 = Base1007.raw0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_1 : project 0 LiveCheck.raw1 = Base1007.raw1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_2 : project 0 LiveCheck.raw2 = Base1007.raw2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_3 : project 0 LiveCheck.raw3 = Base1007.raw3 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_4 : project 0 LiveCheck.raw4 = Base1007.zero := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_5 : project 0 LiveCheck.raw5 = Base1007.raw4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_6 : project 0 LiveCheck.raw6 = Base1007.raw5 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_7 : project 0 LiveCheck.raw7 = Base1007.raw6 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_0_8 : project 0 LiveCheck.raw8 = Base1007.raw7 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_0 : project 1 LiveCheck.raw0 = Base1007.raw1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_1 : project 1 LiveCheck.raw1 = Base1007.raw0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_2 : project 1 LiveCheck.raw2 = Base1007.raw4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_3 : project 1 LiveCheck.raw3 = Base1007.raw7 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_4 : project 1 LiveCheck.raw4 = Base1007.raw5 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_5 : project 1 LiveCheck.raw5 = Base1007.raw2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_6 : project 1 LiveCheck.raw6 = Base1007.zero := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_7 : project 1 LiveCheck.raw7 = Base1007.raw6 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_1_8 : project 1 LiveCheck.raw8 = Base1007.raw3 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_0 : project 2 LiveCheck.raw0 = Base1007.raw2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_1 : project 2 LiveCheck.raw1 = Base1007.raw1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_2 : project 2 LiveCheck.raw2 = Base1007.raw0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_3 : project 2 LiveCheck.raw3 = Base1007.raw4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_4 : project 2 LiveCheck.raw4 = Base1007.raw6 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_5 : project 2 LiveCheck.raw5 = Base1007.raw3 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_6 : project 2 LiveCheck.raw6 = Base1007.raw5 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_7 : project 2 LiveCheck.raw7 = Base1007.zero := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma proj_2_8 : project 2 LiveCheck.raw8 = Base1007.raw7 := by decide +kernel

end PEqualNP.Outside.L_meta_670_aux.ProjectionData

-- PrefixLegality
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds
def legalOp : GateOp → Bool
  | .and | .or | .not => true
  | _ => false

def legalPrefix (gs : List Gate) : Bool := gs.all fun g =>
  legalOp g.op && decide (g.inputs.length ≤ 2)

lemma legalPrefix_sound {gs : List Gate} (h : legalPrefix gs = true) :
    ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  have hh := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨?_,hh.2⟩
  have hop := hh.1
  cases hgo : g.op <;> simp_all [legalOp, hgo]


end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

-- CachedCounting
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open Projection
def cachedConstant (z : Base1007.Sig) : Bool :=
  z == Base1007.zero || z == Base1007.one

def cachedConstants (ps : List Base1007.Sig) : Nat := ps.countP cachedConstant

lemma cachedConstants_map {p : LiveCheck.Sig → Base1007.Sig}
    {v : List LiveCheck.Sig} (hv : v.Nodup) :
    constantCount p v.toFinset = cachedConstants (v.map p) := by
  unfold constantCount constantSignals cachedConstants
  rw [hv.card_eq_countP, List.countP_map]
  congr 1


end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

-- GeneralCachedPrefix
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds
open Projection

def coversCachedFrom (initial : List Base1007.Sig) (gs : List Gate)
    (ps : List Base1007.Sig) : Bool :=
  let w := Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one])
  ps.all fun z => cachedConstant z || w.contains z

def fastCachedCheckFrom (initial : List Base1007.Sig) (budget k : Nat)
    (gs : List Gate) (ps : List Base1007.Sig) : Bool :=
  decide (gs.length + k ≤ budget + cachedConstants ps) &&
    legalPrefix gs && coversCachedFrom initial gs ps

lemma coversCachedFrom_sound {p : LiveCheck.Sig → Base1007.Sig}
    {initial : List Base1007.Sig} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hc : coversCachedFrom initial gs ps = true) :
    ∀ a ∈ v.toFinset, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs (initial ++ [Base1007.zero, Base1007.one]) := by
  intro a ha hproper
  have hm : p a ∈ ps := by
    rw [hp]
    exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩
  have hh := List.all_eq_true.mp hc (p a) hm
  simp only [cachedConstant, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hh
  exact hh.resolve_left (by simpa only [Base1007.proper, not_or] using hproper)

lemma fastCachedCheckFrom_sound {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    {initial : List Base1007.Sig} {budget k : Nat} {gs : List Gate}
    {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hbase : ∀ m ≤ budget, ∀ u T, T ⊆ initial.toFinset → ¬ Base1007.Live m u T)
    (hv : v.Nodup) (hp : ps = v.map p)
    (hc : fastCachedCheckFrom initial budget k gs ps = true) :
    ∀ m ≤ k, ∀ t, ¬ LiveCheck.Live m t v.toFinset := by
  have hchecks : (gs.length + k ≤ budget + cachedConstants ps ∧
      legalPrefix gs = true) ∧ coversCachedFrom initial gs ps = true := by
    simpa only [fastCachedCheckFrom, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hcount : constantCount p v.toFinset = cachedConstants ps := by
    rw [hp, cachedConstants_map hv]
  intro m hm t
  apply exclude_by_prefix_from pt pn pb initial gs
    (legalPrefix_sound hchecks.1.2) (coversCachedFrom_sound hp hchecks.2) hbase
  omega

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

-- ProjectionDomains12
namespace PEqualNP.Outside.L_meta_670_aux.ProjectionDomains

def source (i : Fin 12) : Fin 3 := ![0,1,2,0,0,0,0,1,1,1,2,2] i

def subIndex (i : Fin 12) : Fin 4 := ![0,0,0,0,1,2,3,0,1,3,0,1] i

def project (i : Fin 12) (a : LiveCheck.Sig) : Base1007.Sig :=
  if i.val < 3 then ProjectionData.project (source i) a
  else Base1007.project (subIndex i) (ProjectionData.project (source i) a)

lemma project_target (i : Fin 12) : project i LiveCheck.target = Base1007.target := by
  unfold project
  split
  · exact ProjectionData.project_target _
  · rw [ProjectionData.project_target, Base1007.project_target]

lemma project_neg (i : Fin 12) (a : LiveCheck.Sig) :
    project i (LiveCheck.neg a) = Base1007.neg (project i a) := by
  unfold project
  split
  · exact ProjectionData.project_neg _ _
  · rw [ProjectionData.project_neg, Base1007.project_neg]

lemma project_bin (i : Fin 12) (d : Bool) (a b : LiveCheck.Sig) :
    project i (LiveCheck.bin d a b) = Base1007.bin d (project i a) (project i b) := by
  unfold project
  split
  · exact ProjectionData.project_bin _ _ _ _
  · rw [ProjectionData.project_bin, Base1007.project_bin]

lemma project_zero (i : Fin 12) : project i LiveCheck.zero = Base1007.zero := by
  unfold project
  split
  · exact ProjectionData.project_zero _
  · rw [ProjectionData.project_zero]
    exact Prod.ext (Base1007.reindex_zero _) (Base1007.reindex_zero _)

lemma project_one (i : Fin 12) : project i LiveCheck.one = Base1007.one := by
  unfold project
  split
  · exact ProjectionData.project_one _
  · rw [ProjectionData.project_one]
    exact Prod.ext (Base1007.reindex_top _) (Base1007.reindex_top _)

def budget (i : Fin 12) : Nat := if i.val < 3 then 12 else 10

end PEqualNP.Outside.L_meta_670_aux.ProjectionDomains

-- CachedRawProjection
namespace PEqualNP.Outside.L_meta_670_aux.CachedProjection

def thetaRaw : List Base1007.Sig := [
  (0xffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517, 0xfffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a, 0xfffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c, 0x808390c5d024922020e4317409248808390c5d024922020e4317409248),
  (0xfffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3, 0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238, 0xdbd45209a0000282330446c2e0004002ba9605a20001c441a981418),
  (0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880, 0x71106a60506001000aea58168800a08cc111b0b800036f514826800),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88, 0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]

def initialMap : Nat := 0x818246503862815034864518302815462038
def domainMap : Nat := 0x685841203184256830688521430848356120258041683182486503628185034645188302154682038785364012368257401765483210

def rootIndex (q : Fin 3) (i : Fin 9) : Fin 9 :=
  Fin.ofNat 9 ((domainMap >>> (4 * (9 * q.val + i.val))) &&& 15)

def domainRoot : Fin 12 → Fin 3 := ![0, 1, 2, 0, 0, 0, 0, 1, 1, 1, 2, 2]
def domainTheta : Fin 12 → Fin 4 := ![0, 0, 0, 0, 1, 2, 3, 0, 1, 3, 0, 1]

def literalInitial (q : Fin 4) (i : Fin 9) : Base1007.Sig :=
  thetaRaw.getD ((initialMap >>> (4 * (9 * q.val + i.val))) &&& 15) Base1007.zero

def wireMap (q : Fin 12) (i : Fin 9) : Nat :=
  (domainMap >>> (4 * (9 * q.val + i.val))) &&& 15

def cachedRaw (q : Fin 12) (i : Fin 9) : Base1007.Sig :=
  let j := wireMap q i
  if q.val < 3 then Base1007.raw.getD j Base1007.zero
  else thetaRaw.getD j Base1007.zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma literalInitial_eq : ∀ q : Fin 4, ∀ i : Fin 9,
    literalInitial q i = Base1007.project q (Base1007.raw.getD i.val Base1007.zero) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cachedRaw_eq_initial : ∀ q : Fin 12, ∀ i : Fin 9,
    cachedRaw q i = if q.val < 3 then
      Base1007.raw.getD (rootIndex (domainRoot q) i).val Base1007.zero
    else literalInitial (domainTheta q) (rootIndex (domainRoot q) i) := by
  decide +kernel

lemma cachedRaw_eq_project (q : Fin 12) (i : Fin 9) :
    cachedRaw q i = if q.val < 3 then
      Base1007.raw.getD (rootIndex (domainRoot q) i).val Base1007.zero
    else Base1007.project (domainTheta q)
      (Base1007.raw.getD (rootIndex (domainRoot q) i).val Base1007.zero) := by
  rw [cachedRaw_eq_initial, literalInitial_eq]

end PEqualNP.Outside.L_meta_670_aux.CachedProjection

-- CachedRawIntegration
namespace PEqualNP.Outside.L_meta_670_aux.CachedProjection

lemma rootIndex_eq (q : Fin 3) (i : Fin 9) :
    ProjectionData.project q (LiveCheck.raw.getD i.val LiveCheck.zero) =
      Base1007.raw.getD (rootIndex q i).val Base1007.zero := by
  fin_cases q <;> fin_cases i
  · exact ProjectionData.proj_0_0
  · exact ProjectionData.proj_0_1
  · exact ProjectionData.proj_0_2
  · exact ProjectionData.proj_0_3
  · exact ProjectionData.proj_0_4
  · exact ProjectionData.proj_0_5
  · exact ProjectionData.proj_0_6
  · exact ProjectionData.proj_0_7
  · exact ProjectionData.proj_0_8
  · exact ProjectionData.proj_1_0
  · exact ProjectionData.proj_1_1
  · exact ProjectionData.proj_1_2
  · exact ProjectionData.proj_1_3
  · exact ProjectionData.proj_1_4
  · exact ProjectionData.proj_1_5
  · exact ProjectionData.proj_1_6
  · exact ProjectionData.proj_1_7
  · exact ProjectionData.proj_1_8
  · exact ProjectionData.proj_2_0
  · exact ProjectionData.proj_2_1
  · exact ProjectionData.proj_2_2
  · exact ProjectionData.proj_2_3
  · exact ProjectionData.proj_2_4
  · exact ProjectionData.proj_2_5
  · exact ProjectionData.proj_2_6
  · exact ProjectionData.proj_2_7
  · exact ProjectionData.proj_2_8

lemma cachedRaw_eq_composition (q : Fin 12) (i : Fin 9) :
    cachedRaw q i = if q.val < 3 then
      ProjectionData.project (domainRoot q) (LiveCheck.raw.getD i.val LiveCheck.zero)
    else Base1007.project (domainTheta q)
      (ProjectionData.project (domainRoot q) (LiveCheck.raw.getD i.val LiveCheck.zero)) := by
  rw [cachedRaw_eq_project, rootIndex_eq]

lemma cachedRaw_eq_domains (q : Fin 12) (i : Fin 9) :
    cachedRaw q i = ProjectionDomains.project q
      (LiveCheck.raw.getD i.val LiveCheck.zero) := by
  simpa only [ProjectionDomains.project, ProjectionDomains.source,
    ProjectionDomains.subIndex, domainRoot, domainTheta] using cachedRaw_eq_composition q i

end PEqualNP.Outside.L_meta_670_aux.CachedProjection

-- DynamicClosedCore
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open PEqualNP.CircuitLowerBounds
open LiveCheck ProjectionData

structure Oracle where
  project : Sig → Base1007.Sig
  mapNeg : ∀ a, project (neg a) = Base1007.neg (project a)
  mapBin : ∀ d a b, project (bin d a b) = Base1007.bin d (project a) (project b)
  inputs : List Base1007.Sig
  check : Nat → List Gate → List Base1007.Sig → Bool

def Oracle.Sound (o : Oracle) : Prop :=
  ∀ {k t : Nat} {v : List Sig} {gs : List Gate} {ps : List Base1007.Sig},
    v.Nodup → ps = v.map o.project → o.check k gs ps = true → Impossible k t v

structure PrefixCtx where
  gates : List Gate
  roots : List Nat
  vals : List Base1007.Sig

abbrev Context (n : Nat) := Fin n → PrefixCtx

def Valid {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) (ctx : Context n) : Prop :=
  ∀ i, (ctx i).vals = v.map (oracles i).project

def retrieve (p : Sig → Base1007.Sig) :
    List Sig → List Base1007.Sig → Sig → Base1007.Sig
  | a :: v, b :: ps, z => if z == a then b else retrieve p v ps z
  | _, _, z => p z

lemma retrieve_map (p : Sig → Base1007.Sig) (v : List Sig) (z : Sig) :
    retrieve p v (v.map p) z = p z := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons, retrieve]
    split
    · rename_i h
      exact congrArg p (beq_iff_eq.mp h).symm
    · exact ih

inductive Recipe where
  | unary (a : Sig)
  | binary (d : Bool) (a b : Sig)

def Recipe.value : Recipe → Sig
  | .unary a => neg a
  | .binary d a b => bin d a b

def Recipe.projected (p : Sig → Base1007.Sig) (v : List Sig)
    (ps : List Base1007.Sig) : Recipe → Base1007.Sig
  | .unary a => Base1007.neg (retrieve p v ps a)
  | .binary d a b => Base1007.bin d (retrieve p v ps a) (retrieve p v ps b)

lemma Recipe.projected_map (o : Oracle) (v : List Sig) (r : Recipe) :
    r.projected o.project v (v.map o.project) = o.project r.value := by
  cases r <;> simp only [Recipe.projected, Recipe.value, retrieve_map,
    o.mapNeg, o.mapBin]

def proposedValue (o : Oracle) (v : List Sig) (ps : List Base1007.Sig)
    (z : Sig) (r : Option Recipe) : Base1007.Sig :=
  match r with
  | none => retrieve o.project v ps z
  | some r => if r.value == z then r.projected o.project v ps
    else retrieve o.project v ps z

lemma proposedValue_map (o : Oracle) (v : List Sig) (z : Sig) (r : Option Recipe) :
    proposedValue o v (v.map o.project) z r = o.project z := by
  cases r with
  | none => exact retrieve_map _ _ _
  | some r =>
    simp only [proposedValue]
    split
    · rename_i h
      rw [Recipe.projected_map, (beq_iff_eq.mp h)]
    · exact retrieve_map _ _ _

def findUnary (v : List Sig) (z : Sig) : Option Recipe :=
  (v.find? fun a => neg a == z).map Recipe.unary

def findBinary (v : List Sig) (z : Sig) : Option Recipe :=
  v.findSome? fun a => v.findSome? fun b =>
    if bin false a b == z then some (.binary false a b)
    else if bin true a b == z then some (.binary true a b) else none

def rootOf (v : List Sig) (c : PrefixCtx) (a : Sig) : Nat :=
  c.roots.getD (v.idxOf a) 8

def recipeGate (v : List Sig) (c : PrefixCtx) : Recipe → Gate
  | .unary a => ⟨.not, [rootOf v c a]⟩
  | .binary d a b => ⟨if d then .or else .and, [rootOf v c a,rootOf v c b]⟩

def traceWire (gs : List Gate) : Nat → Nat → List Nat → List Gate →
    Nat × List Nat × List Gate
  | 0, _, seen, out => (8,seen,out)
  | fuel+1, j, seen, out =>
    if j < 10 then (j,seen,out)
    else if seen.contains j then (10+seen.idxOf j,seen,out)
    else
      let g := gs.getD (j-10) ⟨.or,[]⟩
      let acc := g.inputs.foldl (fun (s : List Nat × List Nat × List Gate) a =>
        let q := traceWire gs fuel a s.2.1 s.2.2
        (s.1 ++ [q.1],q.2.1,q.2.2)) ([],seen,out)
      (10+acc.2.2.length,acc.2.1 ++ [j],acc.2.2 ++ [⟨g.op,acc.1⟩])

def compact (c : PrefixCtx) : PrefixCtx :=
  let acc := c.roots.foldl (fun (s : List Nat × List Nat × List Gate) j =>
    let q := traceWire c.gates (c.gates.length+1) j s.2.1 s.2.2
    (s.1 ++ [q.1],q.2.1,q.2.2)) ([],[],[])
  ⟨acc.2.2,acc.1,c.vals⟩

def updateOne (o : Oracle) (v w : List Sig) (c : PrefixCtx)
    (r : Option Recipe) : PrefixCtx :=
  let z := w.headD zero
  let q := proposedValue o v c.vals z r
  let old := c.vals.idxOf q
  let cached := c.vals.contains q
  let free := o.inputs.contains q
  let fresh := !(free || cached)
  let g := match r with
    | some a => recipeGate v c a
    | none => ⟨.or,[]⟩
  let out := if free then o.inputs.idxOf q
    else if cached then c.roots.getD old 8 else 10+c.gates.length
  compact ⟨if fresh then c.gates ++ [g] else c.gates,
    w.map (fun a => if a == z then out else rootOf v c a),
    w.map (fun a => if a == z then q else retrieve o.project v c.vals a)⟩

def update {n : Nat} (oracles : Fin n → Oracle) (unary : Bool)
    (v w : List Sig) (ctx : Context n) : Context n :=
  let r := if unary then findUnary v (w.headD zero) else findBinary v (w.headD zero)
  fun i => updateOne (oracles i) v w (ctx i) r

lemma update_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx)
    (u : Bool) (w : List Sig) : Valid oracles w (update oracles u v w ctx) := by
  intro i
  simp only [update, updateOne, compact]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

def initial {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List Gate × List Nat) : Context n :=
  fun i => ⟨(programs i).1,(programs i).2,v.map (oracles i).project⟩

lemma initial_valid {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List Gate × List Nat) :
    Valid oracles v (initial oracles v programs) := fun _ => rfl

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

-- DynamicPruning
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open LiveCheck
def pruned {n : Nat} (oracles : Fin n → Oracle) (k : Nat) (ctx : Context n) : Bool :=
  (List.finRange n).any fun i => (oracles i).check k (ctx i).gates (ctx i).vals

lemma pruned_sound {n k t : Nat} {oracles : Fin n → Oracle}
    {v : List Sig} {ctx : Context n} (hsound : ∀ i, (oracles i).Sound) (hv : v.Nodup) (hctx : Valid oracles v ctx)
    (hc : pruned oracles k ctx = true) : Impossible k t v := by
  obtain ⟨i,hi,hc⟩ := List.any_eq_true.mp hc
  exact hsound i hv (hctx i) hc


end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

-- ClosedDomains12
namespace PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

open PEqualNP.CircuitLowerBounds

def initial (q : Fin 12) : List Base1007.Sig :=
  if q.val < 3 then Base1007.raw else CachedProjection.thetaRaw ++ [Base1007.zero]

def oracles (q : Fin 12) : DynamicLeaf.Oracle where
  project := ProjectionDomains.project q
  mapNeg := ProjectionDomains.project_neg q
  mapBin := ProjectionDomains.project_bin q
  inputs := initial q ++ [Base1007.zero, Base1007.one]
  check := ProjectionCertificate.fastCachedCheckFrom (initial q) (ProjectionDomains.budget q)

lemma oracles_sound
    (hbase : ∀ q : Fin 12, ∀ m ≤ ProjectionDomains.budget q, ∀ t T,
      T ⊆ (initial q).toFinset → ¬ Base1007.Live m t T)
    (q : Fin 12) : (oracles q).Sound := by
  intro k t v gs ps hv hp hc m hm h
  exact ProjectionCertificate.fastCachedCheckFrom_sound
    (ProjectionDomains.project_target q) (ProjectionDomains.project_neg q)
    (ProjectionDomains.project_bin q) (hbase q) hv hp hc m hm t h

lemma cachedRaw_correct (q : Fin 12) (i : Fin 9) :
    CachedProjection.cachedRaw q i = (oracles q).project
      (LiveCheck.raw.getD i.val LiveCheck.zero) :=
  CachedProjection.cachedRaw_eq_domains q i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma inputs_cached : ∀ q : Fin 12, ∀ i : Fin 9,
    (oracles q).inputs.getD (CachedProjection.wireMap q i) Base1007.zero =
      CachedProjection.cachedRaw q i := by
  decide +kernel

lemma initial_length : ∀ q : Fin 12, (initial q).length = 8 := by decide +kernel

end PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

-- ClosedThetaBridge
namespace PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thetaInitial_eq :
    (CachedProjection.thetaRaw ++ [Base1007.zero]).toFinset =
      (Base1007.raw.map (Base1007.project 0)).toFinset := by
  decide +kernel

lemma oracles_sound_from_base
    (hsmall : ∀ m ≤ 12, ∀ t T, T ⊆ Base1007.raw.toFinset → ¬ Base1007.Live m t T)
    (htheta : ∀ m ≤ 10, ∀ t T,
      T ⊆ (Base1007.raw.map (Base1007.project 0)).toFinset → ¬ Base1007.Live m t T)
    (q : Fin 12) : (oracles q).Sound := by
  have hb : ∀ i : Fin 12, ∀ m ≤ ProjectionDomains.budget i, ∀ t T,
      T ⊆ (initial i).toFinset → ¬ Base1007.Live m t T := by
    intro i m hm t T hT
    by_cases hi : i.val < 3
    · apply hsmall m (by simpa only [ProjectionDomains.budget, ite_eq_left hi] using hm) t T
      simpa only [initial, ite_eq_left hi] using hT
    · apply htheta m (by simpa only [ProjectionDomains.budget, ite_eq_right hi] using hm) t T
      simpa only [initial, ite_eq_right hi, thetaInitial_eq] using hT
  exact @oracles_sound hb q

end PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

-- RecipeContextUpdate
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

-- MemoProtocol
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
  | d+1, key, m => bucket d (key/2) (if key % 2 = 0 then left m else right m)

def insert : Nat → Nat → Entry → Memo → Memo
  | 0, _, e, m => .node (e :: entries m) (left m) (right m)
  | d+1, key, e, m =>
    if key % 2 = 0 then .node (entries m) (insert d (key/2) e (left m)) (right m)
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
  (v.foldl (fun h a => h + 31*(a.1.toNat % 65521) + a.2.toNat % 65521) t)%65521

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

-- MemoChildren
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

-- DynamicMemoCore
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

end PEqualNP.Outside.L_meta_670_aux.DynamicMemo

-- FastRecipe
namespace PEqualNP.Outside.L_meta_670_aux.FastRecipe

structure Algebra (α : Type) where
  zero : α
  neg : α → α
  bin : Bool → α → α → α

def step {α : Type} (A : Algebra α) (rho : Fin 9 → α) (op : Nat) (w : List α) : List α :=
  if op ≤ 9 then rho (Fin.ofNat 9 (op-1)) :: w
  else match w with
  | [] => []
  | a :: tail =>
    if op = 10 then A.neg a :: tail
    else match tail with
    | [] => []
    | b :: rest => A.bin (decide (op = 12)) a b :: rest

def run {α : Type} (A : Algebra α) (rho : Fin 9 → α) : Nat → Nat → List α → List α
  | 0, _, w => w
  | fuel+1, code, w => if code = 0 then w else
    run A rho fuel (code >>> 4) (step A rho (code &&& 15) w)

def value {α : Type} (A : Algebra α) (rho : Fin 9 → α) (code : Nat) : α :=
  (run A rho 31 code []).headD A.zero

lemma step_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (op : Nat) (w : List α) :
    (step A rho op w).map p = step B (p ∘ rho) op (w.map p) := by
  unfold step
  by_cases h : op ≤ 9
  · simp [h, Function.comp_def]
  · simp only [ite_eq_right h]
    cases w with
    | nil => rfl
    | cons a w =>
      by_cases hi : op = 10
      · simp [hi,hn]
      · simp only [ite_eq_right hi,List.map_cons]
        cases w <;> simp [hb]

lemma run_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (fuel code : Nat) (w : List α) :
    (run A rho fuel code w).map p = run B (p ∘ rho) fuel code (w.map p) := by
  induction fuel generalizing code w with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : code = 0 <;> simp only [run,h,ite_true,ite_false]
    rw [ih,step_map A B p hn hb]

lemma value_map {α β : Type} (A : Algebra α) (B : Algebra β) (p : α → β)
    (hz : p A.zero = B.zero)
    (hn : ∀ a, p (A.neg a) = B.neg (p a))
    (hb : ∀ d a b, p (A.bin d a b) = B.bin d (p a) (p b))
    (rho : Fin 9 → α) (code : Nat) :
    value B (p ∘ rho) code = p (value A rho code) := by
  have h := run_map A B p hn hb rho 31 code []
  simp only [List.map_nil] at h
  unfold value
  rw [← h]
  cases run A rho 31 code [] <;> simp [hz]

def newAlgebra : Algebra LiveCheck.Sig := ⟨LiveCheck.zero,LiveCheck.neg,LiveCheck.bin⟩
def oldAlgebra : Algebra Base1007.Sig := ⟨Base1007.zero,Base1007.neg,Base1007.bin⟩
def source (i : Fin 9) : LiveCheck.Sig := LiveCheck.raw.getD i.val LiveCheck.zero

def project (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (a : LiveCheck.Sig) : Base1007.Sig :=
  let code := hint a
  if value newAlgebra source code == a then value oldAlgebra rho code else p a

lemma project_eq (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (hz : p LiveCheck.zero = Base1007.zero)
    (hn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (hb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (hr : rho = p ∘ source) : project p rho hint = p := by
  funext a
  simp only [project]
  split
  · rename_i h
    rw [hr,value_map newAlgebra oldAlgebra p hz hn hb,beq_iff_eq.mp h]
  · rfl

def values (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (v : List LiveCheck.Sig) : List Base1007.Sig :=
  v.map (project p rho hint)

lemma values_eq (p : LiveCheck.Sig → Base1007.Sig) (rho : Fin 9 → Base1007.Sig)
    (hint : LiveCheck.Sig → Nat) (hz : p LiveCheck.zero = Base1007.zero)
    (hn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (hb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (hr : rho = p ∘ source) (v : List LiveCheck.Sig) : values p rho hint v = v.map p := by
  rw [values,project_eq p rho hint hz hn hb hr]

lemma oracle_zero (o : DynamicLeaf.Oracle) : o.project LiveCheck.zero = Base1007.zero := by
  have h := o.mapBin false LiveCheck.zero (LiveCheck.neg LiveCheck.zero)
  rw [o.mapNeg] at h
  have hn : LiveCheck.bin false LiveCheck.zero (LiveCheck.neg LiveCheck.zero) = LiveCheck.zero := by
    rfl
  rw [hn] at h
  rw [h]
  rcases he : o.project LiveCheck.zero with ⟨a,b⟩
  simp [Base1007.bin,Base1007.neg,Base1007.zero]

def initial {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (v : List LiveCheck.Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : DynamicLeaf.Context n :=
  fun i => ⟨(programs i).1,(programs i).2,values (oracles i).project (rho i) hint v⟩

lemma initial_valid {n : Nat} (oracles : Fin n → DynamicLeaf.Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : LiveCheck.Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ source)
    (v : List LiveCheck.Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    DynamicLeaf.Valid oracles v (initial oracles rho hint v programs) := by
  intro i
  exact values_eq (oracles i).project (rho i) hint (oracle_zero (oracles i))
    (oracles i).mapNeg (oracles i).mapBin (hr i) v

end PEqualNP.Outside.L_meta_670_aux.FastRecipe

-- DynamicMemoFast
namespace PEqualNP.Outside.L_meta_670_aux.DynamicMemo

open LiveCheck DynamicLeaf

def fastInitial {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (v : List Sig) (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    CheckedContext oracles v :=
  ⟨FastRecipe.initial oracles rho hint v programs,
    FastRecipe.initial_valid oracles rho hint hr v programs⟩

def runFast {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoProtocol.Memo :=
  MemoProtocol.solve (CheckedContext oracles) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (fastInitial oracles rho hint hr v programs) .empty

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(runFast oracles rho hint hr k t v programs).1

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint hr k t v programs = true) : Impossible k t v := by
  have hs := MemoProtocol.solve_sound (CheckedContext oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound)
    k t v (fastInitial oracles rho hint hr v programs) .empty
    (show MemoProtocol.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint hr k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint hr k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicMemo

-- AutoContext
namespace PEqualNP.Outside.L_meta_670_aux.AutoContext

open PEqualNP.CircuitLowerBounds
open LiveCheck

structure Build where
  gates : List Gate
  values : List Base1007.Sig

def emit (g : Gate) (a : Base1007.Sig) (b : Build) : Nat × Build :=
  if b.values.contains a then (b.values.idxOf a,b)
  else (b.values.length,⟨b.gates ++ [g],b.values ++ [a]⟩)

def unary (i : Nat) (b : Build) : Nat × Build :=
  emit ⟨.not,[i]⟩ (Base1007.neg (b.values.getD i Base1007.zero)) b

def binary (d : Bool) (i j : Nat) (b : Build) : Nat × Build :=
  emit ⟨if d then .or else .and,[i,j]⟩
    (Base1007.bin d (b.values.getD i Base1007.zero)
      (b.values.getD j Base1007.zero)) b

def step (rho : Fin 9 → Nat) (op : Nat) (stack : List Nat) (b : Build) :
    List Nat × Build :=
  if op ≤ 9 then (rho (Fin.ofNat 9 (op-1)) :: stack,b)
  else match stack with
  | [] => ([],b)
  | i :: tail =>
    if op = 10 then let q := unary i b; (q.1 :: tail,q.2)
    else match tail with
    | [] => ([],b)
    | j :: rest => let q := binary (decide (op = 12)) i j b; (q.1 :: rest,q.2)

def run (rho : Fin 9 → Nat) : Nat → Nat → List Nat → Build → List Nat × Build
  | 0, _, stack, b => (stack,b)
  | fuel+1, code, stack, b =>
    if code = 0 then (stack,b)
    else let q := step rho (code &&& 15) stack b
      run rho fuel (code >>> 4) q.1 q.2

def oneGate (a : Base1007.Sig) (b : Build) : Option Gate :=
  let ids := List.range b.values.length
  match ids.find? (fun i => Base1007.neg (b.values.getD i Base1007.zero) == a) with
  | some i => some ⟨.not,[i]⟩
  | none => ids.findSome? fun i => ids.findSome? fun j =>
    if i < j then
      let x := b.values.getD i Base1007.zero
      let y := b.values.getD j Base1007.zero
      if Base1007.bin false x y == a then some ⟨.and,[i,j]⟩
      else if Base1007.bin true x y == a then some ⟨.or,[i,j]⟩ else none
    else none

def add (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (a : Sig × Base1007.Sig) (b : Build) : Build :=
  if b.values.contains a.2 then b
  else match oneGate a.2 b with
  | some g => (emit g a.2 b).2
  | none => (run rho 31 (hint a.1) [] b).2

def insert (hint : Sig → Nat) (a : Sig × Base1007.Sig) :
    List (Sig × Base1007.Sig) → List (Sig × Base1007.Sig)
  | [] => [a]
  | b :: rest => if hint a.1 ≤ hint b.1 then a :: b :: rest
    else b :: insert hint a rest

def order (hint : Sig → Nat) : List (Sig × Base1007.Sig) → List (Sig × Base1007.Sig)
  | [] => []
  | a :: rest => insert hint a (order hint rest)

def compile (inputs : List Base1007.Sig) (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (v : List Sig) (ps : List Base1007.Sig) (reverse : Bool) : List Gate × List Nat :=
  let pairs := order hint (v.zip ps)
  let ordered := if reverse then pairs.reverse else pairs
  let b := ordered.foldl (fun b a => add rho hint a b) ⟨[],inputs⟩
  let c := DynamicLeaf.compact ⟨b.gates,ps.map b.values.idxOf,ps⟩
  (c.gates,c.roots)

def programs (inputs : List Base1007.Sig) (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (v : List Sig) (ps : List Base1007.Sig) : List Gate × List Nat :=
  let first := compile inputs rho hint v ps false
  if first.1.length ≤ 2 then first
  else let second := compile inputs rho hint v ps true
    if second.1.length < first.1.length then second else first

end PEqualNP.Outside.L_meta_670_aux.AutoContext

-- StaticReplay
namespace PEqualNP.Outside.L_meta_670_aux.StaticReplay

open LiveCheck

variable (count : Nat → Nat → Nat)
variable (state : Nat → Nat → Nat → List Sig)
variable (hint : Sig → Nat)
variable (lookup : Nat → Nat → List Sig → Nat × Fin 12)

def linkCheck (k t : Nat) (w : List Sig) : Bool :=
  let found := lookup k t w
  decide (found.1 < count k t) &&
    decide ((w.map (recipeAction hint found.2)).Perm (state k t found.1))

lemma linkCheck_sound {k t : Nat} {w : List Sig}
    (known : ∀ j < count k t, Impossible k t (state k t j))
    (hc : linkCheck count state hint lookup k t w = true) : Impossible k t w := by
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact rotate_recipe_impossible hint (lookup k t w).2 hc.2
    (known (lookup k t w).1 hc.1)

variable (terminal : Nat → Nat → Nat → List Sig → Bool)

def nodeCheck (k t j : Nat) : Bool :=
  let v := state k t j
  terminal k t j v || (decide v.Nodup &&
    match k with
    | 0 => !(search 0 t v)
    | k+1 => !(stepTest k t v
        (fun w => !(linkCheck count state hint lookup k (t-1) w))
        (fun w => !(linkCheck count state hint lookup k t w))))

lemma nodeCheck_zero_sound
    (terminalSound : ∀ k t j v, terminal k t j v = true → Impossible k t v)
    {t j : Nat} (hc : nodeCheck count state hint lookup terminal 0 t j = true) :
    Impossible 0 t (state 0 t j) := by
  simp only [nodeCheck, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hc
  rcases hc with ht | ⟨hn,hs⟩
  · exact terminalSound 0 t j _ ht
  · exact exclude_search hn hs

lemma nodeCheck_succ_sound
    (terminalSound : ∀ k t j v, terminal k t j v = true → Impossible k t v)
    {k t j limit : Nat}
    (known : ∀ u ≤ limit, ∀ i < count k u, Impossible k u (state k u i))
    (ht : t ≤ limit)
    (hc : nodeCheck count state hint lookup terminal (k+1) t j = true) :
    Impossible (k+1) t (state (k+1) t j) := by
  simp only [nodeCheck, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hc
  rcases hc with hterm | ⟨hn,hs⟩
  · exact terminalSound (k+1) t j _ hterm
  · apply exclude_step hn _ _ hs
    · intro w hw
      exact linkCheck_sound count state hint lookup (known (t-1) (by omega))
        (by simpa using hw)
    · intro w hw
      exact linkCheck_sound count state hint lookup (known t ht) (by simpa using hw)

lemma levels_sound
    (terminalSound : ∀ k t j v, terminal k t j v = true → Impossible k t v)
    (budget limit : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ limit, ∀ j < count k t,
      nodeCheck count state hint lookup terminal k t j = true) :
    ∀ k ≤ budget, ∀ t ≤ limit, ∀ j < count k t, Impossible k t (state k t j) := by
  intro k
  induction k with
  | zero =>
    intro hk t ht j hj
    exact nodeCheck_zero_sound count state hint lookup terminal terminalSound
      (checks 0 hk t ht j hj)
  | succ k ih =>
    intro hk t ht j hj
    exact nodeCheck_succ_sound count state hint lookup terminal terminalSound
      (ih (by omega)) ht (checks (k+1) hk t ht j hj)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, start => f start && span f n (start+1)

lemma span_point {f : Nat → Bool} {n start j : Nat}
    (h : span f n start = true) (hs : start ≤ j) (hj : j < start+n) : f j = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    by_cases he : j = start
    · simpa only [he] using h.1
    · exact ih h.2 (by omega) (by omega)

lemma span_join {f : Nat → Bool} {a b start : Nat}
    (h₁ : span f a start = true) (h₂ : span f b (start+a) = true) :
    span f (a+b) start = true := by
  induction a generalizing start with
  | zero => simpa only [Nat.zero_add, Nat.add_zero] using h₂
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at h₁
    rw [Nat.succ_add, span, Bool.and_eq_true]
    refine ⟨h₁.1, ih h₁.2 ?_⟩
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂

def levelCheck (k t : Nat) : Bool :=
  span (nodeCheck count state hint lookup terminal k t) (count k t) 0

lemma levelCheck_points {k t : Nat}
    (h : levelCheck count state hint lookup terminal k t = true) :
    ∀ j < count k t, nodeCheck count state hint lookup terminal k t j = true := by
  intro j hj
  exact span_point h (Nat.zero_le j) (by omega)

lemma checked_levels_sound
    (terminalSound : ∀ k t j v, terminal k t j v = true → Impossible k t v)
    (budget limit : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ limit,
      levelCheck count state hint lookup terminal k t = true) :
    ∀ k ≤ budget, ∀ t ≤ limit, ∀ j < count k t, Impossible k t (state k t j) := by
  apply levels_sound count state hint lookup terminal terminalSound budget limit
  intro k hk t ht
  exact levelCheck_points count state hint lookup terminal (checks k hk t ht)

lemma checked_link_sound
    (terminalSound : ∀ k t j v, terminal k t j v = true → Impossible k t v)
    (budget limit : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ limit,
      levelCheck count state hint lookup terminal k t = true)
    {k t : Nat} {w : List Sig} (hk : k ≤ budget) (ht : t ≤ limit)
    (hc : linkCheck count state hint lookup k t w = true) : Impossible k t w := by
  exact linkCheck_sound count state hint lookup
    (checked_levels_sound count state hint lookup terminal terminalSound budget limit checks k hk t ht) hc

end PEqualNP.Outside.L_meta_670_aux.StaticReplay

-- SharedThetaData
namespace PEqualNP.Outside.L_meta_670_aux.ReplayThetaData

open LiveCheck

def word (data bits i : Nat) : Nat := (data >>> (bits*i)) &&& (2^bits-1)

def hashSig (salt : Nat) (a : Sig) : Nat :=
  (((a.1.toNat % 2147483647) * (65537+salt) + a.2.toNat % 2147483647 + 317) % 2147483647)^3 % 2147483647

def hashState (salt : Nat) (v : List Sig) : Nat :=
  (v.foldl (fun s a => s + hashSig salt a) 0) % 2147483647

def tableSlot (bits buckets mult displacement h : Nat) : Nat :=
  (h*mult % 2147483647 + word displacement bits (h % buckets)) &&& (2^bits-1)

def smallRecipe (c : Nat) : Nat :=
  if c < 9 then c+1 else if c < 18 then c-8+160 else
  if c < 180 then let d := c-18; d % 9+1+16*(d/9 % 9+1)+256*(11+d/81) else
  if c < 342 then let d := c-180; d % 9+1+16*(d/9 % 9+1)+256*(11+d/81)+40960 else
  if c < 504 then let d := c-342; d % 9+1+160+256*(d/9 % 9+1)+4096*(11+d/81) else
  let d := c-504
  d % 9+1+16*(d/9 % 9+1)+256*(11+d/729 % 2)+4096*(d/81 % 9+1)+65536*(11+d/1458)

def signalRecipes : Nat := 0xcb10b10afd1d0ad0ae0ab0aca44cf4cf00a80a60a40a5cc30a30a29ea0610c60bd00bc9609e1ddc8dbff09d742c7209a1e1c84c7b09978f73e00e09c09b9ab9a20600571c2be208abd0bd90876db9090cf1cb1b01b900911718c00c1200880899008f705e05517a64b04c1b4b7f07fb2e06c71181680d05b05215f55804961e54603700a10e1ab00d190aa007e6d20930808a68af05d0545fa04b09007576b05a05115a50b6c90485e85cd5d602d3f912917116300f09205613b04313f69c03f63003953d02e62785505c0531685975ad03853457c03601b4383455a902449201004d04a0410423f002f34e2152a30113572f4008007006005004003002001000

def signal (i : Nat) : Sig := recipeValue sourceSignals (smallRecipe (word signalRecipes 12 i))

def hintDisplacements : Nat := 0xc050202107003000030200600009004090181300007004000000003c090340700004000090000001001004090040d0000501c000000700c00000000280500802038000000000c010140600000000010141b00400010050000600c0000000008020040002004040140080002000000000000400401040020180c008000180800003054070000000c05000050000100c1d000080100001400030010000400020024020000300c0100016000030140800001000000000701400004010000300000014000000001c0500800008000000102c0200c0001802014040000000001004010000100800000000242600400000020040100c0000000004020540201003004030000200005000120000000000004010040100402038060140200004018060000000402010000340305001004050000300001004010000001800004030000000000000070140000c0100402024080180200401008000000600002008000002200c0000000024030000400403000000040000400000000000200000000010000000400018050000a004020200100400000000000a004090041700c010000103c000000002c0000c0200c00000000000000003000090080000c020040000c140000000400000000000000002000020000000000004000600200401000010000300c000080000000000040040000000
def hintRecipes : Nat := 0x1bd0000003fa0001c891c318173a3318d9bf1aa1720000003f16e4d021be13c0385a96e6c9878700000000003914d90912168bc1995b82ac080258f75acc9069ea4e00019acf0184d05bfe7da0005ea91e6bf79434e099cf155bc8400000064e6fb000055740c1115800043a00059307fa600001800c754c0030c69391f10000481400009bd0000006ec644387000000c960000007131af567d03000000004c8515a1d23859ac5ad08f0a60411170004ff6e78fa43109dd1e13d2f4000000000cc85bb6fe5b5894000752000000cc36111574f71d3351775ace08965798978915b0e255864d00794ac831d569265509355d62a13118a1ce1c914f3d858fbd30bd91b51272857c79e7530d05e913b5b11a16431c03451816210b06dc1d794115085169f8ea7926db74200016b3861996a71b859f0000a59c00009ea03600017800072d1df43800000060ea4517c0590403aa44f1b962844cc9982b65f0a3a290000007460000000009e60001c400099140ccb20000000000ae00000b34f0000005130000000066fa01ba62c1250979c00000072e00000047900065a47a49393b0ad5450000005fb122d1d1a99fe776000000000000000000654642357677b098996d11eb5bc40181000f118d0cc0b19b1ddc235276e347c36a36c14570d4dd5348a65660538959aace909250f13272c5f370a00936b010c0fc6a15e1c164b4775630d15b2cf449d000bf75ae65026c6f872350b13414a59a6058ae9366606a56dd1643e6cc51f20006d45141cb5570e164c1b200000000000079171145e0006070007700880005ed6d357600000000040e0000520008e5000000000000bda91d05073151a6a80005491917555186091616710000001019e31791f51d675a02476c19ec3575005113f18c60393851560b08019d68102f149bff0009981ae16373f0001a24ad4e61bc1dccde04c73e803319a5f86c5613f819016ccbc07e00d16751b1661e505bbe26a4c1000a16d5f068d4dc9ad0009ef43d6b118f81618708a05638404b1896b817717a6ad000a2a0001591d40a75521c21ca00056500039850659868277e000ba31daa2ea35000000c058cb00077f0005cdcd6667000000186348000000c7b4e85ff1b503e38900cc9744b478001af71ab7160001ad0006b065c000002560000000000a4f00076b5aa5d700027e6da14800000000079800000081e19800000000000000000049279a43442700009041386800000050ab72000c8d0001f01940000000000577b60000006ae1d879b12b5c06020a81430000000006047d8c8c1ac9a380080dbf40002fe1a85f2144c141951cd78300000000000017b7bf0000760004f6bf66081299b30006f71a018304a0001688e7d3868a00000009eb8912e05463010eb7f0cf169cdf77dc7c79dcd71a512a6c96d25fc1627255bacab86f00000083000000000044a1331824f802d75105f59e0007435d60000000005e800013e53d0005d5a493f9d07cf81a300012c1e80a40000007991ba57840b6e508c9ab0000009be38e98a6530001ee12003b29f1761b35370009a27240aa3df17000818e668cdacbf627a9800084f0e300000017d00000065d6ca09a51c00003f00505c0006f92e7c861e6000000c71d04cad0001f40005965b040d3f098714602e1c60751ea6a361e50ea1015219f55a7c165654e53c54b1b00ab1a48ccce19c585593756918b1e75b75641b6185900ba4c631ef75c000950000000000000bf5000546780c9eb2a000000caa17100000000072f00050800060c6e015d1b74fa00000000000000e00009100050c16e1930009d91e9ce6a4436916f1e0a2bb2e1356905515815fe1d00fd1ec7f41f678f175a011966de03769c64569d0fc7f51cc0ac52ac921bf9fd5faa2c5011971470490001657df51100009c5486838ca79095c85a6591f36f60000000001de700bd000000006c68c00000015c0877b50007860006a600081505a0a11c373465e6629fc0fe09bd2895a73759c1b40000ff8af1c700014c0001e274148104d05d1e100024300000017f6910000009ec0e400000000000014e5b31e40000007f30a259715f3fb4fd940bdc8b020dcd52a3011901000000903000000000000000bd90000000000001d10425f11db782

def hint (a : Sig) : Nat :=
  smallRecipe (word hintRecipes 12 (tableSlot 10 396 999983 hintDisplacements (hashSig 0 a)))

def count : Nat → Nat → Nat
  | 13, 0 => 500
  | 13, 1 => 609
  | 13, 2 => 609
  | 13, 3 => 609
  | 13, 4 => 212
  | 13, 5 => 19
  | 14, 0 => 14
  | 14, 1 => 16
  | 14, 2 => 16
  | 14, 3 => 16
  | 14, 4 => 16
  | 14, 5 => 16
  | 14, 6 => 2
  | 15, 0 => 1
  | 15, 1 => 1
  | 15, 2 => 1
  | 15, 3 => 1
  | 15, 4 => 1
  | 15, 5 => 1
  | 15, 6 => 1
  | 15, 7 => 1
  | _, _ => 0

def stateIndices : Nat → Nat → Nat
  | 13, 0 => 0x922408f63b8ea2087a1985611841fc7edf97d5f47cdf27c5ee799e5775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d966559464d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c5705bd6e5b56c5ad6a5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d465154450d42505404fd3e4f53c4ed3a4e5384dd364d5344cd324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b02bcae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc721c4701bc6e1b46c1ac6a1a46819c661946418c621846017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400
  | 13, 1 => 0x26097e5e9765c96e5a9665895e569565494e529465093e4e9364c92e4a9264891e469164490e42906408fe3e8f63c8ee3a8e6388de368d6348ce328c6308be2e8b62c8ae2a8a62889e268962488e228862087e1e8761c86e1a8661885e168561484e128461083e0e8360c82e0a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d966559464d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c5705bd6e5b56c5ad6a5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d465154450d42505404fd3e4f53c4ed3a4e5384dd364d5344cd324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b02bcae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc721c4701bc6e1b46c1ac6a1a46819c661946418c621846017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400
  | 13, 2 => 0x26097e5e9765c96e5a9665895e569565494e529465093e4e9364c92e4a9264891e469164490e42906408fe3e8f63c8ee3a8e6388de368d6348ce328c6308be2e8b62c8ae2a8a62889e268962488e228862087e1e8761c86e1a8661885e168561484e128461083e0e8360c82e0a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d966559464d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c5705bd6e5b56c5ad6a5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d465154450d42505404fd3e4f53c4ed3a4e5384dd364d5344cd324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b02bcae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc721c4701bc6e1b46c1ac6a1a46819c661946418c621846017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400
  | 13, 3 => 0x26097e5e9765c96e5a9665895e569565494e529465093e4e9364c92e4a9264891e469164490e42906408fe3e8f63c8ee3a8e6388de368d6348ce328c6308be2e8b62c8ae2a8a62889e268962488e228862087e1e8761c86e1a8661885e168561484e128461083e0e8360c82e0a8260881e068160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde775dc76dda765d875dd6755d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da2685a067d9e6759c66d9a6659865d966559464d926459063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd725c5705bd6e5b56c5ad6a5a56859d665956458d625856057d5e5755c56d5a5655855d565555454d525455053d4e5354c52d4a5254851d465154450d42505404fd3e4f53c4ed3a4e5384dd364d5344cd324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b02bcae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc721c4701bc6e1b46c1ac6a1a46819c661946418c621846017c5e1745c16c5a1645815c561545414c521445013c4e1344c12c4a1244811c461144410c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400
  | 13, 4 => 0x9825f97a5d9725b96a599625795a559525394a519424f93a4d9324b92a499224791a459124390a419023f8fa3d8f23b8ea398e2378da358d2338ca318c22f8ba2d8b22b8aa298a22789a258922388a218821f87a1d8721b86a198621785a158521384a118420f83a0d8320b82a098220781a058120380a01801ff7f9fd7f1fb7e9f97e1f77d9f57d1f37c9f17c1ef7b9ed7b1eb7a9e97a1e7799e5791e3789e1781df779dd771db769d9761d7759d5751cd731cb6e1b66c9b16b9ad6b1ab6699966197659956298961d835f97d5e1765c57055d56555505394951d3f4e5224811f46cef3a0e6374db364be2f0ba2c0ad2aca9288a027c97254932308a150521401f0400d0240400400
  | 13, 5 => 0x26097e5e9765c96e5a9665895e208661384a107edf279800
  | 14, 0 => 0xdcba9876543210
  | 14, 1 => 0xfedcba9876543210
  | 14, 2 => 0xfedcba9876543210
  | 14, 3 => 0xfedcba9876543210
  | 14, 4 => 0xfedcba9876543210
  | 14, 5 => 0xfedcba9876543210
  | 14, 6 => 0xfe
  | 15, 0 => 0x0
  | 15, 1 => 0x0
  | 15, 2 => 0x0
  | 15, 3 => 0x0
  | 15, 4 => 0x0
  | 15, 5 => 0x0
  | 15, 6 => 0x0
  | 15, 7 => 0x0
  | _, _ => 0

def activeMask : Nat → Nat → Nat
  | 13, 0 => 0x1012c000001422300001a3e40603fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 13, 1 => 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 13, 2 => 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 13, 3 => 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 13, 4 => 0x1fffffffffffffffffffffffffffffffffff038000146780007e006886143000000e142808200000588000000000081402a00000054012a0580a8140000000000001500000000000080012213
  | 13, 5 => 0x1ff80000000000001020d000008040040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001
  | 14, 0 => 0x3fff
  | 14, 1 => 0xffff
  | 14, 2 => 0xffff
  | 14, 3 => 0xffff
  | 14, 4 => 0xffff
  | 14, 5 => 0xffff
  | 14, 6 => 0xc000
  | 15, 0 => 0x1
  | 15, 1 => 0x1
  | 15, 2 => 0x1
  | 15, 3 => 0x1
  | 15, 4 => 0x1
  | 15, 5 => 0x1
  | 15, 6 => 0x1
  | 15, 7 => 0x1
  | _, _ => 0

def branchMask : Nat → Nat → Nat
  | 13, 0 => 0x0
  | 13, 1 => 0x0
  | 13, 2 => 0x0
  | 13, 3 => 0x0
  | 13, 4 => 0x0
  | 13, 5 => 0x0
  | 14, 0 => 0x3d6b
  | 14, 1 => 0xfd6b
  | 14, 2 => 0xfd6b
  | 14, 3 => 0xfd6b
  | 14, 4 => 0xfd6b
  | 14, 5 => 0xfd6b
  | 14, 6 => 0x3
  | 15, 0 => 0x1
  | 15, 1 => 0x1
  | 15, 2 => 0x1
  | 15, 3 => 0x1
  | 15, 4 => 0x1
  | 15, 5 => 0x1
  | 15, 6 => 0x1
  | 15, 7 => 0x1
  | _, _ => 0

def poolCount : Nat → Nat
  | 13 => 609
  | 14 => 16
  | 15 => 1
  | _ => 0

def poolIndexBits : Nat → Nat
  | 13 => 10
  | 14 => 4
  | 15 => 1
  | _ => 0

def poolData : Nat → Nat
  | 13 => 0xe4a9fc601cfe4ab97e90c63f4e4dff64e38fb3928fb9e477dd1079be7233df4ab97fa49cbfd1ee5fe8872ff3fb97f9f9cbfcf2e5fe7572ff3a397f9cdcbfce4e1fe726fff3933ff9c997fd10c1fe7260ff392dff9c96bfce4b1fe7255ff392a7f9c947fcf29dfe724eff3922ffa690ffce487fe6043ff2721ffa20f3fce479fe7238ff391aff9c8cffce455fe7224ff3911ff9c883fcf23bfe721dff390e7f9c863fce429fe8854febcaa7f5513bfaa887fd5438feb00e7f55063fb2b1ffb9588fdcabcfee5583f6004dfb951cfd930e7ed0c63f710dff7796ffbb7b07dc012beede87f74e38fbb78e7dd2873eede31f78f65d7a899ebde5b7de00d5ef8f51f7c5a8fbe2147defea3ef7951f7b928fbd9147dec0a3ef5b51f7ac28fbd4947dea2a1ef514ef7a8a1fbd44ffdea279ef5138f7a89a7bd44cfde9c57ef002bf7bc8efbda873dea239ef5118f7c442f7e4e237f1f11bf8884df80416fe22037f1ecbbf883cdfc11c6fe20cf7ef267bf7233dfa719efd0ccf7e7067bf3318df804cdfe6472ff1e2d7f8816bfb00b5fc705aff1018ff430c7f8c063fc02a3fe0147ff00a2ff8050ffc0273fe0133ff0097ff804b7fc024bfe0123ffa28fffcfc7ffe563fff231fff908fffc7c77fc023bfe0115ff0089ffd5c47fea623ff4311ffa088ffcfc47fe7623ff3711ff9a88ffcc447fe5623ff2911ff9388ffc8c47fe3e23ff1b11ff8a88ffc4c47fe221ffe010fff8886ff80437fe2217ff1109ff8883ff80417fc0207ff1101ff887fff803f7fc01f7fe00f7ff007affd03cffe79e7ff36f3ff9579ffc8bcffe3de7ff18f3ff8879ffc23cffe0de7fefef3ff7d79ffbe3cffdede7fef4f3ff7978ff803c7fc01dffe00edff0075ff803a7fc01cfff2ae5ff9272ffc7b97fe21cbfefee5ff7e72ffbcb97fdd5cbfee8e5ff7372ff80397fc01c7fee4e1ff0070ffc437ffde5bffee4dfff006effc436ffde5b7ff10d9ff796cff8035ffc01abff10d3ff8f68ffc4347fdc99ffe00cfff8866ff80337fe3d97ff10cbff7965ffb932ffc018ffe00c3ffa760ffd3307fe9583ff3ec1ff9e60ffceb07fe7183ff34c1ff9560ffc7b07fe2183ff08c1ff8360ffbe307fded83fef2c1ff7260ffb7b07fdb183fed0c1ff6560ffb1b07fd8583fec0bfff005fff802f7fc0177ff10b7ff795bffb92dffdc96bfe00b5ff8859ff802cffe2163fef2b1ff7258ffb02bffc015ffef2adff0056ffc42affde557fee4abff8854ffbcaa7fdc953fec0a7ff0053ffc7a8ffe2147fef2a3ff7251ffb028ffc0147ff489dffa04effcda77fe3d3bff189dff8a4effc4277fdfd3bfefa9dff794effb9277fdb93bfeda9dff654effb1a77fd813bfeb69dff584effaaa77fd513bfea29dff4e4dff8026ffd812ffe0095ff0049ffc423ffd811fff108dff0046ffc422ffde517fee48bff6045ffb0227fea90fff5287ffa843ffd2a1ffe910fff3e87ff9d43ffcd21ffe3d0fff1887ff8943ffc421ffe110fff0087ff7c43ffbd21ffde50ffee487ff7143ffb7a1ffdb50ffed287ff6843ffb2a1ffd890ffec287ff6043ffae21ffd610ffeaa87ff5443ffa8a1ffd3d0ffe9c87ff4c43ffa3a1ffd150ffe8685ff0042ffb020ffe3d03ff1081ff6040ffa1a07fe3cfbfe007dff433dff801effe3cf3ff1079ff793cffb91e7fd80f3fe9c79ff433cffbc9dffc00effec075ff003affa19cffc00e7ff4871ffa038ffcd9c7fe3ce3ff1871ff8838ffc11c7fdfce3fef271ff7738ffbb1c7fdc8e3feda71ff6538ffb01c7fd78e3feb871ff5b38ffac1c7fd54e3fea871ff5138ffa71c7fd0ce3fe7871ff3837ff801bffde4dbfe006dff7235ff801affe20cffef267ff7233ffa719ffd0ccffe7067ff6032ffc418ffe20c3fe0061ff882fffc7977fc00bbff105bff002dffa715ffc00afff1055ff792affb9157fd80abfe8655ff4e29ff8014ffd0c9ffe004fff0026ffb012ffe3c93ff1049ff7924ffb9127fd8093fee447ff0023ffbc917fc008bff1e43ff0021ffc7907fe2083fef241ff7220ffb0107fd0c7ffe003fff601eff800f7fe3c77ff103bff791dffb90effd8077fe9c3bff431dff9c0effe9c73ff4c39ffa51cffcf8e7fe7873ff3a39ff9a1cffcc8e7fe5873ff2a39ff8f1cffc40e7fe1073ff0639ff7c1cffbc8e7fdc873fede39ff6c1cffb50e7fda073feca39ff601cffa88e7fd3873fe9639ff4a1cffa40e7fd1c73fe8a39ff441cffa18e7fd0473fe8039ff3c1cff9c0e7fcc873fe5839ff2a1cff930e7fc9473fe4839ff201cff8e8e7fc706ffe0037ff1c1aff800d7fe2067fe0033ffaa18ffd48c7fe9463ff4831ffa318ffcf8c7fe7463ff3431ff9718ffc78c7fe3063ff1031ff8418ffc08c7fe0063fef831ff7918ffb90c7fdbc63feda31ff6b18ffb48c7fda063feca31ff6218ffb00c7fd7463feb831ff5818ffaa8c7fd5063fea231ff4e18ffa60c7fd2463fe8e31ff4518ffa18c7fd0463fe8031ff3c18ff9c0c7fccc63fe5431ff2818ff8e8c7fc7063fe302fff0017ffc78b7fe205bfec02dff1c16ffc40affe2053fef229ff7214ffb00a7fc7053fec027ff1c13ff8c097fc6047fe0023ff1c10ff8c07ffc003ffe301dff1c0dff8c06ffc0037ff1019ff430cff8c067fce02ffe0017ff380aff8e057fc002bfe0001ff
  | 14 => 0x72ff0028fbc023ffe0111ff0079ff80397fc0197fe00c1ff0051ff80277fc010ffe0079ff0038ff800effc0073fe0031ff
  | 15 => 0x1ff
  | _ => 0

def tableSalt : Nat → Nat
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | _ => 0

def tableBits : Nat → Nat
  | 13 => 10
  | 14 => 5
  | 15 => 1
  | _ => 0

def tableBuckets : Nat → Nat
  | 13 => 305
  | 14 => 8
  | 15 => 1
  | _ => 0

def tableMultiplier : Nat → Nat
  | 13 => 65537
  | 14 => 999983
  | 15 => 65537
  | _ => 0

def tableCodeBits : Nat → Nat
  | 13 => 13
  | 14 => 8
  | 15 => 4
  | _ => 0

def tableDisplacements : Nat → Nat
  | 13 => 0x11020020100000c0000c0000800018030000000802000010040000c00000000000500001004010100106000004020080000000028010001900003004020000100002030000000400000000010000203c01000080080400800034000000500000000010000001c060000200000000020000100400010020040100000000000040a0040200000008000000000c0000000004000080100c00000000000000c00000010140000401010000000000801000000100000c01000010000100800008020000600000000010000300000000020140000001000000000b0040101c0000c01004000140000001000030040000800000000080600400000000080000000030000000200002000020080200001000030000200000004000080100400008070001a00400000000000100805000000000000801004000140000000004000040000000004000000400000004000000200000008000000000000004000000000002000000000400c02000000000000003000060000100c0100c000000000003
  | 14 => 0x8108020
  | 15 => 0x0
  | _ => 0

def tableData : Nat → Nat
  | 13 => 0x45e07e5e18c85b0e47d9581bd1c4980000000003920002542000124164d8316b100000024df6dc696929b7fc0000000001b4a000114800000000000003e40000000000000000000000574781d3a27a900024ac0000000000afa00086a9e00000000000402000000000000000007a2ca2b90cd3c888499c9513d17b6204800258a943db1000000098296e000218ac1b0000001aa2000b9c00000011c50000001e5600038d8003873743000068c4b200064980000007d500000000014da5043414000000000000000000034118517389118f9bfe400145ab4700000000000000000000000000000000089da24a96c000028217e9d40000000006e840003fd00003b6aba06b8d5c90c000f75b2ec5a0ea8f996cae0d580452e00009f4f84baecf75a2205efb20000f44000dbd97c0000000a22000000000000000021080008d4d5f50140000000c0b278000000170800000000047cd88ae540001c200000000000003c7aec20000002b282126c98ee37d77160001ab00015bb33b00025667cee152d6bd9a1d379888c6be5cd3985b5f27e28b0d713575631a9f7141b3afb903b96f20e30f08a218ebeea0670ec7c906d80038aa859b2893a599d6700dbd4486492017add055bb580faa4803a4411088cf2bfb442000000012a6080000001e50000e97dd76788001a6455c00000005ac9139b90000d0929b82463ba0000002466a8286c8094b38000000ddd800043bb1119daa5e9ee56b621a680000000000000000000000000000007e5b2280000000000f99a2a6420000002bc6a525dd0f08edb58d62dc504d7c8e00000acc99800142921ce1ab8369e40003aa5052e1d9b68000000000845800000000000065e0000a8bb0a000211ecf3000711c000000ce4541a27c0002dd0771b42630ae49494001854a4b8000000000c0eea6560ec690000000000000b916744000fd50000c3b41d8b49ac80000000000003946fe427000038fc00000000015eaad000083baaa800000007e80036c14c8168d8fc0009962ff8000dd6bab5c3293400188b0000000000000000000283b74fcd23c380000005308a862fd829000000000064d0002fd5ba8000000631ef5225528600000008ed000000000075f00012f80db3310000000000000d9a8b29ce2a9f44a0ec411ce330188002dfad1b00061640000000000000001311000000268d6a29e7d9f5d962ba0001e2aa75804091523d16600080aad9e52a000000521400029509b38400001609bc0d15ef91570000000000000c5b3af84217c787f80034aecec4558000000000d740000000be8000000365a0001fd28340000410672374000e6026f800000000024e00020d816a00000000009d1000418cb96b2028c00021a2175ca0800000063193e61f0000000cd9c0a000044daf6d2fc0000000000000000000caff1d8000a3fc9b415c693b9a6d8db40f5c0001c95d95958000bfcefa400061900031c40004b5000000000000000000000000009ef2cc748e676570b7ed2e427c0003b44a9ebc1492be32074000aee88f0000c8228035df3b16e500057d400115c000000000094ec1e800022c000000000000065facaae505f59170000000000000000361800000000000000001bd00000027747ef0001b448f00001946444b3a0000a2dbbac0200000000000000005e980000000000003d0800000087a0e338ba693000000369ea6d4c6ba06284b3cd77286474f2b80000000000c4d00000000000000006de2f7346500000031f4000000722918e543d91ed1016a000be8800055f213898e6549dca794858000000000149800000000069100000008090000000000000265000272a0000004f0814dbcb24ba8c66320810006351a79c300004494e6a000b828001389235e116a3d79200033251f1f92b5f43ad2aa162eedd366a840013870001bd400000010c80000001a90000000bb9bf73860002d4e3dfd83ad42148e9267198f40011b70005de000060a0000000001780000547800000000000025191b93daea040000000006df6f272af7d100000009b70000000ac800000033040000001e430b000104ed0d6f7c0014f19fceac8ffa74835ed6e73520c100055d675e00165f68ccbe600000065680003ec000000000000077f1dac00000000010a5dc99014b080000014de00000000002ea0003586b52000756d2df8e073a8bb00000018e6c708dc4158c5fac1e8d56e885400000000000000e60000000de702bbf68000b161839c1a5ca83e4d6e49f4071947f450d8037ad4ad2ad3028848c00000000000008560001f6e000000117800000000000000000009f78000000f3b
  | 14 => 0x4bab6d0000009b000000005588020016687c2500bf3f0023a500340000
  | 15 => 0x1
  | _ => 0

def state (k t j : Nat) : List Sig :=
  let index := word (stateIndices k t) (poolIndexBits k) j
  let c := word (poolData k) 25 index
  let inputs := (List.range 9).filterMap (fun i => if c.testBit i then some (signal i) else none)
  inputs ++ (List.range 2).filterMap (fun i =>
    let a := (c >>> (9+8*i)) &&& 255
    if a = 0 then none else some (signal (a-1)))

def isBranch (k t j : Nat) : Bool := (branchMask k t).testBit j

def rawHashes : Nat := 0x4fc52ac86957602c663ac11e237e558d86e5ba381c99b6113a9819b1e7939325c78120

def hashCodes (g : Fin 12) (codes : List Nat) : Nat :=
  (codes.foldl (fun s code => s +
    if code ≤ 9 then word rawHashes 31 (rawSym g (Fin.ofNat 9 (code-1))).val
    else hashSig 0 (recipeValue (rawImage g) code)) 0) % 2147483647

def canonical (k : Nat) (v : List Sig) : Nat × Fin 12 :=
  let codes := v.map hint
  (List.finRange 12).foldl (fun best g =>
    let h := hashCodes g codes
    if h < best.1 then (h,g) else best)
    (hashCodes 0 codes,0)

def compositionData : Nat := 0x5127390a864b4036281b975a680a4b271539791b5a36042832450189ba6723541098ab76046382b179a5157293a068b486a0b472519397b1a5634082ab8967452301ba9876543210

def countNibbles : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, n => if n = 0 then 0 else
    word 0x8da691691448 3 (n &&& 15) + countNibbles fuel (n >>> 4)

def lookup (k t : Nat) (v : List Sig) : Nat × Fin 12 :=
  let c := canonical k v
  let stamp := word (tableData k) (tableCodeBits k)
    (tableSlot (tableBits k) (tableBuckets k) (tableMultiplier k)
      (tableDisplacements k) c.1)
  let poolIndex := (stamp-1)/12
  let j := if (activeMask k t).testBit poolIndex then
    countNibbles (poolCount k) (activeMask k t &&& (2^poolIndex-1)) else count k t
  (j, Fin.ofNat 12 (word compositionData 4 (12*c.2.val+(stamp-1)%12)))

end PEqualNP.Outside.L_meta_670_aux.ReplayThetaData

-- MemoBatch
namespace PEqualNP.Outside.L_meta_670_aux.MemoBatch

open LiveCheck MemoProtocol

variable (Context : List Sig → Type)
variable (cut : (k t : Nat) → (v : List Sig) → Context v → Bool)
variable (next : (k t : Nat) → (v : List Sig) → Context v → List (Child Context))
variable (retain : Nat → Nat → List Sig → Bool)

def run (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j)) :
    Nat → Nat → Memo → Bool × Memo
  | 0, _, m => (true,m)
  | n+1, start, m =>
    let result := solve Context cut next retain k t (state start) (context start) m
    if result.1 then (false,result.2)
    else run k t state context n (start+1) result.2

lemma run_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    (n start : Nat) (m : Memo) (hm : Sound m) :
    Sound (run Context cut next retain k t state context n start m).2 ∧
      ((run Context cut next retain k t state context n start m).1 = true →
        ∀ j, start ≤ j → j < start+n → Impossible k t (state j)) := by
  induction n generalizing start m with
  | zero =>
    refine ⟨hm,?_⟩
    intro _ j hlow hhigh
    omega
  | succ n ih =>
    have hs := solve_sound Context cut next retain cutSound k t
      (state start) (context start) m hm
    simp only [run]
    split
    · exact ⟨hs.1,by simp⟩
    · rename_i hf
      have hd : (solve Context cut next retain k t (state start) (context start) m).1 = false := by
        cases h : (solve Context cut next retain k t (state start) (context start) m).1 <;> simp_all
      have hi := ih (start+1) _ hs.1
      refine ⟨hi.1,?_⟩
      intro hdone j hlow hhigh
      by_cases hj : j = start
      · subst j
        exact hs.2 hd
      · exact hi.2 hdone j (by omega) (by omega)

def check (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    (n start : Nat) : Bool :=
  (run Context cut next retain k t state context n start .empty).1

lemma check_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    {n start : Nat} (hc : check Context cut next retain k t state context n start = true) :
    ∀ j, start ≤ j → j < start+n → Impossible k t (state j) := by
  exact (run_sound Context cut next retain cutSound k t state context n start .empty trivial).2 hc

end PEqualNP.Outside.L_meta_670_aux.MemoBatch

-- CertificateInterfaces
namespace PEqualNP.Outside.L_meta_670_aux.Certificate

open LiveCheck

lemma oracleSound (q : Fin 12) : (ClosedDomains12.oracles q).Sound := by
  apply ClosedDomains12.oracles_sound_from_base
  · intro m hm t T hT
    exact Base1007.noSmallSubset hm hT
  · intro m hm t T hT
    exact Base1007.noThetaSubset 0 hm hT

lemma rhoCorrect (q : Fin 12) : CachedProjection.cachedRaw q =
    (ClosedDomains12.oracles q).project ∘ FastRecipe.source := by
  funext i
  exact ClosedDomains12.cachedRaw_correct q i

def programs (v : List Sig) (q : Fin 12) :
    List PEqualNP.CircuitLowerBounds.Gate × List Nat :=
  AutoContext.programs (ClosedDomains12.oracles q).inputs
    (CachedProjection.wireMap q) ReplayThetaData.hint v
    (FastRecipe.values (ClosedDomains12.oracles q).project
      (CachedProjection.cachedRaw q) ReplayThetaData.hint v)

def terminal (k t j : Nat) (v : List Sig) : Bool :=
  if ReplayThetaData.isBranch k t j then false else
    DynamicMemo.fastLeafCheck ClosedDomains12.oracles CachedProjection.cachedRaw
      ReplayThetaData.hint rhoCorrect k t v (programs v)

lemma terminal_sound (k t j : Nat) (v : List Sig)
    (h : terminal k t j v = true) : Impossible k t v := by
  unfold terminal at h
  split at h
  · contradiction
  · exact DynamicMemo.fastLeafCheck_sound ClosedDomains12.oracles oracleSound
      CachedProjection.cachedRaw ReplayThetaData.hint rhoCorrect h

end PEqualNP.Outside.L_meta_670_aux.Certificate

namespace PEqualNP.Outside.L_meta_670_aux

lemma finish (cert : ∀ t ≤ 7, LiveCheck.Impossible 15 t LiveCheck.raw) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
        (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,hfan,hsize,he⟩
  obtain ⟨k,hk,t,ht,hl⟩ := LiveCheck.circuit_live C hsize hfan he
  exact cert t ht k hk hl

end PEqualNP.Outside.L_meta_670_aux
