import Mathlib
import PEqualNP.Defs
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

namespace PEqualNP.Outside.L_meta_670_aux.ReplayData

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
  if c < 180 then let d := c-18; d%9+1+16*(d/9%9+1)+256*(11+d/81) else
  if c < 342 then let d := c-180; d%9+1+16*(d/9%9+1)+256*(11+d/81)+40960 else
  if c < 504 then let d := c-342; d%9+1+160+256*(d/9%9+1)+4096*(11+d/81) else
  let d := c-504
  d%9+1+16*(d/9%9+1)+256*(11+d/729%2)+4096*(d/81%9+1)+65536*(11+d/1458)

def signalRecipes : Nat := 0xcb10b10afd1d0ad0ae0ab0aca44cf4cf00a80a60a40a5cc30a30a29ea0610c60bd00bc9609e1ddc8dbff09d742c7209a1e1c84c7b09978f73e00e09c09b9ab9a20600571c2be208abd0bd90876db9090cf1cb1b01b900911718c00c1200880899008f705e05517a64b04c1b4b7f07fb2e06c71181680d05b05215f55804961e54603700a10e1ab00d190aa007e6d20930808a68af05d0545fa04b09007576b05a05115a50b6c90485e85cd5d602d3f912917116300f09205613b04313f69c03f63003953d02e62785505c0531685975ad03853457c03601b4383455a902449201004d04a0410423f002f34e2152a30113572f4008007006005004003002001000

def signal (i : Nat) : Sig := recipeValue sourceSignals (smallRecipe (word signalRecipes 12 i))

def hintDisplacements : Nat := 0xc050202107003000030200600009004090181300007004000000003c090340700004000090000001001004090040d0000501c000000700c00000000280500802038000000000c010140600000000010141b00400010050000600c0000000008020040002004040140080002000000000000400401040020180c008000180800003054070000000c05000050000100c1d000080100001400030010000400020024020000300c0100016000030140800001000000000701400004010000300000014000000001c0500800008000000102c0200c0001802014040000000001004010000100800000000242600400000020040100c0000000004020540201003004030000200005000120000000000004010040100402038060140200004018060000000402010000340305001004050000300001004010000001800004030000000000000070140000c0100402024080180200401008000000600002008000002200c0000000024030000400403000000040000400000000000200000000010000000400018050000a004020200100400000000000a004090041700c010000103c000000002c0000c0200c00000000000000003000090080000c020040000c140000000400000000000000002000020000000000004000600200401000010000300c000080000000000040040000000
def hintRecipes : Nat := 0x1bd0000003fa0001c891c318173a3318d9bf1aa1720000003f16e4d021be13c0385a96e6c9878700000000003914d90912168bc1995b82ac080258f75acc9069ea4e00019acf0184d05bfe7da0005ea91e6bf79434e099cf155bc8400000064e6fb000055740c1115800043a00059307fa600001800c754c0030c69391f10000481400009bd0000006ec644387000000c960000007131af567d03000000004c8515a1d23859ac5ad08f0a60411170004ff6e78fa43109dd1e13d2f4000000000cc85bb6fe5b5894000752000000cc36111574f71d3351775ace08965798978915b0e255864d00794ac831d569265509355d62a13118a1ce1c914f3d858fbd30bd91b51272857c79e7530d05e913b5b11a16431c03451816210b06dc1d794115085169f8ea7926db74200016b3861996a71b859f0000a59c00009ea03600017800072d1df43800000060ea4517c0590403aa44f1b962844cc9982b65f0a3a290000007460000000009e60001c400099140ccb20000000000ae00000b34f0000005130000000066fa01ba62c1250979c00000072e00000047900065a47a49393b0ad5450000005fb122d1d1a99fe776000000000000000000654642357677b098996d11eb5bc40181000f118d0cc0b19b1ddc235276e347c36a36c14570d4dd5348a65660538959aace909250f13272c5f370a00936b010c0fc6a15e1c164b4775630d15b2cf449d000bf75ae65026c6f872350b13414a59a6058ae9366606a56dd1643e6cc51f20006d45141cb5570e164c1b200000000000079171145e0006070007700880005ed6d357600000000040e0000520008e5000000000000bda91d05073151a6a80005491917555186091616710000001019e31791f51d675a02476c19ec3575005113f18c60393851560b08019d68102f149bff0009981ae16373f0001a24ad4e61bc1dccde04c73e803319a5f86c5613f819016ccbc07e00d16751b1661e505bbe26a4c1000a16d5f068d4dc9ad0009ef43d6b118f81618708a05638404b1896b817717a6ad000a2a0001591d40a75521c21ca00056500039850659868277e000ba31daa2ea35000000c058cb00077f0005cdcd6667000000186348000000c7b4e85ff1b503e38900cc9744b478001af71ab7160001ad0006b065c000002560000000000a4f00076b5aa5d700027e6da14800000000079800000081e19800000000000000000049279a43442700009041386800000050ab72000c8d0001f01940000000000577b60000006ae1d879b12b5c06020a81430000000006047d8c8c1ac9a380080dbf40002fe1a85f2144c141951cd78300000000000017b7bf0000760004f6bf66081299b30006f71a018304a0001688e7d3868a00000009eb8912e05463010eb7f0cf169cdf77dc7c79dcd71a512a6c96d25fc1627255bacab86f00000083000000000044a1331824f802d75105f59e0007435d60000000005e800013e53d0005d5a493f9d07cf81a300012c1e80a40000007991ba57840b6e508c9ab0000009be38e98a6530001ee12003b29f1761b35370009a27240aa3df17000818e668cdacbf627a9800084f0e300000017d00000065d6ca09a51c00003f00505c0006f92e7c861e6000000c71d04cad0001f40005965b040d3f098714602e1c60751ea6a361e50ea1015219f55a7c165654e53c54b1b00ab1a48ccce19c585593756918b1e75b75641b6185900ba4c631ef75c000950000000000000bf5000546780c9eb2a000000caa17100000000072f00050800060c6e015d1b74fa00000000000000e00009100050c16e1930009d91e9ce6a4436916f1e0a2bb2e1356905515815fe1d00fd1ec7f41f678f175a011966de03769c64569d0fc7f51cc0ac52ac921bf9fd5faa2c5011971470490001657df51100009c5486838ca79095c85a6591f36f60000000001de700bd000000006c68c00000015c0877b50007860006a600081505a0a11c373465e6629fc0fe09bd2895a73759c1b40000ff8af1c700014c0001e274148104d05d1e100024300000017f6910000009ec0e400000000000014e5b31e40000007f30a259715f3fb4fd940bdc8b020dcd52a3011901000000903000000000000000bd90000000000001d10425f11db782

def hint (a : Sig) : Nat :=
  smallRecipe (word hintRecipes 12 (tableSlot 10 396 999983 hintDisplacements (hashSig 0 a)))

def count : Nat → Nat → Nat
  | 13, 0 => 500
  | 13, 1 => 587
  | 13, 2 => 407
  | 14, 0 => 14
  | 14, 1 => 16
  | 14, 2 => 12
  | 15, 0 => 1
  | 15, 1 => 1
  | 15, 2 => 1
  | _, _ => 0

def stateData : Nat → Nat → Nat
  | 13, 0 => 0x51ffb919ffdc947fee4dfff9572ffb92a7fc01cbfe0001ff9272ff80497fdc9c3fe00e1ff7f72ffbab97fc01d7fee4cfff0067ffb932ffdf9cbfe00fdff7235ff801affdc917fee455ff7372ff8039ffdc88ffe0047ff7224ffb90a7fdc883fee8e5ff0074ffb92d7fc016bfee4b7ff7258ffb92affdc8f3fee43bff8f2eff80177fe3c5bff1ea3ff958fffc7b97fe20c3fe0061ff880cffc40b7fe20cfff110bff8851ffc437ffe5623ff10a9ff8872ffbc9b7fc00dbfef267ff7951ffbcb7ffe55e7fef2a9ff7972ffb7277fc01bbfe9c67ff514effaa277fdc93bfeec71ff0076ff9c19ffd44e3fea871ff7238ffb8a1ffc01c7fe8619ff4333ffa8a1ffdbd0ffea887ff7243ffcb8c7fc025ffe3019ff3318ffa88c7fdbc63fea831ff7218ffb029ffc014ffec02dff6051ffb7b07fe5583fee4c1ff961cff804b7fc705bfea239ff6f1cffca8e7fdc873ff451fff00a2ffc7c77fc023bff3f1fff8f68ffc7b2ffe423fff1e43ff0021ffc7927fe3c83ff231fff8f3eff801f7fe3d03ff1e79ff8f1dffd5c47fe221ffe010fffa188ff8050ffe221bfe010dff9888ffc4407fe22037f4111ff887fffca447fe20b7fe005bff8831ffc9c47fe4e237f102bff9188ffc4337fc019bff5311ff8869ffcfc47fe21a3ff1f11ff8f88dfc432ffe20bfff1511ff8846ff80237fe7623ff108fff8884ffc4426fe2117ff1055ff8988ffc40cffc0067ff1049ff8883ffc40a7fe21b3ff1041ff8d88ffc42cffc0167ff3711ff885bffc42c7fe21b7ff10abff9a88ffc4207fe20f3ff103bff9179ff8048ffde5e3fe00f1ffa079ffbfbcffe3de7fef2cbff7d79ffbc9dffc00efff08f3ff7945ffbe3cffde4abfef4f3ff7922ff80117fe79e7fef249ff8379ffbc8a7fde5b3fef241ff7b79ffbcab7fc015bff36f3ff795bffc63cffde563fef2dbff796df7bcaaffe21e7fef279ff791dffc5277fc022bfe9c9bff004dffd0277fdfd3bfefa9dff007dffa715ffd38afde0057ff002bf7c7a77fd953bfec69dff4e29ff8014ffe913bff369dff5b4effc6277fd613bfeda9dff554effc4277fd38f3fef29dff794eff270effe08e3ff0471bf0082ff80416fce0dffe006fffa038ffbf9c7fddce3fe00efff380bff8005ffe3ce3feca71ff5e38ff802f7fce02bff4871ff5c38ffcd9c7fd6ce3ff1871ff5838ffb69c7fd54e3ff1071ff3c38ffbc9c7fce077fe9c71ffa843ff80547fd0d0bfe0085ff8943ff8044ffd0cf7fe007bffaa43ffc021ffde90ffe00f5ff4327ff8013ffea50ffed287ff9f43ffb421ffe3d0ffeca87ff4f43ffa19cffc00e7ff3a87ff4743ffc221ffd150ffe9887ff7c43ffa1957fd850ffe863fff001fffd221ffd710fff1887ff5843ffb6a1ffd550ffec487ffa543ffcd21ffe690ffc8681ff8843ffa19e7fde50ffe863bff4e43ffa721ff90ce3ff4631ff00a3ff8c0bffc005fff0231ff0081ff8c08ffc0047ff5431ff8018ffb58c7fc01affe301fff000fffd48c7fda463ff3e31ff6818ffc78c7fd9463fe9231ff0049ff8c077fe7463fe8e31ff8418ffa28c7fd3063fe3025ff7c18ff950c7fd7463fe00bbff180dffd20c7fd7063ff1831ff5818ffb68c7fd5463fec431ff2818ffd28c7fd0463ff3431ff4018ffc40c7fcf063fef231ff1d18ffa70c7fce063fe8631ff9c60ff804e7fd817ffe00bfff7b60ff803dffd815ffe00afff9f60ffb4307fe3d83fecac1ff6360ff8031ffd80ebfe0075ffa660ffceb07fd811fff08c1ff6045ffbe307fd80abfec2c1ff0061ffb00f7fc007bff4ec1ff6025ffcf307fd8093ff06c1ff6014ffb0197fd804ffed8c1ff6020ffb025ffe9583fec083ff9a60ffb0207fe2183ff10c1fe603cffb0227fde583fec03bff604effb01c7fd810ffec087fe6018ffcc8e7fe6472fe0133ff0099bf8e0dffc006ffed439ff6a1cf780357fc01abde3835ff001affcf8e7fda073ff1e39ff651cffa50e7fd2873ee0095ff004afb8e057fc002bff4c39ff481cffce8e7fd1c73ff0839ff451cffbe0e7fca873fe4c39ff261cfd80137fc009bf6381bff000dffd38e7fc9473ff3c39ff241cffc18e7fc7053fe6439ff1c13ffb60e7fc8073fe9639ff1c10ffd28e7fd0473ff3439ff401cffc40e7fcf073fe8839ff2c1cffbc8e7fc7473fe9c39ff381cffa18e7fc7063fec039ff
  | 13, 1 => 0x45a8fbd4543defea3ef6451f7a89a7bd6d47deb0a3ef5251f7a89ffbd44f3df24e5ff0092ffb9387fc01c3fefee5ff7572ff803affdc99ffe00cfff7265ffbf397fc01fbfee46bff0035ffb922ffdc8abfee6e5ff0073ffb911ffc008ffee449ff7214ffb9107fdd1cbfe00e9ff725aff802d7fdc96ffee4b1ff7255ffb91e7fdc8f3fce43bff721dff49397f9c9c3fcfee5fe7572ff3933ff9c997fcfce5fe7235ff3922ff9c8abfce6e5fe7223ff39127f9c853fce441fe7472ff392d7f9c96ffce4b1fe7255ff47977fc00bbff1e2dff8f16bfc7a8ffe3d47df2b1fff958ffdc7b97fe3dcbfd1061ff0030ffc4067fe2031ff102dff8816bfc419ffe20cf7f110bff8885efc428ffe2147df10dfff886ffbcac47fe5623f710a9ff8854fec4397fe21cbfcf26dff0036ffbc99ffde4cf7ef2a3ff7951f7bcb7ffde5bfef2af3ff9579fdbcaa7fde553faf2e5ff7972ff37277fc01bbfe9c67ff4e33dfa8a77fd453bdea89dff544efeb9277fdc93bfcec71ff0076ff9c19ffce0cf7ea271ff5138f7aa1c7fd50e3fae471ff7238ff38a1ffc01c7fe8619ff430c7fa199ffd0ccf7ea287ff5143f7b7a1ffdbd0feea887ff5443feb921ffdc90ffd2e31ff0097ff8c067fc6031fe6631ff3318dfa88c7fd4463dede31ff6f18fbaa0c7fd5063fae431ff7218ff3029ffc014ffec02dff6016bfb028ffd8147dedec1ff6f60fbcab07fe5583f6e4c1ff7260ff4b0e7fc025bfe382dff1c16bfa88e7fd4473dede39ff6f1cfbca8e7fe5473f6e439ff721cff5147ffc028bff1f1dff008effcfc7ffe3da3ff1ecbff8f65dfc7b2ebe423fff1e43ff0021ffc7927fe3c83ff231fff8f3eff801f7fe3d03ff1e79ff8f1dffd5c47fe221ffe010fffa188ff8050ffe221bfe010dff9888ffc4407fe22037f4111ff887fffca447fe20b7fe005bff8831ffc9c47fe4e237f102bff9188ffc4337fc019bff5311ff8869ffcfc47fe21a3ff1f11ff8f88dfc432ffe20bfff1511ff8846ff80237fe7623ff108fff8884ffc4426fe2117ff1055ff8988ffc40cffc0067ff1049ff8883ffc40a7fe21b3ff1041ff8d88ffc42cffc0167ff3711ff885bffc42c7fe21b7ff10abff9a88ffc4207fe20f3ff1079fe883cdfc41e6fa2077ff22f3ff0091ffbcbc7fc01e3ff40f3ff7f79ffc7bcffde597fefaf3ff793bff801dffe11e7fef28bff7c79ffbc957fde9e7fef245ff0022ffcf3cffde493ff06f3ff7914ffbcb67fde483fef6f3ff7956ff802b7fe6de7fef2b7ff8c79ffbcac7fde5b7fef2dbef7955ffc43cffde4f3fef23bff791dff3c8efbde477dd149dff008affa726ffc0137ff409dff7f4effbea77fc01f7fe9c57ff4e2bf78015ffc00afdf1e9dff654effb1a77fd38a7fe0053ffa44effcda77fd6d3bff189dff584effb6a77fd553bff109dff4e3cffbca77fde53bfc9c3bff8238ffc11c6fc020bfe0105bf3837ff801bffe80e3fefe71ff7738ff803bffce02ffe0017ff8f38ffb29c7fd78e3fe00bdff380affd21c7fd70e3ff3671ff5b38ffc61c7fd60e3feda71ff5538ffc41c7fcf0e3fef271ff381dffa71c7fd38e3ee9c71f6a843ff80547fd0d0bfe0085ff8943ff8044ffd0cf7fe007bffaa43ffc021ffde90ffe00f5ff4327ff8013ffea50ffed287ff9f43ffb421ffe3d0ffeca87ff4f43ffa19cffc00e7ff3a87ff4743ffc221ffd150ffe9887ff7c43ffa1957fd850ffe863fff001fffd221ffd710fff1887ff5843ffb6a1ffd550ffec487ffa543ffcd21ffe690ffc8681ff8843ffa19e7fde50ffe863bff4e43ffa721ff90ce3ff4631ff00a3ff8c0bffc005fff0231ff0081ff8c08ffc0047ff5431ff8018ffb58c7fc01affe301fff000fffd48c7fda463ff3e31ff6818ffc78c7fd9463fe9231ff0049ff8c077fe7463fe8e31ff8418ffa28c7fd3063fe3025ff7c18ff950c7fd7463fe00bbff180dffd20c7fd7063ff1831ff5818ffb68c7fd5463fec431ff2818ffd28c7fd0463ff3431ff4018ffc40c7fcf063fef231ff1d18ffa70c7fce063fe8631ff4318fda18c7ea7183fe0139ff605fff802fffded83fe00f7ff6057ff802bffe7d83fed0c1ff8f60ffb2b07fd8d83fe00c7ff603aff801d7fe9983ff3ac1ff6047ffc2307fd8117fef8c1ff602affb0b07fc0187fec03dff001effd3b07fd8097ff3cc1ff6024ffc1b07fd8053fec065ff6013ffb6307fd8083fec097ffa560ffb020ffe6983fec081ff8860ffc4307f980f3fec089ff7960ffb00effd813bfec071ff6043ffb021ff98063ff3239ff991cbf804cffc0266fe3837ff001bffb50e7fda873de00d5ff006af78e0d7fc006bff3e39ff681cffc78e7fd9473fe9439ff4a1cfb80257fc012bee3815ff000affd30e7fd2073ff3a39ff471cffc20e7fd1473fef839ff2a1cff930e7fc9873f6004dff0026fd8e06ffc0037ff4e39ff251cffcf0e7fc9073ff0639ff1c14ff990e7fc704ffed839ff201cffa58e7fc7043ff4a39ff411cffcd0e7fd0073ff1039ff3c1cffa20e7fcb073fef239ff1d1cffa70e7fce073fe8639ff1c18ffb00e7fd8073fac039fc
  | 13, 2 => 0x5147ffc028bff1f1dff008effcfc7ffe3da3ff1ecbff8f65dfc7b2ebe423fff1e43ff0021ffc7927fe3c83ff231fff8f3eff801f7fe3d03ff1e79ff8f1dffd5c47fe221ffe010fffa188ff8050ffe221bfe010dff9888ffc4407fe22037f4111ff887fffca447fe20b7fe005bff8831ffc9c47fe4e237f102bff9188ffc4337fc019bff5311ff8869ffcfc47fe21a3ff1f11ff8f88dfc432ffe20bfff1511ff8846ff80237fe7623ff108fff8884ffc4426fe2117ff1055ff8988ffc40cffc0067ff1049ff8883ffc40a7fe21b3ff1041ff8d88ffc42cffc0167ff3711ff885bffc42c7fe21b7ff10abff9a88ffc4207fe20f3ff1079fe883cdfc41e6fa2077ff22f3ff0091ffbcbc7fc01e3ff40f3ff7f79ffc7bcffde597fefaf3ff793bff801dffe11e7fef28bff7c79ffbc957fde9e7fef245ff0022ffcf3cffde493ff06f3ff7914ffbcb67fde483fef6f3ff7956ff802b7fe6de7fef2b7ff8c79ffbcac7fde5b7fef2dbef7955ffc43cffde4f3fef23bff791dff3c8efbde477dd149dff008affa726ffc0137ff409dff7f4effbea77fc01f7fe9c57ff4e2bf78015ffc00afdf1e9dff654effb1a77fd38a7fe0053ffa44effcda77fd6d3bff189dff584effb6a77fd553bff109dff4e3cffbca77fde53bfc9c3bff8238ffc11c6fc020bfe0105bf3837ff801bffe80e3fefe71ff7738ff803bffce02ffe0017ff8f38ffb29c7fd78e3fe00bdff380affd21c7fd70e3ff3671ff5b38ffc61c7fd60e3feda71ff5538ffc41c7fcf0e3fef271ff381dffa71c7fd38e3ee9c71f6a843ff80547fd0d0bfe0085ff8943ff8044ffd0cf7fe007bffaa43ffc021ffde90ffe00f5ff4327ff8013ffea50ffed287ff9f43ffb421ffe3d0ffeca87ff4f43ffa19cffc00e7ff3a87ff4743ffc221ffd150ffe9887ff7c43ffa1957fd850ffe863fff001fffd221ffd710fff1887ff5843ffb6a1ffd550ffec487ffa543ffcd21ffe690ffc8681ff8843ffa19e7fde50ffe863bff4e43ffa721ff90ce3ff4631ff00a3ff8c0bffc005fff0231ff0081ff8c08ffc0047ff5431ff8018ffb58c7fc01affe301fff000fffd48c7fda463ff3e31ff6818ffc78c7fd9463fe9231ff0049ff8c077fe7463fe8e31ff8418ffa28c7fd3063fe3025ff7c18ff950c7fd7463fe00bbff180dffd20c7fd7063ff1831ff5818ffb68c7fd5463fec431ff2818ffd28c7fd0463ff3431ff4018ffc40c7fcf063fef231ff1d18ffa70c7fce063fe8631ff4318fda18c7ea7183fe0139ff605fff802fffded83fe00f7ff6057ff802bffe7d83fed0c1ff8f60ffb2b07fd8d83fe00c7ff603aff801d7fe9983ff3ac1ff6047ffc2307fd8117fef8c1ff602affb0b07fc0187fec03dff001effd3b07fd8097ff3cc1ff6024ffc1b07fd8053fec065ff6013ffb6307fd8083fec097ffa560ffb020ffe6983fec081ff8860ffc4307f980f3fec089ff7960ffb00effd813bfec071ff6043ffb021ff98063ff3239ff991cbf804cffc0266fe3837ff001bffb50e7fda873de00d5ff006af78e0d7fc006bff3e39ff681cffc78e7fd9473fe9439ff4a1cfb80257fc012bee3815ff000affd30e7fd2073ff3a39ff471cffc20e7fd1473fef839ff2a1cff930e7fc9873f6004dff0026fd8e06ffc0037ff4e39ff251cffcf0e7fc9073ff0639ff1c14ff990e7fc704ffed839ff201cffa58e7fc7043ff4a39ff411cffcd0e7fd0073ff1039ff3c1cffa20e7fcb073fef239ff1d1cffa70e7fce073fe8639ff1c18ffb00e7fd8073fac039fc
  | 14, 0 => 0x147fe00e5ff008fff8032ffc0223fe0079ff0079ff800effc013bfe0071ff0043ff800c7fc0183fe0039ff
  | 14, 1 => 0x51ff8028fbc01cbfe00e5fe008fff8032ffc0223fe0079ff0079ff800effc013bfe0071ff0043ff800c7fc0183fe0039ff
  | 14, 2 => 0x8fff8032ffc0223fe0079ff0079ff800effc013bfe0071ff0043ff800c7fc0183fe0039ff
  | 15, 0 => 0x1ff
  | 15, 1 => 0x1ff
  | 15, 2 => 0x1ff
  | _, _ => 0

def tableSalt : Nat → Nat → Nat
  | 13, 0 => 0
  | 13, 1 => 0
  | 13, 2 => 0
  | 14, 0 => 0
  | 14, 1 => 0
  | 14, 2 => 0
  | 15, 0 => 0
  | 15, 1 => 0
  | 15, 2 => 0
  | _, _ => 0

def tableBits : Nat → Nat → Nat
  | 13, 0 => 10
  | 13, 1 => 10
  | 13, 2 => 9
  | 14, 0 => 5
  | 14, 1 => 5
  | 14, 2 => 4
  | 15, 0 => 1
  | 15, 1 => 1
  | 15, 2 => 1
  | _, _ => 0

def tableBuckets : Nat → Nat → Nat
  | 13, 0 => 250
  | 13, 1 => 294
  | 13, 2 => 204
  | 14, 0 => 7
  | 14, 1 => 8
  | 14, 2 => 6
  | 15, 0 => 1
  | 15, 1 => 1
  | 15, 2 => 1
  | _, _ => 0

def tableMultiplier : Nat → Nat → Nat
  | 13, 0 => 65537
  | 13, 1 => 65537
  | 13, 2 => 8191
  | 14, 0 => 65537
  | 14, 1 => 999983
  | 14, 2 => 65537
  | 15, 0 => 65537
  | 15, 1 => 65537
  | 15, 2 => 65537
  | _, _ => 0

def tableCodeBits : Nat → Nat → Nat
  | 13, 0 => 13
  | 13, 1 => 13
  | 13, 2 => 13
  | 14, 0 => 8
  | 14, 1 => 8
  | 14, 2 => 8
  | 15, 0 => 4
  | 15, 1 => 4
  | 15, 2 => 4
  | _, _ => 0

def tableDisplacements : Nat → Nat → Nat
  | 13, 0 => 0x809000010000500000000000100000002000000200000c0000001008000000000802024000080200000004010000000001000000000000001000040000000801000000080200003004010080002400000000000000402014000040001801004020000200003000000000000801000000000000401000000040000c0000c00008000000000c0300000000040000101003004000040200c00008000080000000000000040000000004000080000002000000000000001010030000000400000000000000401000000000200800000000040000c0000000000030000000c0001000004000000500001000000000000001000000040000800000010080000001000000000100000000070000200000010010040000403000000040000c010000200000000040000200000004000000000000004010000300000
  | 13, 1 => 0x1c0001000010000000502801000030000300c00000030000000800028010000300000000020000300400004010080703006000000000000c06004000000000002000020000401003000000040000005000010000000400004000040000006000010300200001000020000000c0000c00018000000000c0000400014020000000401000000200100800020020040000000008010040001400000030000200002008020040000005000020080000002000000000100002004000000000800000000000100400008000040200004000030000000000004070000500c0700000000000000100004008010000001800000000040000c0000001000000080000001000000000000000008010040000400000020040100400000000000001c0800400000010040100001000010180000c000000000001018010000b00000000000000000c0202c000140000002008000040600002008010040000001000010140000c00000000000000000000000000000001
  | 13, 2 => 0x1038000000068041b0301c1800000240007020543601010003e010000c101904830000600030000001000120e0182800040001c02060b80000070500400090100c0600090000e0f000241409000001a00000001a0b00008000e008000a00000000000020040200020080001058040a05000940601018002a030080800000001c0804048440001018180200008380200000140606000000003008000002020000401020200800008000001008040000000001200000000000000101400000041200000000207000000200008000001008000001000000201020000400000000000000180c00
  | 14, 0 => 0x108400
  | 14, 1 => 0x8108020
  | 14, 2 => 0x30120
  | 15, 0 => 0x0
  | 15, 1 => 0x0
  | 15, 2 => 0x0
  | _, _ => 0

def tableData : Nat → Nat → Nat
  | 13, 0 => 0xad9a85662800000036fa3493640000000000000b1800000016cd0004d01128083031000000000071acefc000000678800000069d00000000000000000f54000000000000000000000055640000007253c2adc400000006c400000096685d0cd800000000000000000000000000c52000330d5088d29f1cec053d4f400000f6db2a931b1000064554c000000000138f1ba800202a000000000000122500000029ae0000000002c4e000000167c00060d00038740008a37af000000000059400013da000000000000138821b05000007f17968000ece0005cb000000000000000000000000000000001761898800098e00000004bd5e00000000ae4000000a9783b400148f88cdabc0003b16b2b9d1472f94000264854c00000019b400000023100008a60007a30002852fadb9e2258000ae228c800000000000054c80014b00002704ffc96e3e4800000000099880000000005c0ae885a4000396000000000000000017223e5a3b00013e4db90000cb61000009b50001d46a050002b040012b5602b6780000002860585a1a2de55c1ec2af2ff91dd361e026a104b3175c00017b06a00000aa00e0004e021ea38db289ef0d270d53ea8000000000000364ccfe52d7b6a2ea9c4c120003c520d240c85100001921ee4234d4ac8000000026f0000000000336c0012840000001dc91e8a2780000006d906d8d245120000000f81604a51800d3180000000001bc400019f000170d04635f865cf600000000000000000000000000000000092abf1400043e000000000140577c978cb8a1213c115646051c90005bc9b4e00097c80b000168100000000000005dc5166b0ac457168d1c0000000c080000000000000000000be795a14dc0000004cf90a80010fe0000000b682550000ba99da81c0000000000000000453c0000004f080006f60008ec800000000000000000015e10000000000e19000000000077600033440006300002f6c0000008b600002240006934b0c0000000000002048000000457d53c0fd059c7ed2bc88730c92e40000000000000000000000000196b11f000000000121a728dca8dfa000000000000159500000000000004bccca58002835ba8000010000000000000000000047ad68a14500000000000000df1db9833427a261d06b4615a594800000047b000000000000000000000015ed0000000000ecb75700000009b2ba9800000072e79d451ea275f54819505b940000001806a38000a8480018f06397343e089a652000000000000000004ba8d6849f64380000014ab526000000000042c0000000000000000056c87c119ab340014b959c9e680000005f8000000000000e4b7000156e0000000000b5d000000012e00011e46c00004f53de8000000bb9b90000078e000000155032a0009348001f76000000000000000000000000007094a788380004ffa1a99298bc00042e0001fb20000000000000a5d0000b3123a1a900000000000000000000000000000000073319e58546e58c6000324525516b5bc9f6c9bc9ac000000000246a00041f16425306e7a433af400169c0000001554000000000000160a00000000013a46809698000000000000000000010b347c000000000000000134500000019260007b2b5c80e00000001ae049200094e80000000000005bf4000000000000000000000034f80008df00015b0fd08c7000000000000000028a18fae5d58c97cc88d6905b4a74400000000000000000000000000000f8500000000000000004a1c0000000000000000c9d05a8000e2ed5700012b400003217fd9dc000a7f4168000000000b2f00000010e500000000000000eb0001bba000000000014ee823a71975a98941b608001fa0000000101474a00000000014d9745000000062200076a24aebaa0009fec5e80015650003fc0902e8f000481400000036480000005f900000003a80000002441c100005e589ac8e8c3a4378cc40016bb82600000001ea860000000000000044e8000000000000000164c82e80011da00000000028d6f1e00000000000005a780000a8000000000130afa400000027a000000000009d4e95856800195b605000000000078d6f24846e2293a844b4dc4c60000000000000000000000000130613c105c00000000004769f8ad51108000001052000000000176598b124630e000924800000161681f00000000000000000ea919347f9b450100000000002a880002c0000000000000000021300006158001ddce02922dc16b854156bc1a2c3f73b385e40d947110604800007f00000000001e9600000000001e400000000000000006f78000ae366c
  | 13, 1 => 0x50d0b42a45c92b8aa4694cc0000000000000d16000359385504dd241189b630003a8400149cab781eb2d40000000001a72000366800000000000000000003ed0000000000000000000306a00075b3e6b5bc00000000003920009e480003180000001a70000000000342c000c9ab5eab312055abd6a8156ef955415b000303837a56d800000033a000000000151b1c68001eb10a500000000012cd0000002e8f2b7000688c000000000173c00000031e80011a6e890003fb8000b70000287400000000000002b00002270002a10000410bef4f2f3765ef000000000000000000000008e0800000000000000009be0000a3e404000b3800063d40002d1bf9800020b6cf8d4eaac000000534bb81ba30241e4edc53842be0001a7400047ab0b11aefc80007eb2ca800162181ea3180000002988000000000bfb0000001708a3aa7c505c7f94cf2f2400000000000000000005f500005d40003ae000000000000000017b2000b4f28887fae251a28002220000a690001e1e00051aac2589b3997050002c02524a401f807a417917b2c000db0896aac28d4816f04cb064f0da6070760099be6000daf53d230a3a5d26800100b1653618000a8b4b42125d78fd86af7fea3a9bfec5ad8dbe921f343989908181c2876a5d000347800000027b0000000691e2e80018f0000597dee94f69a249e06c20000798a84e1200000042447f0a995a55ca8001594ca580000000002f986dc6ee8538ad9c840000000000000000000000000000000097ec15400000022b0002bca61318d0001f1257109c97d4f65259000384ef00044a0cebb8000000d3eb002cd33f600061e4000c8d0003a640001991af8000000000000000266054f617ce600009cf54180000000002f2463a8b044200034d509830200009b4001b3c000477c000000a948e4d42358993480000017b200000573bbb84000000000173e74280000007a60000001a32660000308f6a400000004aa3f80006c94ecc0000000004ec216800045b80023deae60658456516649268a6380000000005b6c00000000000019fb1afb580001d7a0000004b08e5b6310000000001985000000053600000026a66cac48a308000040bbd00000000000000002e364f615dccf800000079ec4a8758ee2b71b2e05c98c361300000009276490006d0400000000000000019e9000000281cf3778d6c42aba0004f11d78000fcabdfc75d266000cf89565c6c0000000000000631bea3302f5200076a19a4a704eb80900027fc00037260f80004b76678000000a7cb81e32c0000004440000000000000000311a8ac1672c540000005c0dc44f94c3812580d000000000000027c9862000000174a0000001fb4a1a254057c9000000009ee8000000c01000000000056c1efe09e6221ad000000000104b00000000000002cb80080005174bf889ac72739000659994d06917219e911800000056e554a000000000129a1c10005c84000000000000000000091719e19563b16bdc9256a59b8b70d704000000472cc8c9dc000ae8a1ba6e15a096ebca4b807170005ae8001a980000000000af2d928000001a060000001a92a8fa9e0000bac0000000000000d8b00008b800000000000019b74a10000001bbc6e80443fd40000000004d344c33810000002a7c0000006be400000000000000000006d523dc000584487a060000cc500016240018a3764e43b518a585b0988c8bcbb10000000000a01000000327000000040540000006b480028dc0000000000001353000000019ace5c580001b867470004f1498a04ad39800062eac742e800000000000000034b517500000000000000f73924efc00000025c5ddc0bfb3f8001ac068dd5eb6e20c00000000ef483a000000646d568f4a194bd000010800006746bba95b000482b31b84d0006380932efb94a9be40000000000000c5200000007b00017c7246604d904c1373a0a0c00089f4a00d2756e000000437000020200000000011508e5000000000000000034910ed000000123a00000064f6f3f6877d72e5c00000000000000d8000000000136a00081a56031ac000281655e27af0167a8001ecc0003dee806ea200072825a9b472a188c89ee63e000bb700000000000000000000290217d09800000000004d6f2023958e80021c40000000000000000a2112a40012179788000001a1286700000000003c24aaa447975380a4bd07000000000000005b0c04000000000000066f8427128639d7d4d76e6eab1d44f602de4b4ba9a25daf7ea7002a218d1968a600000004100000001fb600000000002140000000000000e5bcd7e9a0000000
  | 13, 2 => 0x1bbc295bc81ad2a7a27dd92000469c72800091d9889138f2ea584cb3dd0ff31d78094a2c4265d63f6336cc270ed7f72c256701d671500012d4000626c9a659af7e672b5ed26638d3ae46bdcdca1d2e04bf45a2f890952c547fb0a329891e999e3df31eb0bd72e088825ad4a4922b6141800033225412584d5a6a26d8cb13b8e2eb8d07644a00000a86c937fc0005b00000000000fae1030000ebc0000004900000d19172000150631a324b62e19ca014cf214e07a0002498001e94c5a00014e194d2ed0003d980000004da93ac00000000018a602a41d77d80000002020002a6400000000000000012aa13092a400027b00025c4000e85357a90151f0698a83ff61c4e252fa851d44437a7de9491353034262c3724140006e88002446e1366280016e2000000300400062367e800000129500005c8e8f0243668001a1600000000022652f11c9800000050d0003b8158e00084480023f897f0003af45201b70000000be60000002e9400051753419a5a4600034eb8d800031777739d154a8ac390a7c485efdb00032686c27715794b080011c1000424431905500035a4674000534981c00000075099e177a589487ad8579294d3969040fc01c151ab000196d39950c2d116ecf502a9a35b70e997e50f49ca084c2b63a2500a5450001ef5f49080446273c96ec3815f32acbc8c1300023a860400001a012800009b72480557621580000000000f1a75b00000012b700000000400002cb800169483817b00000000e10002c7488400028132080000000000001b552780001b0c7f0d55194a78800000039cae040891a947b93452040001a484e5be61050004594ae269c0e4bb510ba3bd595042a45cf013bf01b4b08709066c7bd25f27b8c2c77c79242492ca0ba27a79e11c83cc326da3639a7b045c2a13d92b3242f14c40c2394ab2f291f6b7786bec8d22f41817d4bd98c726388ace0a6e1800000000000035824688c426fa709eb0821235a9f18c25cf787b121fac95b660009960000086345d417e0008ad8d15cb606c00018c45d47017fa85e4f4c0024441f2893229b5ef1be459c94003d21b8dd0876611b52548a67a1d29fb5e6e6602d0889891800055a07b015ef9a57344640012dd87cbd00dc8a110f71e102ba00008a9aec000b704630ec6220adb
  | 14, 0 => 0x9d00000a94001a000077000000530000007927000064008d3f58000000003114
  | 14, 1 => 0x3fab790000007700000000b5581a000a14a031009b2700538d00640000
  | 14, 2 => 0x1479270a1a6477588d3f000000530031
  | 15, 0 => 0x1
  | 15, 1 => 0x1
  | 15, 2 => 0x1
  | _, _ => 0

def state (k t j : Nat) : List Sig :=
  let c := word (stateData k t) 25 j
  let inputs := (List.range 9).filterMap (fun i => if c.testBit i then some (signal i) else none)
  inputs ++ (List.range 2).filterMap (fun i =>
    let a := (c >>> (9+8*i)) &&& 255
    if a = 0 then none else some (signal (a-1)))

def canonical (k t : Nat) (v : List Sig) : Nat × Fin 12 :=
  (List.finRange 12).foldl (fun best g =>
    let h := hashState (tableSalt k t) (v.map (recipeAction hint g))
    if h < best.1 then (h,g) else best)
    (hashState (tableSalt k t) (v.map (recipeAction hint 0)),0)

def compositionData : Nat := 0x5127390a864b4036281b975a680a4b271539791b5a36042832450189ba6723541098ab76046382b179a5157293a068b486a0b472519397b1a5634082ab8967452301ba9876543210

def lookup (k t : Nat) (v : List Sig) : Nat × Fin 12 :=
  let c := canonical k t v
  let j := word (tableData k t) (tableCodeBits k t)
    (tableSlot (tableBits k t) (tableBuckets k t) (tableMultiplier k t)
      (tableDisplacements k t) c.1)
  ((j-1)/12, Fin.ofNat 12 (word compositionData 4 (12*c.2.val+(j-1)%12)))

end PEqualNP.Outside.L_meta_670_aux.ReplayData

namespace PEqualNP.Outside.L_meta_670_aux.ReplayData

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_link_2 : StaticReplay.linkCheck count state hint lookup 15 2 LiveCheck.raw = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_670_aux.ReplayData
