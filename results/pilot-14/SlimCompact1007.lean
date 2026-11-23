import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_670_aux.Base1007

abbrev B := BitVec 252
abbrev Sig := B × B
def top : B := BitVec.allOnes 252
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

private lemma cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private lemma cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private lemma add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private lemma cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def raw0 : Sig := (0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff, 0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def raw1 : Sig := (0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff, 0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def raw2 : Sig := (0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000, 0x288f043070431810c6040140208600486843828c4604588c09191234230)
def raw3 : Sig := (0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000, 0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def raw4 : Sig := (0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000, 0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def raw5 : Sig := (0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000, 0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def raw6 : Sig := (0xfffffe00000000000000003fffffffffffffff0000000000000000000000000, 0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def raw7 : Sig := (0xffffffffffffffffffffffc0000000000000000000000000000000000000000, 0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
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
  by_cases hi : i < 252
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 252
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 252)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 252) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 252 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 252)] <;> simp [hi]
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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

-- The deletion bound uses the theta graph certificate checked in L-meta-517.
namespace Theta

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

lemma kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

lemma Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

lemma run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

lemma run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

lemma cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

lemma required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

lemma next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

lemma next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

lemma next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

lemma zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

lemma next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def xs517 : List ℕ := [0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517, 0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827, 0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248, 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0, 0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418, 0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800, 0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]

lemma proper_fail517 : ∀ zs ∈ xs517.sublists, zs ≠ xs517 →
    (cov 232 zs &&& lo 232) ≠ lo 232 := by decide +kernel

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

lemma moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

lemma move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

lemma move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def deltaA : Nat := (lo 58) ||| ((lo 58) <<< 116) ||| ((lo 58) <<< 232) ||| ((lo 58) <<< 348)
def deltaB : Nat := lo 116 ||| ((lo 116) <<< 232)

def setA (xs : List Nat) := xs.map (moveBits deltaA 58)
def setB (xs : List Nat) := xs.map (moveBits deltaB 116)

lemma runA {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma runB {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setB ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def recipeStep (ma : Nat) (lit : Nat → Nat) (op : Nat) (stack : List Nat) : List Nat :=
  if op < 8 then lit op :: stack
  else match stack with
  | [] => []
  | a :: t => if op = 8 then (a ^^^ ma) :: t else match t with
    | [] => []
    | b :: r => (if op = 9 then a &&& b else a ||| b) :: r

def recipeVal (ma : Nat) (lit : Nat → Nat) : Nat → Nat → List Nat → Nat
  | 0, _, stack => stack.headD 0
  | t+1, ops, stack =>
    if ops = 0 then stack.headD 0 else
      recipeVal ma lit t (ops >>> 4) (recipeStep ma lit (ops &&& 15) stack)


lemma bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

lemma covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

lemma required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

lemma covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]


def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

lemma value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

lemma value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

lemma score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

lemma eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

lemma scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]


def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

lemma span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

lemma span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

lemma extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih


def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8)))))

lemma barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

lemma barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


def rowSignalCodesE : Nat := 0x9000000e41000000e4300ede631400ede21340000ed314000edc53400000cd4300000cd740000000c700ede5143000000e5100ede42510000ed54100000cd640000000c60000ee62100000cd540000ee321000000e210000000c5000000e7100ede627100ede75210000ed721000000e3100ede53210000ed3210000ed413000000e610000ed76100000ec410000ed52100edd763100edd652100edd654100edd632100edd765100edd752100edd542100edd53210000000010000ee64200000ec32000000e4200ede514200ede732400ede532400ede63240000ed32400edd32140000ed41200000cd420000ee6320000ee73200000ec42000000e320000ed3120000ed2130000ee6520000ee75200000ec12000000e520000ed5420000ee762000000e620000ed6420000ed612000000e720000ed7620000ed7320000ed6320000ed7120000ed7520000ed652000000002000dcd7620000ed2170000de3120000de5120000de612000000d210000ee65300000cd410000ee75300000ec13000000e5300ede2135000ece2130000ed54300000ec45000edc4350000ed3150000ee763000000e6300ede21360000ed61300000ec46000ed61c40000ed316000cde51400ede7523000000e7300ede62730000ed723000edc1730000ed74300000ec47000ed72c400000ec43000ed32c400ede62530000ed52300ede75630000ed7630000ed7530000ed6230000ed65300edd621300edd765300edd651300edd752300edd5423000000003000dcd653000dcd61300dee7213000dcd543000dec4230000de213000ed76c4000ed62c4000ed31c4000ed52c40000000c4000ced624000ced614000ced76400000ce64000de51c400000dc41000ced52400000ce54000ced72400000ce7400000dc43000000d31000ed32c10000ed3250000ed326000dcd41200dee75320000ed3270000de5320000de7230000de6230000de632000000d3200000dc420000dd32100000cd3100ede7524000000e7400ede627400ede76240000ed72400edd7214000000e5400ede65240000ed52400edd521400edd5314000ece514000000e6400ede7164000edc56400ede72640000ed764000edc12400edd763400edd731400ede21640000ed61400edd651400edd63140000ed62400edd652400edd765400edd761400edd632400edd621400edd752400edd532400edd732400edd7624000000004000cde21300000ec36000ed76c3000ed74c3000ed52c30000000c3000ced7430000ed415ede425d4100ede51460000de514000ced543000de21c30000ed41600000cd210000000c20000ed426000dcd31200000dc32000ced32400000ec160000ee765000000e6500ede716500ede42560000ed6150000ed54600000ec15000ed52c1000ed54c10000000c1000000e7500ede6275000ced4130000ed725000ced32100000ce31000ced721000edc4750000ed7150000ed76500000000500000ce21000000e760000ed7260000ed5160000ed5260000ed7560000000060000ed437000ced54100000ce5100000dc120000ed5170000ed5270000de7520000ed5370000ed6570000ed6370000ed627000000007000dcd327000dcd617000dcd41700dee6217000dcd54700dee6327000dcd51700dee652700dee6427000dcd317000dec367000dec1270000de62700000dc370000de762000000d7200000dc1700000dc130000de751000ced31400000ce4300000dc470000de3250000de21500000dc450000de7150000de7250000de6250000de652000000d52000dcd416000dec4760000de6570000de7560000de7360000de72600000dc16000000d760000de7530000de65300000ce4100000dc460000de7630000de5370000de3260000de536000000d630000dd7630000de765000000d750000de526000000d65000000d620000dd7410000dd6210000dd6420000dd7650000dd6430000dd7430000dd6320000dd7520000dd5420000dd532000000008
def rowLeafE (op : Nat) : Nat :=
  if op ≤ 7 then xs517.getD (op-1) 0 else
    if op = 8 then 0 else if op = 9 then mask 232 else
      if op = 10 then goal 232 else lo 232
def rowRecipeStepE (op : Nat) (w : List Nat) : List Nat :=
  if op ≤ 11 then rowLeafE op :: w else
    match w with
    | [] => []
    | a :: t =>
      if op = 12 then (a ^^^ mask 232) :: t else
        match t with
        | [] => []
        | b :: r => (if op = 14 then a ||| b else a &&& b) :: r
def rowRecipeRunE : Nat → Nat → List Nat → List Nat
  | 0, _, w => w
  | n+1, code, w =>
    if code = 0 then w else
      rowRecipeRunE n (code >>> 4) (rowRecipeStepE (code &&& 15) w)
def rowSignalE (i : Nat) : Nat :=
  (rowRecipeRunE 9 ((rowSignalCodesE >>> (36*(i-1))) &&& 0xfffffffff) []).headD 0
def rowPackedE : Nat := 0x461ecc63f1509a410000230f6632eca84d208025d187b318fc542690400008c3d98c7e2a13482008c425ecc63f1509a410046200f6631f8a84d2080230fd7b318fc542690401187b3d98c7e2a13482008c3d9e0c63f1509a4100461ecdb631f8a84d2080230f663318fc542690401187b319767e2a13482008c3d98ca43f1509a410000230f63f1e0a84d2080230f6631f8f0542690401187b318fc672a13482008c3d98c7e2f9509a4100001ecc63f17ca84d2080230f6631f8bc542690401187b318fc542913482008c3d98c7e2a134824100461ecc63f1509a411180230f6631f8a84d2086c01187b318fc542690424008c3d98c7e2a134820f00461ecc63f1509a410680230f6631f8a84d208300000994b630f6631f88200004ca30f6632eca841000025b187b319764d20802813f8c3d98c542690400009e461ecc62a13482009fc622af6631509a410000231107b318a84d2080283187b31976542690401408c3d98cbb2a13482009fc61ecc65d9509a41004e230f6632eca84d208026d187b31976542690401328c3d98cbb2a134820097461ecc65d9509a41004b630f6632eca84d2080259187b31976542690401288c3d98cbb2a134820092461ecc65d9509a410048a30f6632eca84d2080231187b31976542690400008c3d98cbb2a13482008c455ecc65d9509a410046214f6632eca84d2080231097b319765426904011881bd98cbb2a13482008c401ecc65d9509a4100461faf6632eca84d2080230f67b31976542690401187b3c18cbb2a13482008c3d9d6c65d9509a4100461ece7632eca84d2080230f671b1976542690401187b3818cbb2a13482008c3d9b6c65d9509a4100461ecd6632eca84d2080230f66a31976542690401187b3198cbb2a13482008c3d98cbb5d9509a4100461ecc65dad4a84d2080230f6632ed605426904013c8c3d98caf2a13482008c3d98cbb579509a410046220f663290a84d2080230f6632ed48542690401187b31976a32a13482008c455ecc64f9509a4100461ecc65da7ca84d2080001187b31938542690401188abd98c9a2a13482008c3d98cbb4d1509a410000230f663260a84d2080281187b31928542690401188abd98c942a13482008c3d98cbb4a1509a4100461ecc64fa50a84d2080001187b31920542690400008c3d98c8b2a134820000461ecc6441509a41004fe30f66d9f8a84d2080231097b36cfc542690401187b38db67e2a134820000461ecd13f1509a410000230f6679f8a84d2080001187b330fc5426904012e963d98c7e2a1348200974a1ecc63f1509a41000024cf6631f8a84d2080259247b318fc5426904000091bd98c7e2a134820000485ecc63f1509a410050630f6631f8a84d2080275187b318fc542690401398c3d98c7e2a134820099c61ecc63f1509a41004c630f6631f8a84d2080261187b318fc5426904012f8c3d98c7e2a134820097461ecc63f1509a410048a30f6631f8a84d2080001187b318fc542690401188bbd98c7e2a13482008c459ecc63f1509a41004621af6631f8a84d20802310c7b318fc5426904011885bd98c7e2a13482008c429ecc63f1509a410046212f6631f8a84d2080231087b318fc5426904011883bd98c7e2a13482008c419ecc63f1509a41004620af6631f8a84d2080231047b318fc5426904011880bd98c7e2a13483368c401ecc63f1509a410046200f6631f8a84d2080230ff7b318fc542690401187f3d98c7e2a13482008c3f5ecc63f1509a4100461f8f6631f8a84d2080230fb7b318fc542690401187d3d98c7e2a13482008c3e5ecc63f1509a4100461f0f6631f8a84d2080230f77b318fc542690401187b3d98c7e2a13482008c3d9e8c63f1509a4100461ecf3631f8a84d2080230f679318fc542690401187b3c58c7e2a1348200973d9e0c63f1509a4100461ecf0631f8a84d2080230f677b18fc542690401187b3b98c7e2a13482008c3d9dac63f1509a4100461ecec631f8a84d2080230f673b18fc542690401187b3918c7e2a13482008c3d9c0c63f1509a4100461ecdb631f8a84d2080230f66b318fc542690401187b3518c7e2a13482008c3d9a2c63f1509a4100461eccf631f8a84d2080230f667318fc542690401187b3358c7e2a13482008c3d998c63f1509a4100461ecc6631f8a84d208025d187b300fc542690400008c3d9807e2a13482008c3d98cc03f1509a4100461ecc65d9f8a84d2080230f6632dcfc542690401187b3196a7e2a13482008c3d98cb33f1509a4100461ecc6589f8a84d2080230f6632c0fc542690401187b319587e2a13482008c3d98ca93f1509a4100461ecc6541f8a84d2080230f66329cfc542690401187b3194c7e2a13482008c3d98ca53f1509a410046212f6521f8a84d2080230f671a90fc5426904011884b19487e2a1348200933d98ca43f1509a4100461ecc6521f8a84d2080230f657a90fc542690401187b319467e2a13482008c3d98ca23f1509a4100461ecc6509f8a84d2080230f6631f8f8542690400008c3d976782a13482008c3d98cbb3c1509a410050630f63f1e0a84d208025d187b1f8f0542690400008c3d8fc782a13482008c459ec7e3c1509a410046212f63f1e0a84d2080231007b1f8f0542690401187ebd8fc782a13482008c3d9ec7e3c1509a4100461ecf03f1e0a84d2080230f66d9f8f0542690401187b318fc782a13482008c3d9767e3c1509a4100461eca43f1e0a84d2080230f63f1f0f0542690401187b1f8f0782a13482008c3d98c7e379509a410000230c65d9b8a84d2080230f6632ecdc542690401187b318fc6b2a13482008c3d8fc78359509a4100461ecc63f1a4a84d2080230f6631f8d0542690401187b31976672a134832e8c3d98c7e339509a4100461ecc63f19ca84d2080230f63f1e0ce542690401187b318fc622a13482008c3d98cbb2f9509a4100001ecc65d97ca84d2080282f6631f8be5426904012e7b318fc5f2a134820096bd98c7e2f9509a41004b1ecc63f17ca84d2080250f6631f8be542690401247b318fc5f2a13482008c3d98c7e2f9509a4100425ecc63f17ca84d2080208f6631f8be542690401007b318fc5f2a13482007ebd98c7e2f9509a41003d9ecc63f17ca84d2080000f6631f8be542690400f678318fc5f2a13482007b3b18c7e2f9509a41003d9c6c63f17ca84d20801ecdb631f8be542690400f663318fc5f2a13482007b319767e2f9509a41003d98caf3f17ca84d20801ecc6521f8be542690401187b1f8f05f2a1348200003d8fc782f9509a41003d98c7e3c17ca84d20801ecc63f1b8be54269040000631f8dc5f2a13482007b318fc692f9509a41003d98c7e3397ca84d20801ecc63f188be542690400f6631f8be5f2a13482008c3d98cbb2f1509a4197461ecc63f178a84d2080230f6631f8bc542690401187b1f8f05e2a13482008c318fc6e2f1509a41003d98c7e2f978a84d2080230f6631f8b2542690401187b318fc552a13482008c3d98c7e2a14c9a4100461ecc65d950a44d2080230f6631f8a8522690401187b1f8f0542913482007b318fc5f2a1489a4100461ecc63f150a24d2080230f6631f8a8502690401187b318fc542793482008c3d98c7e2a1389a4100461ecc63f1509a4c2080230f6631f8a84d2510401187b318fc542692482007b318fc5f2a134924100461ecc63f1509a482080230f6631f8a84d2390401187b318fc542691882008c3d98c7e2a1348a4100461ecc63f1509a442080230f6631f8a84d2190401187b318fc5426908820099461ecc63f1508241004b630f6631f89a412080230f6632eca84d2090401187b318fc542690482008c3d8fc782a1348241004618c7e371509a4120801ecc63f17ca84d2090400008c3d98c7e2a13468008c401ecc63f1509a3400461ecc63f1509a411a00230f6631f8a84d208cc01187b1f8f0542690466008c3d98c7e2a134823200461ecc63f1509a4118001ecc63f17ca84d208c001187b318fc54269045e007b318fc5f2a134822f00461ecc63f1509a411700230f6631f8a84d208b001187b31976542690456008c3d98c7e2a134822b00461ecc63f1509a411500230f6631f8a84d208a401187b31976542690450008c3d98c7e2a134822800461ecc63f1509a411380230f6631f8a84d2089801187b318fc54269044a008c3d98c7e2a1348224004e230f6631f8a84d1180230f6631f8a84d2388c01328c3d98c7e2a10446008c3d98c7e2a13c8223004da30f6631f89a41118025b187b318fc4d2088c011881bd98c7e2690446008c3d98cbb2a134822300461ecc64c1509a411180230f6689f8a84d2088c011881b18fc5426904460090bd98c7e2a134822300461ecc63f1509a411180230f63f1e0a84d2088c0118631f8dc542690446007b318fc5f2a134822300461ecc63f1509a411000230f6631f8a84d2087c01187b318fc54269043c008c3d98c7e2a134821d00461ecc63f1509a410e001ecc63f17ca84d2087001328c3d98c7e2a10436008c3d9c6c63f150821b00461ecc64a1f8a8410d80230f6631f8a8522086c01187b31976542690436008c3d98c902a134821b00461eccf3f1509a410d80246f6631f8a84d2086c01187b318fc542690436008c3d8fc782a134821b003d98c7e2f9509a410d80230f6631f8a84d1886c01187b318fc542690434008c3d98c7e2a134821900461ecc63f1509a410c00230f6632eca84d2085c01187b318fc54269042e008c3d98c7e2a134821600461ecc63f1509a410a80230f6631f8a84d2085001187b318fc542690426009c461ecc63f1509a12004ca30f6631f8a8410900230f671b18fc5420848012d8c3d98c7e2690424008c3d98cbb2a134821200461ece33f1509a410900230f6631f8a84d2084801187b1f8f0542690424008c318fc6e2a1348212003d98c7e2f9509a410900230f6631f8a84d2084401187b318fc5426904200096c61ecc63f134820f00461ecc63f1789a410780230f6632eca84d2083c01187b318fc54269041e008c3d8fc782a134820f004618c7e371509a4107801ecc63f17ca84d2083c01187b318fc54269041c0096c61ecc63f134820d00461ecc63f19c9a410680230f6632eca84d2083401187b330fc54269041a008c3d98c7e2a134820d00461ec7e3c1509a4106801ecc63f17ca84d2083401388c3d98c7e2a134180099461ecc63f150820c0046200f6631f8a841060025b187b318fc4d2083001187b31976542690418008c3d98c882a134820c0046200c63f1509a410600230f6631f8a84d2083001187b1f8f0542690418008c318fc6e2a134820c003d98c7e2f9509a410600230f6631f8a84d2082c01187b318fc542690414008c3d98c7e2a134820900461ecc63f1509a410400230f6631f8a84d2081c01187b318fc54269040c008c3d98c7e2a134820500461ecc63f1509a410200230f6631f8a84d2080c01187b318fc542690404008c3d98cbb2a134820100461ecc63f1509a410080230f63f1e0a84d2080400f6631f8be54269040200004ca5b187b319764100002652d8c3d98c7e2080001328c3d98cad3f104000096c61ecc6561f8820000461ecc656ab0fc4100002652d8c3d8fc7820800013296bd98c7e2f904000099461ecc63f16c8200004ca30f6631f8ac410000265187b318fc552080001187b319287e2a90400009e461ecde631508200004ca30f6632eca8410000230f66f3197654208000118883d98cac2a10400008c3d98cbb561508200004ca30f65d9e0a8410000281187b318e0542080001188abd98c702a10400008c3d98cbb381508200004ca30c65d9b8a8410000231157b318da542080001187b319766d2a10400008c3d98cbb319508200004c9ecc65d97ca841000025b187b318fc512080001187b318fc5b2890400008c3d98cbb2a1448200004da30f6631f89e41000025b187b318fc4f2080001187b31976542790400008c3d98c982a13c8200004b630f6632ec9a410000230f673319764d2080001187b3958cbb2690400008c441ecc656934820000461ecc65dab49a41000025b187b2ecf04d2080001188abd98c762690400008c3d98cbb3b134820000461ecc65d9909a41000025af6632ecbe4d2080001187b319765b2690400008c3d98c9c2d934820000461ecc65d95c9a410000230f6632ecac4d2080001187b31976552690400008c3d98c902a9348200004f251187b1509a410000281258c3d8a84d2080001258c455ec542690400009e461eceb2a1348200004f230f66d9509a4100002791884318a84d20800013f8c4098c542690400009fcd1ecc62a1348200004fa30f6631509a41000027b187b318a84d20800013c8c3d98c542690400009dc61ecc62a13482000046226f6631509a410000231127b318a84d20800011888bd98c5426904000093441ecc62a13482000046220f6631509a4100002310f7b318a84d2080001187b37d8c542690400008c3d9bac62a134820000461ecd5631509a410000230f669b18a84d20800013d8c3d980542690400008c3d98cbf2a134820000461ecc65f1509a410000230f6632f4a84d2080001187b319785426904000092c61ecbb2a134820000461ece85d9509a410000230f670aeca84d2080001187b36576542690400008c3d9aebb2a134820000461ecd15d9509a410000230f667aeca84d2080001187b33176542690400008c4398cbb2a13482000046210c65d9509a41000023102632eca84d2080001187f31976542690400008c3f18cbb2a1348200004d1ecc65d9509a410000252f6632eca84d2080001267b319765426904000091bd98cbb2a134820000485ecc65d9509a410000230f6632eca84d2080001187b30576542690400008c3d980bb2a134820000461ecc65d1509a410000230f6632e4a84d2080001187b31970542690400008c3d98cb62a134820000461ecc65a1509a410000230f6632c8a84d20800013c8c3d948542690400008c3d98ca02a134820000461ecc64f1509a410000230f663274a84d2080001187b365385426904000094bd98c9c2a134820000461ecc64e1509a410000230f66326ca84d2080001188131934542690400008c3d98c992a134820000461ecd14c1509a4100002310363260a84d2080001217b31930542690400008c3d98c982a134820000461ecc64b9509a410000230f663258a84d2080001187b3192a542690400008c4098c942a1348200004d1ecc64a1509a410000230f66324ca84d2080001187b31924542690400008c3d98c912a134820000461eccf481509a410000230fc63240a84d2080001237b31920542690400008c3d98c902a134820000461ecc6479509a410000230f663238a84d2080001187b3191a542690400008c3d98c8c2a134820000461ece1459509a410000230fe6322ca84d2080001187b31916542690400008c3d98c8a2a134820000461ecc6449509a410000230f663220a84d2080001187b3190e542690400008c3d98c862a134820000461ecc6429509a410000230f663210a84d2080001187b31906542690400008c3d98c822a134820000461ecc6409509a410000230f663200a84d2080001187b318fe542690400008c3d9d27e2a134820000461ecdc3f1509a410000231086d9f8a84d2080001187b368fc542690400008c3d9b07e2a134820000461ecd23f1509a410000242f6689f8a84d2080001187b344fc542690400008c3d9a07e2a13482000048deccf3f1509a410000230f6679f8a84d2080001187b330fc542690400008c3d9967e2a134820000461ecca3f1509a410000230f6649f8a84d2080001187b320fc542690400008c3d98e7e2a1348200004a210c63f1509a41004da5d00631f8a84d2080001237e318fc5426904000095bd98c7e2a1348200004a9ecc63f1509a41000024ef6631f8a84d2080001267b318fc5426904000091bd98c7e2a134820000485ecc63f1509a410000240f6631f8a84d20800011f7b318fc542690400008f3d98c7e2a134820000475ecc63f1509a410000238f6631f8a84d20800011b7b318fc542690400008d3d98c7e2a134820000465ecc63f1509a410000230f6631f8a84d2080001187ab18fc542690400008c3d98a7e2a134820000461ecc43f1509a410000230f6619f8a84d2080001187b308fc542690400008c3d9827e2a134820000499ecc03f1509a410000230f6601f8a84d2080000f6632b8fc542690400008c319567e2a1348200004618caa3f1509a410000230f63f1f4a84d2080001187b1f8f6542690400008c3d8fc7a2a134820000461ec7e3c9509a410000279187b1e0a84d208000118883d8f0542690400008c3d976782a134820000461ec9c3c1509a410000230f64c1e0a84d2080001187b240f0542690400008c3d916782a134820000461ec883c1509a41000024cf63f1e0a84d2080001237b1f8f05426904000090bd8fc782a134820000461ec7e3c1509a410000230f63f1dca84d2080001187b1f8e4542690400008c3d8fc712a1348200004f230c6371509a41000023110631b8a84d208000118632ecdc542690400008c319386e2a1348200004618c98371509a410000230c6481b8a84d2080001186322cdc542690400008c319106e2a1348200004617678371509a410000230c63f1b0a84d2080001187b318d4542690400007b318fc612a1348200003d98c7e301509a410000278f66317ca84d2080001107b318be542690400007b319765f2a1348200003d98c9c2f9509a4100001ecc64c17ca84d2080000f663240be542690400007b3191e5f2a1348200003d98c8b2f9509a4100001ecc64417ca84d2080000f6709f8be542690400007b360fc5f2a1348200003d9a27e2f9509a4100001eccf3f17ca84d2080000f6661f8be5426904000084318fc5f2a1348200003f98c7e2f9509a4100001f8c63f17ca84d2080000f6631f8be542690400007b300fc5f2a1348200003d976782f9509a4100001ec7e3c17ca84d2080000c65d9b8be54269040000631f8dc5f2a1348200001f8f06e2f9509a410000230f63f170a84d2080000f6631f8b4542690400007b318fc582a1348200003d98c7e2a1349641004ba30c63f1509a462080001187b318fc542690000008c3d98c7e2a1347e0000461ecc63f1509a3e0000230f6631f8a84d1e80001187b318fc54268f000008c3d98c7e2a134760000461ecc63f1509a3a0000230f6631f8a84d1c80001187b318fc54268e000008c3d98c7e2a1346e0000461ecc63f1509a360000230f63f1e0a84d1b00001187b318fc54268d400007b318fc5f2a1346a00004ca30f6631f8a8340000230f671b18fc541a00001187b319287e2a0d000008c3d98c7e2a1446800004b630f6631f89a340000230f6631f8ba4d1a00001187b3197654268d000008c3d98c9e2a134680000461ecda3f1509a340000230fc631f8a84d1a000012b7b318fc54268d000008c3d98c7e2a134680000461ec7e3c1509a340000230c63f1b8a84d1a00000f6631f8be54268d000008c3d98c54269045a00004d1ecc63f13482230000230f6631cc9a411180001187b318fc542088800008c3d98cbb2a104420000461ecc63f15082210000230f671b6cfc540d80001187b31916542086c00008c3d9c27e2a10436000000230f675388fc410000001187b3795a7e2080000008c3d98c93331040000004d5ecc63f1948200000023114631d0a8410000001347b318e8542080000008c4098c702a1040000004fe68f6759348200000027b187b3a89a4100000013c8c3d95a4d2080000008c4518c7626904000000461ecc63a9348200000026f188a1509a410000001258c408a84d2080000009bcd1ec54269040000004f64cf62a1348200004ba30dc3f1509a410000001187b31916541a00000008c3d9c27e2a0d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def rowDecodeE : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, code =>
    if code = 0 then [] else
      rowSignalE (code &&& 511) ::
        rowDecodeE n (code >>> 9)
def rowsE (i : Nat) : List Nat :=
  rowDecodeE 9 ((rowPackedE >>> (81*i)) &&& 0x1ffffffffffffffffffff)

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x334dd35dbb6fdce370dd369c26b5c733cc1371b871dc5334dd35dcc6c1ce374c7379ae735cc374df2c99a6e1cc374df379ae735cc324cf369c26b5c9304dd35db66c1ce370c935d2e6d99331cc934db96d9c8164e127dae6fdbd31cdd361b25a1ce37cdd2c9b86b9cc34ccd35db06d9ce334d335db66c1ce334dd35dc46c1ce33cc1371b86e5c537cdd2c9b8669cc334e535db66c1ce31cc936dc6711c833cdd35db66c1ce334dd369b86a5ce334dd35dbb6c1ce31cdd35db66c1ce304dd369b86a5ce334dd35db66fdce31cdd379cd6b9cc37cdd379cd6b9cc374cd35db06d9ce33459371c6735cb334dd35db66c1ce else 0x31cdd369b86a5ce324dd369b86a5ce32459371c6735cb33459371c6739cb33459371bd735cb31cdc379cd6b9cc37cdc379cd6b9cc334dc35db66c1ce37cdc2c9b8669cc334dc369b86a5ce374c735db06d9ce374cf35db06d9ce384d831d68669bd374cd35db0711ce374cd35db06edce33cc934dc66d9c8324dd35db66c1ce33cc9371b86e5c531cdd379ce6b9cc31cc936dbd711c837cdd379ce6b9cc3845927dbf6b9bd34cd835d2e6d972334dd35db672dce37cdd379cd721cc334d3371c6735cb334dd35dc46fdce2d4dd35db66fdce334d335db66fdce334e535db63d1ce2d4c1371b86e5c5374cd35dbf6d9ce) else (if i < 96 then 0x334e535dc46c1ce334dd37dbb6c1ce334e5369b86a5ce31cc934dc66d9c831cc934dbd6d9c831cc9375c66edc8294c9375c96edc831cc9375b96edc8364dd379cd6b9cc304d335db66c1ce334dd35da76c1ce374cd361a96e1ce334d8371c6735cb33cdd35db66a5ce164cd371cd719cb334dd361b86a5ce374cd35da96d9ce33cdd379cd669cc37cdd379b86b9cc33cde36dc6711c83845931dbf6b9bd3845933db0669bd37cdd379b8669cc334dd35db66a5ce304e5361b86a5ce334e5361c46fdce304d8371c6735cb364e5379b8669cc304e535dc46fdce334dd35db6689ce364dd2c9b8669cc334dd35db63d1ce else 0x374c7369a9711ce31ca5371c6735cb33cc7371b86e5c5374c7369a96e1ce334dd35db64f9ce334dd35db26c1ce34cd835d2e6d9b8324d831d68669bd370c92d5c26c193374cf35db06edce324dd35dbb6c1ce334d3369b86a5ce374d835d2e6edb833cdd35dbb6c1ce31ce535dc46fdce384d833dbf6b9bd364e52c9b8669cc304e535dc472dce304db35dc46fdce304e535dcc6fdce31ce5379cd6b9cc364e5379cd6b9cc304dc369b86a5ce304e5369b86a5ce364e5379ca669cc394c135dbf711ce334e535dc46fdce304dd35dc46fdce374c135dbf6d9ce304e535db66fdce33cdd35dc46fdce33ce535dc46c1ce)) else (if i < 192 then (if i < 160 then 0x3845933dbf6e5bd334dc35db66fdce374cf35db0719ce374c735db0719ce394cf35db0711ce374d92c99a6e1cc364dd379b8669cc31cdd379cd721cc334d8371c6739cb334dc369b872dce294dd325b8669cc37cdd379ca669cc374cd35dbf6edce334dc361b25a1ce324c736dcc719c8374d835d2e6ed72370c937dbc6ed93374cf35db0711ce294c7371cd719cb33cdd369b86a5ce370c933dc26b19331cd3369b86a5ce31ce5369b86a5ce31cdd369b872dce31cd3371c6735cb31cdd369726a5ce31cdd361b85a1ce374cd369a96e1ce334dd369b85a1ce374cd37db06edce374c1369a96e1ce394cd35db06d9ce else 0x360e5379cd6b9cc360c1371cd6f5cb360c1371c9719cb360c1371cd719cb364e5379c76b9cc394c1361a96e1ce374d9371b8725c5364dd325b8669cc394c9369bf711ce374cd369bf6e1ce368cd371cd719cb374cd361b0711ce334dd361bb6fdce334d3371c66b9cb334dd369726a5ce370c92d5c26b193334dd369b872dce33cc1371b8725c537cc1371b86e5c5374cd35d3e6d9ce37cdd325b8669cc34ccd35d3e6d9ce31cdd325cd669cc31cdd379ca669cc370cd35d2e6d9ce364dd325b86b9cc370dd369c26a5c7324cf31da2669c937cdd379ca6b9cc374cd35dbc6d9ce304dd361c45a1ce37cdd325b86b9cc) else (if i < 224 then 0x324c7375bb6e5c831ca5371c6721cb324dc35db66c1ce370dd369766f5c7360dd325cd6b9cc334dd35db64b9ce294dd379cd6b9cc370dd369766b5c7294c936dc6711c8334dd35db66f1ce374c136168711ce31cdd379cd6f5cc364dd379cd6f5cc374cd35da96e1ce34cd835d2e6d9c6374c735db0711ce374c737db06edce374d935d2e6d9b836ccf35db0711ce31cdb35dc46fdce374d937dbc6edb834cd835d2e6b9bd36ccf35db06b9ce33cdd35dae6c1c9324dd369726a5ce374c1361a96e1ce364d3379b8669cc394cf361a9711ce394c1369bf6e1ce33ce5379cd669cc364e5379b86b9cc384da33dbf6b9bd else 0x374cd361bf711ce374cd361bf6edce370c935d2e6d9ce370c937dbc6edce374d937dbc6edce374c135d2e6d9ce374c137dbc6edce370c937dc26ed9337cd9371b86e5c5370dd369bc6f5c7364dd325b8669ce374d835d2e6e5b836ccf35db06f5ce394cd361bf711ce370cd35dbc6d9ce304dd35db64b9ce370c137dbc6edce370c135d2e6d9ce294dd325b8669ce31cdc325b8669ce370c937dbc6b193294dc36dc6711c8294dc36dc672dc8374c1371b8725c5370c935d2e6ed93370c937dbc6c19337cd8371b86e5c5370dd369bc669c733459371c6729cb324df369c26b5c7364dd379cd721cc)))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segPayloadE : Nat := 0x4500000560030054011803000e805a005405c008800500a0010009000e014c050017003c011002a013005c0160001000c00d0154034019003e01000660044047005805c005003d00b40380138065015c01c00980170010051006c02c0148019019c048002005c006801d0008060017000f008000a006003f017084807c707e7a006e7a706c34645e2c5c5a7e4e4876624c24164a461e3e3a32140c021c04008e4b4f005015d00bc15305340d3050c15c0171158053006802dc04402d8030856815205600ea052c0c105441580554140006314505580d4047415e052016a01901490518158015c1600528141056416b058408e030805ec074154051c0bc056c07b45b1150009415801ea14e005615f0560033c25c03901e4162056021201f1c1f9e801b9e9c1b0d19178b17169f93921d989309059291878f8e8c8503008701002392c8b065c488122823c000647c11f000e922447c12c819412c4001800600e904847c000647400062d000063fe11f041011f000191d03b40d100018ec047c003a001800647c0968001800647c00064b30eb04ac15f019512c057e003a00e800600e80f60018006001800600180062ed11f03fc12b847c12002d2000600e80f657d0006001809a03b800600e800600191f0001803a0018006001800600e8006196000600e809a00195fc0018006001800600180062ec0006001800603c80060018006001800600e8006258000648cc000078c6000070de000096dc00008eda0000687e0000c2d80000bcdedcda3cbab8b4185eaed80ca8a6a20088d6d23082a09a5256c86224285444ea79ec808821d016821c07b419006d422d029223a04ac0368578080054805b085e21608e81d407b015f082023a08b0022808e05a88721a00ac01d507702b102021ed829423a02901d485d21b408242b0887611a054c0a580d821683c6174085c0f08ac61fc012023a03c411a808c23e08e805b84a804903c01d588e842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725800200080e60008016000803a40a001e00080e6006919000f8664009802a460120000280020008dc045800020008002000800200180160008002000800200080024580002005800200080e20009160002800200091600398002000800200080024581160000904037811d000093144ae000200080024581160000803200091d003980024c4116045800ea465002219800425540002572000645800263b800022b80002246001e45800de0d500022c60002338003a46100020d40002555000257335af360034ae350033acb43300002cb2b08030312b2a17a916a8892814a7881310a4852624230422901f8d31a09f0c169e9b811d1b13800c9ab81cc4c10e047410e01c807301d011002b00006438085c438060043805ac4f100d24e100ce002901c002904047410e00028b284381674438000a3801190334000a54c15d8058000a002800a003801a002862802091c00481574438161c031800a002804643c000a002800a032800a002800a48810e000290e04fd000a035800a00287884a6000a004800a002800e002800a438000a002800a0028026002800a00292c80028036036800a003800a00c801a002800a002800a002800a002800a002800a0208006002800e002800a002923200001e3880001c143837a4b7308022b6b6359a3500002f8000002f3635b50f34ad34062c97ac03292ab300280a2d8c27a8a114a199188920a5913b1e400100048e8000400b000405d0034880007c3c02160804001c01f0054858245000500040012080858017c00123a00010004001000400300048580004001001c0010064858000400100040010004858000400b0004001000400b216000500040012160001216000121609ce2160001001cb4e0004001002489a00840010004a900044308000494c0004adc00040010a880032160019001c00115600131c2000f23000010758001161001b0408061224000119800012a8800109602c200040012c99ad89b001a5817da19d69a19800016995700144955c71514d4138593d352041251d08390d04ec20f8c0ac9460e8e07c08d87818b0d0640098c9c0e600f800200280023f80002000800242d0002044000200a91f04100006000800214900022a80002410000241011d000080022be1040005800a41000020009040000800200391d000080020008026438000242c00020078006410003200380123680002410000232c0002008916000e90400039510003803a045000200680165660002439000200090405450520000800200d959c410000a010800a000ab26a9802a25a3802994aa272821a8a2a213a126a311169e9e001d9d0f0e9c198b8b1a980807901705008c92828605ad97ff81ff06b8000c7f000047f000047f000047f0015c7f000047f000047f000047f001887f01fc0540207806620685441860650018081c0190a802a10a82206001f0004a8600040150004001015c003000400b00740051fc07f022800010004001000400300040010004011000400120908200004059000400123a08e8000401300040010004001000400f00040570004001000401b00040010004001000405b015c0010004001002c0010004001015c001000400d0014001008400100650c000000fc000000f0000000e9999400c9994800b8d49c847955a19c614599944941918c313d8984a92d817c912979741925716c01156965b4e20008002000800a02a801a000878001080a60058f6000091d03d800025a700020028002294000229a00020078032000801600f8f6000080023ec0002536000253d04c03b80002000800600091d0009967c000805a0008f6037e1198028800a000869c3240fd4000800200083183760002000809a00094b001680023d80002000847858f0f800168022000802a00080023d8000600c8f604c800023d80e243d8000200080024600344000801e000805a4c000023d800263d800020ba00023d813100d90002000805adeded0c8c4dcc2d6d600d8d0d000cca2705abc3c0080320000260602ba903286b62880b0741e16ac726a0a645c00a8a69e9c12529a92563a4e463ee877001400100040010004520007c00300047b40004001004c0011ec00011b50001000c0011dc0001000477014908b41dc000123a077023a0001007400b29100010054770007416c000477000846d000040010004a421900001000477022c000100740012918a4000340011dc0168003c0010004770007404d000400105a800100440011dc07b600f401d007400105b800b00040011dc07b20014019000401393554012cbd50015521480001511d4d1911090050f8e52cb0e0dca03c94d47c28709cd814cc64a40038048060116cbe422c809d804f09b803f001824c0b28000c0151d40001000431800045181f20728167075000041c01e806381d400011ee01920f183380004a3800040051d4004f00340011d4000b1b00b181d008b8013c7502c0800123c00ba0b30ab81ea00012bd000100440010004021005c0010004001007c0010004005006c001000401027c00010134001000404f00040011d400010004001000400300040010004b16000401b013c0011d40001006400300040010004001002c01300040010004001013c00f000401d0004001000491c9b800d9c00000c9bc000139b8000129b40000b8a5ac0195a9a401918da9a07981797c316d656819595140014d193060f10d14a510f4884864ec51d4f35c000200e8db000080020268042000800200880020008002002807a0058002006800a0008e445080a1000196600100da028a000200080024a8001638d16883180da001c0da035a0dd036816643750da000e8da038c0002505000200180320008da0000915800e943c00e803e00a803a00080020008da000091d000091d03900da050400023700002011000250e0002512000200080025a30002368000200080023b8000201d00020098de000e8d90000800200080060008002509000200e801e36800025130002000800241000023680002000ba0020389daa3926b80037003600350034002300338020803200310c02001bb0b02e9b2e2d012baa122999280f270c970625949409a488230310219e8017bd1f462020066c047066812906380a306660a2868018a038014001f813e00d219f06601a006401728504196068019a85f8021838619e06a023a063c0ef86a40e0862a17f06800a2063a18b008219706a219b846013f028e034066218805c819903ba1a9865004606800ef062e02106881a001fa12803840ee063e1a010900f8e0fcf400dcf4e0d868c8bc58b8b4fc9c90ecc498482c948c3c7c74642818043808011c963706a80e206ac0e386aa13c0003190000b190064019000491900013001c162002c64e13d063018800081a4000b1a60770059864a180069c1a6800b002c160002c0411a7800b003400b19d000b24c0604236000b193038a002c03f002c00b002c017002c00b002c04b002c007002c63419c001005906ae001c009002c00b192038c002c013002c00b002c00b002c640004c047002c00b006c007002c041190000b000c00b002c640002c045000c00b010c00b002c00b004c00b002c007002c00b000c00b002c00b002c00b24416f003c2f0000382900004b71000047700000346f6d0062006c00616d6c6b1e5f6a690c5d5a6806592f67005844651854522229535119124d4114753cba01e211d02e8003e1380bd0010800e268000226b000200280020008002000802a000800e13b00020008ba02ec0bdc00081e02e813f80008b90000801a4fd0ba02e800020008042002800200085fc000913c00087840008bcc0008002009800201e8032000802e0008bc000081ec000801e47400022e8000200080020ec000e39900160038fd0005801200080022e80002003802217c00024da0ba0000805e44c00024fa002200080022e8000200080364f900024d90002000802e2e800022e80002000a6b730802fb6a4b62f35b3802db4ac802c34330029803280288022b31aa91832152b92a7832590198e0ba2130b0f1f0908071e0506021b9e8016389d49804a42c80be426000062bc00022bc00022d400fc2c906e42e004a01430b0003e0be01b80b8400a800e00380022a00b402bc0af028809d828006c02c40b7000385083e810482c1000230600020028b74000801a0008840000802044400022bc000200080220008002000802e0008002000803e000800e000801200080022bc0af00008002000800200080020008af00008042000800200d800e000800a000000200080020008c1c0008032001800201d800200080160098002000800e000800200780020008016000800648cade006cc8000064c6000088be000080bc00005cbae000b2dadc00b4dedcda3ca8d8d618a6d4ae0ca09eac0098947a30927856528c7c5424287644ea79168150156011414c049c1460072158815c15204d80da04e807c04e0032856814a054815e04d213c052015205320d60278092853816c08e816603b6185036a1368418152015e14684ca054855016c855a11604f801c00c814a84c013405600ea8616142010815203b4132027a15c054807c849009203a8166854842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725f088e812a09cc09a09c417a03c012a08e812a049012a049800044a800044a812a074c12a08e426f04a812a09ce09a8015271800117a803308d8001005c9b412807d804c04b800049b61000001000400500040010034001078000104c803300440010004001005c0010004001007c00100cc00100dc0010004350224000112e823400040150004001000400100044a80004021000400100d4033000400526f800100e400100044a8000401912c000100b4001000400b004c00100040330004001003c001000400b000401924725a7139706d00356e6a00436c00003f6b6a693168570054005300526851671e6665640c4f6362064c3e6100604b5f185d485c2c2b452212192914753cd000401f00040010054001008400300149e217a000100049e6002c00700040010004144001c4680004001002c468000400100040010de046800040190004468000400f17b0013000400111600010f10003000400511a0468000401b00c48e800040011170009001c4680004001118000b0f00001000400111a046823a00010014468001c0170df07c0000402f11d0468000400127680010004140007c01900049de004473a06e000100044702200001000422800048840004001000422c11a185a58001a59da4019991996c00016d90000181713d5d00ecd51108fcecd8d0c15d50b8ac9c942c894d447069352c3d286c246018004c440925bce6000803e046002a06d000600990e8000801600280020078ba414902d80008002000800200088d01d800021e0000200b8002003800e1e00790003805a1e00002010800200087a00008002000878000087b000380021e0000247400021e00eac4740002000800a100075000480361e010b000080220008006000800200580020008780000801a090078000080023d8000200087800008770254078000cab29290028a6a82926260024a6a323220e8a82a3210b200901889d1e9c9c1b1998979696158387851392920011908d2d97dd015412f0006852047405201480510148000215c054001800024d3000201580020008002000803e000852014800020f511d0033000213c0002015800e005801600085b014813d4170056000485e000080020008002204002216000020008f3000080561640002433000214c00020008002140000200080024e8000e1480032168000a010000200a8520003878400090400108002000803a49c00020038002148000a036000200e8520000800e00080020008002000888000080263f20002014001e0008002229003600080021480002000b500243ba334208033003100150030ba1fb9b8002f802e802b391338ad37112c2b381d9b1c0e29b79a3729360f2f8c9f09a80727040b97a58218088600013c9f40010011d011e029010812e011c04381e00f2011a0054106090000183e84281288017000a100135800084000008400120078800091d010000a810c000248509084d400021000002000928000083d80f40400028001a000841000083e0114044000980020008400000801e00380020fc000200d80020008002004800200080020088002000800200b800a000800200f80020038400000802a0028042000800200080020058006112000e000800242a04001180458003800200580020008052002800200080020008002000848800c800600080020038400000a0003d801dbd393c9b00000019003b0017003a80153a37b9a780258023b936321323b62090b5b3b30f1e32138ca28a26880e310b86302f2e0303ac80802c2aaa3ea04210c8150000c168056000105a016005a01800004168064000105a002600e092a23a00010004168000402700040010004003001c00100840010120168000417005a016805e01680660148000477005a03e800040130004001000400f000401d001c1880ff83c4001c00100040012130840000400d001400123a016800040250004001002c0010004009001c0010014001000401100040010004001002c0170004001001c001000401f0004001000400100640150004001000400100054c015c013c00a0013001a8012801a400d8000000c800000079a5a19c61999590498d21883110c094a985817c91797518190900f80164f155b4e26009002401e111d008400060900220000824008c0240094024009c0002090025402e0060008800200080020018002090000243610600008264001800e000804200080a4028000221d0870003809809d02400008f10090078000080260008002000801e000803a003800200080020901238000801a00280024740240000803600080020058002000801200380020028002000802200080020058002005802e00080020118002000803e0008002000800200c802a00080020008002000a9002a00273525002380348022b433b319000000170000000f3332b20c31b130893021af862f202e952e2dad122caa28031f1e1d00159c12b69c400101a8001000c0d80f088e8000c001000400100540131de0968000406c20a0001000400120b8007001c00100840d8000400b000400300040d800140010004001001c0010360017002c001000400103e00d80004001000400500040d803f8019003c00103800f600040c8006c001002400100040ce00040d0000401d03600d800040110158001000400103a00070360007000400d0f100d8000400103b80010004050036000100043f623a0001007c0010108001000492200040f00fc00d8315d5c006a685967676558536700535166656062605e5b54234d304e4c462a4945432840241f1d1a160a3f203e3937153836132c0f0d0406006f39800200080020300002036004200a889c3c001104100002000800200080060008002000800200080160440006000800a0008002003811000080020058110000800200080020028002044017000c80020079078474000e00080e000d8002004800200080f0000810000080020440110000802202c00260008002050000e044000e00b800e00e9330058015000080020008054044000200087c0044000204c07880440002000882c474000200681200018110000818000f800201c000200091a4d4c2d600d0ccbecaca0abc74cc00b2c8c600aeb28c584a403cb274a8aaa668a09c96646c5c524e4822183c2e9490841e86820c36328000042ade73220477122031a11e0488122031912304881220474123c4880406028582050084000784c5c113045c0c60319117045c10b048c117045c10f048d117010180a1608140210001e130303f810303180c6840c10303e8123040c10303ea123840c0406028582050084000784cd1d2004d056c000000001d013404d059404d013410f013404d013401d013404d013404d007404d013404d000d020d0e040009000501000000190e98026009802601e803a00980263a402c63fe003a3cc0006009802600980260068080009802600984200098026009800600e84f00098026009802600985e000980063a4002600982163a412183a402be3a4009a3c000260b08026009803a0098e900099164001803a3bc00263a40026009802600e81d205d8bd0009802600980268c722e888888808080707a706c282466641e1660584e82544c4a46807e103e6220023a0a3c0036964fd000001d001404d007404f007401d008c7180574149007401d02c801d007401d056c01d03ec01d00b401d007401d007401d007401d08110002061002080503000000000b04021f11800200a8002027800a0008002001801638c000200080020008410000801e0028e300058002000809e38c009e0008022000803a13805d000080024060002000802638c009e00080020008006451002e000845000080020108002000801a00092040ab800238c0002000803e0988e300008002000800200c8e3084807c707e7a006e7a706c34645e2c5c5a7e4e4876624c24164a461e3e3a32140c021c04008e4b8c0000000063018c063018c000118c0630010000000000000a07918c00000000c0fa3180000000181e4000406e31800003180c00000200000a098c0003188063000000000000014127063018c0015000000000000000000400001c1b180c600078000008201e3018c000d0000010403d80003180c60000000000a098c603180100000201e300dc0630206020009a063018c06300b8091218c063000048b8080d000c070b040a031009ba001c00000006300000000005048c500000c6031800008000028263000040000000630000000000504a3180c60044000000001800000000302e3018c0001000001040380003180c60000000000a098c063000000010080000c00001413180c600008000000201c63018c0080000100f180c6000000000018000800002824080002318000031800000000000302f48004c013004c0130074013004c013004c0031dc0013004c0132300013004c013004c01323f0013004c07f004c748004c013004c748004c0132010013004c013004c013004c4c0c0074705064440058546800381800006814040000a45a41063018c0678004c80822c06d00002000200000906fb00040011c8007f0004001000400100040010004001000404f00040011c60001200071822a00010004718000400123e800100040010004001000400100040010000001000c001100a001f1e0f1e1d00121d1800091d1a001901101600291690a192063018c00011fe08a01bc0000800080000241aae05780d2002800e0028b7000282b20028000002800a002800a0028082002800a0a4800a002800a002800a00284070006090282010502020000000d0763000140004000c0e000802a00280020059074009800200780020038b70005800200083f000080120008b70000800200080022dc00020008022000800e16c0be000080023ee000e01680362dc0002000800a0008006415002e00084c00008002000800e000801a000906400080022dc0002010803e0018b700008002000800200c8b7086827e72767e006e7e706c34645e2c5c5a824e4874624c24164a461e3e3a32140c021c0400904bc0070074023055c01d008c0211600023008c15500000230014023008c0230000023008c023008c023008c000820000010100004200010000008683f1800000108000000181d9007c058009605800b4058017e0580007c7e4000400100540010004580001c00d00040010004001000401d00040010004007000402b00048420004001006c58000040012148001002c001000402100440130004005000400b0004001003c02b0004001001400100040011fb000716000070024001000401d0288001000401931002d443a002a00360014472a460d4526441f431d4201413740153e35380c280524002119094a26801201b800e000009a00482a20a980120048012004813a00480120048012004801200489d0004800e00484890403028289038005058280000c87524007002414b02bc4d0001c007001c14d051c007001c0aa0004007001c0070524007001c007053c0230014007026c007001c00700170a000d09050b0300090000080c0307022012c6000000000038000000002025001c0830004001001400501a400500140050014520001400500040050514005001404100140050014005001400046414301438240c0810003400006c3e00a80020028002000801646600260078002290000e005800200083d000080120008a400008002000800a29000020008022000800e1640c1000080023d6000e00e80362900002000800a0008006431002e00084a00008002000800e000801a00091a800080022900002010803e0018a400008002000800200c8a407c848070827e006e7e706c34645e2c5c5a804e4876624c24164a461e3e3a32140c021c0400904bd809204e80b004e818404e81f304e8220801f0004001000400813a0007050c0010004003000400100040070004001005c4e800040012390001002c0090004007000400700840010004001000489200040030004005005400b000400122280010044001000c00f0004001000400513a0001005c001000403d000400100040193200170039002e00120014480f3908472e4627452544204338420b413640013f1f2c00291e094a26800200a800200980020028002003800200083a0000800200589a026800020048002000802226800020008570000800230c0002003800e00e80022680f68000801e0a090e40008016002800200190d400b8002120000200080020038002006800246e000200089a0000804200f800626800020008002000803226821a09f9e201e000d9e1e9d8d1b9a8b17181c16959b1615090592918792110c8503008701002412cf4055015400b03ec02d10a802d03ec04d00b405d015402d00b402d00b402d00b402d00b413f00b402d00b402d00b4180018100c08000000241000000424703e000823a000889400000020008002000800a0008002000800209e803e000800200080060008026000880700018701808003008181800c06c00100140010004091003c103001401f0004003047400100040550004430000400100400010004001000400102440010004001060f150f1a0011060503001008010401001f11dc08900e708900aa089034c0890000800200a8d88000800e000801a00080020008002000803e3ca000200e88900008002003800201580023550002000803622400020008d6c000801600080020108022009800200280020058002000801e0158002000800a00080020008f1800388900038012000800200e800c000800200c9a001900170015001c800a24152386a313228fa20ea180a11da08a9e9d178614029200108c84a513400100540010014001002c013003c00110c0007002c00100041b0000400900044300004001000400110c0001000401100040070a2869000040011a5000703ec01b10c0001000400500040031ae801700041b400040010004007000400d00046be000400110c0001008401f000c43000040010004001006443042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725800200a8002002800200580260078002214000e00580020008350000801200088500008002000800221400020008022000800e1490d100008002352000e00e80362140002000800a0008006351002e000835c0008002000800e000801a0008d1c00080022140002010803e00188500008002000800200c885084807c707e7a006e7a706c34645e2c5c5a7e4e4876624c24164a461e3e3a32140c021c04008e4ba406901a40030ee806901a411d01a401503f43f201a406901ac11d01a413b04dc0ed01a406901a406901a406901a406901a470003c340014180008181414100018140c7c4701ac10b01ac06b000006b01ac06b04e4000007401d01ac06b01ac06b01ac00f01ac3c801ac06b01ac06b000000040d150001000801060001190ee800200080020068002000803e1e4000200088ec010800201e8002000800a0a4000200080020d2001e00080021e405600008002000803a0008c900008002000803a1fe00021e4079000080021e4000600c803a00a801633f00060008790026867033e00020008022000801600e800200e80020008026000879023a000a32500028c7676888888808080727a6a6e2c286866005e185c5882525048424e221a403c02103a362e0a08964f50f0000001a406901a406901a406901a406904dc06904d411d01a406901a40ed01a4069003406901a40690e12000e000e040b010501000300190eacc03a02741e00328002878015407803200780332078001d0cb40008ec40038b5c0008002000800200080261e000020008cec0078002000800200d80020008ab4000800600080120008edc000800200080320088002000800e000802e00380aa01080020068002000800e1e00002000803e00080020058002000800600a800a000800a0008016300000002600960066008c001c944c920e908e8c008a72885c86768452823e804a7c7a663c60421e9c5100040150004005000400b004c00f00043b8001c00b0004001050800100240010ee0001000400100043b800040010044001001c2a018e00010004684001c01d006c3b800040010014001000c652005c00106780010004001001c001003400119b800100043b80004021007c0030ee0001000400100040190ee10900f8e0fcf400dcf4e0d868c8bc58b8b4fc9c90ecc498482c948c3c7c74642818043808011c960008002000800200080020008002000800200080021b800060008002000800e00086e01b800021b8000200086e0000800200006e000086e0000800200080020008009000f00070f1180058d8480038a0000020b01130a40010004001002c0010d8800100040000000001000c0010004001000400700040010004001002c00100040010004581c1c5050080048481414404000086c3e000800200000020008002000800200080020008002000800200380060008002000800200080020008907098a0705028000048203008c06e86a8000801a006803e006801a00186e01b8005e006805e006800e1b8020600680d2009801a00080220880000006801a006801a00080260998000006805e006801a420000363c2e2c2c141c260c101400260600201a004c2b000400100040010004001000400100040010004348000c0010004001001c0010db8001043000b0da800704200010004000000000000040010004001000400400084003400100028502000184800000c000890520038002001800200080021b806e0007801e007801e000001e007801e0078016007801e007801e0078002017801e00786e0007800505860008800700030a01000000038f0870004003000c009004c003000c05f007401101ac003003c06903f405f0cc03700dc0001007c0030074003000c003000000d000c0030004003000c003000c685074004840000c442834003810082c18000c904f6000803600a80021b800360008000000826202f800600d8036007800200d800200d803600d8036017800e00d80362c3218281e000e26240a0a20000600361f00040150004005000400b004c00f0004370001c00b0004001062000100240010dc00010004001000437000040010044001001c29818c00010004634001c01d006c37000040010014001000c632005c00106300010004001001c001003400118d800100043700004021007c0030dc0001000400100040190dc10900f8e0fcf400dcf4e0d868c8bc58b8b4fc9c90ecc498482c948c3c7c74642818043808011c977001b400301b4071000406d01b406d001c06d01b406d01b4013000400101b400b004c001001406d0dc006d03a000001b412f03a806d04b4001008437001b406d000b2321001d1e060014181c000f1218000701002514b0004001004c00b000400b002c0070dc00410004001000000b0004001002c00b002c00b004c00b000c00b002c00b160b080909060007020009101001041b0f8002000800200080020038002000800207e000200080000000002000800200080020008002001800200080020008b04040485030008020201008400018d87de00080020008002000800203880020008200001800200080021b8000200186e01b800020008002000801600080020008002000800200080020628a08820907008c0609000384038282880280819189f802600086e00008002000800202886e00008002000800200086e000080020000032000800000080020008002000800200080020008186068c850200050402888302008507800f88c05f000c0010d0000f000400100043700004001000400100040010004001001c000001c00100000010004001000400100040010c0a0b170803000805000e0503010800001e119801e00080021b80002000800200086e0000800200180e2000800200080020000002005800200080020008002000800200080020008685860c8482000483000a0301808587800f88cc01d0004013004c01f0dc00010004013004c013000c01301d4011004c013004c013004c01300043cc004c013004c330004c013004c013000c07f0004001004c01300040130000013004c013004c8c947c00049088540c8400506c48706c60342c3440041c1400b867c0010004001000400100040010004001000400101c400100040010004000000400100740010dc000100040010004001002c013000b15160000001b00050a04000209021e1080020008002094815a0008002008800e1b800020008002000800207806e001080021b80002000800200080020178002000800200280020008000003e302a281600102004000e200a1a000e3644250004001000400100040070004370000400100043700dc00010004001000005f000400100040010004001000400100e410100040030400c00000024002030140010541c78420008002065000200180021b8000e00080060388002000800205f80020088190000000200080020008002000800200080020008002001c3822140c003010041c100a06121a043e23f000400b000400100bc0010004001000400100040010dc03700dc00010004001000400100040010004019000000100040010004005c00080010002c0030240000181024784256058802e00081e600000001f8000a00b8002002802e0178080000400838001000704c005000c0010004001000400500140010004001000400101b40010014001000400d00141290014370033406000040000014005001400100140050dc000500140020081c00544c18004c14700060280c0028040094524001000400100040010dc0001001c00500040010004001000400100040000004001000c00100040010004001000400100040010004001b00001405000a0e07000609021e10a0028002000800e00080021b80002000800e000800200180020008002000800200180020008002000800200080020008002000877c0008002000800200000020000002000800200084930d1009908c8f07800a8e8e86828b8c8901000b0380150bdf0004001000401f0004001000400100040190dc00010dc000b00040010004001001400100040010004001000000100040010004001070c110f0a02041302080c020803070c001f11e000800200080020008002000800a093800e00280060028002000800200086e000280020028002000800a1e200060008126000819a030000200080020008002000800a002813e0328000002800a002800a002939210848414130e0212800b810c09908d0906078081098700180cc05f0004071000400100040030004370000400100040010000001000408100040010004001000401f00040010004001180009090b040013050107080802061c0f800209280020138002001800a00080021b800020008002000000200080020008002000800200080020008002000800230021410140e002404000a14120a08381f1007c00100040010dc001f007c0010004001007c01f001c06500000070194003007c01f007c019007c01f007c01f007c01f000e001500050003000a1207000013011d1088002010800202f8002000800200080161b8000200080020000002000800200080020008002000800e00080020008002280214140c0c002804000a12120a06381ff4001000400100040010004370000406d0014000001c001000400100040010004003000400100040010004001000400100040030002c00004c1c002034140010200874420008002003800200080060008002000800200086e01b800020028002000000200080020008002000800200080021600102a2a2800121c1c0a08000404361f002c001000401f0004001000401500140010004001000400500043700004001000400100640010004001000400100040010004540010383424043c241448000004441c281000844e0018002000800200080021e40002000800200086e0000800e0008002000800207d800200080020008002000800200080020018120c00001004001c0808000402003c21001c3b800040010004001000c0010dc0001000400100040010004001000000100040010004001000400100040010004380014602c34200c28081c08000400703f80020008002000800200180021b80002000800200080020008002000000000080020008002000800200080020008700040605868381850103010000828d87c0070dc00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0fa010800200086e0000800200080021b800ee00080020008246000800200380021b8000200080000008002000805e000800200080020008e8e80000c8188800c09858289000205801008c880010004001000400100040070004001000c0010d68320000400100040010004001000411800040010004028000401b00000010004001000400100005c6470043020506028004450000c20184410088c4e007800200286e0000824200080020008026009800208e800200780020008002000800a00080020008630000800200086e008f86e0000800e000805a00000960008002000803200080078603019011920e0e8010880c83810d0c0b098880150b400100040130004001000400f0004001000437000040010004007000403b0004000000400b00040010004001000c00f0004001000d07060005091400020b0400000d001e108000000820a00380021b8017a00d817a00080060008002000800200080020038002000800200080460008002000800200080020e2000003a0000243006243012080218003e2300040030474001000402f0004370000400100040010014001000400100043700004001014437000040000000001001400100040190004001001b001c00170d0f0706090311010e08120021128002000800200180020178002000800e000800200080021b800020000002000809e0008002000800200080020008700040606040308020202050081000d87c01300040010004001000400100040010dc011d0004001003c3700004019004c00501440010004001001400100b40010000001000401f000400100046800584c3844545434101024000000400028088c4e000000200a800a0008002000800200080021b800020008002005800200c0002000800200080060008002000800e00080020010200e00080c1200021800001424063a210004001003c001000c0010004001000400100040010dc0001000401b000000100040070004001000400100040010a0308070d000705070400030002021b0f8002005800200080020008002007803a00080020098002000801e000803a00986e000080020008002224003a00e800200080020008016000800200080020008002000800200080024e3c1c3e1436124628283200202e04001a080200160400562f0004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110c0001000400103ec00100040000004001002c00100121610001f1d1800021c151705110b16061902070029168c001004c00f00040010004001004c00100040510004001000400100740010dc00010004001000400100000000004000000400100040010015151500120c070c050b020a00060900092012801e000802600080020008002000800200086e000080020008002000803a0008000000800200080020008002005801e0008002001a0e0c000a12280004160800001a003c210004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110a00010004001007400100040000004001002c00100121610001f1d1800021c151705110b1606190207002916802600080020008002000801e00e800200086e0000800200086e0000800200080020000002000800200080020058000001e182a00141408000a0e0c000002043821fa03e81fa07e866007e81fa07e823607e81fa07e81fa07e81fa08d821e19801fa07e866003f80fe03f81f603f81fa07d81fa07d81fa07e823607e80fe07e80fe07e81fa3e300030382c282030221806001600001000240c06502bba01800cc018401fc3300c4033018800fb0cc033018886ec1ba807f03f407f0ce00fd01fc07f044407f189007f01fc33003f407f01fc07f03ec07f043407f01fc33c046410f01fc6ee189807f01fc11301fc07f01fc0fb01fc0fb03ec0fb045407f01fc07f01fc03d0cc007f01fc07f01fc07f01fc07f01fc0fd03f407f01fc11701fc07f1800000013004800330000000e4a3b490748474600453a442e43424129331f40253f3c301e21280f4d28d0074750000c000004c013004c109042407f004c01101fc01301fc001004c01301fc0010dc00131d50013004c0010f200130f300131d580131d480fb004c013004c0130004001042c330004c001000407f042401f004c013004c107000c270f0000002e00082811002e192d00231c03001b001800151b01351c800200000020008002000800200080020008002000800e000800200080060008002000800200080362e0e0e000e0802120804000002301b000400000040010004001000400100040010004001001c0010004001004c00100040010004001000c5c1c1c001c100424100800000460360018006009800600186e000d800600b80060048026000802200f80020008002000800600180060018006001800e0000001060b0003810300020382000003010e8840010000001000400700040010004001000400100040210004001000400100040010004001000401b17070700070401090402000001180d800200000020008176000800200080020008002000800a000800200080020008002000800200081062e0e0e000e0802120804000002301b8002000803a000801e0098016000800200080020008002082801e000800200080021b8000200080023a20000000800200080020008026000880f8785800f000a81880502800184808500108940010004103000400100040010004001003401b000400100143700004001001c001000400100040050004001000400500040010004005000471a0004001001400100040011e20100b1827021900021b1d14120e030200180e080e291680023a7000a000800200f800200a8002000800a00080d200080fe00280020058002000803e1b80002000800a016800200c800200080020008002000800a000801600080020008202000801089100707908f0a918212040080000a8d8480008c01160bc0010074005000400100043d0003c001000400100040fb1ce80010004001000400100040050dc001d112074c1cc075e01fc00500040010004001000400100040070004001000400300040010026252a001a2318001c1d030000110b001a02000016080c2d18dc00011d3800100040010004001001401f000407f00540fb0004001000400100040070004001000400100040010004081000400100010f121c000e140905110f05020301041f119c00d0004001000400100740010004001000400500040071c680010004001000437000040010004001000000100040010004001000438143c380050302400003c4400081000240c804a0008002001800200080020008002000800e000800200006e0000800200080020028e5038d0002000800200080020008002000800a060b0005010000060783000203810f0879e1e700400000c0f00f40fd00040ff001400100040050004001000400511d0001000400100140011df0001000478600040010004001000400100043400004800682858300c2c10001038001008804bfc00010180020028002001800203f800a3ba000200e8002002800200080021e40002390000200080020008e440008002000879000080021e4000207d80020008eec0000002000800200091080b8000018010900d0d0e8a0088068d858b00808b948b40010014001000c00101fc0051d30001001c001001400100040010dc00011c600010004001000471a000400100043c800040010dc000103ec001000474e00000010004001000488405c00000c008480686874500440346c2c5804045ca45bf81f203f80fe03f80fe07c81f62f500fe07c80fe03f80fe07c81f203f80fe07c80fe03f86602f600fe03f8bdc03f80fe03f8bd003f80fe03f80000b078a0d87818a83088704028500030111094001000400100040010004079000c00100040010dc000103dc0010004001000400700140010004001000400100040010000004c2c44000028040010141800080410744200080020008e2000086e038b000a000800e00080020008e24000800238a0002000800200280020008006000800200080021b80002000800a000000200000021b8000236301e3a08300038040024002e2a3a3626163210004e2b000400100040010044001000400304b800100040010004001000401f000400108c000103800e20004001001c12c0004000000400100040130004447c4c005840005400502814500c20041000884a06c000200980021b800160258016020801600080160008002003802600580160058016005801600180160058016000878a800a088902800380080001820000010f08dc031805c00bc0fe017005c011c113017005c014c11e41700406028582050084000784d30000000014c053014c0530000853014c008000000000000503d30001800014c0500000000000a094c06e014c05c80b802e814c053014c05c0173053014c00161710406800603858205018804d3014c001600000008074c00020000000000181d0a60298016000000000c000000001816980a600010000000403853014c0100000201c2980000000303c013000400b0000001002c0070004001002c00b000400b000400b002c00b000400b002c00b002c01311000d000c0203000a05000404180dbd02e80ba82980bd82b000040000000000000000000302010a07a600d0000000b0a60000c00001412c2980a60080000100f000400100040000004001001c001000400100040010004001000400100040010004001000400100044400340030080c00281400101060366818c026805a07d409a026808e087809a026806308ec09a02030142c10280420003c2600000000000006000800200180021b8000200080020008002000800200080020038002000800200080020008002000800200086838c01860106000280850000018300008f08c00100040010004001000400100040010034001000400100040010004007001c001000437003d400100040030004001000201000005001a00120116000e00031d108002000800201c8002072802e0008002000800200380021b8005e0008002000800200086e000080021b80002000800200c8002000800202340006160022180008202c0004141c10024225e207980220178000001800600000fe000800200000000060200160f00040010dc00010004001000400100040010004001005c00100040010dc0007000400700840010004001004402f000400100040011618151814170c001302070001010004002011c0010dc0017000401100040010004001001c02100040010004001000400100040010004001000400100040011905021000110505000303040000001b0f80063008001681f4020008001782160200080018823a8200080c050b040a0108000f09c4000000003100c403100c400020c4031002000000000000140f83000c40100000201d406200150000010403f06200000000c0f100000000006800080000202400100040010000001000400700040010004001000400100040010004001000c0010004001000400711000d000c0203000a05000404180dc000001880308001062000000000100000705c40310024000a0000000000000000008000038362000100001880000000000001413101b8031013602c00b803100c4031010004dc0c403100008404101a00180e160814062013000000006200000000010127408402120620276068001300000000000000000000c0804281e7c082020a062027e062000100000000ca00000000c0c0804281ee014c02e00ac04780b802e00bc02f40b802e00c4047c0b80406028582050084000784d8018c058015805b0160058016805a8160058018805b8160080c050b040a0108000f09c403100008000008201e201880004000000100e0c4031004000008078c000118c000001000004038002098000602f81d600001d6034800001c81da077800603f8200000004800180000784c01900e400100040010dc0041000400102bc0010004001039400100040010004017000400100040010004001001c0010004370000403f0054001000400584454844c5c60000c4c184400001058441c904e9800042980000040000100f1800083180000080000201e200010620000010000040380260008016000000200580160008002005801600080160008016005801600780160058016005800e22001a0018040600140a000808301b0004011000400100040010004017000437000040110004001149000100040010004001000400100040010004021001c017000400100040930084007000400100040010000001000424940094208c688008005078400440680c5c00540050a85a000800200080020008006000800200780022400002003800e000800200080020008002000800200080021c2a00240018162c020412000c06341d0000001000401900040010004001000401f00bc015000437000040010004001002c005000400100043700004001000400100040000242c0064345400540400002c0008784200280021b800020008002000800e0608b0400080020008002043801a002800200080020008002000800200080020008002000801a000800e000800203000020008002000800200080023a4c2c0040200448001c1a3a4a3830084800161e022c00582f000400100440630044001000401100340070044011018c011004401100040e9004400100443700044011004401100440000343c005424300054040000440008744200081620008002000800200080021b800020008002006800200080022dd00020008002000800a0008002000800e000801a0028002000800200380020008002000800200080022a404a3800344828102a324a0e041e0002481c420006542d00bc0010004001002c001004400100040010004007008c0010004001000400100040010dc0001000400100040010c19031304000012000a060f0507021c0f80020008002000801e000000200f8002000800200a8002002800200080a200080020008002000800200080021b800320008002000c080000020e3800041634000000243c210004568000400700040010004001000400100040010004001001c00100040010004001000402f00040170c13000d0b1201000103000b000b1a0e8a300038002000800a00080020008002000800200086e0000800600080ae000800200080020008002000800a28d00020008002000800200080080c0c8008000d000189000006800400088181120a41e006201e2000018800020004000705e400000040010004011000400100043700054001135801f0004011000401900040010004001000401100040110004001039403f00040010004001002c0050044001000400100647098008c487448883c6880000088785c202000001408a45ad40af000400100040010064001000400b0004005002c01f006401f00044ee000400100540010014001000437000040010004015000400100040010004001000400100040010004001191d0a22182306240e21002216100b002300161a1b0e052b17e7000447800044ee000400117800af0004001000c5e200040010f60087000400f0004130030400100040010004001000400700040010dc00010004001000400100044ec00040010004001091e0a1c20020521231d001b240d170010130f1e00000d2c17e40010000001000400100040010014051000400103940110004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10f80020000002000800200080020028016000800200a8002000800200080020008002000800a00086e000080020008032000802a002c180600081a2e00042218000000123c210004001000400100040010014015000401f000401900040010dc00010004001002c001000400100040010004001003c00600024005c305c003c0054000008047442000800200080020008002000800002f803e00a800200080020008002000800a0058002000800200080021b800320008002001a020000140436000414320000002c3a2118c863200000004038c6831a0000000201c63018c0000000100e00f8002000800a005802a000800200086e000080020008002000800200c80021b8000200080020008002000800b8685868a87060703000400000401820e88c2980a60000000100e0c603180000000807062018800000004038703540dd021c0e10354017035c0d9021c087021c087021c087036c090021c09801200d5021c08b0334087021c06001800cd021c087021c0870180087021c0d1021c08700d8060021c0871c18060021c0d102a0087021c08701400870160087020008b01800b0022c06802200cd01e00e303540cb01c0087037c08702e0087021c060021c0d50280087004a424b4947413d47454343413d3b38221d1b3733311900152e110d2d2b3c24260c0708342c2303045029cd03440cd021c0cd021c0870180087022c0cd0334087033c0cd03340cd03340cd033408703340cd034c06003340cd0334087021c060033400003340cd03340cd03340cb03340cd24041d16171202181918000a1c000014110100121a06291687031c0010004001021c37011a0001032c0010004001000455402b403f021c00100040600324001000400100040c500040010304001000400100043c4000c3e0001c00102445d80004001024c001007c00100140010004001000458200040191a2f2f29182a24311032232f1522000d0a092f25011600002303200006381db002c00b00040190004003030c00b001c00b002c001002c00b000400b0004001000400b002c00b012c00b0dc000b002c00b0100150f12070c051a0b160007011806001f11a600000a60000002c00040000141200000020008002000800e000800600080020008002000818200080022c106e0000800200080022e800020008002000800200080020200242000282200341a1e0e120e060c043e2302fc460000400100040010004001007c00100040010004015007c0010004005004400100040070004001002c00100043700004001004c00b00200800131d071a161900151015030107082212c4000200003100e0000000020000000c0b00040010004001000401d0004001004c00f0000001000400100040010dc0001001c01300040010004001000400100040010000001c000a02010000081a000801171d10800201c800200089a8001807201c807201c80721b8000e01c800201c803e000807201c8072008807226b007200c807201c80800a848a09040b8d030a8084010103000f88c00300040010004001000400100040010004013000400100040010004001000401d0004001000408482c10103c141804140c000060371800020000c603dc000000020000000c0b00040010004001000400302f454c00040150014001007c001000400102ec0010004001002c001002c0010004370000400100040000544450402c0c6c285c006000301c087c4600880020008006000001600080020008002058800200380020008002000800e000800200086e00008002000800200080022240000010d0006000a00000584000b84008f08400100040010dc0017000c011004401102bc00700440110ee00110044001004401100040110044011004401114180110004011004404005c245c543064201860042c0808200080477000040010084001000c001005c0110004001001c00100040010004007000400100040010004001000400100040010001000b000f010014150d030f07041c0f84370000400300040010004001004400100040010004001000400100044d6002c001000400100040110004001000400005418004814004c380814441800703e200080020018002277000200080020058172000804600080020008002003800200080021b80002000800200080020008002000004340026002800001610003010023c21116000100040010dc00b100040010004003001c00100040010004001000400102bc001000400100045ba0004001000400100040010314151216140c1607080e0002040104002011800200081620008002000800e0018002000800200080020008b4000086e0000800200080022dd00020008002000800200080020200202200241e0e12341a080606300a043e23f786b6000085218d800119b80001c38636030300000000010a078002000800200089dc05889fc0579094000800200089dc05b80020008f84000800200080020008002000800227b0002000800200080020038002277000200080020008004808c120d8f0c018b89880600108900118b808385948b7ca1aa80002108632000465200006fa18c80c0c0000000004281e000800200080022dd01622e5015e410000200080023e1005600080022dd00020008002000800200080020008b8400080020008002000800e0008b74000800200080020012023048363c30062e26201800422400462e020e16522dd02c40b102c483802cc0b102c40b11fb00b122300b502c40b1020c03002c4037007478c02c40b102c40b102c40b102c40b102c40b102c40000444800641860004464140000341c00042c008c522107e4000000100008301b106341a10000000200000241a2500001e500000000010136411c400000003180d300008c604140c7004040200020000140f0004001000400116000b116600af16000010004001212802b00040012080001000400100040010004001000458800040010004001000400700045800004001000400100090118241b1e18031713100c00211200231701070b291680020008002000889005888900578b30000800200089fc01580020008b9400080020008002000800200080022280002000800200080020038002224000200080020008004808c120d8f0c018b89880600108900118b808385948b59000010180020008002000877005888a00578b10000800200089ec00180020008b8400080020008002000800200080021dc00020008002000800200380021dc000200080020008004808c120d8f0c018b89880600108900118b808385948b40010004001000437002c444802bc580000400100044ee000c00100045ba00040010004001000400100040010ee000100040010004001001c0010dc00010004001000400240460906c78600c5c4c4030008448008c5c041c2ca45af80b1800000002980b400010a602da0a8008080400040000281f3c0ef0000000000012c0318000839c131008000000000000503c40127000000003100f800020dc03f40c4010100800080000503c000002c001000c0011490023024c0ad0004001000400100040110004001000400100040010004001000400100040010dc00010004001080016061a14110f090419000c00000b022011c440000400100005240004001001c001000400500040010004093000400100040010004001000400100040010dc0001000400100040010004006800000038602800640058002044482408844a002800200080020138122218000e000813600080020008002000800200080020008002000800200086e00008002000800200081068b080a0d07058d06828000810304000f88c000000400100fc001001c0910004370150000300040010f10001007c00100040010004005000409b000400100040010004001000400100040010004006840584800104864500824246424000410008c4e0008002000800200080020008002000801a0008002000800a00081560008136003800200086e0000800200080020008000060d000180008000030a000000090e886322188000000400023406ba19c865a000000080000090680122052814e048812e0488146000812204f812204881523b501220488ec40478122048812205081220008122048812204881220488122048870e00088100060c83058a010001050005031109498126464012e049813604c81260028ac42ad01260498126049812a049812604c81260448126003812604e812604981260498126049812604981260000d0f088e80088f0a800d0387050003040181079189daa000101dc031800000000f5034800023300c60320010100800080000503c380020018a5000080020008a4000f800200080020008002000800200380020028a700498a6000080020008a4000080020008002000800200080020488002290007e3d000020008002000908f0e8e108c8d8d0a80868b8786058810030010108001160bc3800200188700008002000886000f8002000800200080020008002003800200288600498878000800200088600008002000800200080020008002048800229c007e29e00020008002000908f0e8e108c8d8d0a80868b8786058810030010108001160bc3800200187800008002000878000f80020008002000800200080020038002002887004987d00008002000878000080020008002000800200080020488002294007e29a00020008002000908f0e8e108c8d8d0a80868b8786058810030010108001160bc380020018780000800200086e000f8002000800200080020008002003800200288600498788000800200086e000080020008002000800200080020488002290007e29200020008002000908f0e8e108c8d8d0a80868b8786058810030010108001160be1014c0000000059816400021560530154010100800080000503c340c4000000004a80f400020d803100c8010100800080000503c3810e043811e044810e030010e045810e043810e043810e043810e0438074046810e006010e0438008043810e043810e043810e043810e043810e322a22002a002c2e2a10001604020e000000244627c001000400100040150004001000400100040010dc000100040010004001002c0010004001000403900042c3820280028000c240c3c181000683b80020008002000801e0008002000800200080021b800020008002000800200580020008002000802200085870405000500018481878302000d07401b0004001000400100040010004001000400700040010004001000400100040090004001000408482c10103c141804140c0000603600080020028002003800200080020008002000801a041810a0028002000800200080021b8000200080020008002000800200081000b070084888c0d8c078282010b80000f88f00040010004001003c00100040010004001000437000040010004001000408100040010004001007c0010b0e080a000a000309030f0604001a0e8000000803e000800200a800200080460008002000800200080020058002000800200086e00008002000800222280614001000041a020e0c1200341d000400000040010004027000400100040010004001001c001000400100040010dc0001000400100040010004301c140c0000000834400c04282c683a00000020038002000800200080fe00080020008002000800221400020008002000800200080021b80002000800200089808007800808000007058084030a0e07e36000463600000000001000005048c6400000006078d0001000063401000004038c6031800000000000000002824000000400700040010004001009c0010004001000400100043700004001000400100040010004370000400100040011301000f00101000000e0b010806141c0fa600000004000000001013180c600000000002000200000a09880620000000000100010000050480000038760000800200080020008002000876800086e000080020008a2800186e0000800200080020008002000800200086e00008a20000800200080020008002002e002000260c2a004a3a000000003c001618384c2900040010044001000c0010004001000400100040010004023002c001000400100040010dc00010004001101702130012000a0c01010d00001a0e8c6800000006078c0001000063001000004038c37000040030004001000400100440010004001000400100040010004370002c001000400100040010004001000400005418004814004c380814441800703e9800040000a60040000100f1800080000c60080000201e200010000188010000040380020000002000800203e800200080020008002000800e0008002000800200086e0000800200080020008002180e0a06000000041a2006021416341da9000100006340100000403c603180d100000002000200000a090004001000400110a00010004001000c001000400100040010004000000400710a00010004001000400110a00010004001000400001070005c080000003c6400400c487842000800200080021b8000200080020018002000800200080020008000000800e2140002000800200080021b8000200080020008000020e000b81000000078c800801890f0853014c06040000002000200000a0988000000106201a800000000000000001c1b1b000031b000046e000200000000000c0b0d40008c640000000000200000a090e4000203ed063418d00000004000c00001413180c6036c0000000800080000282400100040000004001000400100040030004001000400100040011340001001c4d00004001000400100044d00004001000400100000418000f020000000a16001503021e10800200080000008002000800200080060008002000800200080021b8000200389a00008002000800200086e00008002000800200000830001e04000000142c002a06043c214c053015c0000000800080000282418c09000000000000000001413100c4000200000000e800000000800003834000001c37000040010004001000400100043ac00044e2000400100044cc000c370000400100040010004001000400100044120004370000400100040010004001001700100013061500251d000000001e000b0c1c2614800000386e000080020008002000800200086e000086e000080020008b680018afc000800200080020008002000800200088400008950000800200080020008002002e002000260c2a004a3a000000003c001618384c290004001000000100040010004001000c00100040010004001000437000040070dc0001000400100040010dc00010004001000400001060003c08000000285800540c087842000000e1c800020008002000800200080021d300021b8000200080021b800061b80002000800200080020008002000800220c0002260000200080020008002000800b80080009830a80128e800000000f0005860e130a6e0000800200080020008002001800200380021b80002000800200080020008002000800200080021b80002000800200080020426281c282218142e2a0a0002040c0a003e23b80002000800200080020008002000800e0018002000800200080021b8000200080020008002000800200086e0000800200081098a070a0806028c0289800a820081000f88c000001c398000400100040010004001000437000043700004001000450c000c5760004001000400100040010004001000437000044b0000400100040010004001001700100013061500251d000000001e000b0c1c26148000003871000080020008002000800200086e00008944000800200086e000186e0000800200080020008002000800200088100008940000800200080020008002002e002000260c2a004a3a000000003c001618384c2900000070e000010004001000400100040010dc0001122800100040010dc000312f8001000400100040010004001000400110000010dc0001000400100040010004005c0040004c18540094740000000078002c30709852000000e1bc00020008002000800200080021b80002249000200080021b8000626f000200080020008002000800200080021b8000224c000200080020008002000800b80080009830a80128e800000000f0005860e130a63018c0000000063018c000118c063018c008080400040000281e000000e1b800020008002000800200080021b800021b8000200080021b800061b8000200080020008002000800200080021b800021b8000200080020008002000800b80080009830a80128e800000000f0005860e130a53014c0000000053014c000214c053014c010100800080000503e201880000000062018800041880620188020201000100000a07fb0014005001400500140f900140050014080420101000142c1e4c093000009d00001ad0104093024c1e1024c093024c093024c0418080018080000003c27f80000098026009802600980260098026009830180820002828583c24000407b600003b60ed83b60ee83b60ae83be00503b60ed83b60ed83b6140e140008020208001e135f000101e816600000000588162058806e058816205881620588162120e00000a000a00061c1305000101c60002034000406ba00000700ab82ae0ab82560ab82e20ab82ae0ab82ae0ab82ae0e08040006100004001e137a0002031000101ca00580000008000000807e0008002049810e0008002000813e120c1200060000000c1e13d700001d7075c1d7075c1d7075c15d075c1d707641d700081d70c0a020900080605050f099802600e802600e8026009802600980fe0098026009802614160c0804000a0a001e13fc000004c000004c013000c013004c013004c013004c013004c01309040007000000060001100aad800002182b60e980860e7839202e03720ad82b601680000ea82b60ad82b60ad82b60ad8007000480040301800000000a8656c000010c15b0744043073c1c901601b1056c15b0734000072c15b056c15b056c15b056c003800240020180c000000005433f41c7000c003000c00307140a700f4003070c003000c003000700000b000700040f098580fe0098026009802600980260098026009802600000808001000001a113004c013004c013004c013004c07f004c1c1c1c040014002c1e06080020008002000800200080028000030004836fc0010704001000400100040010004001414000000281a07d80020008002000800203f8002000838301818180000583cac000407f80fe00c00fe03f80fe049037a03f80fe03f80a003f80fe03f800003f80fe03f80fe03f80fe0e000a12040412100a060000002e1bbb000101bc000407f80fe03f80fe03f80fe03f809004500fe03f80fe03f80fe03f80fe03f80fe00080200080c0c0200060026174904dc001000400100040af00040010004191060007030104020c07cb04dc000000003f00000010004001000400100040010604020002000100000d09826e00080020008002000810e000800300010080050341370004001000400100040010005000006000906bc02f00bc02f00bc02f00bc041400000020176e003800e057828e0dc8372000000e0038366003836a0d7800e003800e003800e0002002000000a06000402002819b7001c00702bc14706c41b10000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c800000083560008002000835a01f800a000800200080020008000e000014001c110014001000400100040010004001410000000241a01f8002000800200080020008002800001800483500040000004001000400100040010004000400140000281bc00f003c00f003c00f003c041400000020174e008000000001ce09b810e0078002000800200080020008002000408000a060000021e1330000013004c0a3004c01301fc013004c0130424013004c0130c00090009010301000f099b800200080020438002002800200080020628480030003820080010704ea40b100040000004001000400100040010005000000000a06af02c40010000001000400100040010004001400000000281b4e058800200000020008002000800200080028000000005036500040000004000000403f0004001024c087000400100041a50906090003000000060f09d1800080c065027c001024c0c9031c03f000400100040010004001021c001020f000b010401020500110a80020008002000000007d80fe00080020008002000800000050000000006847d80fe000800200080020008002000800200000208000400001811940010000001000000100fc0010004093021c0010004001027c241824000c000000183c27c1a1003c00f003c00f003c00f0005030000000906f067c00f003c00f003c00f003c001400000000241bf81f207c803407d80fe07c803000000fe03f80fe03f80fe03f80fe03f80fe03f87888280008001800203000985ff01fc07f01fc0f901fc07f01fc0f901fc07f03e407f0a0a070005050107000f09f066c00f003c00f039c05f01ac00f000006b065c19d01ac199003c00f003c00f003c18f0000001100001104000d0101150cf000101b000101fe000203b000101e000203ce008000000000000c9832a0c8831e00000000020000120f9206481920c681920648266064819206481920e0a0004020202180f6005801600580160058016020a000000100b8a000018a062818a062818a062818a0006000e0000120d100440110044011004401101050000000805c5815a056815a056815a056815a05680008082000005036581960658196000019606581960658196000e00000000140df007c01f007c01f007c01f010500000008059605480960258096025809602581028000000004834b000101bf00000cb02fc0bf02fc0bf02fc0bf0003000700000906bf000101ba82ea0ba82ea0ba82ea0ba82ea0c082ea000030e0ba82de0ba82ea0b583120ba82ea0ba8000800980000607800002000a864c830a04480000c0830604481120448112044811204482fe0448112044811204481120448000820480018001800000000a86438000043810e023010e0ba810e043810e044810e043810e043810e0bc810e043811a1200082000021c0e0c0c0c28170e06a82ea04202fa04380ec046819a043810e0370112043810e043810e043810e043810e043810e04388070608800402010000800081800c8743800004680f400002f6043810e043810e043810e0ba8112043810e0438108043810e043810e043880703008180038000018000810b86c3810e013011a01b02f2043810e066810e0ba810e044810e043810e043810e043810e043810e0e280800020216000c040002002e1b1a013010e043810e066810e043810e04382ea044810e043810e037010e043810e043810e0c1404180600180000060002042e1b0e04382ee03d010e0ba819a046810e043810e043810e043810e023011201b010e04380ec043810e043810e0438a86008388058008880301800586010d87c38000000000004381120ba810e043810e043811a043810e043810e043810e043800082848000008180000380098643800080cc000406bc0af05c40af02bc01d02bc0af02bc04302bc02c02bc0af02bc0af01900af02bc0af02bc1800003828340c0400080010085c36e20b882e20b882e20b882e20b982e201c02e20b882e20b8800c0b882e20b882e20b8801c0b882e20b882e22412002c00021c0a0e0610021400341d00010180020008002000800200080828000000402d48152054814602d02de0b58152054815209f80bc054815205482da05481520548152054815205489000a8186048002820201000200020d07c0050234001000400105a4001000416700040010004001000400100040010188181c140020000814140c0c502e002811a000800200082d200080020b3800200080020008002000800200080540c0e0a001000040a0a06062817f207c81f207c81f207c82800000000382ff81fe07f81fe07f81fe0a000000000e0b0400007f404107ec041078c04101040410009060301000a0686057815e057815e057815e0b8815e000000080008140df707dc00007e41f907dc1f907e41f907e410100c000000002c1fea0f880000f983e60f883e60f983e60f9820201800000000583fbc000010c1cf010c1ed010c1eb010c043010c18000000100c082c1ee2000000009582560e78256095825609582560a0a0800000000160f7105c400005c417105c417105c417105c417105c4081c0024041404301ee200002560958256095825609582560e780028000000205037a400007641d907641d907641d907641cf0005000000040a06fe03f80fe03f80fe03f82800000000382e3c1e5079c000000000000504f180000f183c60f183c60f183c60f183c60f183c60e0a0200000606180f01
def segMetadataE : Nat := 0x354ed506d3f8d42b479d846d0a514273ab77ddcc98e1532a867ddc907d99f1c6a7b5c51160970dde667c166a112fcff89bbdfd9426efb0846b9ecdff6df6d846b6991426d220844b2939f4ac3e7667aed6e232b2878d4aab59ec6a3237b3a6d51f3e93857cfa49ac46a915111aa40dc46a8e601d7a245552e86d4241a07553fe81040d1a03280ea808f03ba01c8076800506d9fe481ce7ef609c9fa9c13e7e5804f9f7e417e7db30469f23049e7c1c0709eecc1a67b400739eafc2067a7004f9e85416e79a20739e54c13e790e0459e26c1ce781f07c9d4c8bb674840ae9c630be270de0ae9bbdc79e6eb60419a6a543667ce1db99dfc13e624453b981cc7465e3423f9773c1965be61e995b6543651a05399324d4364a961fd9236c6ee46ac22f905cd4e63c744ff8ddd53fe354e2278cdf074a2e3154b8b17075626d9583887693fe1f232b7874b87d61b731bb862c4b0a161629b84fbc89e115a29583d847e60a624ff81ec0aca05b81f880f0c7d6014727c7fc1c901fcd822f7ea5c905f7523457d4a08a9f2b926f7c24889dee5523d7b0a88adeb131177a1a8aa5e64022a78cdcc25e0f42437761cdb5db842037660480dd76421d7557481dd33e21f745247d5cf0a23f733c4865caee203723dc7ddc6f42037129c935c21a28d6fc6cbfdbcf42276eb148bdb8642616d9bc7d5b3ea2856c744865afdc1f56b354c1da9e42f169e30961a565227689d0bc5a06920b67654b51982057565150f3192991bb643786ed8ed320b634606ed8b5d1bb623ec98986182e360c0cc557fd832b5f6808e17b5624a5e4bc89d78ee0415dad88e176940225ce8cbc570b22f15b92c99d6c322195a594b3566f626f5938c84d63cb11858bec34162890725858c499611504e5831c139604608157fe01395fb304557df00dd5dc01bc573c03415c7e072570d81215a7a1bc56588461573322f554a082d52d5253547e43714fbc23d537507a14cbc11852fb433d4ba704652d7012d4b2203a52afc18d49041bb521c025147d309d51d881c5463d1255178816d45120d051108341432b1175085045d41c704d505e81354135045503601753fbb11d4f4d8a153cda05c4f1fc16d3c2405b4e9a46ed376a2ff4d66474533722274c174c552e5220b4ad84bc5296c1f549d1489d25741d148c0c9c5228407f47e38bd91c8030e46590c71173822c454348ad130220b443a486510a40454417c115101a0454388c7dd0dde045436641150d5404541ec169104b82f840310fd0fea02243f8b81c8fbf123d3e640984f9090873dbc0864f4cf2213cc886b4f2990893c1a88bcee432273b0188f4ea081fe3a0387e8e5f121d38ed08f4e18522f382d0344dddf2d537438344da392d535f4899cd7160bc35af8160d5ed0d134c60b54d0432d53408008ccd4b2d5329d8b54c9a60d03235c33cc8070d0316f092cc35a262304ac8bcbea62852f26c82cbbe00bb2e5ec994b6ef28c2db3008cb5fb0d12cb7cc70afc331c2b29cc70a98b31c2a2ec340a7eb0d0295b49f8a39a1d32871c74ca01a1ad277ac8bc9c181d3268e477c985a1df2595c80c95e4073256b40dc955005d2539c1a492e420324a38158921d071246b01c48ef52b7234907448ced037232401748a961fa228e817089df05b2261016c87a51df21d2017486d5073212b889c8287227208541c8818608f203f42248089074201940907ff20731fdfc1cc7d582271ecc489c7abf0721e9581a479c708f1dc40adc74592b71c8c889c6f7b2b71b5448a86b2722a1a1c0adc65b92b718c08adc604b2b717de83445cc32b716fcc3405b240cf1695833859321241615c36c583602115c4449456f00211577444c55bc0211567407c558201b15174494543d0201508007452fd1231476049450c511313e304e44dfb191131a86444b54116129843cc49960cb123cc28c483a0b911dcc31c4752021116b4694458c021115b8078441115d10cd0374422c108105ec2c440d80a3101182483ed11750f5705d43c551070eec828c3b0f0a30e93830439be0900e26449437781210da2c3b435c40c70d3f831834370c70cc5048c32f30210c7004cc30c70f90bfc43582ece1230b8a02982d820a60b05c5ac2b101070a610630296801c0a530070292d01f0a44007428f501b0a0d430027590dc09b2424026110b80960024424c70b909004318237009108b1c2a422a801f087c02e021d0020080fc6441eaf190074d45e81b6b1ca066dc6d018111a6059e4660148b1ee04c5c5d012f702004b68074114219803da47640f5001903b0c2340cff1c402e685940a35165026bc21809290860219031407ad0b701b7833c060f0cf014c837404550dd00da83ac02a30c70077031c0157085003d018c00090eb000000240000000
def segIndicesE : Nat := 0x1c8e3f1b8bc4e1f0b83c0dfefb7bbcddeeb73b8dbedb6bb4d9ecb63b0d7ebb5bacd5eab53a8d3e9b4ba4d1e8829a10a6833f9ecee73379acce5b3197c9e4f2596c9e572592ca64b2792c8e431f8ec6e31238bc56271187c36170983c1607017fbf5f6f97bbd5e6f177bb5d6e973b95c2e370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9a01a652e9549a451e8d45a250e8541a04fe7d3d9e4ee75399c4de6d359a4ce6531984be5d2d964ae55299449e4d259248e443190c823f1e8ec72371b8d46630148bc5a2b1489852248f88c41230f8723e1a148642e141484c220f067d41609037d40a02fb7e3edf614803fc28fe18851fafc7dbe9f4f97c3ddecf57a3cde4f16f3c1b8da77bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a28d6833d9ccd6632d22ca64b218ec662b1186c260b017ebe5eaf176ba5cae16eb65aad166b258a3560af572b558ab552a550a75329548a35124542a04fa793a9c4d805349900a612e964aa51269200a45208f47235188b00a29128843a190a8441a090280009fcfc7d3e1ecf4793c1dcec753a1cce471381bcdc0100990c86d0080428610a1b0d6013504cc801009a45e0100850d0010a13428670a0507e0133194aa640098c5e14008509a6230850c0010097cbc5d2c170b65a2c96026572b04caa1309850a8140a14c28140a0505e140a05062140a050a41717050282e0a05028140a0c860140a050a2140a1409e4e261349a4c098047e3f008fc7e131492c94492411c8c461c0e08c13098988a452291426130984c26130984c26130984c88432110456401f8f8263d0984c26130984c26011e0e076131d0e470130984c26130984c26130984c26131b84c6c351a05026331805062140b85002140a05028140a05028141885064170a00428140a05028010985028140b85002140a05028140a05062140a0502e140a050600100804020117850282e1684c2613160ac54291409c4c251208c4418108803e180f0603a1c0d86832180c0602e160a84c281309044200f07034180b050281204020200e06028140803010080201008040201
def segE (i : Nat) : Nat :=
  let j := (segIndicesE >>> (9*i)) &&& 511
  let m := (segMetadataE >>> (30*j)) &&& 1073741823
  (segPayloadE >>> (m >>> 12)) &&& (2^(m &&& 4095)-1)

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 19
  | 7 => 292
  | 8 => 365
  | 9 => 26
  | 10 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 25
  | 8 => 317
  | 9 => 682
  | 10 => 708
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+14*((h/a+d) % b))) &&& 16383

def rotateE (g : Nat) (ws : List Nat) := if g = 0 then ws else if g = 1 then setA ws else if g = 2 then setB ws else setA (setB ws)

lemma rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 232) (goal 232) s ws) : NatRun (mask 232) (goal 232) s (rotateE g ws) := by
  unfold rotateE

  split
  · exact h
  · split
    · exact runA h
    · split
      · exact runB h
      · exact runA (runB h)

def Z (s : Nat) := barrier 232 stateE nsE actionE sixE rotateE s

lemma h0y0 : span (Z 0) 1 0 = true := by decide +kernel

lemma z0 : span (Z 0) 1 0 = true := h0y0

lemma h1y0 : span (Z 1) 1 0 = true := by decide +kernel

lemma z1 : span (Z 1) 1 0 = true := h1y0

lemma h2y0 : span (Z 2) 1 0 = true := by decide +kernel

lemma z2 : span (Z 2) 1 0 = true := h2y0

lemma h3y0 : span (Z 3) 1 0 = true := by decide +kernel

lemma z3 : span (Z 3) 1 0 = true := h3y0

lemma h4y0 : span (Z 4) 1 0 = true := by decide +kernel

lemma z4 : span (Z 4) 1 0 = true := h4y0

lemma h5y0 : span (Z 5) 1 0 = true := by decide +kernel

lemma z5 : span (Z 5) 1 0 = true := h5y0

lemma h6y0 : span (Z 6) 10 0 = true := by decide +kernel

lemma h6y1 : span (Z 6) 9 10 = true := by decide +kernel

lemma z6 : span (Z 6) 19 0 = true := (@span_join (Z 6) 10 0 9 h6y0 h6y1)

lemma h7y0 : span (Z 7) 10 0 = true := by decide +kernel

lemma h7y1 : span (Z 7) 10 10 = true := by decide +kernel

lemma h7y2 : span (Z 7) 10 20 = true := by decide +kernel

lemma h7y3 : span (Z 7) 10 30 = true := by decide +kernel

lemma h7y4 : span (Z 7) 10 40 = true := by decide +kernel

lemma h7y5 : span (Z 7) 10 50 = true := by decide +kernel

lemma h7y6 : span (Z 7) 10 60 = true := by decide +kernel

lemma h7y7 : span (Z 7) 10 70 = true := by decide +kernel

lemma h7y8 : span (Z 7) 10 80 = true := by decide +kernel

lemma h7y9 : span (Z 7) 10 90 = true := by decide +kernel

lemma h7y10 : span (Z 7) 10 100 = true := by decide +kernel

lemma h7y11 : span (Z 7) 10 110 = true := by decide +kernel

lemma h7y12 : span (Z 7) 10 120 = true := by decide +kernel

lemma h7y13 : span (Z 7) 10 130 = true := by decide +kernel

lemma h7y14 : span (Z 7) 10 140 = true := by decide +kernel

lemma h7y15 : span (Z 7) 10 150 = true := by decide +kernel

lemma h7y16 : span (Z 7) 10 160 = true := by decide +kernel

lemma h7y17 : span (Z 7) 10 170 = true := by decide +kernel

lemma h7y18 : span (Z 7) 10 180 = true := by decide +kernel

lemma h7y19 : span (Z 7) 10 190 = true := by decide +kernel

lemma h7y20 : span (Z 7) 10 200 = true := by decide +kernel

lemma h7y21 : span (Z 7) 10 210 = true := by decide +kernel

lemma h7y22 : span (Z 7) 10 220 = true := by decide +kernel

lemma h7y23 : span (Z 7) 10 230 = true := by decide +kernel

lemma h7y24 : span (Z 7) 10 240 = true := by decide +kernel

lemma h7y25 : span (Z 7) 10 250 = true := by decide +kernel

lemma h7y26 : span (Z 7) 10 260 = true := by decide +kernel

lemma h7y27 : span (Z 7) 10 270 = true := by decide +kernel

lemma h7y28 : span (Z 7) 10 280 = true := by decide +kernel

lemma h7y29 : span (Z 7) 2 290 = true := by decide +kernel

lemma z7 : span (Z 7) 292 0 = true := (@span_join (Z 7) 160 0 132 (@span_join (Z 7) 80 0 80 (@span_join (Z 7) 40 0 40 (@span_join (Z 7) 20 0 20 (@span_join (Z 7) 10 0 10 h7y0 h7y1) (@span_join (Z 7) 10 20 10 h7y2 h7y3)) (@span_join (Z 7) 20 40 20 (@span_join (Z 7) 10 40 10 h7y4 h7y5) (@span_join (Z 7) 10 60 10 h7y6 h7y7))) (@span_join (Z 7) 40 80 40 (@span_join (Z 7) 20 80 20 (@span_join (Z 7) 10 80 10 h7y8 h7y9) (@span_join (Z 7) 10 100 10 h7y10 h7y11)) (@span_join (Z 7) 20 120 20 (@span_join (Z 7) 10 120 10 h7y12 h7y13) (@span_join (Z 7) 10 140 10 h7y14 h7y15)))) (@span_join (Z 7) 80 160 52 (@span_join (Z 7) 40 160 40 (@span_join (Z 7) 20 160 20 (@span_join (Z 7) 10 160 10 h7y16 h7y17) (@span_join (Z 7) 10 180 10 h7y18 h7y19)) (@span_join (Z 7) 20 200 20 (@span_join (Z 7) 10 200 10 h7y20 h7y21) (@span_join (Z 7) 10 220 10 h7y22 h7y23))) (@span_join (Z 7) 40 240 12 (@span_join (Z 7) 20 240 20 (@span_join (Z 7) 10 240 10 h7y24 h7y25) (@span_join (Z 7) 10 260 10 h7y26 h7y27)) (@span_join (Z 7) 10 280 2 h7y28 h7y29))))

lemma h8y0 : span (Z 8) 10 0 = true := by decide +kernel

lemma h8y1 : span (Z 8) 10 10 = true := by decide +kernel

lemma h8y2 : span (Z 8) 10 20 = true := by decide +kernel

lemma h8y3 : span (Z 8) 10 30 = true := by decide +kernel

lemma h8y4 : span (Z 8) 10 40 = true := by decide +kernel

lemma h8y5 : span (Z 8) 10 50 = true := by decide +kernel

lemma h8y6 : span (Z 8) 10 60 = true := by decide +kernel

lemma h8y7 : span (Z 8) 10 70 = true := by decide +kernel

lemma h8y8 : span (Z 8) 10 80 = true := by decide +kernel

lemma h8y9 : span (Z 8) 10 90 = true := by decide +kernel

lemma h8y10 : span (Z 8) 10 100 = true := by decide +kernel

lemma h8y11 : span (Z 8) 10 110 = true := by decide +kernel

lemma h8y12 : span (Z 8) 10 120 = true := by decide +kernel

lemma h8y13 : span (Z 8) 10 130 = true := by decide +kernel

lemma h8y14 : span (Z 8) 10 140 = true := by decide +kernel

lemma h8y15 : span (Z 8) 10 150 = true := by decide +kernel

lemma h8y16 : span (Z 8) 10 160 = true := by decide +kernel

lemma h8y17 : span (Z 8) 10 170 = true := by decide +kernel

lemma h8y18 : span (Z 8) 10 180 = true := by decide +kernel

lemma h8y19 : span (Z 8) 10 190 = true := by decide +kernel

lemma h8y20 : span (Z 8) 10 200 = true := by decide +kernel

lemma h8y21 : span (Z 8) 10 210 = true := by decide +kernel

lemma h8y22 : span (Z 8) 10 220 = true := by decide +kernel

lemma h8y23 : span (Z 8) 10 230 = true := by decide +kernel

lemma h8y24 : span (Z 8) 10 240 = true := by decide +kernel

lemma h8y25 : span (Z 8) 10 250 = true := by decide +kernel

lemma h8y26 : span (Z 8) 10 260 = true := by decide +kernel

lemma h8y27 : span (Z 8) 10 270 = true := by decide +kernel

lemma h8y28 : span (Z 8) 10 280 = true := by decide +kernel

lemma h8y29 : span (Z 8) 10 290 = true := by decide +kernel

lemma h8y30 : span (Z 8) 10 300 = true := by decide +kernel

lemma h8y31 : span (Z 8) 10 310 = true := by decide +kernel

lemma h8y32 : span (Z 8) 10 320 = true := by decide +kernel

lemma h8y33 : span (Z 8) 10 330 = true := by decide +kernel

lemma h8y34 : span (Z 8) 10 340 = true := by decide +kernel

lemma h8y35 : span (Z 8) 10 350 = true := by decide +kernel

lemma h8y36 : span (Z 8) 5 360 = true := by decide +kernel

lemma z8 : span (Z 8) 365 0 = true := (@span_join (Z 8) 320 0 45 (@span_join (Z 8) 160 0 160 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 (@span_join (Z 8) 10 0 10 h8y0 h8y1) (@span_join (Z 8) 10 20 10 h8y2 h8y3)) (@span_join (Z 8) 20 40 20 (@span_join (Z 8) 10 40 10 h8y4 h8y5) (@span_join (Z 8) 10 60 10 h8y6 h8y7))) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 (@span_join (Z 8) 10 80 10 h8y8 h8y9) (@span_join (Z 8) 10 100 10 h8y10 h8y11)) (@span_join (Z 8) 20 120 20 (@span_join (Z 8) 10 120 10 h8y12 h8y13) (@span_join (Z 8) 10 140 10 h8y14 h8y15)))) (@span_join (Z 8) 80 160 80 (@span_join (Z 8) 40 160 40 (@span_join (Z 8) 20 160 20 (@span_join (Z 8) 10 160 10 h8y16 h8y17) (@span_join (Z 8) 10 180 10 h8y18 h8y19)) (@span_join (Z 8) 20 200 20 (@span_join (Z 8) 10 200 10 h8y20 h8y21) (@span_join (Z 8) 10 220 10 h8y22 h8y23))) (@span_join (Z 8) 40 240 40 (@span_join (Z 8) 20 240 20 (@span_join (Z 8) 10 240 10 h8y24 h8y25) (@span_join (Z 8) 10 260 10 h8y26 h8y27)) (@span_join (Z 8) 20 280 20 (@span_join (Z 8) 10 280 10 h8y28 h8y29) (@span_join (Z 8) 10 300 10 h8y30 h8y31))))) (@span_join (Z 8) 40 320 5 (@span_join (Z 8) 20 320 20 (@span_join (Z 8) 10 320 10 h8y32 h8y33) (@span_join (Z 8) 10 340 10 h8y34 h8y35)) h8y36))

lemma h9y0 : span (Z 9) 10 0 = true := by decide +kernel

lemma h9y1 : span (Z 9) 10 10 = true := by decide +kernel

lemma h9y2 : span (Z 9) 6 20 = true := by decide +kernel

lemma z9 : span (Z 9) 26 0 = true := (@span_join (Z 9) 20 0 6 (@span_join (Z 9) 10 0 10 h9y0 h9y1) h9y2)

lemma h10y0 : span (Z 10) 1 0 = true := by decide +kernel

lemma z10 : span (Z 10) 1 0 = true := h10y0

lemma checkedE (s : Nat) (hs : s ≤ 10) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

lemma noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False := by
  have h10 : NatRun (mask 232) (goal 232) 10 xs517 := extend_run h hs
  have p : xs517.Perm (stateE 10 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 10 (by decide) 0 (by decide) (Run.perm p h10)


lemma noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False := by
  by_cases eq : ws = xs517
  · subst ws
    exact noRunFull _ hs h
  · exact proper_fail517 _ (List.mem_sublists.2 hsub) eq (required h)

end Theta

def pos0 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cb70ca41b4174c6b5c8dc87531b7a7a7a5074cd8a3e7ab966b5620c41cd99c659b5a7f5391beb8f399eb78a62dc8d4ea48db9593e7aec79a7c8b9b766e71b7a74f5ecdcc88f3e1b4141418a74b9505341cd0cec62667ab940f59beca7c6921beb87925db75062c89689e796cd9b5341b579a7dccdb7cddca741e29253e7a49bb5a77a7a7a50e20c8aec7a66b953f0cd410ccc928f531b39f5a7e359f5f4b78af0a49fdbdc9f668fec7a3ee41be766b7b9c8a77ae2393ea4e759eca74141418ae26650b5410ccd3ef0b97a66fa39873e1b92c6a7e39bc6f9b750f0e760f2c8600c87b54153e41ba40c

def neg0 : Nat := 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a51d000e00000eafaf3ca338a54e90779706a54e970505a39003060202a3970b06071d90030e0b653805a53c054e074e0b03af363c38e807a5a5a51d000e00000eafaf51e84ea538361a0306a538030505e83697066c6ce8030b06071d36970e0b654e05a551053807380b97af90514ea307a5a5a51d00af0000af0e0e774ee8a5a3363c0307a5a3030b0b4e36970744444e030507061d3697af0558e80ba5770ba306a305970e9077e83806a5a5a51d00af0000af0e0e1a38a3a5e890519707a5e8970b0b389003072c2c38970507061d9003af0558a30ba51a0be806e805030e361aa34e06a5a5a5

def pos3 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c360c3900664ec837c687dc6400cdcdcd724e7ad9a2cdb94137e50c667a91c8e7372a9ba4005d92a4f936d9e587de7439deb9e7a2cd574f2ac6b936415900cd4e9b5787c692a200666666d94eb97264667a0c57e541cdb9a69bf5572ac88f005ddc8feb3672e5c694db59947af56466374f2a877a367a872a66f28f645939f5372acdcdcd72f20cd957cd41b9645b7a660cca8f926400a49b2af4e79be336d95b39f78987f7419257cda2f300594136b9c62acdf2a4a23959e7572a666666d9f2417237660c7aa25bb9cd419da4dca2008fc82af4f5c89e36725b59e9e2c6e90cdc376664f300390c

def neg3 : Nat := 0x36363636363636363636363636363636363636360100020000022c2ca238a33665904d910a3665910b0b3890090a0e0e3891050a0401900902054ea30b36a20b65046505092ca5a2a358043636360100020000022c2c64586536a3a518090a36a3090b0b58a5910a44445809050a0401a59102054e650b36640ba304a305912c906465380436363601002c00002c02024d65583638a5a20904363809050565a591046c6c65090b040a01a5912c0be85805364d05380a380b9102904d58a30a36363601002c00002c020218a3383658906491043658910505a3900904afafa3910b040a0190092c0be83805361805580a580b0902a51838650a363636

def pos5 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c890c39660029c687c837b57266a7a7a764292aece7a7b91b87e90c002a78c6a2877a3ba4664019a4b889ece937f01839f0b9a2e7a78a797ac8b9891b3e66a7293b8a37c819e766000000ec29b96472002a0c8ae91ba7b9eb3bb38a7ac6276640b527a68964e9c875b73e752ab3720087797a372a892a377a00c527723e39b3877aa7a7a764c50cec8aa71bb9728d2a000cf427197266a43b7acaa23bcc89ec8d39ee3637ee1b198aa7e7f3663e1b89b9c87aa7c5a4e7393ea28a7a000000ecc51b6487000c2ae78db9a71b8ca4b5e76627c67acab3c63d89648d3ee5cbc8e50cb5870072f366390c

def neg5 : Nat := 0x38383838383838383838383838383838383838386c000e00000e2c2ce836a538181977750a381875090936190b0a02023675030a076c190b0e031aa50938e809180718030b2ca3e8a53c073838386c000e00000e2c2c643c1838a5a3650b0a38a50b09093ca3750a1d1d3c0b030a076ca3750e031a1809386409a507a503752c19641836073838386c002c00002c0e0e77183c3836a3e80b0738360b030318a375070101180b09070a6ca3752c09a23c03387703360a3609750e19773ca50a3838386c002c00002c0e0e65a536383c19647507383c750303a5190b07afafa57509070a6c190b2c09a236033865033c0a3c090b0ea36536180a383838

def pos6 : Nat := 0xdb00a2412a18b3d9b5c62759411b1b1b5718b953501ba70cd960002ab95db33bd9cdc81941a6371940db5360c65536a255a73b501bdc4fcdb5a7db0ca4411b18c8dcc6b53750412a2a2a5318a757592ab900dc600c1ba752c83edccdb33941a627393ddb5760b55b29a45bb93e592ad94fcdc6b9dbb9c6cd2acb3959a4a23ed9cd1b1b1b57cb0053dc1b0ca759deb92a00e13937594119c8cdcc3bc8b8db53dea262c5c6620c37dc1b50e441a40cdba7b5cd1bcb1950a2a43bdccd2a2a2a53cb0c57d92a00b950dea71b0ce31927504139b3cdcc3eb3cadb57dea45eb7b55e0027d92a59e441a200

def neg6 : Nat := 0xa3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3440002000002afaf51a21aa336384e0506a336050303a23852060101a2050906044438520209181a03a351033604360952af19511aa504a3a3a3440002000002afaf58a536a31a194d5206a31a520303a51905060e0ea5520906044419050209183603a358031a041a0905af385836a204a3a3a34400af0000af02024e36a5a3a219515204a3a2520909361905042c2c3652030406441905af033ca509a34e09a206a2030502384ea51a06a3a3a34400af0000af02024d1aa2a3a538580504a3a50509091a3852041d1d1a05030406443852af033ca209a34d09a506a5035202194da23606a3a3a3

def symKeys : Fin 8 → Nat := ![
  0xfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100,
  0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a,
  0xa19d9e9fa09b9ce3e4e25c5b5f5e58575d61605a596263f3f4f28c868d8e8788898a8b7e7f7c7b827d84858180837acac5ccc6c7c8c9cbbdbebbbac0bcc3c4bfc2c1b93d3638373c3b2f302d2c322e343531332b2a40393a3e3ffbf7f8f9faf5f698919a95949796908f999392dedfe1d9dadbdcdde0d1d2ced4d0cfd7d8d3d6d5cd4f524d55564e51504647434945444b4c484a42415354e5e6eae9efeeebf1f0e8e7edec757664657873727974776a6b686e6970716d6c6f6766a6a2a3b8b4b3a4a5b6b5b7abaca9aeaab1b2adb0afa8a718191a05060308040a0b070901020027282911120f1410161713150d0e0c20211e231f252622241c1d1b,
  0x9891f996978f90eb7974e6e576756564f48e8d8887f1f04f5d4e524d6061595adb50514c484342494b454647444a41a61840393aa4a52917130f0d1416101112150e0c3d36a3a21a190b070302080a040506090100ccc6c7b6b59a95949e999392a19dfbf7f8a09f9c9bfaf5f6eae978737289e8e777716d686e706c696a6b6f6766f38c86efeef28b8a85817c8284807d7e7f837b7aedec5b5cdedf5556e36263dcdd53545e5f5758e1d9dae4e2e0d8d3ced4d7d0d1d2cfd6d5cdca3738b82728c8c93e3fb726221e23251f2021241c1d1bc53b3c35312d32342e2f30332b2c2ab4b3cbc4bfbbc0c3bcbdbec2bac1b9b2ada9aeb1aaabacb0afa8a7,
  0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441,
  0x9a78b855562728a64f18e9ea94957273ca5b5c3738dfde794029997762633e3fb75354241f201c2325221e211d261beb745d3a39a5a44e1510110e1416130f12170d0c9e89e7e892936f696a676e706d686b716c66e3c8c9dddc9875763d52191aa18cfbeeef5e5f3b3ce1b3b4e5e691646536a2a34d090405080a010703060b0200f39d86f8f7c55758332e2f32342b312d30352c2adad98e8df0f19697cc6061b5b65051a09f8b8afaecede4cbe0b0aaabaeb1ada9aca8b2afa7f48887f98f90c6c7595adb4a4546494b4843474c424441f29c9b837d7e8284817c7f85807b7af6f5e2c2bcbdc0c3bfbbbec4bac1b9d6d0d1d4d7d3ced2d8d5cfcd,
  0xfbe1b8efeeb4b3caf3c5dfdef8f7dad9a6e5e6a2a3e9eae4cccbfae0f1f0b6b5b7edecb0b1b2afaeaaaca9ada8aba7e3e2f4c7c6c9c8f2c2c3c4c1c0bcbebbbfbdbab9f9dbdddcf6f5d6d7d8d5d4d0d2ced3d1cfcdeba4a5e7e8a15e5f3d8c3b3c98529a56557576191a7828275b5c9d575836373886333435322e2b302d312f2c2a4f914d9495186465090a0b0804010603070502007273616063629fa0408d8e3f3e8a8b97965150995453792977242526231f211e221d201c1b5d5a599e9b9c393a878889838485827d7f7c817e7b807a4e908f4a4b4c4945474348464442419293741516171410120f13110d0e0c6f70716e696b686d6a676c66,
  0x98523d76751a19407929606196975051ccf0f1b5b68d8e4fa618914de6e5a3a236656403070b02080604090a0105005d4eeba4a5393a740f13170d1412101516110e0cf9db595a8f9043484c424947454a4b464441f4c7c687889a5655b8782827fbe1a15e5feeefb3b48c3b3c6362995453b73f3e771e222623211d1f2425201c1be4fae09fa0cbeceda9adb2aeaca8aab0b1abafa78a8bdedf5b5c9495cae9ea37387273f7f8d9da9d5758f3c5862d313532302e33342b2f2c2ae3dcdd9e9293c9c8e7e889686d716e6b696f706a676c66e2f5f6ced3d8d4d2d0d6d7d1cfd5cd9b9cf2bbbfc4c0bebcc2c3bdc1bab97c8185827f7d83847e7b807a]

def invKeys : Fin 8 → Nat := ![
  0xfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100,
  0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a,
  0xa19d9e9fa09b9ce3e4e25c5b5f5e58575d61605a596263f3f4f28c868d8e8788898a8b7e7f7c7b827d84858180837acac5ccc6c7c8c9cbbdbebbbac0bcc3c4bfc2c1b93d3638373c3b2f302d2c322e343531332b2a40393a3e3ffbf7f8f9faf5f698919a95949796908f999392dedfe1d9dadbdcdde0d1d2ced4d0cfd7d8d3d6d5cd4f524d55564e51504647434945444b4c484a42415354e5e6eae9efeeebf1f0e8e7edec757664657873727974776a6b686e6970716d6c6f6766a6a2a3b8b4b3a4a5b6b5b7abaca9aeaab1b2adb0afa8a718191a05060308040a0b070901020027282911120f1410161713150d0e0c20211e231f252622241c1d1b,
  0x9891f996978f90eb7974e6e576756564f48e8d8887f1f04f5d4e524d6061595adb50514c484342494b454647444a41a61840393aa4a52917130f0d1416101112150e0c3d36a3a21a190b070302080a040506090100ccc6c7b6b59a95949e999392a19dfbf7f8a09f9c9bfaf5f6eae978737289e8e777716d686e706c696a6b6f6766f38c86efeef28b8a85817c8284807d7e7f837b7aedec5b5cdedf5556e36263dcdd53545e5f5758e1d9dae4e2e0d8d3ced4d7d0d1d2cfd6d5cdca3738b82728c8c93e3fb726221e23251f2021241c1d1bc53b3c35312d32342e2f30332b2c2ab4b3cbc4bfbbc0c3bcbdbec2bac1b9b2ada9aeb1aaabacb0afa8a7,
  0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441,
  0x98523d76751a19407929606196975051ccf0f1b5b68d8e4fa618914de6e5a3a236656403070b02080604090a0105005d4eeba4a5393a740f13170d1412101516110e0cf9db595a8f9043484c424947454a4b464441f4c7c687889a5655b8782827fbe1a15e5feeefb3b48c3b3c6362995453b73f3e771e222623211d1f2425201c1be4fae09fa0cbeceda9adb2aeaca8aab0b1abafa78a8bdedf5b5c9495cae9ea37387273f7f8d9da9d5758f3c5862d313532302e33342b2f2c2ae3dcdd9e9293c9c8e7e889686d716e6b696f706a676c66e2f5f6ced3d8d4d2d0d6d7d1cfd5cd9b9cf2bbbfc4c0bebcc2c3bdc1bab97c8185827f7d83847e7b807a,
  0xfbe1b8efeeb4b3caf3c5dfdef8f7dad9a6e5e6a2a3e9eae4cccbfae0f1f0b6b5b7edecb0b1b2afaeaaaca9ada8aba7e3e2f4c7c6c9c8f2c2c3c4c1c0bcbebbbfbdbab9f9dbdddcf6f5d6d7d8d5d4d0d2ced3d1cfcdeba4a5e7e8a15e5f3d8c3b3c98529a56557576191a7828275b5c9d575836373886333435322e2b302d312f2c2a4f914d9495186465090a0b0804010603070502007273616063629fa0408d8e3f3e8a8b97965150995453792977242526231f211e221d201c1b5d5a599e9b9c393a878889838485827d7f7c817e7b807a4e908f4a4b4c4945474348464442419293741516171410120f13110d0e0c6f70716e696b686d6a676c66,
  0x9a78b855562728a64f18e9ea94957273ca5b5c3738dfde794029997762633e3fb75354241f201c2325221e211d261beb745d3a39a5a44e1510110e1416130f12170d0c9e89e7e892936f696a676e706d686b716c66e3c8c9dddc9875763d52191aa18cfbeeef5e5f3b3ce1b3b4e5e691646536a2a34d090405080a010703060b0200f39d86f8f7c55758332e2f32342b312d30352c2adad98e8df0f19697cc6061b5b65051a09f8b8afaecede4cbe0b0aaabaeb1ada9aca8b2afa7f48887f98f90c6c7595adb4a4546494b4843474c424441f29c9b837d7e8284817c7f85807b7af6f5e2c2bcbdc0c3bfbbbec4bac1b9d6d0d1d4d7d3ced2d8d5cfcd]

-- Reindex the positive and negative samples to fix one degree-two input at false.
def marker : Fin 4 → Sig := ![raw0, raw3, raw5, raw6]
def posKey : Fin 4 → Nat := ![pos0, pos3, pos5, pos6]
def negKey : Fin 4 → Nat := ![neg0, neg3, neg5, neg6]

def index (key : Nat) (j : Fin 252) : Fin 252 := Fin.ofNat 252 ((key >>> (8 * j.val)) &&& 255)

def reindex (f : Fin 252 → Fin 252) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 252 → Fin 252) (a : B) (j : Nat) (hj : j < 252) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 252 → Fin 252) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 252 → Fin 252) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 252 → Fin 252) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 252 → Fin 252) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 252 → Fin 252) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

def project (i : Fin 4) (a : Sig) : Sig :=
  (reindex (index (posKey i)) a.1, reindex (index (negKey i)) a.2)

lemma project_neg (i : Fin 4) (a : Sig) : project i (neg a) = neg (project i a) := by
  simp [project, neg, reindex_not]

lemma project_bin (i : Fin 4) (d : Bool) (a b : Sig) :
    project i (bin d a b) = bin d (project i a) (project i b) := by
  cases d <;> simp [project, bin, reindex_and, reindex_or]

lemma project_target (i : Fin 4) : project i target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma project_marker : ∀ i, project i (marker i) = zero := by decide +kernel

def thetaWord (a : Sig) : Nat :=
  ((a.1.toNat &&& Theta.lo 232) <<< 232) ||| (a.2.toNat &&& Theta.lo 232)

lemma thetaWord_bit (a : Sig) (j : Nat) :
    (thetaWord a).testBit j =
      if j < 232 then a.2.getLsbD j else if j < 464 then a.1.getLsbD (j-232) else false := by
  simp only [thetaWord, Theta.lo, Nat.testBit_or, Nat.testBit_and, BitVec.testBit_toNat,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hj : j < 232
  · simp [hj, show ¬ 232 ≤ j by omega]
  · by_cases hk : j < 464
    · simp [hj, hk, show 232 ≤ j by omega, show j - 232 < 232 by omega]
    · simp [hj, hk, show 232 ≤ j by omega, show ¬ j - 232 < 232 by omega]

lemma thetaWord_target : thetaWord target = Theta.goal 232 := by decide +kernel

lemma thetaWord_neg (a : Sig) :
    thetaWord (neg a) = thetaWord a ^^^ Theta.mask 232 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, thetaWord_bit, thetaWord_bit]
  by_cases hl : j < 232
  · simp [hl, neg, Theta.mask, Theta.lo, BitVec.getLsbD_not, show j < 252 by omega,
      show j < 464 by omega]
  · by_cases hh : j < 464
    · simp [hl, hh, neg, Theta.mask, Theta.lo, BitVec.getLsbD_not, show j - 232 < 252 by omega]
    · simp [hl, hh, Theta.mask, Theta.lo]

lemma thetaWord_bin (d : Bool) (a b : Sig) :
    thetaWord (bin d a b) = if d then thetaWord a ||| thetaWord b else thetaWord a &&& thetaWord b := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases d <;> simp only [bin, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_or,
    Nat.testBit_and, thetaWord_bit, BitVec.getLsbD_or, BitVec.getLsbD_and] <;>
    split_ifs <;> rfl

lemma live_run {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup)
    (he : v.toFinset = S) :
    Theta.Run neg (bin false) (bin true) target k v := by
  induction h generalizing v with
  | stop =>
    have hp : ([target] : List Sig).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    exact Theta.Run.perm hp Theta.Run.done
  | @unary k t U a ha hf tail ih =>
    let rest := dropped [a] v
    have ham : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn, eq⟩ := edit_list (del := [a]) hv (by simp) (by simpa using he)
    let save := decide (a ∈ U)
    have hkeep : Theta.kept save a rest = keepOf U [a] ++ rest := by
      by_cases hm : a ∈ U <;> simp [save, Theta.kept, keepOf, hm]
    rw [← hkeep] at hn eq
    have hs : (neg a :: Theta.kept save a rest).toFinset = insert (neg a) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (neg a :: Theta.kept save a rest).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem ?_), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := recover_perm [a] v hv (by simp) (by simpa using ham)
    exact Theta.Run.perm p.symm (Theta.Run.one true save (ih _ hnd hs))
  | @binary k t U a b d ha hb hab hf tail ih =>
    let rest := dropped [a,b] v
    have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn, eq⟩ := edit_list (del := [a,b]) hv (by simp [hab]) (by simpa using he)
    let sa := decide (a ∈ U)
    let sb := decide (b ∈ U)
    have hkeep : Theta.kept sa a (Theta.kept sb b rest) = keepOf U [a,b] ++ rest := by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;>
        simp [sa, sb, Theta.kept, keepOf, ham, hbm]
    rw [← hkeep] at hn eq
    have hs : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset = insert (bin d a b) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := recover_perm [a,b] v hv (by simp [hab]) (by simpa using And.intro ah bh)
    have done := ih _ hnd hs
    cases d
    · exact Theta.Run.perm p.symm (Theta.Run.two true sa sb done)
    · exact Theta.Run.perm p.symm (Theta.Run.two false sa sb done)

def thetaInputOrder : Fin 4 → List Sig :=
  ![[raw2,raw7,raw3,raw1,raw5,raw6,raw4], [raw1,raw4,raw0,raw2,raw6,raw5,raw7],
    [raw2,raw4,raw6,raw1,raw0,raw3,raw7], [raw1,raw7,raw5,raw0,raw4,raw2,raw3]]

def thetaInputs (i : Fin 4) : List Sig := (thetaInputOrder i).map (project i)

lemma thetaOrder (i : Fin 4) :
    (thetaInputOrder i).toFinset = raw.toFinset.erase (marker i) := by
  fin_cases i <;> decide +kernel

lemma marker_in_raw (i : Fin 4) : marker i ∈ raw.toFinset := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
lemma thetaInputs_word : ∀ i, (thetaInputs i).map thetaWord = Theta.xs517 := by decide +kernel

lemma thetaWords_nodup : Theta.xs517.Nodup := by decide +kernel

lemma thetaInputs_nd (i : Fin 4) : (thetaInputs i).Nodup := by
  have h := thetaWords_nodup
  rw [← thetaInputs_word i] at h
  exact List.Nodup.of_map _ h

lemma project_raw (i : Fin 4) :
    raw.toFinset.image (project i) = insert zero (thetaInputs i).toFinset := by
  have hm : (thetaInputs i).toFinset = ((thetaInputOrder i).toFinset).image (project i) := by
    ext a
    simp [thetaInputs, Finset.mem_image, List.mem_map, and_comm]
  rw [hm, thetaOrder, ← project_marker i, ← Finset.image_insert,
    Finset.insert_erase (marker_in_raw i)]

def Feasible (i : Fin 4) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image (project i)

lemma root_project_impossible (i : Fin 4) : ¬ Feasible i 10 raw.toFinset := by
  rintro ⟨m, hm, t, T, h, hs⟩
  rw [project_raw] at hs
  have ht : ∀ a ∈ T, a ∈ thetaInputs i := by
    intro a ha
    rcases Finset.mem_insert.mp (hs ha) with eq | hmem
    · exact False.elim ((live_proper h _ ha).1 eq)
    · exact List.mem_toFinset.mp hmem
  let v := (thetaInputs i).filter (fun a => decide (a ∈ T))
  have he : v.toFinset = T := by
    ext a
    simp only [v, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨ht _ ha, ha⟩⟩
  have hh := live_run h v ((thetaInputs_nd i).filter _) he
  have hr := Theta.Run.map (inv' := (· ^^^ Theta.mask 232))
    (meet' := (· &&& ·)) (join' := (· ||| ·)) thetaWord thetaWord_neg
    (fun a b => thetaWord_bin false a b) (fun a b => thetaWord_bin true a b) hh
  rw [thetaWord_target] at hr
  apply Theta.noSub hm _ hr
  have sub := List.Sublist.map thetaWord (List.filter_sublist (l := thetaInputs i) (p := fun a => decide (a ∈ T)))
  rwa [thetaInputs_word] at sub

lemma feasible_mono {i : Fin 4} {k k' : Nat} {S : Finset Sig}
    (h : Feasible i k S) (hk : k ≤ k') : Feasible i k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hk, t, T, hl, hs⟩

lemma neg_rep (w : List Sig) (a : Sig) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases (Or.inl ha : represented w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

lemma feasible_pull {i : Fin 4} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g) ∨
      witness (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image (project i)).toList ++ [project i g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma feasible_free {i : Fin 4} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb

lemma pull_unary {i : Fin 4} {q : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i (q+1) (insert a U) := by
  apply feasible_pull (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_neg]
  exact neg_rep _ _ (by simp)

lemma pull_binary {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i (q+1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_bin]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma free_unary {i : Fin 4} {q : Nat} {a : Sig} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i q (insert a U) := by
  apply feasible_free (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2 (by rw [project_neg,hz,neg_laws.1]))
  · exact Or.inr (fun hp => hp.1 (by rw [project_neg,ho,neg_laws.2]))
  · simp at hm

lemma free_binary_left {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [project_bin, bin_comm]
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
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

lemma free_binary_right {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (project i b))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h

lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Fin 4) :
    Feasible i k S := by
  induction h with
  | stop =>
    refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩
    simp [project_target]
  | unary _ _ _ ih => exact pull_unary ih
  | binary _ _ _ _ _ ih => exact pull_binary ih

lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S)
    (i : Fin 4) (a : Sig) (ha : a ∈ S) (hc : ¬ proper (project i a)) :
    ∃ q < k, Feasible i q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, project_target]; exact target_proper)).elim
  | @unary k t U b hp hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hc (feasible_live tail i)⟩
    · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q+1,by omega,pull_unary h⟩
  | @binary k t U b c d hb hc' hbc hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail i)⟩
      · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q+1,by omega,pull_binary h⟩

def ProjectBound (k : Nat) (S : Finset Sig) : Prop :=
  ∀ i q, q + (if marker i ∈ S then 1 else 0) < k → ¬ Feasible i q S

lemma project_bound_root {k : Nat} (hk : k ≤ 12) : ProjectBound k raw.toFinset := by
  intro i q hq h
  rw [if_pos (marker_in_raw i)] at hq
  exact root_project_impossible i (feasible_mono h (by omega))

def special : List Sig := [raw0,raw3,raw5,raw6]

lemma mem_special (a : Sig) : a ∈ special ↔ ∃ i, marker i = a := by
  rw [← List.mem_ofFn]
  rfl

lemma bound_unary {k : Nat} {a : Sig} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a U)) :
    ProjectBound k (insert (neg a) U) := by
  intro i q hq hf
  by_cases hp : marker i ∈ insert a U
  · by_cases ht : marker i ∈ insert (neg a) U
    · rw [if_pos ht] at hq
      exact h i (q+1) (by simp [hp]; omega) (pull_unary hf)
    · rw [if_neg ht] at hq
      have he : marker i = a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm => ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ proper (project i a) := by rw [← he, project_marker]; exact fun hz => hz.1 rfl
      exact h i q (by simp [hp]; omega) (free_unary hz hf)
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (pull_unary hf)

lemma bound_binary {k : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a (insert b U))) :
    ProjectBound k (insert (bin d a b) U) := by
  intro i q hq hf
  by_cases hp : marker i ∈ insert a (insert b U)
  · by_cases ht : marker i ∈ insert (bin d a b) U
    · rw [if_pos ht] at hq
      exact h i (q+1) (by simp [hp]; omega) (pull_binary hf)
    · rw [if_neg ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ proper (project i a) := by rw [← ha, project_marker]; exact fun hz => hz.1 rfl
        exact h i q (by simp [hp]; omega) (free_binary_left hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ proper (project i b) := by rw [← hb, project_marker]; exact fun hz => hz.1 rfl
          exact h i q (by simp [hp]; omega) (free_binary_right hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (pull_binary hf)

lemma restricted_unary {k t : Nat} {a : Sig} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a U)) (tail : Live k t (insert (neg a) U)) :
    a ∉ special := by
  intro hm
  obtain ⟨i, rfl⟩ := (mem_special _).mp hm
  have hz : ¬ proper (project i (marker i)) := by rw [project_marker]; exact fun hz => hz.1 rfl
  have ho : ¬ proper (project i (neg (marker i))) := by
    rw [project_neg, project_marker, neg_laws.1]
    exact fun hp => hp.2 rfl
  obtain ⟨q,hq,hf⟩ := feasible_const tail i (neg (marker i)) (Finset.mem_insert_self _ _) ho
  exact h i q (by simp; omega) (free_unary hz hf)

lemma restricted_binary {k t : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a (insert b U))) (tail : Live k t (insert (bin d a b) U)) :
    (a ∈ special → d = true ∧ a ∉ U) ∧ (b ∈ special → d = true ∧ b ∉ U) := by
  have leftSide {a b : Sig} (h : ProjectBound (k+1) (insert a (insert b U)))
      (tail : Live k t (insert (bin d a b) U)) (hm : a ∈ special) : d = true ∧ a ∉ U := by
    obtain ⟨i, rfl⟩ := (mem_special _).mp hm
    have hz : ¬ proper (project i (marker i)) := by rw [project_marker]; exact fun hz => hz.1 rfl
    constructor
    · cases d
      · exfalso
        have ho : ¬ proper (project i (bin false (marker i) b)) := by
          rw [project_bin, project_marker, bin_comm, (bin_laws _).2.2.1]
          exact fun hp => hp.1 rfl
        obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_self _ _) ho
        exact h i q (by simp; omega) (free_binary_left hz hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_of_mem hU) hz
      exact h i q (by simp; omega) (free_binary_left hz hf)
  refine ⟨leftSide h tail, ?_⟩
  apply leftSide (a := b) (b := a)
  · rwa [Finset.insert_comm]
  · rwa [bin_comm]

-- A degree-two input can appear only as a consumed operand of a disjunction.
inductive Restricted : Nat → Nat → Finset Sig → Prop
  | stop : Restricted 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hf : neg a ∉ insert a U) (hr : a ∉ special)
      (tail : Restricted k t (insert (neg a) U)) :
      Restricted (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U))
      (hra : a ∈ special → d = true ∧ a ∉ U)
      (hrb : b ∈ special → d = true ∧ b ∉ U)
      (tail : Restricted k t (insert (bin d a b) U)) :
      Restricted (k+1) t (insert a (insert b U))

lemma Restricted.live {k t S} (h : Restricted k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ ih => exact Live.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih

lemma restrict_live {k t S} (h : Live k t S) (hb : ProjectBound k S) : Restricted k t S := by
  induction h with
  | stop => exact Restricted.stop
  | unary ha hf tail ih =>
    exact Restricted.unary ha hf (restricted_unary hb tail) (ih (bound_unary hb))
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩ := restricted_binary hb tail
    exact Restricted.binary ha hg hab hf h1 h2 (ih (bound_binary hb))

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
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Restricted m t (insert (neg a) U))
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
  exact ⟨by simp [ha], gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
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
      gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Restricted m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
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
    (h : Restricted m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  cases h with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf hr tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf hr tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf hra hrb tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Restricted m t S) (k : Nat) (hk : m ≤ k)
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
  ∀ m ≤ k, ¬ Restricted m t v.toFinset

lemma exclude_search {k t : Nat} {v : List Sig} (hv : v.Nodup) (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hv rfl))

lemma exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible k (t-1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

-- Graph automorphisms permute the diagnostic pairs and preserve the four degree-two inputs.
def symmetrySelector (g : Fin 8) : Fin 252 → Fin 252 := index (symKeys g)

def inverseSelector (g : Fin 8) : Fin 252 → Fin 252 := index (invKeys g)

set_option maxRecDepth 10000 in
lemma symmetry_left_inverse : ∀ (g : Fin 8) (j : Fin 252),
    inverseSelector g (symmetrySelector g j) = j := by decide +kernel

lemma reindex_injective {s inv : Fin 252 → Fin 252} (h : Function.LeftInverse inv s) :
    Function.Injective (reindex s) := by
  have hs := Finite.surjective_of_injective h.injective
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨x,hx⟩ := hs ⟨j,hj⟩
  have c := congrArg (fun a : B => a.getLsbD x.val) eq
  simpa only [reindex_bit _ _ _ x.isLt, Fin.eta, hx] using c

def action (g : Fin 8) (a : Sig) : Sig :=
  (reindex (symmetrySelector g) a.1, reindex (symmetrySelector g) a.2)

lemma action_neg (g : Fin 8) (a : Sig) : action g (neg a) = neg (action g a) := by
  simp [action, neg, reindex_not]

lemma action_bin (g : Fin 8) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := by
  cases d <;> simp [action, bin, reindex_and, reindex_or]

lemma action_zero (g : Fin 8) : action g zero = zero :=
  Prod.ext (reindex_zero _) (reindex_zero _)

lemma action_one (g : Fin 8) : action g one = one :=
  Prod.ext (reindex_top _) (reindex_top _)

lemma action_target (g : Fin 8) : action g target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma action_injective (g : Fin 8) : Function.Injective (action g) := by
  intro a b eq
  have hi := reindex_injective (symmetry_left_inverse g)
  have hf : reindex (symmetrySelector g) a.1 = reindex (symmetrySelector g) b.1 :=
    congrArg (fun x : Sig => x.1) eq
  have hs : reindex (symmetrySelector g) a.2 = reindex (symmetrySelector g) b.2 :=
    congrArg (fun x : Sig => x.2) eq
  exact Prod.ext (hi hf) (hi hs)

lemma action_proper (g : Fin 8) (a : Sig) (h : proper a) : proper (action g a) := by
  constructor
  · intro h0
    exact h.1 ((action_injective g) (h0.trans (action_zero g).symm))
  · intro h1
    exact h.2 ((action_injective g) (h1.trans (action_one g).symm))

set_option maxRecDepth 10000 in
lemma action_special : ∀ g : Fin 8, (special.map (action g)).Perm special := by decide +kernel

lemma action_mem_special (g : Fin 8) (a : Sig) : action g a ∈ special ↔ a ∈ special := by
  rw [← (action_special g).mem_iff]
  constructor
  · rintro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact ((action_injective g) he) ▸ hb
  · exact List.mem_map_of_mem

lemma restricted_action {k t : Nat} {S : Finset Sig} (h : Restricted k t S) (g : Fin 8) :
    Restricted k t (S.image (action g)) := by
  induction h with
  | stop => simpa [action_target] using Restricted.stop
  | @unary k t U a ha hf hr tail ih =>
    simp only [Finset.image_insert, action_neg] at ih ⊢
    have hne : neg (action g a) ∉ insert (action g a) (U.image (action g)) := by
      rw [← Finset.image_insert, ← action_neg]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Restricted.unary (action_proper _ _ ha) hne (fun h => hr ((action_mem_special _ _).mp h)) ih
  | @binary k t U a b d ha hb hab hf hra hrb tail ih =>
    simp only [Finset.image_insert, action_bin] at ih ⊢
    have hne : bin d (action g a) (action g b) ∉ insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← Finset.image_insert, ← Finset.image_insert, ← action_bin]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    have hm (v : Sig) (hv : v ∉ U) : action g v ∉ U.image (action g) := by
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hv ((action_injective g) he ▸ hy)
    refine Restricted.binary (action_proper _ _ ha) (action_proper _ _ hb)
      (fun e => hab ((action_injective g) e)) hne ?_ ?_ ih
    · intro hx
      obtain ⟨h1,h2⟩ := hra ((action_mem_special _ _).mp hx)
      exact ⟨h1,hm _ h2⟩
    · intro hx
      obtain ⟨h1,h2⟩ := hrb ((action_mem_special _ _).mp hx)
      exact ⟨h1,hm _ h2⟩

lemma rotate_impossible {k t : Nat} {w z : List Sig} (g : Fin 8)
    (hp : (w.map (action g)).Perm z) (hn : Impossible k t z) : Impossible k t w := by
  intro m hm h
  apply hn m hm
  suffices hi : z.toFinset = w.toFinset.image (action g) by rw [hi]; exact restricted_action h g
  ext a
  simp only [List.mem_toFinset, hp.mem_iff.symm, List.mem_map, Finset.mem_image]

def rawPermCodes : Fin 8 → Nat := ![0xfac688, 0x5717e0, 0x977053, 0x3aa13b, 0x8c7c8d, 0x2c2be6, 0xe1ca56, 0x419d3d]

def rawImage (g i : Fin 8) : Sig :=
  raw.getD ((rawPermCodes g >>> (3*i.val)) &&& 7) zero

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rawImage_eq : ∀ (g i : Fin 8),
    rawImage g i = action g (raw.getD i.val zero) := by decide +kernel

def recipeShift : Nat := 0x40000201c0001400030000040800003000000300200002000080000700c000240600001008000080300005000020040202c04004060000000400018020080000c020040100002000000000100009000070040500003018010000000003004040080402c0000400004010000901c000180000000004070000202c0400000038030000000002000010080200c040180000401000000080001c0000000000010000000c0001c03004080040000002000000240200000014000000400400020020200003c0202c060180102c020000400800008000040000402018000040000005000070080400000000000040a0080102401000060040200803000020000100801024010040100c000000500c0400001028000080001400000000080300803004000240000c0200009000050040c0000000c000280200800004090040200402

def recipeData : Nat := 0xab5a329800000000000000bb79b538000ab7a295200000000000000ab6a32980000ab82a350000000000000000000a350000000000000000ab2598000000000000000000000000000000000000000000000000000000000000000000000a9a82b35000a29bb58300000000b65000a9a8b52300000000000000bb298a3500000009a820000000b5920000bb3a58600000000000000000000000000b3ab85200000000000000b7ba329800b7ab4a5230000b3a2a8500000000000000000ab7350000000000000000000000000b5b39b8200000b3b29500000000b870000000000000000000b3200000000000000b59b7a8500ab6a32b3500000b5b39800b4ab58a2300000000000000000000000000000000000ab5a32b28000000000000000ab6a358000000000000000000000000000b3a598000009ab852000000000000000000000000000000000000009ab58300000009a320000000000000000000000000b9a8b5230000bb6a358000a2b3a59800bbb8a235700000000000000b3ab25980000000000000000a8a59300a8b7a5a23000000000000000a2b5a83000ba329b8500000000000000009b2a850009ba85a320000ab8a23500000000000000000a5b8300000000000000000b7b350009ab4a52300000a2b398000000000000000000000400000000000000000b2a380000b2ab58300000000000000b4a2b39800000b39b82000000000000000000000000b5ab4a5830000000000000000000a8300000a9a285000000a5a32000000a3b250000ab2a85300000a5a398000000000000000000000000000000000000000000000000000000000000000000000b29b8a530000ab7a85500ab85b2a350000000b2980000000000000bb7a85a32000000b1a8500000000000000000000000000000b29500000b7b298ab8a23b6a3200000b3b592000a9a35b3500000000000000000000000000000000000000009b35000000000000000000a5920000b7a8b5200000000b3500000000000000b9a82b3500b2ab4a5830000000000000b8b7a5a230000b4a5b83000b2a9a8530000000a892000a89b7a2800000000000000000000000000a8b2a3500000000000000b5b3a298000000000000000a8b7a2300000000000000000000000000000000000000b9a358000a9a85b3500000a3b298000b2a5b39800000000b54000009a5a32000009a3b2500000b29b8300000009a380009ab2a8530000b5a3b28000000b3a28000b8b7a29500000b9a23500ab7a8a32200bb7a2b3850000b4b3a8500000ab829300000000000000000a8b530009b2ab583000000ab7250000ba85a32000b2b5b398000000b2a850000b1a8a230000b2a5b830000ab4a523000000000000000b92a893000000000000000000000000000b9a853000b4a29b58000b39b7a82000000000000000000000000ab7a5a23200a3ab6a582000a29b7a8500b1ab4a523000b4a29b83000000000000000a3b8a52000a9ab2385000000b4b3500000a8a3950000b93a298000000ab58300000000a3200ab8a23b3200000a89b35000000ab8520000ab4a58800ab6a35b3500000a9a5820000ab89593000000000000000000000000000009b320000b5a8a2300ab7a23b320000a5b6a32000a2b39b850000000000000000000000000000000000009b3a2a8500b1ab8a23500000000000000000000000000000000000abb8a23750000000000000000ab3925000000000000000000000000b2ab4a23300000000000000000000000000000000000b2ab6a3230000000000000ab7a82b3500000000a8200ab4a58a350000000a295000000000000000000000000000000000000bb79b3520000ba82a350000000000000000b89b25000bab3259800b8ab6a323000000a8b720000b6a8a32000b59b7a280009ab82a3500000009a35000000b7a3500000b2a59800b6ab4a23300000000000000000000000000000000000000000000000000000000000000000000bb4a58a32000000bb32500b1ab2a8530000ab7a822000000000000000000000000000b8a293000000000000000000000000000000000000000000000000000000000000000000000009b4a2300000000000000000000000000000000000000009a85000000ab6350000000000000000000000000ab79b538000000000000000000a89300ab4a25b350000000000000b1ab85a3200ab6a35a32ab7a23b6a3200000b9a25800000000000000000000000000000000000b2ab6a533000ba859b8500ab4a58b350000a8bb32500000000b72000b49bb58300b4ab28a530000ab52b3800000a8b39500a2ab4a58300000b2b89300000b89b35000000000000000000000000000000000000000000000000000000000000000000ab5a32b6a32000000000000000b5b2a380ab7a239a230000000000000000000000000000000000000000000000000000000000000000000000000000000000009b850000000000000000b49b3800000000000000ab79b352000a29b8a53000ba35a2980009ab6a533000000bb583000ba359b850000a5b2a38000b4a3a29800000ba8293000b4a5a298000000b5a82000000ab325000000b6a580000a2b8a53000000b7a850000000000000000000000000000000000000b8ab325000000b4a250000000000000bb6a32a8500b6ab58a3200000b9a532000000b8a52000009b3a25000000b7b320000b8bb3250000000000000000000000000009a3a58000009b8a2300009b79b35000000000000ab7a859a850000000000000b2a3b6a58000009b7a8200000000000000000b4a5800000000000000000000000009a3b6a58000ab3a25980000000000000000000000000ab7a23980000b6a5b8300a3ab6a5880000000000800000000b620000b4a3b2500000b3b8920000bb8a2350000000000000000000000000000000000000bb8a2360000000000000b8ab4a58300000ab329800000000000000000000000000000000000000000000000b1a3a29800b5ab6a3230000b4a5a32000b29b7a85000000bb8520000000a8950000000000000000009b3800000000000000000000000000000a39200000a39b85000a29b7a8200000000b630000b1a3b28000ba359b38000ba85a29800000ab5983000000000000000b1a3a5800000000000000ab35a298000000000000000000000000b6a3b5a82000ab329b85000000000000000000000000ab7b5a32200a2ab7a853000000000000000000a29800abb7a8235000000000000000ab39598000bb398a2500bb7a82a3500b7ab2a5830000000000000000000a5200ab5a32b23000b59b8a230009b7a5a23000a59b7a850000ab5929800b6ab8a32500000b4a298000000bb82700000a3a892000b7a2a398000ab7a295300b1ab4a58300b7ab8a32500000000000000a3a29b58000000000000000ab2959300000000000000000000000000b6b2a350000000000000000000000000000000000000b7b5a32000000000000009b7a8a3200000000000000ba3b259800000a29b5800000a9a2350000000000000000000000000000a2a850000000a293000b3a5a2980000a5b3a2800b1ab4a233000b3b8a59200000000000000b6ba3298000b5a9a82300000009b82000000bb837000a59b8a2300000a9a35800000a5b3980000b8a5a32000000a8b7300b5a3b6a5800000a59b3800000b59b3800000b9a28500000b3a298000000b8a5300000009b250009ab4a583000000000000009ab6a3230000000000000000000000000009a2b38000ab529b3800000a39b5200000000000ab4a25b3a250009ab4a233000ba839b380000000a3980009ab85a3200ab7a82a3500000a9a523000009a8b5200ab7a82a320000000000000b1ab82a350000000000000000a3b5920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a2b35000ba83a298000009bb23800000b39b8500000000000000009b6a350000ba52a38ab7a5a23a320009bb8a23700000b29b580b9b6a35a35000000b7a23000000000000000bb2a857000b2ab598300ab85b3a25000ab7a29550000000000000000000000000000000000000000000000000000000000bb598a32000000000000000000000000000000000000000000000000b3a5b82000a2b5b398000000ab72300ab4a23a380000000000000000a3a298000ab25a398000000000000000000000000000ba32980000000a59300000b6a3980000a8b3a25000000000000000000000000000000005000000000000000000000000000b2b398000b29bb58300000b7b59800000a2b59300000a9a5320000bb7a285000a9a82b8200000b6b598000b5a29b830000b2a3a5800000000000000000b2a350000000000000a8bb7a8230000000000000ab7a23b3500000000000000000000000000000a5980000ab52a380000000000000000000b7300000a2a89300000000000000000000000000b92a598000b39b7a8500000ba8593000000000030000ab82b35000000000060000b1a8b53000000000000000000a39500ab7a23a350009bb3a582000ab52b398000ba329b380000ab6a3280009a3b5a82000b89b7a85000000b6a320000ab4a23800ab7a82b32000009a8a230000b4a5b820000000000000a2ab4a5230009bb7a8230000000000000000a59b2800000000000000b3a29b5800000000000000a5b39b820000b7a2b380000bb7a23400000000092000000000000000000000000009b7a29500b8ab4a23300000a89b2500000b2a39800000000000000009b5a32000b29b7a2300000000000000000000000000ab7a2350009ab85b3200ab6a398980000000000000000000000000000000000009a3bb85200000000000000000000000000000000000a5ab4a23300000000000000000a3b2800000000000000b9a85b32000000000000000a3bb8520000ab5a3280000a2bb5830000ab85b32000b2b3a5980000ab3a5820009b7a2b380000b7a3a8500b7ab4a58300000a9a38500000ab2935000000b5a3200000b5b29800b4ab8a23500000b7a29500000000000000ab6a5898000000000020000000000000b6ab4a58300000000000000a59b7a28000000ab23800000000000000ba32a598000b5a2b3980000b6a3b250000bb3a58200000000093000ab85b398000000b3a580000bb7a823000ab7a8298000000a8a2300b7bb3a582000009b6a320000a3b5a820ab7a829a82000000b7b52000b6ab598300ab52b3a2800b8ab4a523000000b6b350009ab82b3500000a3b29500000000000000b5b29b830000b95a29800000000000ab8a23b7a230000b6a5a23000000000000000000000000000b9a82300000a9a85300000009b7300000000000000000000000000000b895000a9a85b3200000000000000000000000000000000000b5ab4a233000ab6a3598000009b2a3500000a89b3200000000000000b79bb853000a89b7a850000000000000ab8a23b3500ab7a85b3200000a9a32800000ba53920000ab4a2320000b6a3a85000a9a25b35000000000000000b2a8b530000000009500000000000ab5a32b7a230000000000000009b6a3980000000b395000000b1a3200b6ab2a5830000000000000b7ab4a23300000b9a582000a8b3a592000000000000009b3a5b8200000b9a3280000b4ab325000000000000000000000000000000000000ab32b59800000000000000000000070ab6a359a35000000000000000b8b3a25000000b6a35000000b5a8300b7ab82a350009ba52a380000bb6a32400000000000000000000000000bb8a2370000000000000000ab859300000b7b395000009b7a2300000000000000000000000000b4a8a23000000bb23800a8b7b5a320000ab85a3200000000000000ab79b35300000000000000000a2b380000b4b5a32000000000000000b4b3a250000000000000000000b75000000a8b5200000000000000a39b7a820000bb8a2340000000b8930000000000000000000000000000b4a350000000000000000b2b5930000ab4a2330000b95a8930ab79b35b350000a5b4a2300000000b520000ab6a32300ab6a35b8200ab4a58a8300000000b820000b8a2b350000ab4a5830000ab89293000000000000000000000000000000000000009b8a530009b8a5a3200bb7a82b350000000000000000b8b39500000ba35980000000000000000000000000000000000000b2b8a5300000000000000000000000000b7a8a320000000b39200000ab3928000bb7a295300000000b43000009a2a850009b7b5a3200b6ab82a350000000b69800000ba239500000b8b59200000b3a592000000000000000000000000000000000000000000000000000000000000b9a832000a9a82b32000000000000000bb7a2360000000000000000b8a2950000000000000000000000000000000000000b7a5a2300000000000000000000000000000000000b6ab4a523000000000000000ab7a823000000000000000000000000000009a250000000000000000000000000000000000000000000000bb7a8a325ab6a32b4a230000000b892000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ab7a5a23300000000001ab3a85b4a58000a9a32b3200000000000000000000000000000b598000b7a29b85000000000000000b93a8950000b5ab23800abb8a2373000000000000000000b29300000b5b8930000000000000000000000000a8b7a29500000ab598200000000b83000000b1a38000a5a29b83000009bb852000000ab632000000000000000000000000000000000000000ab73200ab4a52a38ab4a2b35b350000000000000000b89b32ab7a23b4a2300000000000000a5b3a29800000000098000000000000009bb8a235000000000000000000000000000a29b8300000000000000000000000000000000000b4ab2a853000000000000000000000000000000000000000000000000a3b6a58000000000000000b8a3b250000ab7a285000000b7a8200ab6a32a8300b8a3b6a5800000a3a5920ba859b7a8500000b79b35000000a3a580009b8bb325000000b8a2300b7ab85a23000000b3a2500000000000000000000000000000000000000000000000009b8a520ab49b38b3800000000000000000000000000000000000000000000000a39b7a8500ab4a23b35000009bb583000ab2b3985000009b7a85000b6a2a39800000a9a258000009b6a5800000a9a8230000b7a3b250000b6b5a3200000000b420000ab6a53300000b7b593000b6ba35980009b5b2a3800000b9a52300b8ab6a5330000000000000a5ab6a323000ba529b380000b4a2b3500000b5a39800000000b8500000000000000000000000000ab4a258000b9ab2385000000000000000b1a5a3200ab82b3a2500ab7b5a32300000000000000b2b39b85000000a5b820000a5bb238000a9a85b85000b5ab329800000ab35980000000000000000a39b820000ab6a5320000000000000abb8a23720000000000000000009b72000000000000000000000000000000000ab3a58b6a580000000000000a3ab6a5850000000000000000a5a2980000000000000000000000000ab32a598000abb32598000000000000000000b398000b5a3a2980000000000000bb1a85a2300000000000000000000000000000000000000000a8500000000000000009bb325000000b4a23000000000000000b4a3a5800000a9a8320000000000000ab7a2b3850000000000000000000000000000000000000ab3929800000b5a298000000000000000000000000b7a2b8a53

def recipeHint (a : Sig) : Nat :=
  let p := a.1.toNat % 4294967291
  let q := a.2.toNat % 4294967291
  let b := (p*31+q) % 256
  let h := ((p*1299710+q*1786) % 4294967291) % 1024
  let d := (recipeShift >>> (10*b)) &&& 1023
  (recipeData >>> (44*((h+d) % 1024))) &&& 17592186044415

def recipeFuel : Nat := 11

-- A short gate expression can evaluate a known frontier value under a row permutation.
def recipeStep (rho : Fin 8 → Sig) (op : Nat) (w : List Sig) : List Sig :=
  if op ≤ 8 then rho (Fin.ofNat 8 (op-1)) :: w
  else match w with
  | [] => []
  | a :: t =>
    if op = 9 then neg a :: t
    else match t with
    | [] => []
    | b :: r => bin (decide (op = 11)) a b :: r

def recipeRun (rho : Fin 8 → Sig) : Nat → Nat → List Sig → List Sig
  | 0, _, w => w
  | n+1, code, w =>
    if code = 0 then w else
      recipeRun rho n (code >>> 4) (recipeStep rho (code &&& 15) w)

lemma recipeStep_map (g : Fin 8) (rho : Fin 8 → Sig) (op : Nat) (w : List Sig) :
    (recipeStep rho op w).map (action g) =
      recipeStep (action g ∘ rho) op (w.map (action g)) := by
  unfold recipeStep
  by_cases h : op ≤ 8
  · simp [h, Function.comp_def]
  · simp only [ite_eq_right h]
    cases w with
    | nil => rfl
    | cons a w =>
      by_cases hi : op = 9
      · simp [hi, action_neg]
      · simp only [ite_eq_right hi, List.map_cons]
        cases w <;> simp [action_bin]

lemma recipeRun_map (g : Fin 8) (rho : Fin 8 → Sig) (n code : Nat) (w : List Sig) :
    (recipeRun rho n code w).map (action g) =
      recipeRun (action g ∘ rho) n code (w.map (action g)) := by
  induction n generalizing code w with
  | zero => rfl
  | succ n ih =>
    by_cases h : code = 0 <;> simp only [recipeRun, h, ite_true, ite_false]
    rw [ih, recipeStep_map]

def recipeValue (rho : Fin 8 → Sig) (code : Nat) : Sig :=
  (recipeRun rho recipeFuel code []).headD zero

lemma recipeValue_action (g : Fin 8) (rho : Fin 8 → Sig) (code : Nat) :
    recipeValue (action g ∘ rho) code = action g (recipeValue rho code) := by
  have h := recipeRun_map g rho recipeFuel code []
  simp only [List.map_nil] at h
  unfold recipeValue
  rw [← h]
  cases recipeRun rho recipeFuel code [] <;> simp [action_zero]

def sourceSignals (i : Fin 8) : Sig := raw.getD i.val zero

lemma sourceSignals_image (g : Fin 8) : rawImage g = action g ∘ sourceSignals := by
  funext i
  exact rawImage_eq g i

def recipeAction (g : Fin 8) (a : Sig) : Sig :=
  let code := recipeHint a
  if recipeValue sourceSignals code == a then recipeValue (rawImage g) code
  else action g a

lemma recipeAction_eq (g : Fin 8) : recipeAction g = action g := by
  funext a
  simp only [recipeAction]
  split
  · rename_i h
    rw [sourceSignals_image, recipeValue_action, beq_iff_eq.mp h]
  · rfl

def wireBits : Nat := 10

def wireMask : Nat := 1023

def wireRecipes : Nat := 0xbbb8532bbba328750009aa5320000bb8730000bb87200bba3287bbaa532870bba95287000000b87000b9a328000b9a528000bb928600bba538600bba3286000000b860000bb853000bb928300000b9280000bb85200bba3285000000b85baba327580000ba758000ba9258000bb938200000b938000b9b32800bba32840000bb83200bba5283000000b8300bab72380000ba73800bba538200bab52380000ba5380bba3295800000b95800bab4238baba524380000ba438000000b82000ba9328000ba952800bab6328000b9b538baba536280000ba62800bab53280000ba5280000ba3280baa9532800baa532800000000800bba3276baba32687000bb9273bbba827530000bb7530000bb752bbab8327500bab528700bba3275bbaa83275bba85a327baba32587000000b75baba328570000ba8570009aa853000b9a532000009a53000bb9372000ba93870ba9b3287baba5248700bba3274baba32487000bb95730000bb73200bba82730bba95273000000b7300bab82370000ba837bba53a827baab32857baba8543700bab5237baba85237baab528370000ba537baab8253700baa85370bba829570bba3295700000b9570bb9b5372000b9b5370b9bb5327000bb9872000000b7200bab852700bab8327baba538270bab958270000ba8270bab95327000ba95270baa958270ba9b532700bab6327baba5362700bab5327baba85327baab538270000ba527baab8352700baa852700bab4237baba524370bba329870000ba327baab853270baa9532700baa83270baa9832700baa53270ba9b85270b9bb853700000000700000b9320009aa832000b9a325000009a32000a9a3280009ab523000009a830009ab85300000009300bba856300bba3265baba3258600bab8356baba328560000ba8560000ba8650bb9a8532000b9a85200000b95200bba5362000000b62baab5382600baa85260009aa852000009a5209aab328509aab5382000ba9256000b9a85300000b953000009a8509aba32850a9a85b85000ba329500000009500000a95800bba3264baba3248609aba325809ba85a320b9b53a530009ab538baba53684000000b6300bab5236baba82536baba85236baab5283600bab42360bab982360000ba326baab8532600baa8326baba854360bab985360000ba536baab8253600baa8536aba536b82baba52436000b9b826000ba98360baa985360baa9832600baa5326000000006000a9a536000000b42baba536240bb9a825300000b925000ba8592000b9a8230b9ab852300000b9230b9b32a32000009a820009ab8320000000920a9a82b8200000a92809aba532809ba53a820009ab32809ab85b32000b9b5210b9ab52830009ab52809ab83b5209abb532800bba854300bba3254000000b5400bab82540000ba8540000ab548000ba935400bba524300bab5324baab538240000ba52400baa852400aba5248000000b43baba82734baab528340bab983240000ba32400baa8324baab8253400baa8534000b9b834000ba98240ba9b83240b9bb85340baa985240baa9832400baa53240000000040000ab83400ba64a320000ba851baba5238100baa85210000ba831baab5283100bab42310000ba321baba85431baba524310baa9832100baa5321000000001000a9a321000a9a831000a9a85100ba32a6100ba32a410bbb985320000bb53200bba825300bba835200bba8532000bb9852000000b520000ba82500bab835200ab83b520000ba8520000ab5280000ba7520000ba6250000ba512000bb98320bba985320bb9b8532000000b320000ba82300bab853200ab85b320000ba8320000ab3280ba9a8532baba854320000ba53200ba53a8200baa85320000ba43200000b9820b9b82a82000ba9852000b9b832000ba9832000b9b852000000002000a9a5320000ab8520000ab83200aba5382000000a820a9a32b320a9a52b520ba9a85230a9a85b32000a9a85200000a95200000b963000ba5396009ba983609aba53680009ba53609aba32680009ba326000bb98530bba982530bb9b8253000000b530000ba83500bab82530000ba85300ab53b820000ab5380a9a53b5300bab213500bab3125baba8312500bab623500bab42350bba329850bab983250000ba32500baa8325bab825a3200ba85a320000ba2150000ba43500000b9850bab329850b9ba3285000ba9825000b9b8350baa98325000000005000a9a3250000ab8350b9b85a850000ab82500aba3285000000a8500bab5423baba85423baba8512300bab42530bba529830bab982530bab985230000ba52300baa8523aba835b32bab823a5200ba83a5200ab53b42bab325a320000ab532aba851b320bab325980ab985b320000ab325000000a520ba9a8253000ba92530baa928530ba925a320a9a82b53009ab95280a9a82b520000ba513bab813a51aba513b21aba831b52aba512b3100ba32a510000ab5210b9ba85630009ab6580009ba8560000ba4230000ba213bab813a2100ba83a2100000b9730b9ba82730000ba6530000ba5430b9ba857300000b9830bab529830b9ba5283000ba9853000b9b8230ba9b82530ba985a830b9b83a83000ba9823000b9b8530ba9b85230baa985230b9bb8523000000003000a9a5230abb9285300abb851300abb85230000ab853000ab95830ab983b820000ab823000000a8300abb7523abba827530000ab753009ab93580a9a85b53000a9a853000ab9523bab213a2100abb5213000ba3297bab536a32bab534a3200ba54a3200abb6523abba856230000ab62300abb5423abba854230bab523980ab983b520abb985230000ab52300aba825300aba85230000ab423000ba32980ba985a320b9b83a320b9b85a32000ab98320ab9b85320aba98532000000a3200aab85320000aa832009ab93280a9a82b32000a9a8230a9ab85230a9ab528300aba531209aba32780009ba32709baa85270009ab7280009ba827000ab5397bab536a530000ab43500aba834509baa8537009ba93870a9ba82730000ab6530aba9256300aba8563000ab98630ab9b826300aba5263000000a630000ab543abab8254300aba8543000ba53980b9b82a530b9b83a53000ab98350b9b85a53000ab98530ab9b82530ba982a530aba982350aba98253000000a5300aab82530000aa8530009ab7580009ba85709bab52870a9ba85730a9ba857200aab435200aab21530aba9824300aba5243000000a4300aab51320000000980abb5329809baa53280009ba328000ab5298009ba95380aba3259800000a9850a9ba32850009ba53809bab523809bab3258009ba9238000009b830a9b83b5209bba5283000ab42980aba524980aba3249800000a9840aba3219800000a981000ab329800000a9830aba532980aab32985009ba9258000009b850a9b85b3209bba328500000a9820a9ba5382000a9b832000a9b8520009bb8530a9bb8532000009b8609bba3286000a9b86509bba53860aab53982000aa98520aa9b8352000aa98320aa9b8532000009b87000a9b87509bba3287000a9b87200aab635200aab65320000aa63200aab31520000aa5320000aa52109bbb8532
def readWire (i : Nat) : Sig :=
  recipeValue sourceSignals ((wireRecipes >>> (36*(i-1))) &&& 0xfffffffff)

def readWires : Nat → Nat → List Sig
  | 0, _ => []
  | fuel+1, packed =>
    if packed = 0 then [] else
      readWire (packed &&& wireMask) :: readWires fuel (packed >>> wireBits)

def frontierCount : Nat → Nat → Nat
  | 8, 0 => 1343
  | 8, 1 => 349
  | 8, 2 => 6
  | 9, 0 => 602
  | 9, 1 => 378
  | 9, 2 => 41
  | 10, 0 => 64
  | 10, 1 => 84
  | 10, 2 => 43
  | 10, 3 => 8
  | 11, 0 => 5
  | 11, 1 => 6
  | 11, 2 => 6
  | 11, 3 => 6
  | 11, 4 => 1
  | _, _ => 0

def frontierRawIds : List Nat := [153,219,267,309,323,376,442,519]

def frontierIds : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, v => if v = 0 then [] else (v &&& 1023) :: frontierIds n (v >>> 10)

def insertFrontier (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertFrontier a bs

def sortFrontier : List Nat → List Nat
  | [] => []
  | a :: xs => insertFrontier a (sortFrontier xs)

def frontierCodes : Nat → Nat → Nat
  | 8, 0 => 0x74862bf000007e042bf0000076861bf000007cc5cbf000006d4767f0000000161ff000000002eff000007fc41bf000000019fff0000000167ff000007480bbf0000074863bf0000060811df00000608fcdf0000000029ff0000000168ff0000000165ff0000000001ff0000000160ff000000002dff00000001a0ff0000000192ff0000070809bf0000070866bf000007e00bbf000007e043bf0000061c13df0000061cfadf000006ac14df000006acb1df000000001bff0000000193ff000008281b7f000008299a7f0000000036ff00000820367f0000071864bf0000077c5dbf0000000166ff000006d4387f0000036838fd0000000035ff0000000162ff0000000016ff0000076838bf00000001a2ff000000002fff000007cca6bf000006ecf5bf0000051cf5ef000007fd62bf000008296c7f0000000163ff0000000068ff00000608fedf00000608ffdf0000074808bf00000748aabf000007485bbf000006082fdf00000000a4ff0000000019ff00000749a2bf000007651dbf000007652ebf000006ec16bf00000001bbbf000000009aff0000000015ff0000000170ff0000000069ff001f86ac429f001f856c42af001f850042b7001f849442bb001f83c842be0000070886bf0000061cffdf000006ac12df000006acb2df000007e03fbf00000708abbf000007e00abf000007e0a7bf000007e040bf00000828357f0000061c35df0000070835bf0000039c35fd00000000dfff0000000030ff0020a61c355f0020a708353f0020a39c357d00000828df7f00000828307f00000828187f00000829b87f000008e9c2bf000007e1a2bf000008ea0a7f000008ea087f00000719a2bf000008e9bdbf000007dc8afe0000022838fe000000001eff000004001afb000000008cff0000074038bf000005f438df000005282bef00000001dabf000007cc38bf000000002cff000000006cff0000000033ff00000000bbff0000067838df0000061c38df0000070838bf0000060838df000007542bbf00000000a2ff000005082bef00000590b3f7000004a4b3f700000000b3f7000007692ebf000005907af70021e84d7d5f0023184d7d5f000008b60f7f0021e84d0e7b0000042018fb00000738f5bf000000002bff0022b84d7d5f0022b84d117b000000002aff000005542bef000000004fff000004f42bf7000000009fff000008282b7f000007082bbf000007e02bbf000005382bef000004e82bf7000004942bfb0000000074ff0000000018ff000007482bbf000000004eff000005f4f5df000005f446df0000076ddabf000005f456df00000528f5ef0000052846ef000007b9dabf000005283aef000007691dbf000007686fbf00000768f5bf0000076846bf000005f4a2df00000000f6ff000000004aff0000087a0f7f000008a20f7f0000052818ef0000043818fb000005202bef0000052018ef00000001cebf00000000a1ff000000000eff00000528a6ef001694181a7b000000016dff000005dc46df000004f533f7000006cd33f70000000133f70000074971bf000007486abf000008ca0b7f0000026003fe00000821a17f000006f5a1bf00000719a1bf000006fd6dbf000006156ddf00000000efff000007496dbf00000741a1bf00000000baff00000749a1bf000000006aff000005c46afe0000026046fe00000000c0ff000000006bff000001bc6afe000008296d7f000007096dbf0000061d6ddf0000000171ff00000709a1bf000007e1a1bf00000829a17f0000000174ff00000000bcff000003d46afe000006096ddf000000009dff000000001dff0022885ce17d0000088a207f0000042417fb000007c91dbf000007e01dbf000004941dfb00000000d8ff000000001cff000007081dbf000008281d7f0000000073ff0000000017ff000007481dbf000000004cff000000011eff0000000071ff0000088a137f0000043017fb000006f01dbf000006f017bf00000001bcbf000000009cff000000000cff001b53686f7d00196354317d000d522831fc000000019bff001873686fdd000004d06ff7001c23686fbd001c26d9879f001c26d94eaf001b661d4ecf001ab66c31dd0000050132f70000066d32f70000000132f7000007e1a8bf001ab66c8ade000006ac8adf000006ac8ade000007e19dbf001f866c8abe000007e08abf000007e08abe000004948afe000008ce0a7f0020a3686f7d0020a6d9875f0020a709b63f0020a6d8e77d000003c88afe00000829b77f0019b4948afa000004948afb000004948afa000006d4037f0000036803fd00000821b67f000007199bbf0000077d9bbf0000000105ff000007e19bbf00000829b67f0000066c8afe000000008aff000000008afe000006748afe000006a08afe0019b4048afa000004048afb000004048afa0000022831fe0000000103ff000008a08afe000003686ffd0000045c8afe000004040ffb00000001a9ff0000000102ff000004748afe000002286ffe000007099bbf000008299b7f000004a48afe000000008bff000003d48afe0000040446fb0000022846fe000000019dff000007499bbf001ab56c38cf002286ac38dd000007d1c2bf0000056c25ef001f86ac389f001f856c38af001f850038b700000811c2bf0000050023f7001f849438bb001ab49438db0015b49438eb0014049438f3001253c838fa000008920a7f000006b438df0000075438bf000005f038df00000001d0bf00000761d2bf000004f423f700000000c4ff00000000e0ff0000039838fd000006fc38bf0000061438df0020a61c385f0018753838cf00000775c2bf0000053826ef0020a708383f001c261c389f001c253838af001c24e838b70000070dc2bf000004e824f70000000032ff0020a39c387d0018739c38dd001c239c38bd000008620a7f0000039c32fd00000828767f0000061c76df0000070876bf0000039c76fd0000061c0ddf000007080dbf0000039c0dfd000007006fbf000006f86fbf000008246f7f000007fc38bf0000000037ff0000063438df000000007dff0000039c38fd00000000a5ff0000044c38fb0000077c38bf0000060038df0000071838bf0000068c38df00000779d2bf0000055427ef0000000020ff00000820387f000005e438df000006f438bf0000060850df000005540fef000005ec46df000006ac38df000007e038bf0000049438fb0000060c38df000007e0e1bf000006ace1df00000494e1fb00000748e1bf0000085e0b7f00000000c3ff00000828e17f0000061ce1df00000708e1bf00000000e9ff0000085e0a7f000003e04bfe0000060ce1df0000024c46fe0000060c4bdf00000001d3bf00000000ceff00000000bfff000003d44bfe00000608e1df001ab0e031dd0000038431fd0000035431fd000008a2177f000006ac31df000007e031bf0000049431fb001ab35431dd000006ac31dd001f835431bd0012535431f90000035c31fd0000074831bf000000001fff00000828317f0000061c31df0000070831bf0000039c31fd0000000075ff0000060831df000000011fff0000000070ff000000004dff0000087a127f000005ec31df0000074838bf0000062038df0000000031ff0000000076ff0000044472fb0000000050ff000003844dfd000002984bfe00000748a6bf000008ae0b7f00000000a0ff00000494a6fb000007e0a6bf000006aca6df00000500a6f70000056ca6ef0000088e0a7f000000007cff00000554a6ef00000000d0ff0000000097ff0000048072fb0000053ca6ef0000022446fe000004a472fb0000053c72ef00000001d1bf00000000e8ff000000012fff000000007bff000003544dfd00000000cfff0021e84d117b000008b2137f000004f4a6f70000000120ff000000009eff0000047472fb00000828a67f00000708a6bf0000061ca6df00000538a6ef000004e8a6f70000039ca6fd00000000f8ff00000000a3ff00000608a6df000004441afb0000000038ff000004181afb000004a81afb0000043c1afb000008ae137f001494441aeb00000771d0bf0000052428ef00000524a6ef000005f01adf000005f0e1df000005f031df000005f0a6df000005241aef00000000e1ff0000000034ff0000037831fd000005ec38df00000000a6ff0000000022ff000004341afb00000828387f000005e838df000006f838bf0000037038fd000007481abf001d24181abb000004a01afb000000001aff0000000000ff000004241afb000007e01abf000006ac1adf0000056c1aef000005001af7000004941afb000003c81afe00000000bdff000004901afb000005541aef000000000fff000004201afb000004f41af70000000092ff000007081abf0000061c1adf000005381aef000004e81af70000039c1afd000000000dff001293d41af90000000010ff000006081adf000004541afb0000000049ff001494181aeb001765241aeb001494a41aeb000008d5d0bf0000067859df000005f0f5df000005f046df0000075dd0bf000005f057df000007cd1dbf000007cc6fbf00000805d0bf000005643aef00000564f5ef0000056446ef00000524f5ef0000052446ef000007add0bf000005243cef000007411dbf000007406fbf00000740f5bf0000074046bf000004a41afb00000678bfdf0000000047ff000000004bff0000087a117f000008a2117f000005240fef000005181aef000005180fef00000001cfbf000000009bff000005249eef0000000072ff00000000f7ff0000000048ff00000896137f000005f00ddf000008281a7f000006f81abf000005e81adf000005141aef000004dc1af7000003701afd000008280d7f000005e80ddf00000001c0bf000006f80dbf00000001bebf00000000beff000003700dfd00000002097f00000000f1ff000007fd2ebf000007fc7abf000008e5d5bf0000055cc8ef000006352edf00237879d53f001573d477ee0021e829d53f000003987afd000005407aef000004f07af7000007887abf000006287adf0000044c7afb00000570f3ef0000057045ef000008ddd5bf000006b45adf0000075dd5bf0000063482df00000801d5bf0000057052ef00000570f5ef0000055cf5ef000007b1d5bf0000055c77ef00000754f5bf00000634f5df0000087a0c7f0021e84d277b0021e84dad5f0021e84dd53f87a134a4f57987a134a4f5780000057046ef00000690f5df00000724f5bf00000558f5ef0000078046bf0000060446df0000053046ef0000078045bf00000001e0bf0000060445df00000001c9bf0000053045ef00000001c7bf0000075446bf00000828467f0000055c46ef000005fc46df0000060845df00000554c9ef0020e608465f0018f60846cf001825d446cf001cc608469f001aa60846dd0018248846dd0000060860df000005547aef000008e1d2bf000006085adf000008d1d7bf0000055453ef0000055477ef00000554d1ef00000554d4ef00000608a9df000007487abf000004f4b8f700234879d23f0021e84dd23f0018255446cf0000074955af00000759d2bf00000805d2bf000004f496f70000060882df000007b1d7bf000007488ebf0000054c3bef000005743bef000004f4ecf7002155543b6f00000839825f001c45543baf0000074951af0017e5543bcf000007c555af001554e03be700000731829f000004f4aef7001554483beb00000899d23f000004f4b9f7001553883bed00000871d23f0000060807df0000080dd2bf000004f4b6f7000004a4b6f700000000b6f7000004f47af70021e84d825f0023084d825f0000079dd2bf000004f402f7001d2608469f00000749829f0000075046bf00000000c9ff0021984d157b000004f52cf70000074879bf000007b1d2bf000004f4acf700000554f5ef0021984d825f00000000caff00000748cdbf000008660b7f00000554cdef000004fccdf70000063079df00000001d4bf0000055ccdef0021e84d157b000004f4cdf700000608cddf00000748ccbf0000044c03fb00208608035f0000082e087f00000820457f00208608465f00000821825f00000820cd7f001bd608039f002086f4463f000004f8cdf70000077c03bf00000785bdbf000004d804f7001bd608469f000006f5829f000004d8cdf7002085e4465f001bd5e4469f00000550cdef0000060003df00000749bfbf000005103eef00000510cdef0018251003cf00208510466f001bd51046af0017951046cf00000718cdbf0000071803bf0018251046cf0000060944cf000007a1bfbf000005e407df000005e4cddf001bd55403af002084d84677001df52c46af0018052c46cf001444d846e7000006f4cdbf0018252c46cf000006094bcf00000721bdbf000004d83df70000068ccddf0000068c03df000000011aff000007491dbf0000070494bf0000061894df00000820947f0000060846df00000001d2bf000000011bff000007fd1dbf000000023cff000000012cff0000000094ff000007551dbf000008291d7f0000087a0b7f000008a20a7f00000000cbff000006092edf0000060894df000007b5d2bf000004f4adf7002348a1d23f000007492ebf0000074894bf000007991dbf000007046fbf000007046ebf00000001c1bf000007f0e4bf000007fc6fbf00000755d2bf0000060806df000006087adf00000001bfbf00000001bdbf000007086ebf00000708e4bf0013a4846ff3001945386fcf001ef5386faf0020561c6f9f002277086f3f001c248c6fbb001d25386faf001825386fcf0021061c6f5f001c55386faf001895386fcf001cd61c6f9f0014e4486feb0021d7086f3f000002d46ff7001c26086f9f00206709879f0014e4e930e7001f86ad1d9f001f86ac6f9f001fe709879f0015b50051e7001c26bd879f001f86ac589f0014e4e8f5e70014e4e846e7001c2695879f0014e4e877e7001c2639879f001c261c809f001c261d1d9f001c261cf59f001c261c469f001f07094eaf001874e931d7001c25d94eaf001874e880d7001ab56d1dcf001ab56c6fcf001fe7094eaf001ab56c51cf001c25794eaf001ab56c58cf001ab56cf5cf001ab56c46cf001c25494eaf001c253877af001c25391daf001c2538f5af001c253846af709875386f8f001c261d4e8f0022161d4ecf001f856c51af0019561d4ecf0018753941cf001f856d1daf001f856c6faf001875794ecf001ab50058d7001f856cf5af001f856c46af001875d94ecf0018753880cf001875494ecf0018753877cf001875391dcf00187538f5cf0018753846cf0000061c82df0000056c7eef000005387fef00000538a8ef0000056cd3ef0000061ca9df0000056c7aef0000061c85df0000056ccdef00000755c2bf0000063446df00000538cdef000008e1c2bf000006ac5adf000008ddd7bf0000056c53ef0000053877ef000004e8eef700000538afef0000061cebdf000005383eef0000061c94df00000500c5f7002378a1c23f0000070894bf000007f1c2bf000007f06fbf00000001fcbf001f861c6f9f000007e1879f001f85386faf001ab5386fcf000007e14eaf000008edc2bf000006ac81df000008ddfebf000004e887f7000007088fbf0000057451ef00000500e3f70021456c516f00000835ab5f001e556c51af000006514ecf0018456c51cf000007bd4eaf0015b4e451e700000815879f00000500d2f70015b45851eb0000089dc23f000006ac05df000004e8b9f70015b38851ed00000871f83f00000805c2bf000004e8b7f7000006ad2edf000006ac7adf00234879f83f0021e84df83f00000708cdbf0018256c46cf000007494eaf0000072dc2bf000004e83df7000006accddf000007e07abf0000053884ef00237879c23f0021e84dc23f000007e0cdbf0018253846cf000006094ecf000007a5c2bf0000061ccddf000008e5c2bf000005385fef0000061c80df000007a9d7bf000007e08dbf0000056851ef0000057877ef0014e3d477ee000004e8edf700216538776f00000841875f001c553877af000007154eaf0018953877cf000006254ecf0014e4ec77e700000735879f000004e8aef70014e44877eb00000899f83f00000538eaef0014e3a877ed00000875c23f0000061c07df0000061d2edf000006ac94df000007b5c2bf000004e888f7002348a1f83f000007e094bf001c261c6f9f00000709879f001c25386faf000007094eaf001875386fcf0000061d4ecf000007e12ebf000005007af700000809c2bf000004e8b5f7000004a4b5f700000000b5f7000007092ebf0022f84d875f0021e84d875f0021e84dab5f0022e84dab5f00000500cdf700000791c2bf000004e804f7001c2608469f00000709829f000004e8cdf7000007ec6fbf000007e46fbf0000049478fb0000000003ff000008286e7f0020a6ac6f5f0020a7e06f3f0000084e0a7f000007546fbf0020a7486f3f00000000e4ff000003c878fe00228828e77d001253c86ffa00187538e7cf000007e078bf000008ddc2bf0000053883ef00000538f5ef000005387aef00228829c23f001f84946fbb001ab3c858de0014e39c46ed0000061cf5df0000061c7adf0018739c46dd001c261ce79f001c2538e7af001c24e8e7b7000007e12bbf000006ac78df000007f9c2bf000004e8b4f70000056cf5ef000004e87af700228829875f001ab4946fdb0015b3c851ee0013a39c46f500000708f5bf000007087abf001c239c46bd0000000095ff000006b8e7df000007ece7bf000004946ffb0000078c78bf00000001e3bf0000062c78df00000001cabf00000828787f000000012bff00000000ccff00000002087f00000828947f000007e0e7bf000006ace7df001c24946fbb00000829f83f001874946fdb00000829ab5f00000000e5ff000003c87afe00000748e7bf0000082e0a7f00000000c7ff000003c894fe0000061ce7df00000708e7bf000000012eff000000007aff00000634e7df0000039c46fd00000000f3ff0000000045ff000006347adf00000001d5bf00000000cdff000000006fff0000000046ff00000608e7df00000494cdfb0018239c46dd00000829d23f0020a6b06f5f0020a7e46f3f0020a4946f7b0020a7546f3f0020a6086f5f829875386f4f0020a61d4e4f0022f829875f0013a39cb4f500213829875f001c239c7abd0020a695875f0020a538776f00229829875f001ab49478db0020a6bd875f001ab49458db0020a538f56f0020a538466f0021e829875f0013a39c7af50020a639875f0020a61c805f0020a61d1d5f0020a61cf55f0020a61c465f829c261c6f1f0020a709871f829c25386f2f0020a7094e2f829c24e86f370020a7093a3700237829c23f0014e39c83ed00213829c23f0018739c7add0020a75dc23f0018739c80dd00229829c23f001f849478bb0020a7f9c23f0015b49451eb0020a4e8f5770020a4e846770021e829c23f0014e39c7aed0020a7a9c23f0014e39c77ed0020a7091d3f0020a708f53f0020a708463f0020a61ce75f0020a708e73f000008a60a7f00000828e47f001253c878fa00000828f57f0020a39c467d829c239c6f3d0020a708e73d00229828e77d0020a39ce47d0020a474e77d0020a3d4e77d0020a39c7a7d00000828957f001e349478bb00000829f93f0018b49478db00000829ac5f00000494e7fb0020a494787b00000829257b000004947afb0000039c7afd0000087a137f00000494f3fb0018d39c7add00000829d53f0000039ccdfd000008820a7f0000039cc7fd0000049494fb0020a61c6f5f00000829875f0020a7086f3f00000829c23f00000828e77f0020a39c6f7d00000828e77d000008aa0a7f00000494e5fb000008292e7f000008287a7f0021e84ce77d0021e84d257b000008320a7f00000828457f0020a608465f00000829825f00000828cd7f0020a61c035f0018753803cf0020a708033f001c261c039f001c253803af001c24e803b70020a39c037d0018739c03dd001c239c03bd00000494ccfb000006acccdf000007e0ccbf00000000e7ff000000006eff0000039803fd0020861c035f00208708033f0020839c037d0000082a087f000008286f7f000000020a7f000008206e7f0020861c6f5f00000821875f002087086f3f00000821c23f00000820e77f0020a3986f7d00000828e67d00000820037f0020a5e4035f001c25e4039f0018751003cf001c251003af0017939c03dd002085e46f5f001795106fcf000005e4e7df0020a6fc6f3f00000829bf3f000005e403df00000709bfbf000005e406df001c25e46f9f00000709799f001c25106faf0000070944af001875106fcf0000061d44cf000006fce7bf0020a5e46f5f00000829795f000006fc03bf0020a6f4033f001bd61c039f001bd53803af001c24d803b7001bd39c03bd002086f46f3f001bd5e46f9f001bd5106faf001855346fcf00000614e7df0020a6f46f3f00000829bd3f0000061403df00000709bdbf000007086fbf00000001c2bf000004d839f7001c26146f9f00000709859f001c25346faf000006ad4bcf001875346fcf000007e14baf000006f4e7bf0020a6146f5f00000829855f000006f403bf000006ac03df000007e003bf0000049403fb0000074803bf00000828037f0000061c03df0000070803bf0000039c03fd0000060803df000000011dff0000000078ff00000000f5ff0000000079ff0000044c6ffb0000039846fd000008a2087f0000044c78fb0000084e087f0000039879fd000008211d7f000008206f7f00000820f57f00000820467f00000718ccbf002085e4035f00000821795f0017951003cf000005e544cf000008d1bfbf0000060058df000005e4f5df000005e446df0000075dbfbf000005e455df000007191dbf000007186fbf000007f5bfbf000005503aef00000550f5ef0000055046ef00000510f5ef0000051046ef000007a9bfbf000005103bef000006fd1dbf000006fc6fbf000006fcf5bf000006fc46bf0000068cccdf002086f4033f00000821bd3f001bd5e4039f000006f5799f001bd51003af000006f544af001bd4d803b70000077d4baf000008d9bdbf0000068c54df00000614f5df0000061446df0000075dbdbf0000052c5eef0000077d1dbf0000077c6fbf000007e9bdbf0000052c51ef0000052cf5ef0000052c46ef00000534f5ef0000053446ef000007a9bdbf000004d867f7000006f51dbf000006f46fbf000006f4f5bf000006f446bf
  | 8, 1 => 0x6c5975ac38780000065c387d000005ac387b0000000061bf000002c0385f00000108383f000005ac357b00000188383f000000005cbf000003e4385f00000194383f0000065c357d000003ec385f000003f4385f0000000041bf00000000367f0000000064bf000000005dbf0016b3541d7900000368387d001b6474387a00000000357f0016b2402b7a00000768383f001a14a438790000084d627b000fb3d446dc00000000fedf00000001bbbf00228354423d000006ac429f0000056c42af0000050042b70000049442bb000003c842be0000000086bf000008a0423f0011d1bc357a0000061c355f00000708353f0000039c357d001f865c383d001974943879001d25ac383b00000001dabf000007cc383f00000740383f001d265c383d00000228387e65d1d1bc3878001c265c383d00000660387d00197228387c0000066c1d7d001974441a79001d065c383d00000678385f0016b554386b001c25ac383b001875ac385b0016b538386b0016b56c386b0016b39c3879000005c8387b000005f4385f0016b524386b5acf51183878001825ac385b000006cc2b7e0017d5ac385b001b14441a7a0017c5ac385b0000084d107b00000000b3f7001da3d446bc000000009f7f0013d2402b760000064446fc0000027c2b7e00000001107b000002442b7e0014a2402b6e00000001cebf000002402b7e000008ad117b000003bc46fc0000000133f7002137496d3b0000000104fb0000084d6a7b000005b56a7b000000016a7b000005a41a7b0000084d6d7b000008a0d87d000007e01d3f00000000d87f001f83541d3d001253541d79000005b86ffa000003601d7d000003541d7d00000001bcbf000004146ffa0011d3686ff80000000132f7000006ac8ade002287e19b3d000007e08abe000004948afa0022866d25790000000105fb000008a1997d0000066d997d000008a19b7d000000008afe000004048afa0022866c8a7c002286ac385d001ab56c384f001f86ac381f001f856c382f001f85003837001f8494383b001ab494385b0015b494386b001404943873001253c8387a00000001d0bf000006b4385f00000754383f000005f0385f00000398387d000006fc383f00000614385f000007fc383f0012935c38790000044c387b0000077c383f00000600385f00000718383f0000068c385f000006ac385f000007e0383f00000494387b000007e0e13f00000001d3bf001ab0e0315d000006ac31dd00000748383f00000001d1bf000004441a7b00000000387f0000000000ff00000001cfbf00000001c0bf00000001bebf00000002097f61d1d1bc385a00187538384f0014e474386b7091d1bc383a001c261c381f001c2538382f001c24e83837001c2474383b474e71bc38780018739c385d001c239c383d0011d1d86f7a0000061c765f00000708763f0000039c767d00000634385f0000039c387d000f51e8387c608f5118385c000005e4385f000006f4383f0000060c385f00000620385f00000000767f00000444727b001494441a6b000005ec385f000005e8385f000006f8383f00000370387d0018d3d47adc0000084d267b87a134a4f57800000001e0bf00000001c9bf00000001c7bf84d063d44678000004a4c9f90012e31846f8001823d446dc000006385ade001553d446ec0000074955af000005603bee00000839825f0000074951af000007c555af00000731829f00000899d23f00000871d23f00000000b6f7001d23d446bc00000749829f001554a4cde900000001d4bf000003d479fc0000082dd23f0012933403f8002083d4467c00000821825f00000865137b001bd3d446bc000006f5829f00000865df3f001793d446dc001443d446ec0000060944cf0000082dc63f0014b3d446ec0000082da35f000006094bcf00000001d2bf000008a1ff3f00000001c1bf8a11d3546f78000008a0e47d0012e3086ff8001d24746fba000004746ffa001293346ff800000001bfbf00000001bdbf709874746f9a002287e1ab1f002287e1ab1d7094e4746faa002287e1403761d4e4746fca001c261d4e8f002287e15b2f002287e15b2d000006c058de001873d446dc0000063880de001f84746fba00000001fcbf000007e1879f000007e14eaf0000057c51ee00000835ab5f000006514ecf000007bd4eaf00000815879f0000089dc23f00000871f83f0015b3d446ec0000082dab5f000007494eaf000006094ecf0000082df83f0000054877ee00000841875f000007154eaf000006254ecf00000735879f00000899f83f00000875c23f0014e47477ea001c24746fba00000709879f000007094eaf0000061d4ecf00000000b5f7002287e0f53d001c23d446bc00000709829f00000865f83f002287e0f23d00000001e3bf00000001cabf00000002087f0000047478fa000004ac6ffa00000829f83f00000829ab5f00000001d5bf000003d446fc00000829d23f829874746f5a0020a61d4e4f0020a5391d6b0020a61d1d5b002286ad2559829c24746f3a0020a709871f0020a7094e2f0020a7093a370020a7091d3b00228494f2798291d39c6f780020a708e73d0020a474e7790020a474e778000004ac78fa00000829f93f00000829ac5f00000829257b000003d47afc00000829d53f0020a4746f7a00000829875f00000829c23f00000828e77d0020a3d4467c00000829825f00000829157b0011d39c03f8002084746f7a000000020a7f00000821875f00000821c23f00000828e67d001bf4746fba00000829bf3f00000709799f0000070944af0000061d44cf00000829795f001bd4746fba00000829bd3f00000001c2bf00000709859f000006ad4bcf000007e14baf00000829855f00000821795f000005e544cf00000821bd3f000006f5799f000006f544af0000077d4baf
  | 8, 2 => 0x1107b000000016a7b002287e1ab1d002287e15b2d002286ad25590020a474e778
  | 9, 0 => 0x1970e3fc005ac38ff000000e3fc005ac1dff001b60e3fc005ac2bff001a10e3fc0085c31ff0022b06bfc003d416ff001903d7fc006d07aff0000058bfd823ec46df001d218afc001182fff002190bffc000002fff001f711bfc008a016ff0022d05bfc0000016ff00166477fc006c894ff0000059bfdf835442bf001f810afc001bc35ff0020a0d7fc0000035ff8286f0d5fc00828357f001b81bffc008e803ff0000068bfc0066c38ff0000066ffc000e01dff00000077fc0085c38ff001970c7fc0067038ff0019706bfc005b438ff000005b7fc000e02bff000000affc0088c38ff0016b06bfc005bc38ff0016b0c7fc005cc38ff001b106bfc0047438ff0006f0e3fc003d438ff000460e3fc008802bff000d90affe1e84c2b7f8794a0afbc00768f5bf0021328bfc0087818ff88e1e0adfc004a42bff000c10affc008782bff000900affc004742bff0006f0affc003d42bff000460affc005282bef0000076afc003742bff0000028bfc000ac18ff00000063fc002982bff001f611bfc0042846ff5b50606bedf560846df001d25b6fc00684cdff001a100ffc007d4f5ff001f511bfc005b41aff001a13d7fc0068446ff001715b7fc0000171ff0016d1abfc000006aff0016d477fc005b46fff0016d3d7fc005b446ff0022a077fc002501dff8a217075fc008a09dff0022805ffc008a01dff000d5077fc004741dff0006f077fc003d41dff00046077fc003841dff0009d077fc000009dff0001d05ffc0000017ff001b71bffdb63686ffd000da1bffc003686ffd66cd50c7f5c26d86fbf001f866efc006d8e7ff829b61bdfc00829b67f001b600ffc006d91dff001b61bffc0066c31ff0019d66ffc000019dff0019b22bfc0066c8afe0000022bfc000008afe0019b477fc0066c6fff0019b3d7fc0066c46ff000940e3fc000e031ff000000c7fe2835438fd6acd50e37c006ac38df7e0d50e2fc007e038bf494d50e3ec003c838ff001250e3ec0038438ff00000387fc0035c38ff000910e3fe1e84c387f0003806bfc000001aff878900e3f93d24038f7001d20e2fc0046438ff000f40e3fc0029838ff0000029bfc0088038ff001180e3fc0030838ff00120477fc0047422ff0003808bfc0000022ff0020a0e3fe0a1bc387f0020a0e1fc0065c03ff61c6f0e37c0061c38df7086f0e2fc0070838bf000e70e3fce71bc38fd000e70e3f4001d86fff000760e3fc0000076ff0006f037fc008a838ff000f00e3fc004b838ff0007a0e3fd293d438fd84d290e3ec003e0f5ff001290d3fc000e034ff000000d3fc0082c38ff0016b00ffd8211838df001820e37c0033438ff0003800ffc0014046ff000500e3fc0000050ff000c103ffc0035438ff8a0e10e3f40012c38ff00228387fc008a2177f0016f1bffc0084ce1ff001b911bfc00474e1ff000e11bffc003e0e1ff000e112ffc000004bff000f5387fc0038446ff354380c7f40038431ff384380c7f40038431fd002280e3fc0028c38ff000d50c7fc0035431fd002130c7fc0024031ff0011d0c7fc001bc31ff000f50c7fc0011831ff002280c7fc0028c31ff0000028ffc000c40fff000900e3fc0048038ff000720e3fc003e038ff0004d0e3fe1344438fb0011129bfc00384a6ff000a60c7fc0084ca6ff001a711bfc008a0a6ff001731bffc004a4a6ff0011111bfc00480a6ff00000483fc0029872ff000001cbfc003e0a6ff000003e3fc002984dff00000137fc00878a6ff0022b84dfc0067046ff0011d29bfc002986fff000f529bfc0029846ff4183806bed290e01afb0011106bfd110e01afb0011106bec003841aff0003106bfc002981aff0002106bfc0084c38ff5243806bbc005f038df000de0e3fc000e00fff0009e0e3fc000e00dff0010606bfc004181afb0022806bfc003541aff0012906bfc004a41afb000c106bfc008781aff0009006bfc004741aff0006f06bfc003d41aff0004606bfc0084c1aff0014906bbc00001d0bf000de06bfc00000bfff0001a03ffc000000fff0009e06bfc000009eff0001a037fc000000dff000f53c7fc00000f1ff0023c3d7fc004a495ff0022a4bbfc008a87aff001241ebfc004b87aff002133cffd8d4a47adf001573d7bd2939c7afd001291ebfc008787aff0021a1ebfc00000f3ff00091117fc006347adf00000756fc000006fff002131ebfc00000e7ff000f51ebfe1e84e0a7f00000829fe2a87a137f84d291ebee2087a137f4a4f51ebf61e84cf57f87a134a5ec0024446ff0012d3d7fc0084c45ff00046117fc0000045ff0011411bfc00000c9ff0010811bfe1e84c467f000c611bfd293d446fd84d8211b7dd241846bf6998211b7d553043bef6092911b7d8224046df6398211b7d8216846df608f511b7c00608f5df0018211b7c0075dd2bf0018216b7c00554f5ef0015511bbc007b1d2bf001550efbc00748f5bf001d211afc0086c46ff0010711bfe1984c467f0012911bfc0082ccdff6091511b7c00554cdef00213337fc0046446ff00129337fc0045446ff0021f337fc000012cff001281e7fc0000079ff00000477fc004547aff00000253fc00878cdff0021e82dfc0047046ff000cd11bfc0082c03ff0004400ffd8211803df0018200f7c0033403ff0011311bfe08118037f00208119fdbd11803bf001bd11afd7911803df0017911b7d4411803ef0014411bbd3611803f70014b11bbc004751aff0000046bfc008f11dff00228257fc008812eff0023c4bbfc000023cff0022a257fc0000095ff0022a253fc0042494ff0022d253fc008a11bff0011d11bfc008a094ff0011d253fc0046c94ff0000046ffc002506eff000f4253fc0000046ff002203d7fc004a494ff0022a477fc008a07aff000004bbfc003d4cdff00000337fc004b91dff0011d1ebfc004b8f5ff000f5253fe1e84d1d7f8a21e84dfc0088046ff0010911bfc004b846ff0009411bfc008a0cdff6091d11b7c007491dbf0011d337fc002506fff0012b477fc008a06eff0006f1bbfc000006eff000e41bffc00000e4ff000c21bffc008a86fff000d71bffc004b86fff87a131bdfe134a46ffb000f41bffd821bc46df001d21befc003346fff0007a11bfc0000003ff8ddc21befdab35458df61cf51bf7d871bc46df75dc21befd872006fdf8a1c21befdc23546fbf7f9c21befd5b35451ef4e8f51bfdd3a1bc46f7538f51bfbd4e1bc46ef7a9c21befd4e1dc6fef7091d1befdc23d46fbf7086f11afdc261c6f9f001c261e7dc25386faf001c253abd875386fcf0018753b3c008ddc2bf001ab1637c0061cf5df0018711b7c0075dc2bf001872037c007e11dbf001f81befc007f9c2bf0015b147bc0056cf5ef0015b11bbc00538f5ef0014e11bbc007a9c2bf0014e1dfbc007091dbf001c21befc00708f5bf001c211afc008a46fff000d61bffe288286f7f828d51bdfc003d46fff0007a1bffce71bc46fd0020a39ffd8739c6fdf0018739f7dc239c6fbf001c239efc008a4e7ff000004affc0049478ff000001e3fc008a0e7ff00228829fc003c86fff001251bfec0084ce7ff0012511bfc00474e7ff000e71bffc00000f5ff000e71ebfc000007aff000f539ffc0039c46ff000e711bf6298286f7f828d61bdfe138286f7f39c7a1bff60a4746f7f828f51bdfe0a1bc467f829871bd7c00829875f829c21bcfc00829c23f828e71bdfc00828e77f828e71bdf400828e77d00229829fc0049478fb00213829fc0039c7afd0020a475fc008286f7f0020a3d5fc00828467f0020a00ffe0a1bc037f0020a00dfc001b403ff61c6f00f7c0061c03df7086f00efc0070803bf000e700ffce71bc03fd000e700ff4003986fff8206f00dfc008206f7f5e46f00f7c006fc6fbf6f46f00efc006f46fbf0022800ffc0035403ff0021300ffc0024003ff0011d00ffc001bc03ff000f500ffc0011803ff0020800ffc00000ccff0020800dfc00002087f0017900f7c00001bfbf001bd00efc00001bdbf
  | 9, 1 => 0x65d6b0e1f5975ac387b65d6b0e1e40065c387f0016b0e1fc0000038ff000000e1fc005ac1dfb001b60e1fc005ac2bfb001a10e1fc0000162ff000fb11b7c0074862bf0000018afc000002fff0000005bfc0000166ff000d510afc007e042bf0000010afc0000035ff0006f0d5fc00828357f000000d5fc00001a2ff8a1970e1f597354387d0000066ffc000001dff002170e1fc0065c31fd84d6b0e1edb1240387e000005b7fc000002bff002230e1fc005ac1afb0019c0e1fc0065c1afd65cf50e1f597118387d0019b0e1fc000e01d7f65ce10e1f5970e0317d65d1d0e1f5971bc387d66d970e1f5970e01d7d65ca60e1f5970e01a7d001730e1fc006c41afe5ad290e1edb1118387e0016f0e1fc005ac31fb5ad1d0e1ed6b1bc387b0016d0e1fc000e02b7f5ad110e1ed6b0e01a7b5acf50e1ed6b118387b5b56b0e1edb10e02b7e5ace10e1ed6b0e0317b5aca60e1edb10e01a7e878900adf800768f5bf000900adfc002402b7e002130adfc005282bef0000076afc00000a2ff00000063fc0088c2b7f7d4f511bf0007496dbf002135b5fc0084d6d7b0016d06bec0000171ff000001abfe283541d7d000d5075fc003541d7d00217075fc000009dff0000005ffc003686ffd6d91d1bfe8007e19bbf0020a6d9fc008a19b7f0022866df40066c31fd00000677fc0066c8afe0000022bfc000008afe000000c7fc00250387f000380c5fe28354387d001ab0e37c007e038bf001250e3ec00000e1ff6acd50e17c006ac385f7e0d50e0fc007e0383f494d50e1ec003c8387f001250e1ec00384387f0000006bfc0035c387f000910e1fc000e01a7f878900e1f80074838bf0000029bfd3d2403877001d20e0fc00464387f000f40e1fc00298387f002200e1fc00460387f0000008bfd1d1bc38fa0020a0e1fc0065c03fd001870e37c0070838bf000e70e3f40000076ff0022a0e1fc003c0387f84d290e1ec0000034ff3d4460e3f00082c387f0016b00fec0060838df00000143fc00354387f8a0e10e1f4008a2177f0016f1bfec000004bff354380c5f40038431fd002280e1fc0035431fd002280c5fc00000a3ff000900e1fe13444387b00213299fc0000120ff000001cbfc00000f8ff00000137fc008ae137f0019c11bf5060e01a7b0011106bec0084c387f0017c0e37c004181afb0012906bec0084c1a7f0014906bbc00001d0bf000002fffc000000fff0000027bfc000000dff000c20e1fc000e0227f4746f0e1ed1d1bc387a61c6f0e17c0061c385f7086f0e0fc00708383f000e70e1fce71bc387d000e70e1f4001d86f7f000760e1fc00000767f0012e0e1fc001e8387f4a4f50e1f4000e0347f3d4460e1f8f5118387d3d4460e1f182118385f001820e17c00334387f0003800dfc00140387f0004b0e1fc00384317f384380c5f40028c387f001200e1fc001c8387f000f80e1fc00134387f00111299fd290e01a7b00111069fd110e01a7b00111069ed490e01a6f0017c0e17c00378387f0003803dfc00278387f00038035fc00000f1ff0012e1ebf80055cf5ef000003cffc006347adf00000756fc000006fff0000039ffc003d47afe00000829fd293d47afc000f51ebf4003d47afc87a134a5ec0000045ff00000327fd293d446fc87890119fa133d446fc84d06119ed2e3d446fc3d4c611bf1823d446dd608f511b7000608f5df0018211b7c0075dd2bf0018216b7c00554f5ef0015511bbc007b1d2bf001550efbc00748f5bf001d211afd153d446fc00155337bc004a4cdfd000004b3fc0000079ff00000477fc0000094ff0021e82dfc003d046fd3d44600ff00060803df0011500fec00820467f001bd11afc005e446df0014411bbc0052c46ef0000046bfc000023cff00000257fc008b494fe0000046ffc0000046ff000004bbfc00000cdff0011d1ebf8003d494fe474f511bf0007491dbf000001bbfc00000e4ff8a11d1bfea283546f7d4b91d1bfe91d3086ffa474f51bfe91d1bc46fa3d46f11bf0007486fbf001151bfec0000003ff61d1d1bf6dc24746fbb7091d1bee9c261c6f9f001c261e7dc25386faf001c253abd875386fcf0018753b3c008ddc2bf001ab1637c0061cf5df0018711b7c0075dc2bf001872037c007e11dbf001f81befc007f9c2bf0015b147bc0056cf5ef0015b11bbc00538f5ef0014e11bbc007a9c2bf0014e1dfbc007091dbf002287e0fc007086fbf001c23d6fc0070846bf474e71bfe80061ce7df001c239efc000012bff000001e3fc008a20a7f001251bfec00000f5ff000001ebfc0039c46fd8291d1bdee0a4746f7a829871bd7c00829875f829c21bcfc00829c23f0020a39dfe0a39c6f7d0020a39df4008a60a7f001251e3ec0084e0a7f000e71ebf4008291d7f0020a1bdfc00828f57f0020a119fd1d1bc03fa0020a00dfc0061c03df001c200efc0039c03fd002081bdfc006fc6fbf001bd1befc00000ccff0020800dfc00002087f0017900f7c00001bfbf001bd00efc00001bdbf
  | 9, 2 => 0x1975ac3879000000e1fc0000062bf0000010afc00000357f000900adf800001dabf002135b5ec003541d7d0022866df4000008afe001ab0e17c007e0383f001250e1ec00748383f00000742fd1d1bc387a001870e17c00708383f000e70e1f400000767f3d4460e1f000608385f00111069ec005f0385f00000756fc000020a7f000f51ebf1823d446dc7091d1bee800709879f001c253abc0061d4ecf002287e0fe0a4746f7a0020a61d7c00829c23f0020a39df400002087f000006fefc00001bdbf
  | 10, 0 => 0x65c38ff5ac38ff00038ff00000ff8782bff0002bff7d446ff0016dff8a01dff0001dff6d86fff0019bff8a038ff35438ff84c38ff24038ff47438ff1bc38ff3d438ff11838ff38438ff000e1ff0e031ff00031ff29838ff000a6ff0e01aff0001aff84cf5ff4b8f5ff4a47aff0007aff4a4f5ff87a137f84c46ff41846ff4a446ff24046ff3d446ff60846df001d2bf45446ff000cdff11803ff8a11dff4b91dff0012eff8a094ff00094ff474f5ff47446ff8a06fff3546fff4746fff3d46fff1bc46ff7086fbf001c2bf39c6fff000e7ff8286f7f0020a7f1bc03ff00003ff
  | 10, 1 => 0x65c38ff5ac38ff65c387f65c387d5ac387f5ac387b00038ff00000ff8782bff0002bff7d446ff0016dff8a01dff0001dff6d86fff0019bff8a038ff8a0387f35438ff354387f84c38ff84c387f24038ff240387f47438ff1bc38ff3d438ff11838ff38438ff000e1ff0e031ff00031ff29838ff000a6ff0e01aff0001aff474387f1bc387f3d4387f118387f384387f0e0317f298387f0e01a7f84cf5ff4b8f5ff4a47aff0007aff4a4f5ff87a137f84c46ff41846ff4a446ff24046ff3d446ff3d446fd3d446fc60846df001d2bf45446ff000cdff11803ff8a11dff4b91dff0012eff8a094ff00094ff474f5ff47446ff8a06fff3546fff4746fff4746ffb4746ffa3d46fff1bc46ff7086fbf001c2bf39c6fff000e7ff8286f7f0020a7f1bc03ff00003ff
  | 10, 2 => 0x65c387f65c387d5ac387f5ac387b00038ff00000ff0002bff0016dff0001dff0019bff8a0387f354387f84c387f240387f000e1ff00031ff000a6ff0001aff474387f1bc387f3d4387f118387f384387f0e0317f298387f0e01a7f0007aff87a137f3d446fd3d446fc60846df001d2bf000cdff0012eff00094ff4746ffb4746ffa7086fbf001c2bf000e7ff8286f7f0020a7f00003ff
  | 10, 3 => 0x65c387d5ac387b00000ff3d446fc001d2bf4746ffa001c2bf0020a7f
  | 11, 0 => 0x38ff3d7fc46ff477fc6fff
  | 11, 1 => 0xe3fc387f3d7fc46ff477fc6fff
  | 11, 2 => 0xe3fc387f3d7fc46ff477fc6fff
  | 11, 3 => 0xe3fc387f3d7fc46ff477fc6fff
  | 11, 4 => 0x387f
  | _, _ => 0

def frontierRead (k t i : Nat) : List Nat :=
  let width := 8 + 10*(12-k)
  let code := (frontierCodes k t >>> (width*i)) &&& (2^width-1)
  let rs := (List.range 8).filterMap fun j =>
    if code.testBit j then some (frontierRawIds.getD j 0) else none
  sortFrontier (rs ++ frontierIds (12-k) (code >>> 8))

def frontierState (k t i : Nat) : List Sig :=
  (frontierRead k t i).map readWire

def tableData : Nat → Nat → Nat
  | 8, 0 => 0x2d8400000015f700023b943c66b35385f99119d549781c00000000005245d916a251311cc40f933b80000001e5a0000afe000254000029d2000000087106f30001b0900028290ec400000000000000000000000074e40008f840001704000000119a00013093b3c0000000000000000040340bf6e044a722c00000001c4304440007524000000000099196e60eed12e166c0000000cfc0000000000119f000248969e0000000242300000000000000000145673c420638842700001de000000001065077a16c0008e045b033d80000000ed123e21390000000000000000000006bde2d1950589100000004be4000733cb9478cdb413fae11124d51a9521c8d11db630300000000000000000000039190ab000000000000005a98edf0000000000000000007e915ac000000214a00000000000000487c0005c05d1700006311ac40005d84000a504000000000000000000000000000000037b40000a78dbe196800062f40000000a0e9e8554c04140000000ddb76163440cbd2a294140006e5a43f0000e20000000000026bf0000056451ca410001df9000000000009ff5d5400000000004b9000000022612b50000000000032980000000000000000000020a300018a9000000000000c90001b374f9898100000000000000000000000000000000000000118982156df50ca229000000000024f1000000000000000002569000000000000006dac89ca7867b008040000001b290b35dd23eb460d00000001ff40004638ad374240df4b3c00084c83bf56e45770000000000000008480008ae57c76bfe4fe2784d27054a1a19d1d7450000000296a02246ac0006665ca900008f00000b3e8490b2941f576d67791b34f211b22c0e17c9c7ca0a7f0c9a60001ff14d84ef10001fd26a85ed15adcaf923fe7a40c7c6bf8964d69211000000000000000000000000031640006dd400009900000000000000000020916840000000000000000021cc30f00009155e6c00000000cc400000000000000b3c0000000517c0009ae428e932615193f5d21000000000010e4000000000009d7a0c59b78c3000000006890001c693ee887127a61817ae605c9371ce176a6411399def900f60934da64088a980004a2424953bca0437a400097d408558e444440840440b3000000006e90001d7984ade3132d4ac305e85c90001d07000000000024613222191652406629843c94df0f5126454ca888d11180a66e59d0d72d66040008d458a560797d167bc65905ae01c036529f000292a00000000b3c0000000000000088900000009e68000000000060c41ea34c01aa1465d660000567095d9715bec00002480000000000000066909603b3000228d65a4c9992a80000000000445e73f0c65ffc48e625e4d3c046892515074cd6916ae40000001f4900029520002717000000044ec2090de590b000000007a4ee9926a499770400000023f3000000000006490000000000000016e40000001d0400000000000db100005970000000000000098e608b1824000647ce5b00025850000000000000000008a156580004d91f79a4d0000000000010c40000000ba4000000013cc000464e4767fd8a51000000000028b100000000001e7ca5e872d00000350000f240005da17fa400037e41910000000000196f966448a0000ac174a69f1000000000000006b9048c5a6c000000000092480006abc00001918790000000000000000000004f91cf9981cf9946f4393440e2e4a735d620b2863b6325e53627539e0d1e62068dc0a43d4de393a7e5e70d248417f926de0000ab32e663838b84d9f92f8f4f8a55b77098e4a1000000020240006402824646d285000000000004e98de21f300000006ba42dd77c24f495b5a6178e8afb00000003c2000043380000002817598400000000003fa56540001e8921fc5b482a4000000115b000000093640004fa451400000003b645f85b7440b832df2107ad45d2ce1a747d062813f04000689df5b70b0d830f845276c44ebb2f7cb510000000000180f2a04000000001700026c8000188000007218b2d3709ff0a990000000853240f0002572126a11a0bbe6a77f040f30000000970da2909059d10b0c000000218a1b1800011e400054d000000008eb000000000019c115a400000000000000a9196f54160000f750000000a2703e92708ec749bc21172645bb0bd4000162e38b000179d000091945726831e858414f7616c000289800000000001ad35a1a0710000000000000000000000000000069c000000000000015f9000000000000000000cef0001f859761dd192947c33368d9161d690244d4000000000000013d30000ef700000006ce4b963e293591a448e5000090126f00000b6e1d90002451300400000002670000000000268700000000f5d8218e2479c3c000003b0400077a000000000003a0400000000007acd03941056e8000000000000005e2970a000160d000110f22c63771f0444320656190000f1a00000000551afa4b6c000000196100000000000000000054100444c9a224482000000000000004491479000000000000002d0e6e1089d4510ba5d2b198c5de3420000000000018a40000164000089071103b485792440001c2d63200001e40e2d44a44e69230000fc70464d2100a4c912a25e1900001d34d051c162b5fbb00002f379918300001e4f1aa5d890000000839c000000000005401d934ede1782c60db0000927000000000029a40000f0c312c0000001a770002069442400000000000000a5c805000054e21381b8db570002053118400000024204f1ccc0192c65496c5f837e261a7197187c8cc49f966440000000d31878c00070c542995c47d300000000000000a26c0000000000976c000000000000006139d649032dd94bf6cc400000000002355785723c0004ff40002bfc0000001faf12865c907780000001b611ade68d000020e59c82601ccc00006056ac00026758dd4e699f84f841b04000000093d00013380000000545114e000250a0ca4f3a193d1b9000090471259790d4c0000000000000000000017d70000000093db7e5f6545347c49ac286667d00021c9670e11c0b6590400000000000000993a53c0001c6100007058255cc90000884097df6b85d0000319e3ba0864000946800012ec0005798e5251800008bec00014fdc594684f473390000000000033055236004000571e62956aa3fa19e50d20000000000000000000006a440000000000265c000000000081e400099b1029000000076e4a0c02c400000000000000000000000000019bf61fc00000000000000b4930b5b0f000000043025910a300000000daaa2ae1362df08d3867d6b24e089564950bc91f8415b3a381dc0d14a3a9ccc9791205bc129aca71a0640000002311893e851662400000000000000000000000007e24b45e49ae700021f49a24000154400000022c99ef0df4409dc9807d09cb2c4095a0ea4000323d1814c7d19b000171133963da00000000000000000000032b0000000000000014f10001b5933ce63f03f60c17478000000000000000006220327000000000000005c825c200000007dfc35710ddc408104dfc70840000001d3c7d0ccf23fc54d1679dcfc23d0000826d0617cddfb1266417150fd2057bc4b175d6e5149999160887de9b87e80004b0435d000000055742510000000825c000791c000000000000010030000000000100f00000002305dcb6ea5dfe23300834264c73000139f0000000285c17300011b118f40004768000000171c00000003d5400000008f95e6208168c50eb2430b9f960400013c63047e34c1175be3686b8449c00000000000000000240900005d1379400000000006fe691e1dcd2f100018da0000a730000000000000069249d90001a93000023b8ca60bb80dc0001cbc8ab3d85d1c44de78a00000003b9d21737ac000000000000000008b660a188fc8624985ebf000000000023330000000a0d0000000000016cd55200000004aa00000000000000075384889f1146c000000210382500000001a6a30c800049c5651753d4a81d258297fbe05a1bc5ee10b261b3000000022021b107454036825125851a63731e5af133085611d8c0000b15ea17d7e61e61a40001734000a5a40000000427774000000000000000000000056f00009c887e4a1380aa73900019c700000000000ee1196d332000000000028860002711000089390a69bc00007091a65c191e9cf1718852188c161eb48240002eb4000000264b2564000000030747e40006b041b900003a10001542000000018040000811ce98f403f10000000337463f2bd80008ea40a900025d200015a294f8000648c5e872740000000000000000055701fb00000002c3c0005d349be3734c21084df1b5cd4a7b0001ec391a64e4000000000009701e78c61000090b00000002e9e529000000000015740000611000000000003993ea5f193c100005ee400000013e10001339396544b00028ba1dddd1f55556894024de101b8af4000258e000116400000000000efa2ba1b1f00004c16d9ca1f000000000026dc00017e17072144a25199700000003764000000000039ac19955c08633d2400000000000000000810c00024c400017f40000a8e3325a762697c2c90908e437d743e5b72c9e2173331b947f3d03e0b1e88a7981ff76c944e1486934900025770001af96305649883c0000ead0f3157e6d10835c6ba07962c8565081a245a014ead79083c4bf12719a994cb25a60c25b21363a1e4780487aa2e4db41eec6df00002083fe4a7f000000000000000000000000277b0dc4000009c0001644000315400000000006db0000000023c0000c9578bddd900000000000000000221b4aa55f500000000000000000000000028710c5e50100000000fe40009db05183e5800044f4a3e000000000000004c1c00000000000001a72000042910e5c0340650a98de5d641b5a7943d019872a2e5cf183dafb01b1c518c1c72582fc0e897c400000028625ca22c4891cad73d14a9a00000008d0427d176400000006af21842290001aef0001f2900000002ce49860000000585c0000000000088c00012c40000000000000000012e4a9300000000acc0008085b9f454c00018cd90800024ad4e566672ee5a9f79d0f4b3714def24740008dc6511182c000a0000000000000a3110a7000036d56227299dc61d14369dec8bc655d00000000001c719f440009c0502500000000001a41000000000000008f08000000020700027db73640005304d7720d4000306c00020c667029a400050200000000000000000000000005844000000157f63c4ffb0001e296cfc00003c483a0000c318d76112100c0009ee40000b12221040c00000000000c46562000000024b5e09000082b000000048f169400008d900027b80000000000047143fe1f63d0400000024818b314b3250c00000000003e39fc70b9e7219eb00000000000000087e00007ff4ae443b03891438ef45c600026f9000000000022a900007cd407c27b2b925e217680008be400044b661f60dd0b374bcb1f71700005e2400061aa0754de4a27043400085400000000000000000000000007b64000368478700000002e6c00000000008fac0000000f690ee40000000000000220000000008ac400056a68c29489ef748c400000021ec6d24b7407852ea1a94000000000023865da6df1001881d398248c0003f3400000004846cbccf44f3088200008e08124fe10f0501d674894e00ed2a014e47511771b28000000000020d4a4380003c880005b440005074000952904a000000043b40b90001db10000000000000006fc0005e8c00000028490001d0b473206f9ec800000003211ebc000000201900000000001898000000000000006e109d18a25ac74c458a1656546721750f925fc0009ced3b18ca9277a649d0158260280000000000000000000000b8400000000000d04a7d8bf18594e65bd105621d60000891072540d0b080000000000185dec92a6e9c60e0deac8eb20e10000a215064f3119c4fd90002698848c4547ef597a00000000000000000218c1e057e939f102c81946a16b9938900027e5000206155905340001091351800084d1a817dc51a3689836900000000000000000000000000008330aaf812a803866496179a02051865f67590400020e61c17f259a10000ed30001ec5589c80744a498a0001cef766c00011255b70001eef21468a43f2697100000008778000022dd31673ce3500004113226679479625c3bd53a700028a917d000068c0000000000000008d00970389749e7491c6c00000000000885fee00004836a3d1ca000000078dce73384400000025d100000000f3e70b43bd23000022916ac449432d18e2a38a5950000000000000000000008f0200155ac0000d2c00052a49690000e613c4400000000006c0c000000252600026af8245eaf27251e27e851d300000002afe6a600000000001e8b8b8c1b0132da2f0002299000265c809cce05fe504359e83b59fa68cc0265f1f000166b44fca8f3805e7e5cf51fd8c40ead244400081649ef0001c1400000002844000322d35137249a447a5d1100000009fd24e56b6400090000000000000362400000000001ae40001da6339212000000000007448b69000023f3f4e4b969fde993a40000a2315ef3e98e947d3c00000004e745047392804000000289a0001d5980e9a753849fe243d66e900017b46c9e23900007d923f6004000288071cd5df0001a4f40cda32204c849460e1e6404c00000004537ce45d50b7cd7946649db22c800000000000000000000000000000000000000000000064e65d56a392d77465c410000e491fcc000317515483e5629000263131066c200025af04da3ed7f5e2db719d29100000007d640005b369d14ca442191651051d656af00000000001f5300002d15dc51132190000000247d0d3ca2f000143b10bc44c0000cd88db400082640000000ab9000000000000001bedbf717b5897000000000000000000000844c4927fe400093b45733c096ee000010100000000001c020001acf7c5c00094c800000000002be000000016bb9958000000000018e40000001b91000000000000002fe40000001c0c06851ed0a941610000635370d0c82c240004f62417541a37b3d34000000079371fdb2461c87b30000000000000046eda510000000387e83a000000000002373ce400000011d4212d27f61364d189e44d74fbc1323d9400051053f39b690f700000009ab400084643d1000101128c00002f85a949d84a878150727a289b263dc65b53bbe809a08404c0d6493937897bf21a21c67dec5e43f0dddc0000000953800000003d90001601000050f68e610900019c41dc520320c8000000240100011840000000657c0009564000000000000000000000d527884ac901d9b8f04f800098442c1000000000000000001e9109318e6540628530a4e0f0002047a3c40000001d5111a455900001300000000000000005a441f72851a09b24f860002366271000034345080000000000125c0001a3c000000000006d967850310000000052a0e50001c91000000093181df5b0c000a36698e38f5e6a65040000000000897c0003525edf000025512a58b195940001a554dd02dc00000013972bc877f9bad40b90b000087b800020a400025482950000000000063700000000000000000000090dca3c00019115234000220c0007610b409a65301193458992a0000170887d6ed46d497bcf5d0000f916f2cf59185475746d17cb69c502aa3e8000000086725045bd6d45cd194d60e9724a2a215f188e76ddb7f1be400941acfb21d859f71fe546f3e84000000000000000009a4cfe3000216100000005044000000000006de3a40000459000000009647410000000000000000014fb0000000000000000012240000000000000017758d10000dd1452826f95466250000000000098c00017c10000000000095c8dc80000cfc86f225c0000a7286963b91d26f911795e65d4194ea5390dd400000000000001f010000000720467700006472cd9bc9000000000026f14db40000000859000000000000000000000000000007d4000210de81a4e800000000001404bc8000000006c400051dc0c10000000000000000022c3000000000011f5000000000000000001cc17b5c000990a79907f000081ac00000024d5000000000012410000000894878c77fc7eb0d0c0006844b896daa1ce66a40004b8555321a400000000d784a400000000002ad400000000003aa00002109a21816d17e41a464123b0efc602480f5fc49429968b3a45645b11a3cf29381104058a233a56e0000907c00037f48cb24a4d233e89be91258a4a7f81aa931c682c76bd6598fd4f1c906800009d400003eca9c9189df1a21c000000000055015d7846de1f98895090d440000bed05d347000000002690000000000000067fc0003d5c8be8a6c00068900000aae2e900023970ce44c5947800000000008b940000001abf49252485de4879699cf090984de61aac00000016f1000035b000234900008478944c0f223c5210000000000036532367510000000705c000000000019be3743b2608900019f950c44ef52724244764000000021aa6699310505a6959aa7c446447d12d64ca804948117e2e83b423e1635b05861000000000000004e0c0000000000000223100000001ca45e0000053d26e9cb993342380000000000094a6e864f90000000983c0d16dc4d0174e91d14f642cb8ec41212e4a31c3e761d4563650606d0f7d0001cfe15c5b046724000275400000000000000000000044264a8000000145200020c926bc00077f29dc6720c8411ce3999d052f0a52513300023ad00021a90f9c00067194210000ad909ce7191414caf8f54e159f30250a7a69b2181e4e1a00a5793564eb69e0e5f417e412e821df4d1238000000000000000008348000446400045140006c0400000021bc0001d730001a57931c0007ba41d51ab5a596da653f0000000877112a070400000000004ac4000000001f8b9e3213444c6d00026f7000000000008dc1e2400077a40007c4c0004e3c000000000000021a300000006c680000000000414800000000000000000242a42138bc18900010e900000004dc551945316b9112c45184040003e327ba0474000000295c00000e90000aea0000b4b000000015245a1000000083ce9ad3a01c0f000298300012c99ec58d505304d986e9a33220471923c65c19cc40009b8c0009149aa79c24000000202c71a99b145be35f14a40000001f93783c00000000000000287000000093b8000685c00000000005ea4f153b94000000000000000000000000000097100019f10000000a351b79013a121000000000023131a0548470a400000028ec6f647b973fd1710e9c7b1a58800097b000000003df35887a9696e42b00020d17d440007168000000000000018390001cb17c8c46f986936f9a083610fdcbe991256b3000192761b4bd396b899366e5b198c691e100658de3de4bb10002841070dbb900023bc686581765dc00057380001dd4b87000291213e4cf75f34000000000000023701105bef3c38000000000000000790000000a2d24dd00027ed20a091200004af1ced6a400000000000000675c1da00026d362d466128cd5990e0400000002bf1c4d23400000000001b8754c200f778450400007919fe0000000000000000000000000000189600005b2461dab70000000654419f8c04cd1995d8cd4c840008f21899928a39100026a93e4a5e3131c00000000001458281000021488640000000aa9735c00000018fc0000f8200000008230cc942c4cdc97fc0002a91f117f846e100018512004000000000000025f09555de4082899f942c9b10eb624b70919e95dde4471de598f0e8c000000000070f0a790c055311b24000000000000000000000000000029345e8db92638000160dc874ef8000000023100005119ea45e9000227100000000000000000000000004d1
  | 8, 1 => 0xf96f77495ab2f907500051f0000000000005370000a9a367db14100453186148d6844c9000000478000000a2c4516b500f9b92990009ea5e60359d188551700000000067a0000000d10007312ac29059122b3617840005f70f75e70000005490006e59b73fc6295470000590000000001090005730005d12fd0d3306071120467000069000000000959249a1932a8370e10002a791e0003946ff3c13ab76c00044f5b10007d4000331a890000000000000000548896611280000000009a100000000012c00074b10b42f96b5d38910001917b90002e11735799552c01b90001d032c0570008b1a419268b70004500005af92b8c100045a3a90000004cb6f900035221137f6ea2551395090000000000000008c716170c4c17900001154a210f000000a1a00043d9710000000008f63049dc94121904b7dd0006800000008460000000003cf0001c91030000520000000007720003b4a256410008716670006da0007a3000000907000a53000a8b00073700077c000000293aa91a17b16cb0000001b12a8664000a114c72ca0002810ef00000092d0005df3300514f186581900000071a00000000000038200000000002f0000000000009afab1000000000000000000000000000000ab95011992a9a74a8300000068a8c98e23d472433300099900065c00000000000000090103c0000000005a39439f40004e20000b90890001438a900053b00026799f00012961962f9570007395a79e89f21c8459ac31842f15997d18f10000000002d20d90006019a90008e72600002044190008090000e97617940000005d900078e1d16150af0008390000000000950000000000001b500000000049701900064700036f0006c309b55f00035a99b6af5970295613d10004b30003493af21c97c000499ae10000000000003b90006e900094b3e100060d5f35c90008d90000002fe8595198be6430b1a796fe1a35818010001596df0001cc0098419510837890000007d36070006bd000000aac02173b5a13b20000002b54d1000a3908d38b0000000000007113119146535cda44a276350c116d704a2178c16fa642390614a900000053a0003d000000000005f82a00047f4333020008fc0009e1000a940930000000000000005510000000002916660b49d2000000269ad95590004013ad4fd0000000001a95710000007210000000000000469c10c9939a54000ab71821bb1b200096100090c0001ab00069c73385591f71f0531eb0a735c6b300072201199d4f91977f95e12859f1000000000033a306bb7e175958fa6933b5fb1a78ec826a328dfa0108b4430001717b50006590000007a90008d10000000009650001d20005b39fc8f79119691498a66cf5c1688569044000811564a910000000000000000000004e90b22271119f90000000000000000009f03013354e0000000714ac90000000007a1000a2674aac120b9e46a10004fe82966946d7517744211fe0009310009750f10001450009670a1a499225f186e43800000079f2e9ad11e46d17ca66f0000000000000008af1860009b100000000000000000000000058932449d0003397967190000000000000000009912c689f56f9a33e963f6b91c35bca821315e92df4cd24e9e903e6940797c157b68c189091906ad51e1a42ab478195327f0004493196f61dc00000067111c7410001f11c4529309a29a315a96490009850001e3000a4c17f000399000000241000a9a5391fc9895c348200000000000078a3a100000000000007d0000007e916300000000072900000000001f0000000000004b900037500000000055b8813220008e398e7ef9932091d98954b169e23106b39aa0931a6a82e68ff9804096d700000000000000000060b1ef3080000003f19cc0000004146ec000aa47097f10001473810000008ee0817930000000000000000f30009490000000000004397dc5b96211f56f1000000a818fe2ee0000000007d917900087d0000000009d95113ba0000000000000557863446ac7df06f27172a4df2fa0000003e0527000369067a515cf909000a0530b6e300000000067700000000000000000093737355719564f3910000001690000000000b329aa5c7013c47206603371248493894b037913b154ad6a99
  | 8, 2 => 0x50002e30038a00101200085a
  | 9, 0 => 0x6ec952051e000000000000000000006cc00109689c80018580d187e00002fe6d527a0b4da22f0c0000000dd200005980009b80004d780009e22240001e94f6f02773c800036e80500000000f239f000000230e0000000000000b71000116c000b4995e270611800000001a400000000000000001a10f0b866526203547800000090800033b80007540c7af9c001289350ca100000150789a4c65600000040e8000a7f0eb82e4a58c47748900ce580000004294ce8f0117094c073ae93840abec63c00000012e4ac27dc00000009d69a90000001c58000000446599e000000000000124600000004388010000ce4000000000000000063959c800000114e6a480000000000004561fd225900000000000006449ea40000001e0b0e40000007b93ccc7ac23a8fe00a400000019036f0bf20001a5000184311111881b0000191106000000117b000000156326a7758000000306880845c000cf903088440000000002a660c20004e4800000000056cb9cc000000856bd440007ac00025c40000007fa318476210b65f80021bce2934480014a235b0000000ab44705b0800000000000018a400000000000000004c92c5800000124e000000189217117a8000001254000000064cfaa1250000000000028c1f5f5600018d80000001ad0003805ecec94713800000013d5ac8b44000229074c1ca2c5169000022653cfdc7f099a46d21390001164fbe0008e0ca7cecc000000352c000000000461545f14174dbc291ff0c70243080d225170000ca009291a73680000000000000000382000557b949eca0000000000000d811080545c6800000000000000000000c7d69ec9e40d3cad0626ac02db79e08870c5ffa768eca999954bdc5d670590002c9c00000009580000000000003c4400125924880000000002ae8000000a5f18c9505ef4c09260b58c0e8e590000000132ad1000000190e87915cc4fcaf200025e00003f2f410000000a4200069c800000000000000000000008d9cac400066c0001301b62fd94c489c4e9ae692ce41bd6626d35f4a7442620871f11aa1fa8f646cca0d88e709a6e6213a57517d026407df8829700000000000000000002322eb18ec97c43b200000000059f0811000000000056c6ef819400000000000000001c90000000000f594708000ece9817c5800161e0006f9800000084c0a23484c040000338000d34c5f9050000000ed90001ce42420001f342e54ae0000000000000e2e7fb46c40000004e380000000000001384000000000281c0000000c48001b5ef3b27d0000001071000199d04a30466f8000db200082499247c800000000000000d90002ea4a520000000464736000964804da12ca200000000000000000000987020000000000022134812a8000000000000000000000000000009f100000012320000000002298cd18513f4400000018e80011042f17e600000000000000000512f13549424800000000000000d0c1a00040496eeea93640255ffe8340000c69b603f300000000000000002d04ff420a000000018200000000000003a9778af6489a00000000000003e73ea000151800000000000007994ecb96c0000000001a210d25662c6273c0000002a60a64802000111000000000038400000000007988000000b1100048f134e00000012844c20006eb0000000aee83730040000000001bc1aa22ab054ada407320400032dc000fa92d08f953b60000003f2c8240007c89ee089800029bae65dfc000000000144219700039099a6000000000079e0000002784000bc10000000b523790002b85dc30a93680b74aa2ff535d291c0000000000000000bac00000007d05ac00020b9e925e100007c91700001b18000000ed119100016ae00000035c5e00000373c7ad1a20000000ef40000000000000c220000bc89ac0008b5158c59c7df1994120002566c79548800000085b25f9435c82000000486a1e51934a3c26436a2a18140e643de2334efbf0400000047006c54f23714b4b2280000000001facb12df10000000000d6b00039fc000af75208000a7244447c000000000000000000000006791344000b9154b8fb400117900000010de0000000000000692862c244042e3c0ac9ac40004797dc80008e20000333704df2e3773a0c7131f134000118c0009e96ca25240000002e8b9f400000000000003460002b2800000000000000000004993d200000007170000000000e318290000000e115c08c465680000000000000c9c744800000038900015700007bc6948bf9a3656928615b57ee9bf2aca98620a51f41480000004d927601cd3f20000000000000dcf4748d44000f792f52edc000de987b886800046b84a0001102e4967bc8d0000000310ade64c200010dc45c00048145490f2558ab9198be24000de60001fb09980810002bf4a06e5162080000000008dd00008e400000043e400000000000000007c969b80005020000001a540001b90003d7d07600075087c40001cf0000000e48ea31922a85bfa92979c9dadce308a6c4a85c000d5971f8000686fa31a0c02800075e000432800000000000000000000000000fb2fec53b80000004e733cc485e5283984e838c7920006d526c58620000648001c72d470000000cb8000000000030643100000000000000cc824cee2213619800000000066481ec0000000000000000e2182880004560003e8be0401e0000000000000ae7000274e2600003c8813c000000960bd8c0000000000001c8e0000000ee40004c4000215d9b200078d9e84a6248a14d3c8519e782000000172e00000000007c68372a5000000000006bae900000000000000000000000000000055b0000000000db9000329c0005b9000000000006f07ca93e2122ed000000000000000024e40000000000000000562000000000000000000000000000000000ae25f202caa38000fe400000009664412d00001df4000584800146290a07380013ae0002c0800000000000004cc0000000000000000000000000000052f28080017deeab95101c00000000000000000f0794e8b2652200000039297f21df4acc5a1b527c17aebbcc0006a96fcb264ea27898a92aa5652ee91c08e95b34000000000000000000000020080004dc9d74000ccc89e3aecabce4f634a749064c2712f807cbb20007058fad1220000001bcc00000016080009ea0000003b05e0a000343885e17e0000b0c5fc0002730000104000f69000000182207c9089d08000000000000000000000000000000004d080023c6000100a2a23126418b0bd0d7629b778c9f848731713502c6400026f08f80000011a900000012cae824c8caa800000075c80010a513179191840d6000000000000054b000079dec2b518a20000276000000000206200000017082ef2bb7122cdc0006f1050b4040000000004348064694912000000074167884fc0003e10f48001bded916e88001b420000000b5ca231490002bb000094140ab7908f8000000000000074e7cc8001eb80005f09f0825221941e811000063100000000000000000001f361877308f643a27f90000001172ba20000000000760691800000000000000015920007dd0f1c6760000002424eb8efc4bcae84e1200016a8000e4318356f93bcc18000380106400029b2720000d6e000229a965c392b938cb3a40000003ce22c658c2422d89225c3edc374500021e23f900000000000007650000000d410000000000000000000239600000000008770fa00000005f80000000c38000caf0000000a3282d00034fc0007b90000a4450ef5b76d80021d200000004447d26a70000000000000000102ddc69212c8b585ad2af1761936081284993f0000ef485144ea10400055573b966547e58a5809e05b6e00000000008a40000000ba4000e99279b82254c0eb1288a70000c3b7fc0000e620006a780022ee18b00000000000006409f9000000000000000000007d08000000000000000000000000000022be0000000001bbc00004790845460006ea800000000009ab27c4470013008002204f530001f5d80e0002148385116f9300043058a20000000000012baa7690000000ffe7e19865c5e000000333946ed4300000000005ba06fa8e4000e7b000455cd180000000000000000000000116c6f50000000000000000000116e1497a5c0a8202109872c1896423b55e8a02400000050cc62cee8000858937550a00088780012630117fe81ca4e200000000000000000001da800000027da1840000000000001cdec9178183be142fc98d19945c12833514ad9c35673a6ad800084843700000000320000004518000000000000000000069880016ff04c3faa1c5c4c00000000019168e7000000000000073e00014e25ca41092c62520715afa55a076269383af25bc2c718689a7db472a15dc801c8f6ac100048b251c8c144015262e90c93779e503ed18173a899d32e09f0002844000000000474573e0000002fc472284300035e44f200000000000000000b48000000a690000001aa6509000000162e0000000002082b898d0b3040000000239562112d1900000020b400000047cdf6200000000000009f742c87d4000671897c37dc3cdc913ba3c4000e81504867c00000000029240000003f38001f6418167080012226b943d0000000000
  | 9, 1 => 0x8e1a0497aa31b8abc47690003817ca4338f21c84397839a40002c716c56c5f93ad7ff0002190000007bf2f911a0009f60000004d90000000000008910003c1000380b020000001a6b4c00085f1c687180f57b0736c97272810000000002d23fa00000030436846200019500039d0000f33199fc11b4898d1417007000b3c26100011c001a87aa4000000843000000371bb19e20008f100000000000000000027bbc13a18999690000001897a933c0f17227126890e7a490002d9a33000443000244883000ae100042e3f97737398aab610000005214e10005a9a3f00fb9100087500900061119c1baad3b195875813d9bc94cf8690719f78210005541db1bc559b990000009b99a19c109d9e76438fc0d77817999b722b9e90002a40001b90674290000c12292590000000000000006a71700003774618bb00076fa1e00000000008951105f7f9000857000bbb9917134a12093316f1a5996f5a12b181c000811b2326d9716741128016874d7539ad14016597df95d8b97a17110fd76766198d9a92e15d1aa17edb9b9990000007b11fb0005c12c93f10a173e0000000eb0002b93410003b700081f000750b7d5f1000a890003445ab0006b73890000000000f94c1817a190e91618376f30000000001070320000008b465782c0000007bc0d90004593a48c2adb0000c9282939601561a851bd8c40008141e345128a0007712d60000004df9223e1000a9d00037f00000007f1c0547942000000a09bb30005d30006e74352391ea0009977929acae900034f8297f12316d1bc69899856ec0004912213ef7d1b8c22d425a3540ca9f45738a7cf1be6796776af9560006e1141701ab070974972c0001390000003b6ba4000ac79f4000000000000000000000bcb000ad922f97900019e84c0001f15e10000000000003b534a000000b7203f0399493340009ff0000000005010930000008595d700071c00000036d00061e909000000746a710000002a9579a07000000b815490000ac359b9a8272c155112a4a92539118c97e97ac8d389baf94c90915c78b1b7e0152f1a1f5b18490ef1bf2ea8540a380e13292900039e0008770003093f48810b18c87d07373ca00025492b5e347183f1ae63f0001110001819f10002798c6000329ac123543d40d0df08146b1b1a0e32171f7c5392a999ef625aaa173a736816c14ff31143bbae013975b896476c20211496992d51714d10002116a17e1651000b11000000000832a617fe274000b8601f9d1a81ac9000291000000b566171470008f923d8a3000000b595890005e9000bb90000001e15d900020313f0003ec0000007515171590297b95c98e96f90004210002e400001973c00064f0009020000000005b30000000005b924f8934874990000002519579327de3e4000a69569000000ba218d0ff480000b7f691a17b69000a390000002b588ba910000003d200000084e1230001d10008898eb8e3a793ac345000a933549fe00082f0008310000004e979b5ed29992c919a8f14352f351b9452900051948f4f10003845db36b2c81bb54bba9531b2c9d90004450000005fc35abc700000000023b0003ba77b97d175809000000b930001210007c14090000008b30000007fc85a000000000000000000000642000a37ba30001190000000002692c400017d00075b0009e13ae7d7861177a7b7c60000002a30000009a7000000000a110000990004b1b0973f1011c254184f1916395df00044b9f9a3bbbc000000af13e900010926500010f24900076b1c487987b4310b9b9c2d10007f8000000aaf3d1ab7a014029140795cf6c47d9ab955c81e1a48a14e70008fb7d43b09ec00096100044957714b5913c46769c900004594180ca290516d92b49af35099cb826b19df66d4bfa216a974fa414f900000027366741d6317b3063b34aa67593393bb8d9a1804974a2bf8412410e306965f1d97c9719851862839641729609a0c2a10430a5a2c4af83aba109b15100000071e00000000000054abac7794114410000000e1000599741271816000789824a51a959210001160d100096a0006290008db6b98190000000004141cb5ef087a3d90c000115000000391a2894a000000b4228900000091c061a8b9019980a78a942d059761509791
  | 9, 2 => 0x49afe889c68800c2514900262000001de200001ee02d913b0c000d5b80000318a801220060b7212000000022690c92658e93696c011da1c8552006f801120000000d60021cf0000047801c8732ca6416000000000ab0017400000000056de003500000008010e000017df4000000000295c80078007c9c5e70a9dd05df3a70ba880005dc64673966b9c42d758c09422f
  | 10, 0 => 0x310012600003e488c105ca56321d9001f8a118e51e600b780057dd00002a37bc7d6401d5000007e000061508000000000000014400000000352b420800000000001c0730000000003780302e99b800b2006a4fc0000000037409003ab15f6198f6d2003b8030e19e1785b3113afa69373a0b70007400225e4000000052000066400000044000000d800080300002104bb60000000001b673f12388e620000344000000000007a000000037001c4724f64cbe4f9a358039386bc935c2000068ac20000000000048a64980000000000000450d800c8ae80000002bc028c52000008b1a800018b001173800000440000b200104000000001f90000000002480077923e10c42b0b89a400000043c26008c80000006fc1c000000003126100002ce00
  | 10, 1 => 0x1c8d9000a3346011118902c00305818c8312c60c001134700073c000ae5d000006c5ff76db995400812890fc005eded250000000000000a046179400401718a4c4104000000000059000830007f809e9001097c46965c0059cf40cd9f00000000008e8097e90a50487a583d724857be615bc19908f94c5d36a669565a17dcfc0008444973264000004b0002900219000004c0000000006c04000030016c001287300053c7d0019916c2311e9164400784f10004f9248a0007b000519f0379fc810e5693a58f61d01869ee001e7765c113551386227c8000000000000284a9130009f800844004d0001f000824ca00001000bf000b4270000021c26c359e5fb0004504400524007cc4971000248790003b8529951d799c4215912f82a8b230c010c007452700013000ff4e400584000000000000000e4848717e519001c79d9e6
  | 10, 2 => 0x50c2a03467488c0003618ec000060b45ef027e3be520000000000110a216ee19286de61312801f28798ce4000079469620000000b0000025c00001c89c328f2d12c00bb18a655e610592422897d002a2aca3ae400423a000014900510aed715c10e33e260000000223c5b2690001000006480012003d0019e2900504000016bb5231200000f6b4003b8002f002a40153
  | 10, 3 => 0x2100000000d0390000030000490002d100f000000a5ac76
  | 11, 0 => 0x84a06300001575988002400900000000045a796482000
  | 11, 1 => 0x900a4a06b000015759aa302c00900002284045a796482000
  | 11, 2 => 0x900a4a06b000015759aa302c00900002284045a796482000
  | 11, 3 => 0x900a4a06b000015759aa302c00900002284045a796482000
  | 11, 4 => 0x58084
  | _, _ => 0

def tableDisplacements : Nat → Nat → Nat
  | 8, 0 => 0xc00401100000300100500001300100000400200000f00100400400300000000000000d00000f00000100000500001100100b00000000000000000000000000200000000100500000500700300100600000000000100000100100000000000100000000900000900100700100100200200100300100000a00000000100700100000600000000000000000000600600000200200000000000200100100000000200100300100300200200600300100300400000200000000000000000000000000100300000000000000000300000400200f00000200500001500300100000000200a00200000000200000000a00400000000000900200000200000100400600000600000300900400100000400300100900000100201100100b00000100000700200900200700000200000000100200a00000000000000000200400100000000400000a00a00100200101100200000300000100100700100000000200100000000000100000100200200100500000000100000000200000100200200100100000400000000600500100000000300000000600000000200100100000300200000200000100000400100000000200200000000600400400300100100601000100e00000c00200000c00600000100900000000000100000a00300100000000000000a00200700000000300000000000000000000000200300100100000100100c00400000500000300000100000b00000300600200000000100100700200000000100000100000700000000000000500000100e00700100600100600200000700a00500200000000000000200000000100000300000400000100100000000400500000000200000000400000100200100000100100100000100000200000600000000300100600400200000000000400500300000100100000100c00100800101800100d00400200300000400100100100c00400000000000300000100200300000000000000100100200200200000c01200000100000000000000000000000100200100100f00000000a00600000700100000000000300000200000400000300100000000000800100200000000100000000100100200600000000200100000300100100000100100100300400300000100100000200000000300400500100000200600100000000400300100100100200000000200100000100000000000200100000500100000000000500200100100700c00000d00100000100500900000000000000000100100000300200000100200000300200000100000000000200000800900100200601900000200100000100000200200000800000000000100700300900600100200000200300100100b00300300300000400b00000000800200000000000000000b00d00000000000000000600d00000100000300600100300d00000300200000000200100000000400400600600400200000900000000000400100200000000100500000000200b00100200000000100200700500000100100300000100800300900100000300000000100000200100000100a00000000100000000000200100400101400600500400200000000200a00000000800100400200100200500000000100000000000000100000100700100000000400000300000200300000000300300300000200700200000000200700100500100300200200300900000301300000000000200100000000000100100100000000000100100100000000500200100100000000900100200000000500900200300000100a00000000500300000200700200000300000100100300100500100000000000000000300300000200000300100000000000000000200000600400000700900100200100000200000400000200000600200600000000100000301000000600800100300000000300000000000100000200000000100400200000300800800000100100500000100400000200300800800000000800100100300700000500c00200300000a00100000100400000900000000600000300000000100000000500200000400000100000000800000d00000400000000600000100001100100900100000000000700100000000000000100200300000200100900300400f001000003004000000
  | 8, 1 => 0x200001401000020000b00000000010000500002000000000101417018000140400000000060080e018020000000000000060000000802004020000000005000000140001c05000000000000c04004000080200001000010040200c0401800000010040001000000000100500803020030140a0040000c0202c020281c00c0000005058000040100c000000a000000000100c02020010040000c00008000000b0440702400008020000000000000000000000002004000040000800000000080609c0001404000000040001c0800c000000100c0103401000030040201c070380000c0400000028030180001c0000400000000040802c0101400004020280200400000010040000002008010000b01c000040100000000020000100001028000000400c000080c00000000020040000000008020400102001008010180200402
  | 8, 2 => 0x1000
  | 9, 0 => 0xc000010000020000180800000000800000000000000000000000100201400000002004008010020000000001200800004012004018010080240100300000000001000004008010000000080500400c01000000000040040040000000100000005800002000000000060080000700a01001800004000000010000080000100000002800000004000030020000100100a010000000000000300200200c0000100000000001012008010040000000100100600000000000000000010000040000a0100000000200001c01801000000000070000000100100000000000002008000010140000480000001c000020000000200000000001806002000008000000080080100000c0080000000c000000000000300000000001803000004008000000540000100200801004002000010000040000180001200400000000000008000140000000000800c030010000200000300c0040e00100800001802000000000010000000080200600001000000010018030140000000000000c0000200400c0000001000400802002030000000020000080000000c018010000040080100000401007000008000010020000680000200000003000000000000040000000000203c00000008000010000000080100000a00400009012000008030000040100201200c0000100000c00802000000010000000140000000000001003000000008020040040000200001802802004000000010040000000300800000003002000000020020000100000a0000000000000001800000010008000000000000a006008000000000000000000000400003022014010020060080000300200c008000000000100000200001801006004010010000080080000200400801002000010030080000000c00000401800002000000010000200100500800001004000008038030040000000500602c008040000040380000001c0080000600c0000000600808002
  | 9, 1 => 0x80800c1102c00000020200304407000000000003c030640500000008000080300001004070101900400004000000a000000000500418030000001f0100a01400018060100c0000800801000000000a000050100c0000006c030180000019008000380800007004000140100c02044060140301008000180000603402098020000001001008010040b00002008030040d010000140a00000000060480100c060000101002000060140000400000040280507c020000000401008020100100819008000081a014000180a000010100002c02034000080300c060100100c0706000000040140101c00008040180600c1f00406028030a000004060201501804014100000001c000180904000014020000000406000000080201409010070240502005000010000401403004020040102c05008000180300c03014000040200405
  | 9, 2 => 0x14040050008081062c08300000000000103000808b00000800c00806
  | 10, 0 => 0x1000000000105010203010301000402000101030301020000000100000109000101010001000501000003000100000401020200000002000000000101
  | 10, 1 => 0x50002010000000000170402050103030200060001030104000101010001000704080101010000020a0f00090c0f00010100040a0406000000050200010d0301
  | 10, 2 => 0x1a1010114000022a1c0810c001840208000000c00604040010010090
  | 10, 3 => 0x10c00
  | 11, 0 => 0x800008800
  | 11, 1 => 0x800008800
  | 11, 2 => 0x800008800
  | 11, 3 => 0x800008800
  | 11, 4 => 0x0
  | _, _ => 0

def tableBuckets : Nat → Nat → Nat
  | 8, 0 => 1024
  | 8, 1 => 256
  | 8, 2 => 4
  | 9, 0 => 512
  | 9, 1 => 256
  | 9, 2 => 32
  | 10, 0 => 64
  | 10, 1 => 64
  | 10, 2 => 32
  | 10, 3 => 4
  | 11, 0 => 8
  | 11, 1 => 8
  | 11, 2 => 8
  | 11, 3 => 8
  | 11, 4 => 4
  | _, _ => 1

def tableMultiplier : Nat → Nat → Nat
  | 8, 0 => 1000
  | 8, 1 => 1000
  | 8, 2 => 1000
  | 9, 0 => 1000
  | 9, 1 => 1005
  | 9, 2 => 1001
  | 10, 0 => 1000
  | 10, 1 => 1000
  | 10, 2 => 1001
  | 10, 3 => 1000
  | 11, 0 => 1001
  | 11, 1 => 1001
  | 11, 2 => 1001
  | 11, 3 => 1001
  | 11, 4 => 1000
  | _, _ => 0

def tableSalt : Nat → Nat → Nat
  | 8, 0 => 28
  | 8, 1 => 0
  | 8, 2 => 0
  | 9, 0 => 3
  | 9, 1 => 0
  | 9, 2 => 0
  | 10, 0 => 0
  | 10, 1 => 0
  | 10, 2 => 0
  | 10, 3 => 0
  | 11, 0 => 0
  | 11, 1 => 0
  | 11, 2 => 0
  | 11, 3 => 0
  | 11, 4 => 0
  | _, _ => 0

def tableBits : Nat → Nat → Nat × Nat
  | 8, 0 => (12, 14)
  | 8, 1 => (10, 12)
  | 8, 2 => (4, 6)
  | 9, 0 => (11, 13)
  | 9, 1 => (10, 12)
  | 9, 2 => (7, 9)
  | 10, 0 => (8, 9)
  | 10, 1 => (8, 10)
  | 10, 2 => (7, 9)
  | 10, 3 => (5, 6)
  | 11, 0 => (5, 6)
  | 11, 1 => (5, 6)
  | 11, 2 => (5, 6)
  | 11, 3 => (5, 6)
  | 11, 4 => (3, 3)
  | _, _ => (0, 0)

-- The numerical lookup selects a candidate. The permutation test verifies the candidate.
def signatureHash (salt : Nat) (a : Sig) : Nat :=
  (((a.1.toNat % 1048573) * (65537+salt) + a.2.toNat % 1048573 + 317) % 1048573)^3 % 1048573

def frontierHash (salt : Nat) (v : List Sig) : Nat :=
  (v.foldl (fun s a => s + signatureHash salt a) 0) % 1048573

def stamp (k t : Nat) (w : List Sig) : Nat :=
  let h := frontierHash (tableSalt k t) w
  let (width, codeWidth) := tableBits k t
  let lane := h % tableBuckets k t
  let mask := 2^width-1
  let d := (tableDisplacements k t >>> (width*lane)) &&& mask
  let slot := (h*tableMultiplier k t % 1048573+d) &&& mask
  (tableData k t >>> (codeWidth*slot)) &&& (2^codeWidth-1)

def transport (g : Fin 8) (w : List Sig) : List Sig :=
  if g = 0 then w else w.map (recipeAction g)

def certificateMatch (k t : Nat) (w : List Sig) : Bool :=
  let n := stamp k t w
  let i := (n-1)/8
  let g := Fin.ofNat 8 ((n-1) % 8)
  decide (n ≠ 0) && decide (i < frontierCount k t) &&
    (transport g w).isPerm (frontierState k t i)

lemma perm_impossible {k t : Nat} {w z : List Sig} (h : w.Perm z)
    (hz : Impossible k t z) : Impossible k t w := by
  have he : w.toFinset = z.toFinset := by
    ext a
    exact List.mem_toFinset.trans ((h.mem_iff).trans List.mem_toFinset.symm)
  unfold Impossible at *
  rwa [he]

lemma certificateMatch_ok {k t : Nat} (h : ∀ i < frontierCount k t,
    Impossible k t (frontierState k t i)) {w : List Sig}
    (hw : certificateMatch k t w = true) : Impossible k t w := by
  let n := stamp k t w
  let i := (n-1)/8
  let g := Fin.ofNat 8 ((n-1) % 8)
  change (decide (n ≠ 0) && decide (i < frontierCount k t) &&
    (transport g w).isPerm (frontierState k t i)) = true at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hw
  obtain ⟨⟨_,hi⟩,hp⟩ := hw
  by_cases hg : g = 0
  · exact perm_impossible (by simpa only [transport, ite_eq_left hg] using hp) (h i hi)
  · exact rotate_impossible g (by simpa only [transport, ite_eq_right hg, recipeAction_eq] using hp) (h i hi)

def leafOk (k t i : Nat) : Bool :=
  let v := frontierState k t i
  decide v.Nodup && !search k t v

def middleOk (k t i : Nat) : Bool :=
  let v := frontierState (k+1) t i
  decide v.Nodup &&
    !stepTest k t v (fun w => !certificateMatch k (t-1) w) (fun w => !certificateMatch k t w)

def rootOk (t : Nat) : Bool :=
  !stepTest 11 t raw (fun w => !certificateMatch 11 (t-1) w) (fun w => !certificateMatch 11 t w)

lemma leaf_impossible {k t i : Nat} (h : leafOk k t i = true) :
    Impossible k t (frontierState k t i) := by
  simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact exclude_search h.1 h.2

lemma middle_impossible {k t i : Nat} (ht : t ≤ 5)
    (hp : ∀ t ≤ 5, ∀ i < frontierCount k t, Impossible k t (frontierState k t i))
    (h : middleOk k t i = true) : Impossible (k+1) t (frontierState (k+1) t i) := by
  simp only [middleOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  apply exclude_step h.1 _ _ h.2
  · intro w hw
    exact certificateMatch_ok (hp (t-1) (by omega)) (by simpa using hw)
  · intro w hw
    exact certificateMatch_ok (hp t ht) (by simpa using hw)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_0 : Theta.span (leafOk 8 0) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_30 : Theta.span (leafOk 8 0) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_60 : Theta.span (leafOk 8 0) 30 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_90 : Theta.span (leafOk 8 0) 30 90 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_120 : Theta.span (leafOk 8 0) 30 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_150 : Theta.span (leafOk 8 0) 30 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_180 : Theta.span (leafOk 8 0) 30 180 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_210 : Theta.span (leafOk 8 0) 30 210 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_240 : Theta.span (leafOk 8 0) 30 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_270 : Theta.span (leafOk 8 0) 30 270 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_300 : Theta.span (leafOk 8 0) 30 300 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_330 : Theta.span (leafOk 8 0) 30 330 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_360 : Theta.span (leafOk 8 0) 30 360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_390 : Theta.span (leafOk 8 0) 30 390 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_420 : Theta.span (leafOk 8 0) 30 420 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_450 : Theta.span (leafOk 8 0) 30 450 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_480 : Theta.span (leafOk 8 0) 30 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_510 : Theta.span (leafOk 8 0) 30 510 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_540 : Theta.span (leafOk 8 0) 30 540 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_570 : Theta.span (leafOk 8 0) 30 570 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_600 : Theta.span (leafOk 8 0) 30 600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_630 : Theta.span (leafOk 8 0) 30 630 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_660 : Theta.span (leafOk 8 0) 30 660 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_690 : Theta.span (leafOk 8 0) 30 690 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_720 : Theta.span (leafOk 8 0) 30 720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_750 : Theta.span (leafOk 8 0) 30 750 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_780 : Theta.span (leafOk 8 0) 30 780 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_810 : Theta.span (leafOk 8 0) 30 810 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_840 : Theta.span (leafOk 8 0) 30 840 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_870 : Theta.span (leafOk 8 0) 30 870 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_900 : Theta.span (leafOk 8 0) 30 900 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_930 : Theta.span (leafOk 8 0) 30 930 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_960 : Theta.span (leafOk 8 0) 30 960 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_990 : Theta.span (leafOk 8 0) 30 990 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1020 : Theta.span (leafOk 8 0) 30 1020 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1050 : Theta.span (leafOk 8 0) 30 1050 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1080 : Theta.span (leafOk 8 0) 30 1080 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1110 : Theta.span (leafOk 8 0) 30 1110 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1140 : Theta.span (leafOk 8 0) 30 1140 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1170 : Theta.span (leafOk 8 0) 30 1170 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1200 : Theta.span (leafOk 8 0) 30 1200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1230 : Theta.span (leafOk 8 0) 30 1230 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1260 : Theta.span (leafOk 8 0) 30 1260 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1290 : Theta.span (leafOk 8 0) 30 1290 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_0_1320 : Theta.span (leafOk 8 0) 23 1320 = true := by decide +kernel
lemma f8_all_0 : Theta.span (leafOk 8 0) 1343 0 = true := (@Theta.span_join (leafOk 8 0) 660 0 683 (@Theta.span_join (leafOk 8 0) 330 0 330 (@Theta.span_join (leafOk 8 0) 150 0 180 (@Theta.span_join (leafOk 8 0) 60 0 90 (@Theta.span_join (leafOk 8 0) 30 0 30 f8_0_0 f8_0_30) (@Theta.span_join (leafOk 8 0) 30 60 60 f8_0_60 (@Theta.span_join (leafOk 8 0) 30 90 30 f8_0_90 f8_0_120))) (@Theta.span_join (leafOk 8 0) 90 150 90 (@Theta.span_join (leafOk 8 0) 30 150 60 f8_0_150 (@Theta.span_join (leafOk 8 0) 30 180 30 f8_0_180 f8_0_210)) (@Theta.span_join (leafOk 8 0) 30 240 60 f8_0_240 (@Theta.span_join (leafOk 8 0) 30 270 30 f8_0_270 f8_0_300)))) (@Theta.span_join (leafOk 8 0) 150 330 180 (@Theta.span_join (leafOk 8 0) 60 330 90 (@Theta.span_join (leafOk 8 0) 30 330 30 f8_0_330 f8_0_360) (@Theta.span_join (leafOk 8 0) 30 390 60 f8_0_390 (@Theta.span_join (leafOk 8 0) 30 420 30 f8_0_420 f8_0_450))) (@Theta.span_join (leafOk 8 0) 90 480 90 (@Theta.span_join (leafOk 8 0) 30 480 60 f8_0_480 (@Theta.span_join (leafOk 8 0) 30 510 30 f8_0_510 f8_0_540)) (@Theta.span_join (leafOk 8 0) 30 570 60 f8_0_570 (@Theta.span_join (leafOk 8 0) 30 600 30 f8_0_600 f8_0_630))))) (@Theta.span_join (leafOk 8 0) 330 660 353 (@Theta.span_join (leafOk 8 0) 150 660 180 (@Theta.span_join (leafOk 8 0) 60 660 90 (@Theta.span_join (leafOk 8 0) 30 660 30 f8_0_660 f8_0_690) (@Theta.span_join (leafOk 8 0) 30 720 60 f8_0_720 (@Theta.span_join (leafOk 8 0) 30 750 30 f8_0_750 f8_0_780))) (@Theta.span_join (leafOk 8 0) 90 810 90 (@Theta.span_join (leafOk 8 0) 30 810 60 f8_0_810 (@Theta.span_join (leafOk 8 0) 30 840 30 f8_0_840 f8_0_870)) (@Theta.span_join (leafOk 8 0) 30 900 60 f8_0_900 (@Theta.span_join (leafOk 8 0) 30 930 30 f8_0_930 f8_0_960)))) (@Theta.span_join (leafOk 8 0) 180 990 173 (@Theta.span_join (leafOk 8 0) 90 990 90 (@Theta.span_join (leafOk 8 0) 30 990 60 f8_0_990 (@Theta.span_join (leafOk 8 0) 30 1020 30 f8_0_1020 f8_0_1050)) (@Theta.span_join (leafOk 8 0) 30 1080 60 f8_0_1080 (@Theta.span_join (leafOk 8 0) 30 1110 30 f8_0_1110 f8_0_1140))) (@Theta.span_join (leafOk 8 0) 90 1170 83 (@Theta.span_join (leafOk 8 0) 30 1170 60 f8_0_1170 (@Theta.span_join (leafOk 8 0) 30 1200 30 f8_0_1200 f8_0_1230)) (@Theta.span_join (leafOk 8 0) 30 1260 53 f8_0_1260 (@Theta.span_join (leafOk 8 0) 30 1290 23 f8_0_1290 f8_0_1320))))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_0 : Theta.span (leafOk 8 1) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_30 : Theta.span (leafOk 8 1) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_60 : Theta.span (leafOk 8 1) 30 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_90 : Theta.span (leafOk 8 1) 30 90 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_120 : Theta.span (leafOk 8 1) 30 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_150 : Theta.span (leafOk 8 1) 30 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_180 : Theta.span (leafOk 8 1) 30 180 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_210 : Theta.span (leafOk 8 1) 30 210 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_240 : Theta.span (leafOk 8 1) 30 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_270 : Theta.span (leafOk 8 1) 30 270 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_300 : Theta.span (leafOk 8 1) 30 300 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_1_330 : Theta.span (leafOk 8 1) 19 330 = true := by decide +kernel
lemma f8_all_1 : Theta.span (leafOk 8 1) 349 0 = true := (@Theta.span_join (leafOk 8 1) 180 0 169 (@Theta.span_join (leafOk 8 1) 90 0 90 (@Theta.span_join (leafOk 8 1) 30 0 60 f8_1_0 (@Theta.span_join (leafOk 8 1) 30 30 30 f8_1_30 f8_1_60)) (@Theta.span_join (leafOk 8 1) 30 90 60 f8_1_90 (@Theta.span_join (leafOk 8 1) 30 120 30 f8_1_120 f8_1_150))) (@Theta.span_join (leafOk 8 1) 90 180 79 (@Theta.span_join (leafOk 8 1) 30 180 60 f8_1_180 (@Theta.span_join (leafOk 8 1) 30 210 30 f8_1_210 f8_1_240)) (@Theta.span_join (leafOk 8 1) 30 270 49 f8_1_270 (@Theta.span_join (leafOk 8 1) 30 300 19 f8_1_300 f8_1_330))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f8_2_0 : Theta.span (leafOk 8 2) 6 0 = true := by decide +kernel
lemma f8_all_2 : Theta.span (leafOk 8 2) 6 0 = true := f8_2_0
lemma f8_all_3 : Theta.span (leafOk 8 3) 0 0 = true := rfl
lemma f8_all_4 : Theta.span (leafOk 8 4) 0 0 = true := rfl
lemma f8_all_5 : Theta.span (leafOk 8 5) 0 0 = true := rfl
lemma f8Checked (t : Nat) (ht : t ≤ 5) (i : Nat)
    (hi : i < frontierCount 8 t) : leafOk 8 t i = true := by
  interval_cases t
  · exact Theta.span_ok f8_all_0 i (Nat.zero_le i) hi
  · exact Theta.span_ok f8_all_1 i (Nat.zero_le i) hi
  · exact Theta.span_ok f8_all_2 i (Nat.zero_le i) hi
  · exact Theta.span_ok f8_all_3 i (Nat.zero_le i) hi
  · exact Theta.span_ok f8_all_4 i (Nat.zero_le i) hi
  · exact Theta.span_ok f8_all_5 i (Nat.zero_le i) hi
lemma f8Impossible (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i < frontierCount 8 t) :
    Impossible 8 t (frontierState 8 t i) :=
  leaf_impossible (f8Checked t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_0 : Theta.span (middleOk 8 0) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_30 : Theta.span (middleOk 8 0) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_60 : Theta.span (middleOk 8 0) 30 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_90 : Theta.span (middleOk 8 0) 30 90 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_120 : Theta.span (middleOk 8 0) 30 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_150 : Theta.span (middleOk 8 0) 30 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_180 : Theta.span (middleOk 8 0) 30 180 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_210 : Theta.span (middleOk 8 0) 30 210 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_240 : Theta.span (middleOk 8 0) 30 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_270 : Theta.span (middleOk 8 0) 30 270 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_300 : Theta.span (middleOk 8 0) 30 300 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_330 : Theta.span (middleOk 8 0) 30 330 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_360 : Theta.span (middleOk 8 0) 30 360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_390 : Theta.span (middleOk 8 0) 30 390 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_420 : Theta.span (middleOk 8 0) 30 420 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_450 : Theta.span (middleOk 8 0) 30 450 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_480 : Theta.span (middleOk 8 0) 30 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_510 : Theta.span (middleOk 8 0) 30 510 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_540 : Theta.span (middleOk 8 0) 30 540 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_570 : Theta.span (middleOk 8 0) 30 570 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_0_600 : Theta.span (middleOk 8 0) 2 600 = true := by decide +kernel
lemma f9_all_0 : Theta.span (middleOk 8 0) 602 0 = true := (@Theta.span_join (middleOk 8 0) 300 0 302 (@Theta.span_join (middleOk 8 0) 150 0 150 (@Theta.span_join (middleOk 8 0) 60 0 90 (@Theta.span_join (middleOk 8 0) 30 0 30 f9_0_0 f9_0_30) (@Theta.span_join (middleOk 8 0) 30 60 60 f9_0_60 (@Theta.span_join (middleOk 8 0) 30 90 30 f9_0_90 f9_0_120))) (@Theta.span_join (middleOk 8 0) 60 150 90 (@Theta.span_join (middleOk 8 0) 30 150 30 f9_0_150 f9_0_180) (@Theta.span_join (middleOk 8 0) 30 210 60 f9_0_210 (@Theta.span_join (middleOk 8 0) 30 240 30 f9_0_240 f9_0_270)))) (@Theta.span_join (middleOk 8 0) 150 300 152 (@Theta.span_join (middleOk 8 0) 60 300 90 (@Theta.span_join (middleOk 8 0) 30 300 30 f9_0_300 f9_0_330) (@Theta.span_join (middleOk 8 0) 30 360 60 f9_0_360 (@Theta.span_join (middleOk 8 0) 30 390 30 f9_0_390 f9_0_420))) (@Theta.span_join (middleOk 8 0) 90 450 62 (@Theta.span_join (middleOk 8 0) 30 450 60 f9_0_450 (@Theta.span_join (middleOk 8 0) 30 480 30 f9_0_480 f9_0_510)) (@Theta.span_join (middleOk 8 0) 30 540 32 f9_0_540 (@Theta.span_join (middleOk 8 0) 30 570 2 f9_0_570 f9_0_600)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_0 : Theta.span (middleOk 8 1) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_30 : Theta.span (middleOk 8 1) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_60 : Theta.span (middleOk 8 1) 30 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_90 : Theta.span (middleOk 8 1) 30 90 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_120 : Theta.span (middleOk 8 1) 30 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_150 : Theta.span (middleOk 8 1) 30 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_180 : Theta.span (middleOk 8 1) 30 180 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_210 : Theta.span (middleOk 8 1) 30 210 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_240 : Theta.span (middleOk 8 1) 30 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_270 : Theta.span (middleOk 8 1) 30 270 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_300 : Theta.span (middleOk 8 1) 30 300 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_330 : Theta.span (middleOk 8 1) 30 330 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_1_360 : Theta.span (middleOk 8 1) 18 360 = true := by decide +kernel
lemma f9_all_1 : Theta.span (middleOk 8 1) 378 0 = true := (@Theta.span_join (middleOk 8 1) 180 0 198 (@Theta.span_join (middleOk 8 1) 90 0 90 (@Theta.span_join (middleOk 8 1) 30 0 60 f9_1_0 (@Theta.span_join (middleOk 8 1) 30 30 30 f9_1_30 f9_1_60)) (@Theta.span_join (middleOk 8 1) 30 90 60 f9_1_90 (@Theta.span_join (middleOk 8 1) 30 120 30 f9_1_120 f9_1_150))) (@Theta.span_join (middleOk 8 1) 90 180 108 (@Theta.span_join (middleOk 8 1) 30 180 60 f9_1_180 (@Theta.span_join (middleOk 8 1) 30 210 30 f9_1_210 f9_1_240)) (@Theta.span_join (middleOk 8 1) 60 270 48 (@Theta.span_join (middleOk 8 1) 30 270 30 f9_1_270 f9_1_300) (@Theta.span_join (middleOk 8 1) 30 330 18 f9_1_330 f9_1_360))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_2_0 : Theta.span (middleOk 8 2) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f9_2_30 : Theta.span (middleOk 8 2) 11 30 = true := by decide +kernel
lemma f9_all_2 : Theta.span (middleOk 8 2) 41 0 = true := (@Theta.span_join (middleOk 8 2) 30 0 11 f9_2_0 f9_2_30)
lemma f9_all_3 : Theta.span (middleOk 8 3) 0 0 = true := rfl
lemma f9_all_4 : Theta.span (middleOk 8 4) 0 0 = true := rfl
lemma f9_all_5 : Theta.span (middleOk 8 5) 0 0 = true := rfl
lemma f9Checked (t : Nat) (ht : t ≤ 5) (i : Nat)
    (hi : i < frontierCount 9 t) : middleOk 8 t i = true := by
  interval_cases t
  · exact Theta.span_ok f9_all_0 i (Nat.zero_le i) hi
  · exact Theta.span_ok f9_all_1 i (Nat.zero_le i) hi
  · exact Theta.span_ok f9_all_2 i (Nat.zero_le i) hi
  · exact Theta.span_ok f9_all_3 i (Nat.zero_le i) hi
  · exact Theta.span_ok f9_all_4 i (Nat.zero_le i) hi
  · exact Theta.span_ok f9_all_5 i (Nat.zero_le i) hi
lemma f9Impossible (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i < frontierCount 9 t) :
    Impossible 9 t (frontierState 9 t i) :=
  middle_impossible ht f8Impossible (f9Checked t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_0_0 : Theta.span (middleOk 9 0) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_0_30 : Theta.span (middleOk 9 0) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_0_60 : Theta.span (middleOk 9 0) 4 60 = true := by decide +kernel
lemma f10_all_0 : Theta.span (middleOk 9 0) 64 0 = true := (@Theta.span_join (middleOk 9 0) 30 0 34 f10_0_0 (@Theta.span_join (middleOk 9 0) 30 30 4 f10_0_30 f10_0_60))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_1_0 : Theta.span (middleOk 9 1) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_1_30 : Theta.span (middleOk 9 1) 30 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_1_60 : Theta.span (middleOk 9 1) 24 60 = true := by decide +kernel
lemma f10_all_1 : Theta.span (middleOk 9 1) 84 0 = true := (@Theta.span_join (middleOk 9 1) 30 0 54 f10_1_0 (@Theta.span_join (middleOk 9 1) 30 30 24 f10_1_30 f10_1_60))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_2_0 : Theta.span (middleOk 9 2) 30 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_2_30 : Theta.span (middleOk 9 2) 13 30 = true := by decide +kernel
lemma f10_all_2 : Theta.span (middleOk 9 2) 43 0 = true := (@Theta.span_join (middleOk 9 2) 30 0 13 f10_2_0 f10_2_30)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f10_3_0 : Theta.span (middleOk 9 3) 8 0 = true := by decide +kernel
lemma f10_all_3 : Theta.span (middleOk 9 3) 8 0 = true := f10_3_0
lemma f10_all_4 : Theta.span (middleOk 9 4) 0 0 = true := rfl
lemma f10_all_5 : Theta.span (middleOk 9 5) 0 0 = true := rfl
lemma f10Checked (t : Nat) (ht : t ≤ 5) (i : Nat)
    (hi : i < frontierCount 10 t) : middleOk 9 t i = true := by
  interval_cases t
  · exact Theta.span_ok f10_all_0 i (Nat.zero_le i) hi
  · exact Theta.span_ok f10_all_1 i (Nat.zero_le i) hi
  · exact Theta.span_ok f10_all_2 i (Nat.zero_le i) hi
  · exact Theta.span_ok f10_all_3 i (Nat.zero_le i) hi
  · exact Theta.span_ok f10_all_4 i (Nat.zero_le i) hi
  · exact Theta.span_ok f10_all_5 i (Nat.zero_le i) hi
lemma f10Impossible (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i < frontierCount 10 t) :
    Impossible 10 t (frontierState 10 t i) :=
  middle_impossible ht f9Impossible (f10Checked t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f11_0_0 : Theta.span (middleOk 10 0) 5 0 = true := by decide +kernel
lemma f11_all_0 : Theta.span (middleOk 10 0) 5 0 = true := f11_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f11_1_0 : Theta.span (middleOk 10 1) 6 0 = true := by decide +kernel
lemma f11_all_1 : Theta.span (middleOk 10 1) 6 0 = true := f11_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f11_2_0 : Theta.span (middleOk 10 2) 6 0 = true := by decide +kernel
lemma f11_all_2 : Theta.span (middleOk 10 2) 6 0 = true := f11_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f11_3_0 : Theta.span (middleOk 10 3) 6 0 = true := by decide +kernel
lemma f11_all_3 : Theta.span (middleOk 10 3) 6 0 = true := f11_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma f11_4_0 : Theta.span (middleOk 10 4) 1 0 = true := by decide +kernel
lemma f11_all_4 : Theta.span (middleOk 10 4) 1 0 = true := f11_4_0
lemma f11_all_5 : Theta.span (middleOk 10 5) 0 0 = true := rfl
lemma f11Checked (t : Nat) (ht : t ≤ 5) (i : Nat)
    (hi : i < frontierCount 11 t) : middleOk 10 t i = true := by
  interval_cases t
  · exact Theta.span_ok f11_all_0 i (Nat.zero_le i) hi
  · exact Theta.span_ok f11_all_1 i (Nat.zero_le i) hi
  · exact Theta.span_ok f11_all_2 i (Nat.zero_le i) hi
  · exact Theta.span_ok f11_all_3 i (Nat.zero_le i) hi
  · exact Theta.span_ok f11_all_4 i (Nat.zero_le i) hi
  · exact Theta.span_ok f11_all_5 i (Nat.zero_le i) hi
lemma f11Impossible (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i < frontierCount 11 t) :
    Impossible 11 t (frontierState 11 t i) :=
  middle_impossible ht f10Impossible (f11Checked t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_0 : rootOk 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_1 : rootOk 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_2 : rootOk 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_3 : rootOk 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_4 : rootOk 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_5 : rootOk 5 = true := by decide +kernel
lemma rootChecked (t : Nat) (ht : t ≤ 5) : rootOk t = true := by
  interval_cases t
  · exact root_0
  · exact root_1
  · exact root_2
  · exact root_3
  · exact root_4
  · exact root_5
lemma rootImpossible (t : Nat) (ht : t ≤ 5) : Impossible 12 t raw := by
  have h := rootChecked t ht
  simp only [rootOk, Bool.not_eq_true'] at h
  apply exclude_step raw_nd _ _ h
  · intro w hw
    exact certificateMatch_ok (f11Impossible (t-1) (by omega)) (by simpa using hw)
  · intro w hw
    exact certificateMatch_ok (f11Impossible t ht) (by simpa using hw)

lemma noSmallLive {k t : Nat} (hk : k ≤ 12) : ¬ Live k t raw.toFinset := by
  intro h
  have sz := live_size h
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length = 8 := rfl
  exact rootImpossible t (by omega) k hk (restrict_live h (project_bound_root hk))


lemma noSmallSubset {m t : Nat} {T : Finset Sig} (hm : m ≤ 12)
    (hT : T ⊆ raw.toFinset) : ¬ Live m t T := by
  intro h
  have he := necessary h (fun a ha => List.mem_toFinset.mp (hT ha))
  rw [← he] at h
  exact noSmallLive hm h

lemma noThetaSubset (i : Fin 4) {m t : Nat} {T : Finset Sig} (hm : m ≤ 10)
    (hT : T ⊆ (raw.map (project i)).toFinset) : ¬ Live m t T := by
  intro h
  apply root_project_impossible i
  refine ⟨m, hm, t, T, h, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hT ha))
  exact Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb, rfl⟩

end PEqualNP.Outside.L_meta_670_aux.Base1007
