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

def bit (side : Bool) (i : Fin 252) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 252).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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

def sample (s : Bool) (i : Fin 252) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 252), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
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


def rowSignalsE : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8c9f79fdfb2bd3fd7590fffe7aabd0a2dfe6db65e8f9cfb2fd7f7f724786eba9fdfabc90fdf41abf7c3f035dff4f24db45c0fc33b2c57c7f7ff38d8f7df77b7254ff7713bbd27c9958b8ddeafeb724efe7b1f67d3ff80c392ffd625b22021e471fd89658808fbdc5f0be922028e731746d2e8ff38c9f79fd7b23d0fd7590ffde788bd0a2dfe2da65e0f9cfb2fc7f3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ff38c8f7df57b7254fd7713bbd27c9958a8ddeada3724efc7b1f67d3ff004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ff38c8f79f57b2250fd7510bbd2788950a0dde2da2520e9c7b0f47d3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0feff7f7f7ffb7dfffffbfefff6de7ffef7fbbffeffffffff9effff2dbfffffff7f6ffb7dffff3bfedffeff7fffe6fbaffffffffdfdfcfbbf7dbffddffffceefb5ffffffffef75fffffffffffbdd7fffff77ffff3bbed7fffffff7fefff5ffffebbbef7ffffffffaeefbdfffffffffffdffbffd7ffd58e1bcee4b073debd7e8b75977ffbd8aafbd95b71e437cfd31a3e177ff5f733eee4f47fffc90aeb7d97fffff8eef959faf9ffefff515a7e977fd18d8f5df77b7254ff771333d27c9958b8ddea7eb724efe7b1b23d37f808390c5d024922020e4317409248808390c5d024922020e4317409248fcd8e97d3fdb32bdbfd7d9c77ffebefe0e2bbf74fe7e9f9dde3b9bb73f243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151ffcd8e97d3fdb32bdbfd7d9877ff6befc0e2bbf74b67e9f9dde3b93b73f24386c0009da09c90e1b0002768270350420a044145c0d410828110517fcd8c9751fdb32bd3fd759077fe6aabc0a29be64b65e8f9cda2b93b73724386c0009da09c90e1b0002768270350420a044145c0d410828110517fbdfbffff9fb7dfef7effffe7edf7ffffffbeff6fdfffffffefbfdbf7ffffffffd79fafdffffffff5e7ebf7ffff73beff6fffffffdcefbfdbffffbd8aafbd95b71e437cfd31a3e177fd58e1bcee4b073debd7e8b75977ffff8eef959faf9ffefff515a7e977ff5f733eee4f47fffc90aeb7d97fff7ff7feeffffdffffe3afffff7fdff7ff7feffdfffffff63afffff6ddf277f7f0eafdf4fc9de1baea7f7fbf27f8eecb1dfbfdc9df7fd3cb76d37f7ff7feefdfddffff63affffd6ddff7ff7feefdfddffff63affffd6ddffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7d8fbeefdffd7fdf63efbbf7ff5ff7d8fbeefdffd7fdf63efbbf7ff5fa7fbfecfddffdfe9feffb3f77ff7fa7fbfecfddffdfe9feffb3f77ff7ff7d86beefddb57fdf61afbbf76d5ff7d86beefddb57fdf61afbbf76d5f27786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d37f7af5fa2dd65dfff56386f3b92c1c90df3f4c68f85dfef62abef656dc7fff242badf65ffffd7dccfbb93d1fffbffd4569fa5dfffe3bbe567ebe7f6ff5f671dfffaff363a5f4ff6ccaa7e7778ee6edcffbf838aefdd3f9f24b8ecc119fab9c90f7f514a768270357530ea64547c0d410aea59179ff6ff5f661dffdaff363a5f4ff6ccaa7e7778ee4edcffbf038aefdd2d9f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f6d86b6e3ddb52fdb61adb8f76d4be7c063aef5cb47f9f018ebbd72d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f6d84b661ddb52fd361a5b0f76c4aa7c0638ee4c947f9f018aabd52d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f5d8d9e4ddff97bd763679377fe5eb3d8baceec7dd7ecf62eb3bb1f75fa4bbfcc5d9fe9be92eff31767fa6f83d3d2cfd465d7e0f4f4b3f51975ff5d869ecfddb17bdf612f9b776d5ff7d86aeefd5b57edf61af3bb3655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f5d849e4dddb17bd7612793776c5eb3d82aceec5957ecf60ab3bb1655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f518d8e4dd779725463671333d25c9158b8cce87c9724e626b1b21d35f808390c5d024922020e4317409248808390c5d024922020e4317409248f4ff5d643fff9ebffe327de7f7ecaa3e73ecbf5fdfdeaf428b7f9b6d97243f7d06afdf0fc91e1baea7f7eaf03f0cecb15f1fdc0d77fd3c936d17f4ff5d641dff9abf36325d47f6ccaa3e7368ae4edcdeaf028a6f992d9724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4df7f6c7dfb5ffff63afff776dcff7ef7faafd6ddffff638efbb92d1fffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1ff4d8696c3ddb12bdb612d98776d4be7c062aaf54b47e9f018e3b93251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d859641dff92bd3632590776c4aa3c0328ae46dc5e8f028a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849643ddb12bdb612598776c4aa3c0228af54945e8f008a3b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641fdb12bd3e12590777e4aa3c0228be44965e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb16bd7612792776c4aa3c02acae45955e8f408b3b91651724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb12bd3612594776ccaa3e0228ae44dc5e8f008a2b99251724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb12bd3612590776c4aa7c0628ae44947e9f018a2b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb12bd3612590776c4aa3c0228ae44b45e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb12bd3612590776c4aa3c0228ae44947e8f008a3b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517f4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517efe7f7bff7efeffbf9fdeffdfbfbffeffff7f3ffffaffbfffdfcffffeb035753beb645e7c0d5d4efad9179f24bdfdc539fab9c92f7f714e7eae7efe767bbf7cb6dfbf9d9eefdf2db7feff6f7f3fdb7affbfdbdfcff6deb7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7efe0e2bbf74fe7e9f9dde3b9bb73ffcd8e97d3fdb32bdbfd7d9c77ffeb035042ba9645e7c0d5d4c3a99151f243dfd4529da09c92e3b30467eae7efc0e2bbf74b67e9f9dde3b93b73ffcd8e97d3fdb32bdbfd7d9877ff6b0350420a044145c0d41082811051724386c0009da09c90e1b000276827efa0c2b3d747e7e159dd6339bb23c9c58e95d2eda323dafd799c77dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ef60e0bbf74fa721e9d5e1b9b933ffc58e87d3fdb3225afd7d1c77d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ef20c0b3f747a729c9d561b9b963c98d8a85d3bda32a4bfc791c67fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0ef20c0b3d747a72149d56139b923c9858a85d2ada3224afc791c67d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0ef20c0b39747a22109d54109b92388850a05d22da2020a9c790c47d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0e7c062aaf54b47e9f018e3b93251ff4d8696c3ddb12bdb612d98776d4b0350420a044145c0d41082811051724386c0009da09c90e1b000276827dcffff7d7bfefffffffffff6fffefffafffbbff65ffffdffdeffb9bfbdffbffdf5fbfeffffffffff7effbeffff7d3ffff65fffff7fcffff9bfdfb7ffffceeefddffffe3ebfffdffdff7ffdfe7ddffffff763e7f7fffede83d7d3cff665d7e0f4f4bff5997dfa4bbfcc5d9febbe92fff717e7fa6fb3ffbecffdfdffeef62eb7fbbffdff5ffdde4ffff9fbffe367df7ffede83f3decfd5f5ffe0f7fff3fd3ff5fa4bffdc7ffff9fe93effbff7ffeefb3df3fceecf95dfef62abeff56dd7f7ff5fe6ddffdfff763a7f3ff6c5effffff4f6dfb5dfffe3bbed77eff7fffa6ebadfffffffdfdfcfbbf7d3fb3d8baceec7dd7ecf62eb3bb1f75ff5d8d9e4ddff97bd763679377fe5e83d3d2cfd465d7e0f4f4b3f51975fa4bbfcc5d9fe9be92eff31767fa6fb3d82aceec5957ecf60ab3bb1655ff5d849e4dddb17bd7612793776c5e0350420a044145c0d41082811051724386c0009da09c90e1b000276827b1d898c4cc7d97ac762631331f65eb1d898c4cc7d97ac762631331f65e8093d0c5d06493e024f431741924f8093d0c5d06493e024f431741924faff7f7dfe6ffeffbf9ffbefdfffffffffdff79ffffaff3fff5f4fffefa035fff4fa6df47c0fc33bee5fd7ff24f8eefb9fffbbc90fff51ebf7c3fabf7bedff7fffdeafdefb7fdffff7ffffddf7bfffbebffff77defffefa03fdffcf35fbfdc0ff7ff3cd7eff7247f7fbebfdfafc91fdfefaff7ebfabe7b69be66dedeaf9eda6f99b7b7fcffdd751fffbabf3ff75d47ffeeadbd7d3fff665f7f6f5f4fffd997dffcbffdf5fbfebbff2fff7d7effaefabd0a2dfe6db65e8f9cfb2fd7f7f7fff8c9f79fdfb2bd3fd7590fffe7a035dff4f24db45c0fc33b2c57c7f724786eba9fdfabc90fdf41abf7c3fabc0a29be64b65e8f9cda2b93b737fcd8c9751fdb32bd3fd759077fe6a0350420a044145c0d41082811051724386c0009da09c90e1b000276827a7e77fcff7fdfffbfc38bffdf7f9ff6ff5f673ffffefffe3a7feff7eca03f7dfcfb7f5ffc0d77fffedb7f9f24bffdc7bfffbfc91f7fffeff7eafa7e7778ee6edcffbf838aefdd3f9ff6ff5f671dfffaff363a5f4ff6cca0357530ea64547c0d410aea59179f24b8ecc119fab9c90f7f514a76827a7e0628ae64dc7e9f818a2b99371ff4d849651ddb32bd3612594776cca0350420a864547c0d41082a19151f2438ec4109da09c90e3b104276827a7c0638ee4c947f9f018aabd52d1ff6d84b661ddb52fd361a5b0f76c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827a3e73ecbf5fdfdeaf428b7f9b6d97f4ff5d643fff9ebffe327de7f7eca03f0cecb15f1fdc0d77fd3c936d17243f7d06afdf0fc91e1baea7f7eafa3e7368ae4edcdeaf028a6f992d97f4ff5d641dff9abf36325d47f6cca0350420a044145c0d41082811051724386c0009da09c90e1b000276827a3c03acae47dd5e8f428b3b916517f4d859641dff96bd7632792777e4a03d0c2cb1461d5c0d47493c110517243b7c0489de0bc90e1b202677a2fa3c0328ee46dc7e8f028a2b91371ff4d859641dff92bd3632590776c4a0353520e844547c0d410a2a51171f24b8ecc119fa99c90e7f114276827a3c02acaf5d955e8f408b3b936d17f4d849643ddb16bdf61279a776c4a03704e0a05d14dc0d61b828136d1724386c020ddb0dc91e1b828376c27a3c022cbe4d965e8f008b2f936597f4f849641fdf92bd3e125907f7e4a0350ce4b04d145c0d43392c13451724386c028fdf0bc90e1b00a3f7c2fa3c0228ee6c945e8f808a2fd53797f6f849671ddfb2bd3612590ff6c4a0355530e244145c0d410a2851079724386c8019daa9c90f5f410a76827a3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827a3c0228ae44945e8f008a2b912517f4d849641d5b12bd361259077644a0350420a044145c0d41082811051724386c0009da09c90e1b000276827a2e71e4315fdf8ea34281749b6c82a4e7550426ed8ebbf8302ce5d3e8a00b0ccc111f0b9c0077f51483680700175106a64507c01410aea59168fa1c00080c44905a87000203112416b0d808440c5912ac360211031644a00104000004001c0041000001000700104000004001c00410000010007a0c02008244900a8b000808112503e4c04020154b02a9301041013240a00104000004001c0041000001000700104000004001c00410000010007a0c00000244904a8f00020a112402a0c0084015d910a83400110136c0200104002044105c0141082811040700304c0001d009c0061b000036807a0c00000044900a83000000112402a0c00000044900a8300000011240200104000004001c0041000001000700104000004001c004100000100079d7ffdddeefebf3feff7bdf7fdfffffbfdef7dff7ffe75fff777bbfafc808fbdc7f6bf962038e7bff5ed6e880e39effd7b5ba2023ef71fdafe589bffbfdfeafcfdfeffefbefedfff7ffbfdff7dff7ffff5fff7f7fffefcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9bffbedffbfeffe6ffefb7feffbffff3fddf7fff7bf3fcff77dfffdefc80afbdc5f1beba202bef717c6fae880c793fff625b62031e4fffd896d89b3fbedfea74ff66cfefb7fa9d3fddd3fddf5dbf6bf374ff77d76fdafcdbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae89958b8ddeafeb724efe7b1f67d3ffff38d8f7df77b7254ff7713bbd27c808fbdc5f0be922028e731746d2e880c392ffd625b22021e471fd896589958a8ddeada3724efc7b1f67d3ffff38c8f7df57b7254fd7713bbd27c000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418993f9cd5ca74bf264fe735729d2fc993f9cd5ca74bf264fe735729d2fcd88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c8991898d5ca76b7244fe731323d27c991898d5ca76b7244fe731323d27c808390c5d024922020e4317409248808390c5d024922020e431740924898dfbf5d6afa7dfeffefbef67ffe7ffafdfb3df67ffff5ffd6f3bbbe3cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f9858b85d6afa3524efe7b0f67d3e7ff28d8b3df67b7254ff5613bb923c808fbd4560ba1020282330546c2e080c202bad625b22001c441b9814189858a85d2ada3224afc791c67d3ebef20c0b3d747a72149d56139b923c000dbd45209a0000282330446c2e0004002ba9605a20001c441a98141897bfdfc7fff4ffffde3e3fffffedc97bfdfc7fff4ffffde3e3fffffedc80a79dc7f7b5be2033effffdafec880a79dc7f7b5be2033effffdafec8953fddc4eef49f3fce363df7ddedc93bf9ec7d9f4ffe6562e377abfadc808791c7f625962030e4bff5896c880a39cc5d1b4ba2023ef717c2fa48953f5dc4eef49f3fce323df7d5edc93bf1ec7d9f4ffe6562a377ab68dc00071106a60506001000aea58168800a08cc111b0b800036f5148268009518d9c4ccf4973d463639375de5c93989ac6c874d7e4562e333a1f25c808390c5d024922020e4317409248808390c5d024922020e431740924894ff7f4c6efcdffffe3abef7d7fcff7af5fe3ddf5ffff56387f7bb6c9cffbffd47efff5ffffe3bbef7fffeffff2cefbdff5ffffd7ffdffbb7d1f94df7f4c6cf85ffff63abef756dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f943f5d442ef49e3fce323de7d5ec883a71ec3d1f4fde254283778b689400071106a60506001000aea58168800a08cc111b0b800036f51482680093ff3fcee8fcddfef62abefed6dd7f7bf5fe6ddf5dfff563a7f7fd6cdcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff93d8bacee87cd7e4f62eb3ba1f35ff518d9e4ddf7973d463679377de5c808390c5d024922020e4317409248808390c5d024922020e431740924893bf9ec7d9f4ffe6562e377abfadc953fddc4eef49f3fce363df7ddedc80a39cc5d1b4ba2023ef717c2fa48808791c7f625962030e4bff5896c893bf9ec6c8f4dfe6562e377a9fadc953fddc4ccf49f3f46363d77ddedc808390c5d024922020e4317409248808390c5d024922020e431740924893989ac6c874d7e4562e333a1f25c9518d9c4ccf4973d463639375de5c808390c5d024922020e4317409248808390c5d024922020e4317409248933f9ec7c874ff66462e377a9d2dc953fddc4caf49f374e363d76ddadc808390c5d024b22021e4717c09248808791c5f224922020e43d74892c8933898c7d974b7244626313abd25c911898c4eaf49724ce2631f65d2dc808390c5d024b22021e4717c09248808791c5f024922020e43174092c892ff3f4f79fcfdfef62abffef6dc7f7af5fa6ffe5dfffde386fffd3e9cffbffdc579fafdffff7fff5e7ebe7fff753beff65ffffd7dcefbf93f9f92df3f4e68f85dfef62abefe56dc7f7af5fa6dde5dfff56386f3fd2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f91dfbfcce8fcdffef62ebff65ffdff7bfdfe6dd75dfff563e7f3b9fe5cffbffdc5f9fedffffeffbf767fbeffff3d2ffdf65fffff7fcffff9bf5f91df3fcce8f85dfef62abef656dd7f7bf5fe6dd75dfff563a7f3b96c5cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f9158b8cceafc9724ee26b1f65d3dff738d8e7dd77b7254636713bbd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c092489158b8cce87c9724e626b1b21d35ff518d8e4dd779725463671333d25c808390c5d024922020e4317409248808390c5d024922020e4317409248913f9cc4eaf49f26ce2635f6ddadc933f9cc7d9f4bf264626357abdadc808791c5f024922020e43174092c8808390c5d024b22021e4717c09248913f9cc4c8f49f26462635729dadc913f9cc4c8f49f26462635729dadc808390c5d024922020e4317409248808390c5d024922020e4317409248911898c5c8f4b724462631723d2dc9538d8c4ce7497254e3631339d25c80839cc5d0b4922020e731742d248808390c7d625922020e431f589648911898c4ec74972cc62631b31d65c919898c4d9f497a4562631323fa5c808390c7d425962030e4b3f50964880a39cc5d1b49a2022ef31742fa48911898c4eaf49724ce2631f65d2dc933898c7d974b7244626313abd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c09248911898c4cc74972c462631331d65c919898c4c87497a4562631321f25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c4c8f49724462631721d2dc913898c4c8749724462631329d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c4c8f49724462631365d25c931898c6c87497244626313a1d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c4c8749724462631321d25c9518d8c4cc749725463631331d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c4c8749724462631321d25c911898c4c8769724462631323d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911898c0c8749724462631321c05c911898c4c8701724462630321d25c808280c1d024922020e411700904880839045c024122020a0307409248911898c0c8749524462631321d254911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248911818c4c8749724462231321405c911818c4c8749724462231321525c008080c110209000006411400000000031004800402000000202401208911818c4c8749724462231321405c911818c4c8749724462231321405c808390c5d024922020e4317409248808390c5d024922020e4317409248911818c4c87015244622303214054911818c4c8749724462231321405c8083904540201020202030540824080820080d024922000c4013001008911808c4c8501724460231321405c911808c4c8501724460231321405c000000000000000000000000000000000000000000000000000000000090ff3f4c68fcddfef62abef6d6dc7f7af5fa2dde5dfff56386f7b92c9cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90df3f4c6cf85dfef62abef756dc7f7af5fe2ddf5dfff56387f3bb6c1cffbffd476dfb5dfffe3bbed77efe7fff24ebadff5ffffd7dfcfbbb7d1f90df3f4c68f85ffef62abff656dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90df3f4c68f85dfef62abef656dc7f7af5fa2dd67dfff56386f3bb2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90df3f4c68f85dfef62abef656dc7f7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90df3f4c48f859f6362a9e56569c7f72f57a2cc65cf7f42386e3b9041cffbffd4569fa59ffee3b3c567ebe7ffd242bade65f7ffd5d4cfbb9151f90df3e4868785de6f62ab6f2161c7f52f5da0dd659f3f46306d3390c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90d82b4c685855fcf60abab656547f7884ba2dd4157fd56186b3b1241cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f90d82a48485851e4360a921216147f50841a0cc41073d421068331041cffb8ec4149fa59ffee3b10527e967ff52423ace4547ffd4908eb39151f90d8294c28d810bcb60298c656dc3e7a042a2d545c7e9501863399241c243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151f90d8094408d810bc3602180656c42a3800282c44145e8500822391241424386c0009da09c90e1b0002768270350420a044145c0d410828110517909f1f4448f05dfe562a3e7656cc493af1f82c864ddfe56282e3a92c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f908f1f0048605dfe56282e3212c04908f1f0048605dfe56282e3212c04ffb2400049605dffd6188e1212907ffb2400049605dffd6188e1212907905f3d4c68f81d3ee622bcf654dc7f3af1ea2d965dde65628673a92014ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f9058210c6848053ce202a8b650547f3880aa2d94151e41608431a12014ff1f7104684a45fffc10ae16583e7fff042b85960f9ffc7dc411a129179018184448701524462230321404491081880c8649724462021321001c8083904540201020202030540824080820080d024922000c40130010089018084408501224060211021404881000080c0400520400020301001400000000000000000000000000000000000000000000000000000000008b27b69be264ed62c9eda6f8993b5dc3fdd751bf6ba370ff75d46fdae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae88950a0dde2da2520e9c7b0f47d3f7ff38c8f79f57b2250fd7510bbd278000dbd45209a0000282330446c2e0004002ba9605a20001c441a98141885275584e6e48f3bc8302cf5d1e9c92bf1e4719f4fae6162a174ab68c800071106a60506001000aea58168800a08cc111b0b800036f51482680083c0228ae04845e8f008a2b812517f49849641dd312bd1612590776c480350420a044145c0d41082811051724386c0009da09c90e1b00027682783c0228ae04845e0f008a2b812117f41849641dd3123d0612590774c48000000000000000000000000000000000000000000000000000000000083a71ec3d1f4fde254283778b6894943f5d442ef49e3fce323de7d5ec800a08cc111b0b800036f51482680000071106a60506001000aea58168881402088e0480520e000a0b010117f41848641d53122506125103340480000000000000000000000000000000000000000000000000000000000810018c0c0749520442031301401490181844087496244622312215248008080c11020900000641140000000003100480040200000020240120881001084c0648720402020301121c9018184408749224062211021404800031004800402000000202401208008080c110209000006411400000081000080e4400528c00020b1104149098084419d012a416021102368480000000204010400100082810040000200c0001900800020b00002680081000080c0400520400020301001490180844085012240602110214048000000000000000000000000000000000000000000000000000000000080c02208604845e8f008a2b012507f48849201d4112bd1610490312c0803104000004045c0d41082001010724304000094009c90618000212807800000000040002000000000100008000000000400020000000001000000000000000000000000000000000000000000000000000000000000006fe7f7bbf7afeddbf9fdeefdebfb77effff7f3fbffadfbfffdfcfeffebffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6fe0e2bbb70fe2c1b9ddc389ab33b6c50e17d379b2219a9d7d9c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06fa7def397b7fac31dfd5749afab80c77f55d26beae1be9f7bce5edfeb00e08efb97b5ba0003ef51e9a7c18000fbd47a69f06003823bee5ed6e86fa7d6b397a7eac319fd4749abab80c77f55d26beaa1ba9f79cc5edfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06fa0c2b3b707e6c9d9dd63a9ab6380cd0e95d379a3299bdd799c56ffeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae06fa0c2b39707e2c119dd4309ab2380c50e15d269a2219a9d798c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06fa0c0b39707a28119d54109ab2380850a05d269a2008a9c790c56d7e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f70e0ffb79fa201a9d7d1cded3fb6f70e0ffb79fa201a9d7d1cded3fb004dbfffb69fa20029e771eded6f8004dbfffb69fa20029e771eded6f86f60e0bbb70fa609e9d5e1a9a973b6cd0e87d379b3281bdd7d1c56fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae06f60e0bbb70fa201a9d5c189a933b6c50e07d379b2201a9d7d1c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f60c0b3970fa20129d54109a923a2850a05d269b2000a9c790c56d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f30c0f79717a20109d75109ad2780950a0dda29a2000a9c790c46d3f3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f27d6b3d727ef4349fd6739a923c185fbd5d2aba3816afe79cc66dbe3dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae06f27d5b7b7a7ae1bc9f56dede9eb80af7be5f33bef8c2bdef97ccefbe3004713beb605a60011c4efad8169800adbdc531bab8002b6f714c6eae06f27d5b797a7aa1b09f54d4de9eb80af7b65f22bee8c2b9ef96ccefbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae06f27d4b3b7a7ae0bc9f565e9a9eb808f7bc5d33beb882bde795c4efbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae06f27d4b397a7aa0309f54549a9ab80877b45d22bea802a9e794c4edbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20e2bbf707e741c9dde3b9a933d5c58e97d3b9a3215afd7d9c66dbeb034002ba9605e600d1c4c3a981518242dbd45299a08092a2b30466eae06f20d0b39727a20109f54109a92380850b05d22bea000a9e790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c8f39717b2010dd55109ad2380850a05d229a2400e9c7b0e46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c1b7b787a619c9d569ade9e380ad0aa5f339a70c0bdcf93cc6fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae06f20c1b79787a21909d5490de9e380ad0a25f229a60c0b9cf92cc6f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b79787a20109d5410de92380a50a05f229a2000a9c790cc6d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b79707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b3b707a609c9d561a9a963808d0a85d339a3080bdc791c46fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae06f20c0b3b707a20189d54189a92380850a05d339a2000a9c791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39787a20109d54149a92b80870a05d229ea000a9c790c4ed3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39787a20109d54109a9a380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a60149d56129a92380850a85d229a3000adc791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20909d54109a963808d0a05d229a2080b9c790c46f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20109d54109a92380c50e05d269a2201a9d790c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20109d54109a92380850a05d229a2200a9c791c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20109d54109a92380850a05d229a2200a9c790c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46dbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e06ee7f73b37afe8dbb9fdcecdebfa36ee7f73b37afe8dbb9fdcecdebfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6ee7773f37afeedbf9f9eeede3fab6ee77f7b37bff8dbbdf9dfcde6da37f7f7f3eafdf6fdfdf1beeaff7fbf7ffceffb3ffbfddfdf7fdfcbf6db76ee7773b37afe8dbb9f9cecde2da36ee7773b37afe8dbb9f9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db76ee7673b378fe8dbb9d9cfcde2da36ee7673f378b68dbb9d9cecde3fa37f7c6fba3fdbeddfdf5fcf8bf6db77f7d7f3e2fdb6ddfdf1bee8ff6fb76ee7673b378b68dbb9d9cecde2da36ee7673b378b6adbb9d9cfcde2dab7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db76ee7673b378b68dbb9d9cecde2da36ee7673b378b68dbb9d9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db76cc76738268b48dbb9d9cec542da36ee7673b150b68db31d9ce09a2d237f7c6f3a2fdb4ddfde1b8e83f6db77f786e3a0fdb6ddfdf1bce8bf6d376c50e07d379b2201a9d7d1c56d3eb6f60e0bbb70fa201a9d5c189a933b000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814186c40e039370b2201a9d5c1812932b6c40e039370b2201a9d5c1812932b00000000000000000000000000000000000000000000000000000000006c27d53537a7ae1bc9f56de5e9ea80ae7be5b33bef8c2bded97c8afba300071106a60506001000aea58168800a08cc111b0b800036f5148268006c00c0311703220109d54101292280840a019220a2000a9c5808029323000000000000000000000000000000000000000000000000000000000066e7672a358948dbb018cecdc2d8366e7672a358948dbb018cecdc2d837f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db766c0632a358b40d9b018ca8d62d0366c0632a358b40d9b018ca8d62d0327786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d376427552437a78e1bc8306de5e1e8802e73e4b31bcf8c2b42897c8a698300071106a60506001000aea58168800a08cc111b0b800036f5148268005f3ffffffbb6ff57cffffffeedbfd5f3ffffffbb6ff57cffffffeedbfdffefbfffffbffe3ffbefffffefff8ffefbfffffbffe3ffbefffffefff85c3fdd751bb6ba170ff75d46edae80b27b69be224ed42c9eda6f8893b5fcafbdf5fbbeba3f2bef7d7eefae8dbc793fff625f636f1e4fffd897d827275586a6a58e1bc8302cedc1e9802f71e4711bef8c2342a174ce68c20047130ea60506001000aea58169800a8acc111bab8000b6f51486682023c0228ae40945c8f008a2b90251774d849641d9b129d3612590766c4a0350420a044145c0d41082811051724386c0009da09c90e1b00027682722c0220a240940c8b00882890250364c04120158b00993010480562c020350420a044145c0d41082811051724386c0009da09c90e1b00027682710df3f4c28b858deb62a9ec646dc367a757a2d525cddb50386e3982c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f0f27f79fe6a4ef5bc9fdaefdc9fbd5ebfdf771bb6fad71fff5f4eefae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae80ef7ff5f37befedbfdffbfedeffeb6fa7dff7b7b7fedbddfd7fedefeb800afbdc7b7bfbe003b6fffedefee800e79fffb7b5be0013efffeda7e980c77f55d26beae1be9f7bce5edfeb6fa7def397b7fac31dfd5749afab8000fbd47a69f06003823bee5ed6e800e08efb97b5ba0003ef51e9a7c180c77f55d26beaa1ba9f79cc5edfeb6fa7d6b397a7eac319fd4749abab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814180c67f51d26aeae1be9f5ace5e9fab6ea7de7317b7fac31dfd5749afaa800071106a60506001000aea58168800a08cc111b0b800036f5148268000c50e15d269a2219a9d798c56dfeb6fa0c2b39707e2c119dd4309ab238000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814180c27d51526a6ae1bc9f52ce5e9ea80aa79e5313b6f8c21ded1748afaa000071106a60506001000aea58168800a08cc111b0b800036f5148268000b77b6dfe2beed42e9efb6fced3f77f3fddf79fb7ba170ff75d4fedaf8dbcfbffff6bff636f9e7fffded7f8fcefbfffffbfba3f2bef7dffefef80b67b69be22ced42e9eda6f8893b77c3fdd751fb7ba170ff75d47edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae80b27b69be226ed42c9eda6f8a93b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae80b27b69be224ed42c9eda6f8893b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae80af7be5f33bef8c2bdef97ccefbe36f27d5b7b7a7ae1bc9f56dede9eb800adbdc531bab8002b6f714c6eae0004713beb605a60011c4efad816980af7b65f22bee8c2b9ef96ccefbe36f27d5b797a7aa1b09f54d4de9eb8000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814180ae7271b228868dab9c98eccc2da36ea74733178368db19d94e4de2ca07f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db70ad0a25f229a60c0b9cf92cc6f3e36f20c1b79787a21909d5490de9e38000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814180a27b61b2224e84289ed86c8893a14c27d53113a6a81309f54c44e9aa0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae80a27261b2200684289c986c8801a14c2745311382281309d14c44e08a05b44033a26016416d100ce89805907c2c2d302b9a281f0b0b4c0ae68a00927b499e224ad02c9e5a4f0893b5583f9c711b36b8060fe75542ad2e0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae808d7be5d22ba78c2bdef96c46fbe36f27d5b39727ae1b49f56d29a9e3800adbd4521ba18002a2b30446eae0004202ba9605a60011c4cfa98141808d0a85d339a3080bdc791c46fbe36f20c0b3b707a609c9d561a9a9638002dbd45219a08002a2b30446eae0004002ba9605a60011c4c3a9814180877b45d22bea802a9e794c4edbe36f27d4b397a7aa0309f54549a9ab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a9814180850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418082794110224a80209e50440892a0082794110224a80209e50440892a0d88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c806a75f4737b4fedbdc383fede7e8806a75f4737b4fedbdc383fede7e8800a79dc7b7b5be00136fffeda7e8800a79dc7b7b5be00136fffeda7e8806a7570626a4cedbd8382eedc3e8806a75f4715b4fadb14381f4de6c8800071106a60506001000aea58168800a08cc111b0b800036f5148268000477554426be8e1be8323ce5e5eca23a71ec395b5f8c214281749a6890000f3d06a69f06001803aea5e56a800e08ecb15b1b800036f51c926c100467750c26ac8e1be830ace5c1f8b66a75e6315b7fac314385749a688800071106a60506001000aea58168800a08cc111b0b800036f5148268000427554526b4ae1bc8303ce5e5e8806a75e4317b4fac31c381749a7a8800079d47a69506001023bee5a568800a08cc397b5ba00036f51e9a7c080427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f51482680003a79ec391b4fac2142c1748afa980437d54426b48e1bc8363ce5cdec800a08cc191b4ba0003ef51682780800079147a60506003020bee5896c80327368ae024cd42c028a6f880195543f5d6419b49a1706325d46c48c8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae803271682c024cd424028263880014101f1d4408b0181606221c46448c0dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae00300228ae0004540c008a2b800115541849641992121506125906648480340020a04014400d00082810051024282c00099a08090a0b00026682002f71e4711bef8c2342a174ce68c227275586a6a58e1bc8302cedc1e9800a8acc111bab8000b6f5148668200047130ea60506001000aea58169802e73e4b31bcf8c2b42897c8a69836427552437a78e1bc8306de5e1e8800a08cc111b0b800036f51482680000071106a60506001000aea58168802c0220a200840c0b00882880210364004124158302190010490560c08000000000000000000000000000000000000000000000000000000000002b79e4711b4f8c2142e1748afac00527d584a6a48e1bc8342de5c9e9800a19cc511b0b800236f714c2ea4000071186b605860010c4afa58168802a71e4733b4f8c29c2817cce7a800627550737a4ae1bc8302dede1e8800a59dc531b0b800036f714c26a8000071186b605a6001144efad8168802a71e4711b4fec254283768a7a8804275d4426b49e1bcc303de5c5e8800a39cc591b4ba00036f716c27a08008791c7b62596001064bfe58168802a71e4335b4fccad42837e9a6c8004a75d4437b49e9bdc303de5e7e8800a08cc315b1bc00136fd3c926c0000271d06a7950e00120baea5a7e8802a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea58168802a71e4311b4f8c214281748a68800427550026a48c1bc8302ce5c1e8000a08cc111b0b800036f51482680000071106a60506001000aea58168802a71e431134f8c214281748a60800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea58168802a71e4300b4f8c214281648868800427550406a48e1b48302c65c1e8800a08cc111b0b800036f51482680000071106a60506001000aea58168802a71e4211b4d8c214281748a68800427550424a48e1bc0302ce5c0c8800200c0001900800020b0000268000000000204010400100082810040002a71e4211b4d8c214281748868800427550424a48e1bc0302ce5c0c8800a08cc111b0b800036f51482680000071106a60506001000aea58168802a71e4200b4d8c214281748868800427550404a48e1b40302c65c1e88008080c11020900000641140000000003100480040200000020240120802a71e031124f8c214280748828800427550422a48e1bc8302ce4c1e8800a080c11120b800036c51480280000071104a20406001000ae248128802a7164300b4e8c210281648a68800427550406a48a1b08300c45c1e8800008c410090000000231040240000000000286050200000000a18140802a7160311a4e8c210280748a28800427550426a48a1b88300cc5c1e88000000801000a00001444108000000005110420000000000020040028002a7160311a4e8c210280648a28800427550426a48a1b88300cc5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea58168802a7160311a4e8c210280648a28800427550026a4881b88300cc5c0c8000200c0001902800030b400826800000401022601040010008e818048002a716030024e8c210280648820800427550406a48a1b08300c45c1e88008080c11020b000016451480000000071104a204020000002c248128802a7160200a4c8c210280648828800427550404a48a1b00300c45c0c88000000000000000000000000000000000000000000000000000000000002a70603118068c210080648a2880042745002680081b88100cc5c0c8000200c0001902800030b400826800000401022601040010008e818048002800202240044c8d00822a90240004804944159012991410190566c080000000204010400100082810040000200c0001900800020b00002680002800202000040c0100802080200004004104048002190010080540c080000000000000000000000000000000000000000000000000000000000022716030024e84200280648800800427550402a48a1308300c44c1a88008080c11020b000016451480000000071104a204020000002c248128801009080c024850040242030092141018984408349204062611020d248808390c5d024922020e4317409248808390c5d024922020e431740924800d00844119a1080340211046684223000082a4010408c00020a90041000282c00019a08000a0b0000668200040020a04010400100082810041000c7370860a84ddaf028aef442d8776af5f221d25dadf16384f0b82c08ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f00c72708208848dab0088ec442d8366a74722150148db10184e0982c007f3c6d0029da4ddfde1b8e02769a77f70423a0f416ddfd718ce8b92d1700871e4000b058c214281640068800427550004248e1b40302c2180c0800a08c4101b01800022b104026800000200028605060010008ea1814080050a04c20180000a00690800d3436500c0a095078201001441012921800019045000000002020304408240000000809004820000c40120010080050204c209a0000a002908464143670040a295030201001041092001800082c00009a000008030000640200040020a0401000000000081004100050204c20980000a00290c4441c3672040a2950582010010410980018000dbd45209a0000282330446c2e0004002ba9605a20001c441a98141800500045009a200020021044640c2272040828605820108100009812180008ac41009a000008231040640200040020a86050200000000a1814180040204920982000a00090c024183642040201707820108104101a120800008c410090000000231040240000000000286050200000000a1814080040200c22880000a80080c441383662040231507a20100104109a000800051104200000000000200400280000000801000a00001444108000000040200824080408e000a0a100503648048601593128114105101268080000000204010400100082810040000200c0001900800020b0000268000040200820080000a0008080001036400402015030201001041012000800000000000000000000000000000000000000000000000000000000000027150422a48c1ac8202ce4c1e8002a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f5148268000027150420a48c1ac0202ce4c0c8002a71e0211a4d8c2142807488288000071104200004001000ae040028000a000801120b800034c4108028000027144100b4a80200201440a48800427540006a48a030830044181a8800008c410090000000231040240000000000286050200000000a1814080027140422a48802882004c4c1a800227140311a4a80200200548a088000051104200000000000200400280000000801000a00001444108000000027140400a48e024020246081a8800271c4000b49802042015408488000031004800402000000202401208008080c11020900000641140000000027140024a48c0ac02024e180c8000a71c4011b4988214201540a68800000000204010400100082810040000200c0001900800020b0000268000027140022248c02c82024e08128000271c4111b4b80204201540a488000071106a60506001000aea58168800a08cc111b0b800036f5148268000027140000a4880200200440808800027140000a48802002004408088000000000000000000000000000000000000000000000000000000000000010984400349000042611000d24001009084802486004024212009218008190c5102090002064314408240000310849004820000c42124012080010904400348600402630200d248010098c080349200042411000d21800039045800402002020306409248008080c19024920000e41160010080007360860204d42c028a6f000185542f5d2019249a1706304d0280808db87914560205436f020be54083c0fca200b0db24ba3f03cc4d3a838080007150420a00c1ac0202ce440c8002a71e021124d8c2142807088280000071104200004001000ae040028000a000801120b800034c4108028000000184400349600442031200520800001844003496004420312005208008390c5902492000064316401208008390c59024920000643164012080000184100b4b00004201140240800420500406248601483020218120800808cc110b0900000671140240000003100686050200000020a5816080000100424248608c02020a1016080080184011b49080142011002680000031006840506001000a2a50160800a08cc111b09800026f1140268000000100422a48600c82020e441288022018431134b00004201108a400000071104a00402000000202401288008080c11020b0000164514800000000010040024860040202020012080000184000349000042011000400000031004800402000000202401208008080c1102090000064114000000000010000024800000200000000000000100000248000002000000000000000000000000000000000000000000000000000000000000000000000000004522902000880010c465280062040031704a20108100109a120800059d45209000000023304424280000000829605a200014441a981408000000410090200000001040240800420400006048201081000018120800008c410090000000231040240000000000286050200000000a1814080000000426800408c80020e54168002a008431194b08014001108a680000051106240104001000a2850068000200c801190a800034f4108268000000000422800000880000c441280022000031104a00000000108a000000051104200000000000200400280000000801000a00001444108000000000000024000408c00020a100400008008401190108014001100268000000000204010400100082810040000200c0001900800020b000026800000000001100000000000100200000000000020000000800000800000000000000000000000000000000000000000000000000000000000000000000000004000008000000010040000800000000000801000000002000000000000000000000000000000000000000000000000000000000000000000000040000000000000100000000000400090000000001000240000000000204010000000000810040000000c000090000000030000240000000000000800000000000400008000200000000480000000000080000000000000000000000000000000000000000000000000000000000000000000000000482000000000001208000000400010000000001000040000000000080040200000000200100800008041000000000020104000000000000000004800000000100000000000000400000000000000000120000000080100080000044010000000000110040000000000002004002000000000000000400400020200000000000840001010000400110004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040040000400020100100001000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000010000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def rowPackedE : Nat := 0x461ecc63f1509a410000230f6632eca84d208025d187b318fc542690400008c3d98c7e2a13482008c425ecc63f1509a410046200f6631f8a84d2080230fd7b318fc542690401187b3d98c7e2a13482008c3d9e0c63f1509a4100461ecdb631f8a84d2080230f663318fc542690401187b319767e2a13482008c3d98ca43f1509a410000230f63f1e0a84d2080230f6631f8f0542690401187b318fc672a13482008c3d98c7e2f9509a4100001ecc63f17ca84d2080230f6631f8bc542690401187b318fc542913482008c3d98c7e2a134824100461ecc63f1509a411180230f6631f8a84d2086c01187b318fc542690424008c3d98c7e2a134820f00461ecc63f1509a410680230f6631f8a84d208300000994b630f6631f88200004ca30f6632eca841000025b187b319764d20802813f8c3d98c542690400009e461ecc62a13482009fc622af6631509a410000231107b318a84d2080283187b31976542690401408c3d98cbb2a13482009fc61ecc65d9509a41004e230f6632eca84d208026d187b31976542690401328c3d98cbb2a134820097461ecc65d9509a41004b630f6632eca84d2080259187b31976542690401288c3d98cbb2a134820092461ecc65d9509a410048a30f6632eca84d2080231187b31976542690400008c3d98cbb2a13482008c455ecc65d9509a410046214f6632eca84d2080231097b319765426904011881bd98cbb2a13482008c401ecc65d9509a4100461faf6632eca84d2080230f67b31976542690401187b3c18cbb2a13482008c3d9d6c65d9509a4100461ece7632eca84d2080230f671b1976542690401187b3818cbb2a13482008c3d9b6c65d9509a4100461ecd6632eca84d2080230f66a31976542690401187b3198cbb2a13482008c3d98cbb5d9509a4100461ecc65dad4a84d2080230f6632ed605426904013c8c3d98caf2a13482008c3d98cbb579509a410046220f663290a84d2080230f6632ed48542690401187b31976a32a13482008c455ecc64f9509a4100461ecc65da7ca84d2080001187b31938542690401188abd98c9a2a13482008c3d98cbb4d1509a410000230f663260a84d2080281187b31928542690401188abd98c942a13482008c3d98cbb4a1509a4100461ecc64fa50a84d2080001187b31920542690400008c3d98c8b2a134820000461ecc6441509a41004fe30f66d9f8a84d2080231097b36cfc542690401187b38db67e2a134820000461ecd13f1509a410000230f6679f8a84d2080001187b330fc5426904012e963d98c7e2a1348200974a1ecc63f1509a41000024cf6631f8a84d2080259247b318fc5426904000091bd98c7e2a134820000485ecc63f1509a410050630f6631f8a84d2080275187b318fc542690401398c3d98c7e2a134820099c61ecc63f1509a41004c630f6631f8a84d2080261187b318fc5426904012f8c3d98c7e2a134820097461ecc63f1509a410048a30f6631f8a84d2080001187b318fc542690401188bbd98c7e2a13482008c459ecc63f1509a41004621af6631f8a84d20802310c7b318fc5426904011885bd98c7e2a13482008c429ecc63f1509a410046212f6631f8a84d2080231087b318fc5426904011883bd98c7e2a13482008c419ecc63f1509a41004620af6631f8a84d2080231047b318fc5426904011880bd98c7e2a13483368c401ecc63f1509a410046200f6631f8a84d2080230ff7b318fc542690401187f3d98c7e2a13482008c3f5ecc63f1509a4100461f8f6631f8a84d2080230fb7b318fc542690401187d3d98c7e2a13482008c3e5ecc63f1509a4100461f0f6631f8a84d2080230f77b318fc542690401187b3d98c7e2a13482008c3d9e8c63f1509a4100461ecf3631f8a84d2080230f679318fc542690401187b3c58c7e2a1348200973d9e0c63f1509a4100461ecf0631f8a84d2080230f677b18fc542690401187b3b98c7e2a13482008c3d9dac63f1509a4100461ecec631f8a84d2080230f673b18fc542690401187b3918c7e2a13482008c3d9c0c63f1509a4100461ecdb631f8a84d2080230f66b318fc542690401187b3518c7e2a13482008c3d9a2c63f1509a4100461eccf631f8a84d2080230f667318fc542690401187b3358c7e2a13482008c3d998c63f1509a4100461ecc6631f8a84d208025d187b300fc542690400008c3d9807e2a13482008c3d98cc03f1509a4100461ecc65d9f8a84d2080230f6632dcfc542690401187b3196a7e2a13482008c3d98cb33f1509a4100461ecc6589f8a84d2080230f6632c0fc542690401187b319587e2a13482008c3d98ca93f1509a4100461ecc6541f8a84d2080230f66329cfc542690401187b3194c7e2a13482008c3d98ca53f1509a410046212f6521f8a84d2080230f671a90fc5426904011884b19487e2a1348200933d98ca43f1509a4100461ecc6521f8a84d2080230f657a90fc542690401187b319467e2a13482008c3d98ca23f1509a4100461ecc6509f8a84d2080230f6631f8f8542690400008c3d976782a13482008c3d98cbb3c1509a410050630f63f1e0a84d208025d187b1f8f0542690400008c3d8fc782a13482008c459ec7e3c1509a410046212f63f1e0a84d2080231007b1f8f0542690401187ebd8fc782a13482008c3d9ec7e3c1509a4100461ecf03f1e0a84d2080230f66d9f8f0542690401187b318fc782a13482008c3d9767e3c1509a4100461eca43f1e0a84d2080230f63f1f0f0542690401187b1f8f0782a13482008c3d98c7e379509a410000230c65d9b8a84d2080230f6632ecdc542690401187b318fc6b2a13482008c3d8fc78359509a4100461ecc63f1a4a84d2080230f6631f8d0542690401187b31976672a134832e8c3d98c7e339509a4100461ecc63f19ca84d2080230f63f1e0ce542690401187b318fc622a13482008c3d98cbb2f9509a4100001ecc65d97ca84d2080282f6631f8be5426904012e7b318fc5f2a134820096bd98c7e2f9509a41004b1ecc63f17ca84d2080250f6631f8be542690401247b318fc5f2a13482008c3d98c7e2f9509a4100425ecc63f17ca84d2080208f6631f8be542690401007b318fc5f2a13482007ebd98c7e2f9509a41003d9ecc63f17ca84d2080000f6631f8be542690400f678318fc5f2a13482007b3b18c7e2f9509a41003d9c6c63f17ca84d20801ecdb631f8be542690400f663318fc5f2a13482007b319767e2f9509a41003d98caf3f17ca84d20801ecc6521f8be542690401187b1f8f05f2a1348200003d8fc782f9509a41003d98c7e3c17ca84d20801ecc63f1b8be54269040000631f8dc5f2a13482007b318fc692f9509a41003d98c7e3397ca84d20801ecc63f188be542690400f6631f8be5f2a13482008c3d98cbb2f1509a4197461ecc63f178a84d2080230f6631f8bc542690401187b1f8f05e2a13482008c318fc6e2f1509a41003d98c7e2f978a84d2080230f6631f8b2542690401187b318fc552a13482008c3d98c7e2a14c9a4100461ecc65d950a44d2080230f6631f8a8522690401187b1f8f0542913482007b318fc5f2a1489a4100461ecc63f150a24d2080230f6631f8a8502690401187b318fc542793482008c3d98c7e2a1389a4100461ecc63f1509a4c2080230f6631f8a84d2510401187b318fc542692482007b318fc5f2a134924100461ecc63f1509a482080230f6631f8a84d2390401187b318fc542691882008c3d98c7e2a1348a4100461ecc63f1509a442080230f6631f8a84d2190401187b318fc5426908820099461ecc63f1508241004b630f6631f89a412080230f6632eca84d2090401187b318fc542690482008c3d8fc782a1348241004618c7e371509a4120801ecc63f17ca84d2090400008c3d98c7e2a13468008c401ecc63f1509a3400461ecc63f1509a411a00230f6631f8a84d208cc01187b1f8f0542690466008c3d98c7e2a134823200461ecc63f1509a4118001ecc63f17ca84d208c001187b318fc54269045e007b318fc5f2a134822f00461ecc63f1509a411700230f6631f8a84d208b001187b31976542690456008c3d98c7e2a134822b00461ecc63f1509a411500230f6631f8a84d208a401187b31976542690450008c3d98c7e2a134822800461ecc63f1509a411380230f6631f8a84d2089801187b318fc54269044a008c3d98c7e2a1348224004e230f6631f8a84d1180230f6631f8a84d2388c01328c3d98c7e2a10446008c3d98c7e2a13c8223004da30f6631f89a41118025b187b318fc4d2088c011881bd98c7e2690446008c3d98cbb2a134822300461ecc64c1509a411180230f6689f8a84d2088c011881b18fc5426904460090bd98c7e2a134822300461ecc63f1509a411180230f63f1e0a84d2088c0118631f8dc542690446007b318fc5f2a134822300461ecc63f1509a411000230f6631f8a84d2087c01187b318fc54269043c008c3d98c7e2a134821d00461ecc63f1509a410e001ecc63f17ca84d2087001328c3d98c7e2a10436008c3d9c6c63f150821b00461ecc64a1f8a8410d80230f6631f8a8522086c01187b31976542690436008c3d98c902a134821b00461eccf3f1509a410d80246f6631f8a84d2086c01187b318fc542690436008c3d8fc782a134821b003d98c7e2f9509a410d80230f6631f8a84d1886c01187b318fc542690434008c3d98c7e2a134821900461ecc63f1509a410c00230f6632eca84d2085c01187b318fc54269042e008c3d98c7e2a134821600461ecc63f1509a410a80230f6631f8a84d2085001187b318fc542690426009c461ecc63f1509a12004ca30f6631f8a8410900230f671b18fc5420848012d8c3d98c7e2690424008c3d98cbb2a134821200461ece33f1509a410900230f6631f8a84d2084801187b1f8f0542690424008c318fc6e2a1348212003d98c7e2f9509a410900230f6631f8a84d2084401187b318fc5426904200096c61ecc63f134820f00461ecc63f1789a410780230f6632eca84d2083c01187b318fc54269041e008c3d8fc782a134820f004618c7e371509a4107801ecc63f17ca84d2083c01187b318fc54269041c0096c61ecc63f134820d00461ecc63f19c9a410680230f6632eca84d2083401187b330fc54269041a008c3d98c7e2a134820d00461ec7e3c1509a4106801ecc63f17ca84d2083401388c3d98c7e2a134180099461ecc63f150820c0046200f6631f8a841060025b187b318fc4d2083001187b31976542690418008c3d98c882a134820c0046200c63f1509a410600230f6631f8a84d2083001187b1f8f0542690418008c318fc6e2a134820c003d98c7e2f9509a410600230f6631f8a84d2082c01187b318fc542690414008c3d98c7e2a134820900461ecc63f1509a410400230f6631f8a84d2081c01187b318fc54269040c008c3d98c7e2a134820500461ecc63f1509a410200230f6631f8a84d2080c01187b318fc542690404008c3d98cbb2a134820100461ecc63f1509a410080230f63f1e0a84d2080400f6631f8be54269040200004ca5b187b319764100002652d8c3d98c7e2080001328c3d98cad3f104000096c61ecc6561f8820000461ecc656ab0fc4100002652d8c3d8fc7820800013296bd98c7e2f904000099461ecc63f16c8200004ca30f6631f8ac410000265187b318fc552080001187b319287e2a90400009e461ecde631508200004ca30f6632eca8410000230f66f3197654208000118883d98cac2a10400008c3d98cbb561508200004ca30f65d9e0a8410000281187b318e0542080001188abd98c702a10400008c3d98cbb381508200004ca30c65d9b8a8410000231157b318da542080001187b319766d2a10400008c3d98cbb319508200004c9ecc65d97ca841000025b187b318fc512080001187b318fc5b2890400008c3d98cbb2a1448200004da30f6631f89e41000025b187b318fc4f2080001187b31976542790400008c3d98c982a13c8200004b630f6632ec9a410000230f673319764d2080001187b3958cbb2690400008c441ecc656934820000461ecc65dab49a41000025b187b2ecf04d2080001188abd98c762690400008c3d98cbb3b134820000461ecc65d9909a41000025af6632ecbe4d2080001187b319765b2690400008c3d98c9c2d934820000461ecc65d95c9a410000230f6632ecac4d2080001187b31976552690400008c3d98c902a9348200004f251187b1509a410000281258c3d8a84d2080001258c455ec542690400009e461eceb2a1348200004f230f66d9509a4100002791884318a84d20800013f8c4098c542690400009fcd1ecc62a1348200004fa30f6631509a41000027b187b318a84d20800013c8c3d98c542690400009dc61ecc62a13482000046226f6631509a410000231127b318a84d20800011888bd98c5426904000093441ecc62a13482000046220f6631509a4100002310f7b318a84d2080001187b37d8c542690400008c3d9bac62a134820000461ecd5631509a410000230f669b18a84d20800013d8c3d980542690400008c3d98cbf2a134820000461ecc65f1509a410000230f6632f4a84d2080001187b319785426904000092c61ecbb2a134820000461ece85d9509a410000230f670aeca84d2080001187b36576542690400008c3d9aebb2a134820000461ecd15d9509a410000230f667aeca84d2080001187b33176542690400008c4398cbb2a13482000046210c65d9509a41000023102632eca84d2080001187f31976542690400008c3f18cbb2a1348200004d1ecc65d9509a410000252f6632eca84d2080001267b319765426904000091bd98cbb2a134820000485ecc65d9509a410000230f6632eca84d2080001187b30576542690400008c3d980bb2a134820000461ecc65d1509a410000230f6632e4a84d2080001187b31970542690400008c3d98cb62a134820000461ecc65a1509a410000230f6632c8a84d20800013c8c3d948542690400008c3d98ca02a134820000461ecc64f1509a410000230f663274a84d2080001187b365385426904000094bd98c9c2a134820000461ecc64e1509a410000230f66326ca84d2080001188131934542690400008c3d98c992a134820000461ecd14c1509a4100002310363260a84d2080001217b31930542690400008c3d98c982a134820000461ecc64b9509a410000230f663258a84d2080001187b3192a542690400008c4098c942a1348200004d1ecc64a1509a410000230f66324ca84d2080001187b31924542690400008c3d98c912a134820000461eccf481509a410000230fc63240a84d2080001237b31920542690400008c3d98c902a134820000461ecc6479509a410000230f663238a84d2080001187b3191a542690400008c3d98c8c2a134820000461ece1459509a410000230fe6322ca84d2080001187b31916542690400008c3d98c8a2a134820000461ecc6449509a410000230f663220a84d2080001187b3190e542690400008c3d98c862a134820000461ecc6429509a410000230f663210a84d2080001187b31906542690400008c3d98c822a134820000461ecc6409509a410000230f663200a84d2080001187b318fe542690400008c3d9d27e2a134820000461ecdc3f1509a410000231086d9f8a84d2080001187b368fc542690400008c3d9b07e2a134820000461ecd23f1509a410000242f6689f8a84d2080001187b344fc542690400008c3d9a07e2a13482000048deccf3f1509a410000230f6679f8a84d2080001187b330fc542690400008c3d9967e2a134820000461ecca3f1509a410000230f6649f8a84d2080001187b320fc542690400008c3d98e7e2a1348200004a210c63f1509a41004da5d00631f8a84d2080001237e318fc5426904000095bd98c7e2a1348200004a9ecc63f1509a41000024ef6631f8a84d2080001267b318fc5426904000091bd98c7e2a134820000485ecc63f1509a410000240f6631f8a84d20800011f7b318fc542690400008f3d98c7e2a134820000475ecc63f1509a410000238f6631f8a84d20800011b7b318fc542690400008d3d98c7e2a134820000465ecc63f1509a410000230f6631f8a84d2080001187ab18fc542690400008c3d98a7e2a134820000461ecc43f1509a410000230f6619f8a84d2080001187b308fc542690400008c3d9827e2a134820000499ecc03f1509a410000230f6601f8a84d2080000f6632b8fc542690400008c319567e2a1348200004618caa3f1509a410000230f63f1f4a84d2080001187b1f8f6542690400008c3d8fc7a2a134820000461ec7e3c9509a410000279187b1e0a84d208000118883d8f0542690400008c3d976782a134820000461ec9c3c1509a410000230f64c1e0a84d2080001187b240f0542690400008c3d916782a134820000461ec883c1509a41000024cf63f1e0a84d2080001237b1f8f05426904000090bd8fc782a134820000461ec7e3c1509a410000230f63f1dca84d2080001187b1f8e4542690400008c3d8fc712a1348200004f230c6371509a41000023110631b8a84d208000118632ecdc542690400008c319386e2a1348200004618c98371509a410000230c6481b8a84d2080001186322cdc542690400008c319106e2a1348200004617678371509a410000230c63f1b0a84d2080001187b318d4542690400007b318fc612a1348200003d98c7e301509a410000278f66317ca84d2080001107b318be542690400007b319765f2a1348200003d98c9c2f9509a4100001ecc64c17ca84d2080000f663240be542690400007b3191e5f2a1348200003d98c8b2f9509a4100001ecc64417ca84d2080000f6709f8be542690400007b360fc5f2a1348200003d9a27e2f9509a4100001eccf3f17ca84d2080000f6661f8be5426904000084318fc5f2a1348200003f98c7e2f9509a4100001f8c63f17ca84d2080000f6631f8be542690400007b300fc5f2a1348200003d976782f9509a4100001ec7e3c17ca84d2080000c65d9b8be54269040000631f8dc5f2a1348200001f8f06e2f9509a410000230f63f170a84d2080000f6631f8b4542690400007b318fc582a1348200003d98c7e2a1349641004ba30c63f1509a462080001187b318fc542690000008c3d98c7e2a1347e0000461ecc63f1509a3e0000230f6631f8a84d1e80001187b318fc54268f000008c3d98c7e2a134760000461ecc63f1509a3a0000230f6631f8a84d1c80001187b318fc54268e000008c3d98c7e2a1346e0000461ecc63f1509a360000230f63f1e0a84d1b00001187b318fc54268d400007b318fc5f2a1346a00004ca30f6631f8a8340000230f671b18fc541a00001187b319287e2a0d000008c3d98c7e2a1446800004b630f6631f89a340000230f6631f8ba4d1a00001187b3197654268d000008c3d98c9e2a134680000461ecda3f1509a340000230fc631f8a84d1a000012b7b318fc54268d000008c3d98c7e2a134680000461ec7e3c1509a340000230c63f1b8a84d1a00000f6631f8be54268d000008c3d98c54269045a00004d1ecc63f13482230000230f6631cc9a411180001187b318fc542088800008c3d98cbb2a104420000461ecc63f15082210000230f671b6cfc540d80001187b31916542086c00008c3d9c27e2a10436000000230f675388fc410000001187b3795a7e2080000008c3d98c93331040000004d5ecc63f1948200000023114631d0a8410000001347b318e8542080000008c4098c702a1040000004fe68f6759348200000027b187b3a89a4100000013c8c3d95a4d2080000008c4518c7626904000000461ecc63a9348200000026f188a1509a410000001258c408a84d2080000009bcd1ec54269040000004f64cf62a1348200004ba30dc3f1509a410000001187b31916541a00000008c3d9c27e2a0d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def rowDecodeE : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, code =>
    if code = 0 then [] else
      ((rowSignalsE >>> (464*((code &&& 511)-1))) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) ::
        rowDecodeE n (code >>> 9)
def rowsE (i : Nat) : List Nat :=
  rowDecodeE 9 ((rowPackedE >>> (81*i)) &&& 0x1ffffffffffffffffffff)

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x334dd35dbb6fdce370dd369c26b5c733cc1371b871dc5334dd35dcc6c1ce374c7379ae735cc374df2c99a6e1cc374df379ae735cc324cf369c26b5c9304dd35db66c1ce370c935d2e6d99331cc934db96d9c8164e127dae6fdbd31cdd361b25a1ce37cdd2c9b86b9cc34ccd35db06d9ce334d335db66c1ce334dd35dc46c1ce33cc1371b86e5c537cdd2c9b8669cc334e535db66c1ce31cc936dc6711c833cdd35db66c1ce334dd369b86a5ce334dd35dbb6c1ce31cdd35db66c1ce304dd369b86a5ce334dd35db66fdce31cdd379cd6b9cc37cdd379cd6b9cc374cd35db06d9ce33459371c6735cb334dd35db66c1ce else 0x31cdd369b86a5ce324dd369b86a5ce32459371c6735cb33459371c6739cb33459371bd735cb31cdc379cd6b9cc37cdc379cd6b9cc334dc35db66c1ce37cdc2c9b8669cc334dc369b86a5ce374c735db06d9ce374cf35db06d9ce384d831d68669bd374cd35db0711ce374cd35db06edce33cc934dc66d9c8324dd35db66c1ce33cc9371b86e5c531cdd379ce6b9cc31cc936dbd711c837cdd379ce6b9cc3845927dbf6b9bd34cd835d2e6d972334dd35db672dce37cdd379cd721cc334d3371c6735cb334dd35dc46fdce2d4dd35db66fdce334d335db66fdce334e535db63d1ce2d4c1371b86e5c5374cd35dbf6d9ce) else (if i < 96 then 0x334e535dc46c1ce334dd37dbb6c1ce334e5369b86a5ce31cc934dc66d9c831cc934dbd6d9c831cc9375c66edc8294c9375c96edc831cc9375b96edc8364dd379cd6b9cc304d335db66c1ce334dd35da76c1ce374cd361a96e1ce334d8371c6735cb33cdd35db66a5ce164cd371cd719cb334dd361b86a5ce374cd35da96d9ce33cdd379cd669cc37cdd379b86b9cc33cde36dc6711c83845931dbf6b9bd3845933db0669bd37cdd379b8669cc334dd35db66a5ce304e5361b86a5ce334e5361c46fdce304d8371c6735cb364e5379b8669cc304e535dc46fdce334dd35db6689ce364dd2c9b8669cc334dd35db63d1ce else 0x374c7369a9711ce31ca5371c6735cb33cc7371b86e5c5374c7369a96e1ce334dd35db64f9ce334dd35db26c1ce34cd835d2e6d9b8324d831d68669bd370c92d5c26c193374cf35db06edce324dd35dbb6c1ce334d3369b86a5ce374d835d2e6edb833cdd35dbb6c1ce31ce535dc46fdce384d833dbf6b9bd364e52c9b8669cc304e535dc472dce304db35dc46fdce304e535dcc6fdce31ce5379cd6b9cc364e5379cd6b9cc304dc369b86a5ce304e5369b86a5ce364e5379ca669cc394c135dbf711ce334e535dc46fdce304dd35dc46fdce374c135dbf6d9ce304e535db66fdce33cdd35dc46fdce33ce535dc46c1ce)) else (if i < 192 then (if i < 160 then 0x3845933dbf6e5bd334dc35db66fdce374cf35db0719ce374c735db0719ce394cf35db0711ce374d92c99a6e1cc364dd379b8669cc31cdd379cd721cc334d8371c6739cb334dc369b872dce294dd325b8669cc37cdd379ca669cc374cd35dbf6edce334dc361b25a1ce324c736dcc719c8374d835d2e6ed72370c937dbc6ed93374cf35db0711ce294c7371cd719cb33cdd369b86a5ce370c933dc26b19331cd3369b86a5ce31ce5369b86a5ce31cdd369b872dce31cd3371c6735cb31cdd369726a5ce31cdd361b85a1ce374cd369a96e1ce334dd369b85a1ce374cd37db06edce374c1369a96e1ce394cd35db06d9ce else 0x360e5379cd6b9cc360c1371cd6f5cb360c1371c9719cb360c1371cd719cb364e5379c76b9cc394c1361a96e1ce374d9371b8725c5364dd325b8669cc394c9369bf711ce374cd369bf6e1ce368cd371cd719cb374cd361b0711ce334dd361bb6fdce334d3371c66b9cb334dd369726a5ce370c92d5c26b193334dd369b872dce33cc1371b8725c537cc1371b86e5c5374cd35d3e6d9ce37cdd325b8669cc34ccd35d3e6d9ce31cdd325cd669cc31cdd379ca669cc370cd35d2e6d9ce364dd325b86b9cc370dd369c26a5c7324cf31da2669c937cdd379ca6b9cc374cd35dbc6d9ce304dd361c45a1ce37cdd325b86b9cc) else (if i < 224 then 0x324c7375bb6e5c831ca5371c6721cb324dc35db66c1ce370dd369766f5c7360dd325cd6b9cc334dd35db64b9ce294dd379cd6b9cc370dd369766b5c7294c936dc6711c8334dd35db66f1ce374c136168711ce31cdd379cd6f5cc364dd379cd6f5cc374cd35da96e1ce34cd835d2e6d9c6374c735db0711ce374c737db06edce374d935d2e6d9b836ccf35db0711ce31cdb35dc46fdce374d937dbc6edb834cd835d2e6b9bd36ccf35db06b9ce33cdd35dae6c1c9324dd369726a5ce374c1361a96e1ce364d3379b8669cc394cf361a9711ce394c1369bf6e1ce33ce5379cd669cc364e5379b86b9cc384da33dbf6b9bd else 0x374cd361bf711ce374cd361bf6edce370c935d2e6d9ce370c937dbc6edce374d937dbc6edce374c135d2e6d9ce374c137dbc6edce370c937dc26ed9337cd9371b86e5c5370dd369bc6f5c7364dd325b8669ce374d835d2e6e5b836ccf35db06f5ce394cd361bf711ce370cd35dbc6d9ce304dd35db64b9ce370c137dbc6edce370c135d2e6d9ce294dd325b8669ce31cdc325b8669ce370c937dbc6b193294dc36dc6711c8294dc36dc672dc8374c1371b8725c5370c935d2e6ed93370c937dbc6c19337cd8371b86e5c5370dd369bc669c733459371c6729cb324df369c26b5c7364dd379cd721cc)))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x101 else 0x101) else (if i < 7 then 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07 else 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x63c1e5079c000000000000504 else 0x1fc07f01fc07f01fc07f05000000000705) else (if i < 11 then 0x7a400007641d907641d907641d907641cf0005000000040a06 else 0x7a400007641d907641d907641d907641cf0005000000040a06)) else (if i < 14 then (if i < 13 then 0x5c400004ac12b04ac12b04ac12b04ac1cf0005000000040a06 else 0x5c4171000017105c417105c417105c417105c4171020700090105010c07) else (if i < 15 then 0x171000000004ac12b073c12b04ac12b04ac12b050504000000000b07 else 0x1fc07f01fc07f01fc07f05000000000705)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x1fc07f01fc07f01fc07f05000000000705 else 0x1ef0000043073c04307b404307ac043010c043060000000403020b07) else (if i < 19 then 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07 else 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07)) else (if i < 22 then (if i < 21 then 0x7dc1f700001f907e41f707e41f907e41f9040403000000000b07 else 0x4302bc0af02bc0af02bc0af05c40af0000000400040a06) else (if i < 23 then 0x10400007f404107ec041078c04101040410009060301000a06 else 0x3fc0ff03fc0ff03fc0ff05000000000705))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x3e40f903e40f903e40f905000000000705 else 0x1001408d000400100041690004001059c001000400100040010004001000402a0607050008000205050303140b) else (if i < 27 then 0x1001408d000400100041690004001059c00100040010004001000400100040620607050008000205050303140b else 0xa902a40a9028c05a05bc16b02a40a902a413f01780a902a40a905b40a902a40a902a40a902a40a9120015030c090005040402000400041a0f)) else (if i < 30 then (if i < 29 then 0x100040010004001000400101050000000805 else 0x1000101) else (if i < 31 then 0x100040010004001000400101050000000805 else 0x17105c417105c417105c417105cc17100e017105c417105c400605c417105c417105c400e05c417105c41711209001600010e05070308010a001a0e))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0xaf02bc17102bc0af00740af02bc0af010c0af00b00af02bc0af02bc06402bc0af02bc0af0600000e0a0d03010002000402170d else 0x13000101) else (if i < 35 then 0x87000101 else 0x87000101)) else (if i < 38 then (if i < 37 then 0x87000101 else 0x87000000000000870224175021c087021c0870234087021c087021c087021c087000105090000010300000700130c) else (if i < 39 then 0x21c08705dc07a021c175033408d021c087021c087021c087021c0460224036021c08701d8087021c087021c087150c0107100b0011100603000b0c021b0f else 0x8d0098087021c0870334087021c087021c1750224087021c08701b8087021c087021c087060a020c03000c000003000102170d))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x21c087009808d00d8179021c087033408705d40870224087021c087021c087021c087021c0870714040001010b000602000100170d else 0x87000008d01e800005ec087021c087021c087021c1750224087021c0870210087021c087021c087100e0601030007000003000102170d) else (if i < 43 then 0x87000101 else 0x21c0d505d408405f408701d808d0334087021c06e0224087021c087021c087021c087021c087021c087100e0c1100080402000100010300190e)) else (if i < 46 then (if i < 45 then 0x87000101 else 0x21c000021c087011808705d4087021c0870224087021c087021c08705e4087021c08d0900041000010e07060606140b) else (if i < 47 then 0x9906140890000181060c08902240890224089022408905fc089022408902240890224089000104090003000300000000150c else 0x17505d417505d417505d417505d418105d4000061c17505bc17505d416b062417505d41750001001300000c0f00000400150c)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x87000101 else 0xbf000101) else (if i < 51 then 0xbf00000cb02fc0bf02fc0bf02fc0bf0003000700000906 else 0x4b000101)) else (if i < 54 then (if i < 53 then 0x12c0a9012c04b012c04b012c04b0205000000000906 else 0x1f007c01f007c01f007c01f01050000000805) else (if i < 55 then 0x32c0cb032c0cb00000cb032c0cb032c0cb0007000000000a06 else 0x18b02b40ad02b40ad02b40ad02b40ad0001010400000a06))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x1100440110044011004401101050000000805 else 0xc500000c503140c503140c503140c50003000700000906) else (if i < 59 then 0xb002c00b002c00b002c00b01050000000805 else 0xc903240c906340c9032413303240c903240c9070500020101010c07)) else (if i < 62 then (if i < 61 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 63 then 0x100040010004001000400101050000000805 else 0xe700400000000000064c195064418f000000000100000907)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x7000101 else 0x1000101) else (if i < 67 then 0x1000101 else 0x1b000101)) else (if i < 70 then (if i < 69 then 0x101 else 0x101) else (if i < 71 then 0x101 else 0x101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x101 else 0x7f000101) else (if i < 75 then 0x1000101 else 0x1000101)) else (if i < 78 then (if i < 77 then 0x1000101 else 0x13000101) else (if i < 79 then 0x1000101 else 0x1000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x1000101 else 0xb000101) else (if i < 83 then 0x1000101 else 0x1000101)) else (if i < 86 then (if i < 85 then 0x1000101 else 0x1000101) else (if i < 87 then 0x1000101 else 0x1000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x1000101 else 0x101) else (if i < 91 then 0x1000101 else 0x13000101)) else (if i < 94 then (if i < 93 then 0x1000101 else 0x1000101) else (if i < 95 then 0x1000101 else 0x100040010004001000400101050000000805))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x101 else 0x1000101) else (if i < 99 then 0x1000101 else 0x1000101)) else (if i < 102 then (if i < 101 then 0x1000101 else 0x1000101) else (if i < 103 then 0x101 else 0x1000101))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x13000101 else 0xf000101) else (if i < 107 then 0x1000101 else 0xb000101)) else (if i < 110 then (if i < 109 then 0x1000101 else 0x1000101) else (if i < 111 then 0x1000101 else 0x1000101)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x1000101 else 0x1000101) else (if i < 115 then 0x1000101 else 0x1000101)) else (if i < 118 then (if i < 117 then 0x1000101 else 0x101) else (if i < 119 then 0x1000101 else 0x13000101))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x1000101 else 0xb000101) else (if i < 123 then 0x1000101 else 0x7f000101)) else (if i < 126 then (if i < 125 then 0xf066c00f003c00f039c05f01ac00f000006b065c19d01ac199003c00f003c00f003c18f0000001100001104000d0101150c else 0x100040010004001000400101050000000805) else (if i < 127 then 0x1000101 else 0x7f01fc07f01fc0f901fc07f01fc0f901fc07f03e407f0a0a070005050107000f09))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x7f03e40f900680fb01fc0f9006000001fc07f01fc07f01fc07f01fc07f01fc07f0f11050001000300040600130b else 0x3c19f003c00f003c00f003c00f0005000000000906) else (if i < 131 then 0x100040010004001000400101050000000805 else 0x3c1a1003c00f003c00f003c00f0005030000000906)) else (if i < 134 then (if i < 133 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 135 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 139 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 142 then (if i < 141 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 143 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x100040010004001000400101050000000805 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 147 then 0x3ec07f000400100040010004001000400100000104000200000c08 else 0x10004001000400000000fb01fc001000400100040010000000a000000000d08)) else (if i < 150 then (if i < 149 then 0x100040010004001000400101050000000805 else 0x4065027c001024c0c9031c03f000400100040010004001021c001020f000b010401020500110a) else (if i < 151 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x1a3000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x101 else 0x100040010004001000400101050000000805) else (if i < 155 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 158 then (if i < 157 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 159 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x6500040000004000000403f0004001024c087000400100041a50906090003000000060f09 else 0x100040010004001000400101050000000805) else (if i < 163 then 0x69c0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06)) else (if i < 166 then (if i < 165 then 0x6a40b100040000004001000400100040010005000000000a06 else 0xb002c00b002c00b002c00b01050000000805) else (if i < 167 then 0x137000400100040870004005000400100040c50900060007040100020e09 else 0x130000013004c0a3004c01301fc013004c0130424013004c0130c00090009010301000f09))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x1a7004000000000e704dc087003c0010004001000400100040010002040005030000010f09 else 0xf003c00f003c00f003c00f01050000000805) else (if i < 171 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 174 then (if i < 173 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 175 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 179 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 182 then (if i < 181 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 183 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06) else (if i < 187 then 0x1f007c01f007c01f007c01f01050000000805 else 0x100040010004001000400101050000000805)) else (if i < 190 then (if i < 189 then 0x100040010004001000400101050000000805 else 0x403f0004001000400100040010005000003000906) else (if i < 191 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x403f0004001000400100040010005000003000906 else 0x403f0004001000400100040010005000003000906) else (if i < 195 then 0x40050004001000400100040010005040000000906 else 0x400000041ab000400100041ad00fc005000400100040010004000700000a000e08)) else (if i < 198 then (if i < 197 then 0x1b7001c00702bc14706c41b10000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c else 0x1b7001c00702bc14706e41b90000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c) else (if i < 199 then 0x2f00bc02f00bc02f00bc02f01050000000805 else 0x1100440110044011004401101050000000805))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x100040010004001000400101050000000805 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 203 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x101)) else (if i < 206 then (if i < 205 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 207 then 0x101 else 0x100040010004001000400101050000000805)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x41370004001000400100040010005000006000906 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 211 then 0x104dc00100040010004001021c0010006000201000a06 else 0x41370004001000400100040010005000006000906)) else (if i < 214 then (if i < 213 then 0xcb04dc000000003f00000010004001000400100040010604020002000100000d09 else 0x14904dc001000400100040af00040010004191060007030104020c07) else (if i < 215 then 0x1fc07f01fc07f01fc07f01fc048022807f01fc07f01fc07f01fc07f01fc07f0004010004060601000300130b else 0x1000101))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x1000101 else 0x2f000101) else (if i < 219 then 0x1000101 else 0x1000101)) else (if i < 222 then (if i < 221 then 0x1000101 else 0x7f000101) else (if i < 223 then 0xf000101 else 0x1000101))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x1000101 else 0x1000101) else (if i < 227 then 0x1000101 else 0x1000101)) else (if i < 230 then (if i < 229 then 0x7000101 else 0x1000101) else (if i < 231 then 0x1000101 else 0x7000101))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x13000101 else 0x1bb000101) else (if i < 235 then 0x1000101 else 0x1000101)) else (if i < 238 then (if i < 237 then 0x1000101 else 0xb000101) else (if i < 239 then 0x1000101 else 0x1000101)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x1000101 else 0x1b000101) else (if i < 243 then 0x1000101 else 0x1000101)) else (if i < 246 then (if i < 245 then 0x1000101 else 0x1000101) else (if i < 247 then 0x1fc07f006007f01fc07f02481bd01fc07f01fc05001fc07f01fc00001fc07f01fc07f01fc07f07000509020209080503000000170d else 0x1000101))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x1000101 else 0x12b000101) else (if i < 251 then 0x1000101 else 0x100040010004001000400101050000000805)) else (if i < 254 then (if i < 253 then 0x100040010004001000400101050000000805 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 255 then 0x100040010004001000400101050000000805 else 0x1bf00041c10004001000400100040010005050000000a06)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x40c10004001000400100040010005000006000906 else 0x100040010004001000400101050000000805) else (if i < 259 then 0x4c013004c013004c013004c01301fc013070707010005000b07 else 0x42c07f004c013004c013004c013004c013004c01300000404000800000d08)) else (if i < 262 then (if i < 261 then 0x3f41c7000c003000c00307140a700f4003070c003000c003000700000b000700040f09 else 0x15b0000043056c1d1010c1cf072405806c415b056c1cd00001cb056c15b056c15b056c15b000e00090008060300000000150c) else (if i < 263 then 0x15b0000043056c1d3010c1cf072405c06e415b056c02d00001d5056c15b056c15b056c15b000e00090008060300000000150c else 0x4c013004c013004c013004c01301fc013070707010005000b07))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x1fc000004c000004c013000c013004c013004c013004c013004c01309040007000000060001100a else 0x4c01300740130074013004c013004c07f004c013004c0130a0b060402000505000f09) else (if i < 267 then 0x1d700001d7075c1d7075c1d7075c15d075c1d707641d700081d70c0a020900080605050f09 else 0x101)) else (if i < 270 then (if i < 269 then 0x101 else 0x65002c0000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 271 then 0x1000101 else 0x11000101)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0xbd000101 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 275 then 0x1000101 else 0x101)) else (if i < 278 then (if i < 277 then 0x1000101 else 0x1b000101) else (if i < 279 then 0x15d0000038055c157055c12b055c171055c157055c157055c1570704020003080002000f09 else 0x101))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x5000101 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 283 then 0x63000101 else 0x105000101)) else (if i < 286 then (if i < 285 then 0x101 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 287 then 0x1000101 else 0x1000101))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x740b3000000002c40b102c403702c40b102c40b102c40b10907000005000500030e09 else 0x1000101) else (if i < 291 then 0x104dc00100040010004001021c0010006000201000a06 else 0x1000101)) else (if i < 294 then (if i < 293 then 0x101 else 0x15f000101) else (if i < 295 then 0x1000101 else 0x101))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x101 else 0x1b000101) else (if i < 299 then 0x1db00001db076c1db07741db05741df00281db076c1db076c1db0a070a0004010104000f09 else 0x101)) else (if i < 302 then (if i < 301 then 0x101 else 0x5000101) else (if i < 303 then 0x100040010004001000400101050000000805 else 0x109000101)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x101 else 0x7f0000013004c013004c013004c013004c013060301040005050b07) else (if i < 307 then 0x93024c000027400006b4041024c0930784093024c093024c0930106020006020000000f09 else 0x1000101)) else (if i < 310 then (if i < 309 then 0x11000101 else 0x1000101) else (if i < 311 then 0x101 else 0x101))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x3ec0050014005001400503e40050014005020108040400050b07 else 0x5000101) else (if i < 315 then 0x5000101 else 0x101)) else (if i < 318 then (if i < 317 then 0x101 else 0x6201880000000062018800041880620188020201000100000a07) else (if i < 319 then 0xa6029800000000a6029800042980a60298020201000100000a07 else 0x4000001c3700004001000400100040010004370000437000040010004370000c370000400100040010004001000400100043700004370000400100040010004001001700100013061500251d000000001e000b0c1c2614)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x18c0630000000018c0630000463018c0630020201000100000a07 else 0x4000001c3780004001000400100040010004370000449200040010004370000c4de000400100040010004001000400100043700004498000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 323 then 0x4000001c3800004001000400100040010004370000448a00040010004370000c4be000400100040010004001000400100044000004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x4000001c388000400100040010004001000437000044a200040010004370000c3700004001000400100040010004001000440800044a0000400100040010004001001700100013061500251d000000001e000b0c1c2614)) else (if i < 326 then (if i < 325 then 0x4000001c398000400100040010004001000437000043700004001000450c000c5760004001000400100040010004001000437000044b0000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x3700004001000400100040010004001001c00300040010004001000437000040010004001000400100040010dc000100040010213140e14100c051805130015040102001f11) else (if i < 327 then 0x370000400100040010004001000c001001c0010dc0001000400100040010004001000400100040010dc0001000400100040010213140e14110c0a1715050001020605001f11 else 0x4000001c39000040010004001000400100043a6000437000040010004370000c3700004001000400100040010004001000441800044c0000400100040010004001001700100013061500251d000000001e000b0c1c2614))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x400100040000004001000400100040030004001000400100040010dc0001001c3700004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x4000001c37000040010004001000400100043700004370000400100045b4000c57e0004001000400100040010004001000442000044a8000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 331 then 0x4000001c37000040010004001000400100043ac00044e2000400100044cc000c370000400100040010004001000400100044120004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x620188000400000001d00000000100000706)) else (if i < 334 then (if i < 333 then 0x106302400000000000000000504 else 0x2980a602b80000001000100000504) else (if i < 335 then 0x400100040000004001000400100040030004001000400100040010dc0001001c4d00004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x101)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x400100040000004001000400100040030004001000400100040011340001001c4d00004001000400100044d00004001000400100000418000f020000000a16001503021e10 else 0x63018c06d80000001000100000504) else (if i < 339 then 0x7b418d06340000001000300000504 else 0x872000101)) else (if i < 342 then (if i < 341 then 0x86a00046320000000000100000504 else 0x18d800018d8000237000100000000000605) else (if i < 343 then 0x620000000418806a00000000000000000706 else 0x2980a603020000001000100000504))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x400100040010004370000400100040030004001000400100040010000001001c428000400100040010004370000400100040010000041c0017020000000f19001003121e10 else 0x400100040010004428000400100040030004001000400100040010000001001c428000400100040010004428000400100040010000041c0017020000000f19001003121e10) else (if i < 347 then 0x63018c06880000001000100000504 else 0x101)) else (if i < 350 then (if i < 349 then 0x1a9000100006340100000403 else 0x40010000001000400101f40010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e) else (if i < 351 then 0x62000100001880100000403 else 0x630001000018c0100000403))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0xa6000100002980100000403 else 0x230dc0001000c0010004001000401100040010004001000400100040010dc000b00040010004001000400100040010000150600120500130e02051106001c0f) else (if i < 355 then 0x18c000100006300100000403 else 0x101)) else (if i < 358 then (if i < 357 then 0x46340000000303 else 0x100040010044001000c0010004001000400100040010004023002c001000400100040010dc00010004001101702130012000a0c01010d00001a0e) else (if i < 359 then 0x4000001c3b000040010004001000400100043b4000437000040010004514000c370000400100040010004001000400100043700004510000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x18806200000000001000100000504))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x18c06300000000001000100000504 else 0x2980000001000000000404) else (if i < 363 then 0x4000000400700040010004001009c0010004001000400100043700004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f else 0x101)) else (if i < 366 then (if i < 365 then 0x118c06300000000000000000504 else 0x18d000100006340100000403) else (if i < 367 then 0x101 else 0x46320000000303)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x63600046360000000000100000504 else 0x400000040070004001000400101fc0010004001000400100044280004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f) else (if i < 371 then 0x400100000010004001009c0010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e else 0x4000000401f000400100540010004023000400100040010004001002c00100040010004370000400100040011114030a000800020d01070609001a0e)) else (if i < 374 then (if i < 373 then 0x700040010004001003c00100040010004001000437000040010004001000408100040010004001007c0010b0e080a000a000309030f0604001a0e else 0x4001000400500040070004001000400100040010034083021400500040010004001000437000040010004001000400100040010200160e010911181b180f0504021700001f11) else (if i < 375 then 0x18c000100006300100000403 else 0x1006c0010004001000400100040010004001001c0010004001000400100040010024001000400102120b04040f05060105030000180d))) else (if i < 380 then (if i < 378 then (if i < 377 then 0x700040010004001003c00100040010004001000437000040010004001000400b0004001000400100440010b0e080a000a000309030f0604001a0e else 0x700040010004001005400100040010004001000437000040010004001000400b0004001000400100e40010b0e080a000a000309030f0604001a0e) else (if i < 379 then 0x21c087021c08f02240870180087022c087021c087021c087021c087021c03a02340870030087021c004021c087021c087021c087021c087021c08719151100150016171508000b020107000000122313 else 0x868188000000009501e800041b00620190020201000100000a07)) else (if i < 382 then (if i < 381 then 0xc2029800000000b302c800042ac0a602a8020201000100000a07 else 0x8700040030f0000100040010dc001f0004001000400100040010004007000400510c00930f1000100040010dc00010004001000400100040010004091000452000fc52400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17) else (if i < 383 then 0x8700040030f0000100040010f0001f0004001000400100040010004007000400510e00930fa000100040010f000010004001000400100040010004091000452800fc53400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x87000400310e0001000400110c001f0004001000400100040010004007000400510c009310f0001000400110c00010004001000400100040010004091000453800fc53c00040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x87000400314a00010004001148001f0004001000400100040010004007000400514e009314c0001000400114800010004001000400100040010004091000452000fc7a000040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x1b8063000000001ea0690000466018c0640020201000100000a07) else (if i < 387 then 0x5aa000101 else 0x93024c8c8025c093026c099024c005158855a024c093024c0930254093024c099024c089024c007024c09d024c093024c093024c093024c093024c0001a1e111d00111e15001a070e0a00060803020f2313)) else (if i < 390 then (if i < 389 then 0x1002440a5029c091025c091028c001024409f024409102a476a02440911d8808f024409102440a1024400102440910244091024409102440910e1c001102000c19060b140200020a000a062212 else 0x6322188000000400023406ba19c865a0000000800000906) else (if i < 391 then 0x62000100001880100000403 else 0x4001000400100040010004001000400100340010004001001400102ac001026c00700040010dc00010004001000400100000c1a0003000100000614000000121d10))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x10000001000403f000400702440010dc0540000c00100043c4000401f000400100040010014001026c00100040010004001000400100040010004001001a10161200041219140209091909000104002313 else 0x4005000400100040270244430001c001026c0010004001000400100040010004001000400100040010dc000100040010004001020d1610141a0e0b1a0d050001020608001f11) else (if i < 395 then 0x31100001000400014900010004007000400100140010004001024c00100040010004001000400100040010004370000400100040010004001001a0000000e180a001900160008111209022112 else 0x4000002c001000c0011490023024c0ad0004001000400100040110004001000400100040010004001000400100040010dc00010004001080016061a14110f090419000c00000b022011)) else (if i < 398 then (if i < 397 then 0x88024e000000006201f000041b807e8188020201000100000a07 else 0x6781de0000000000025806300010738262010000000000000a07) else (if i < 399 then 0xbe02c600000000a602d000042980b682a0020201000100000a07 else 0x1000400100040010dc00b111200af1600001000400113b8003000400116e800100040010004001000400100043b800040010004001000400700043700004001000400100090118241b1e18031713100c00211200231701070b2916)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x1000400100040010ee00b111400af1620001000400113d80030004001170800100040010004001000400100043b800040010004001000400700043b80004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x590000101) else (if i < 403 then 0x10004001000400111200b111200af1660001000400113f802b00040011728001000400100040010004001000445000040010004001000400700044480004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x10004001000400116000b116600af16000010004001212802b00040012080001000400100040010004001000458800040010004001000400700045800004001000400100090118241b1e18031713100c00211200231701070b2916)) else (if i < 406 then (if i < 405 then 0x1b208e2000000018c0698000463020a0638020201000100000a07 else 0x8940000794000000000404) else (if i < 407 then 0x8841f90000000400020c06c418d06840000000800000906 else 0x740b102c40b120e00b302c40b102c47ec02c488c02d40b102c408300c00b100dc01d1e300b102c40b102c40b102c40b102c40b102c40b100001112001906180011190500000d0700010b002314))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x10004001000400116e80b117280af208000100040011f0802b000400116e800100040010004001000400100045c200040010004001000400700045ba0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f286aa000084218c800119480001be8632030300000000010a07) else (if i < 411 then 0x10004001000400113b80b113f80af2128001000400113b80b700040011f0800100040010004001000400100044f600040010004001000400700044ee0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f786b6000085218d800119b80001c38636030300000000010a07)) else (if i < 414 then (if i < 413 then 0x400100040b100040010004007000c0010004001000400100045a000043700004001000400116e80010004001000400100040010100101100120f07091a0d0403031805021f11 else 0x1116000100040010dc00b100040010004003001c00100040010004001000400102bc001000400100045ba0004001000400100040010314151216140c1607080e0002040104002011) else (if i < 415 then 0x110004001000c00113b80010004001002c0b9000402300040010004001001c00100040010dc00010004001000400100040010000021a0013001400000b08001808011e10 else 0x210dc0001000c001000400100040110004001000400100040010004001135800b00040010004001004400100040010000150600120500130e02051106001c0f))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0x37000040010084001000c001005c0110004001001c00100040010004007000400100040010004001000400100040010001000b000f010014150d030f07041c0f else 0x18c000100006300100000403) else (if i < 419 then 0x100040010004370005c003004401100440af001c01100443b8004401100040110044001004401100440110044506004400100440110100170917150c19080618010b020208002011 else 0x40110004001000c000002c001000400100040b1000400700040010004001001c00100040010dc00010004001000400100044480000021a000c001400000b08001708011e10)) else (if i < 422 then (if i < 421 then 0x400100040010004001000c0bd15300010054005000401f000400100040bb0004001000400b000400b00040010dc000100040010000151114100b031b0a170018000c07021f11 else 0x18c000100006301ee000000010000000605) else (if i < 423 then 0x1000c0010004001000400100040010004001004c0010004001000400100040010074001000400102120b04040f05060105030000180d else 0x100040390004001135000300e403900e403900e4370001c0390004039007c00100e403900e401100e44d600e401900e403901001509141208171a06150108020206001f11))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x62000100001880100000403 else 0x100040010004001000401d0004001004c00f0000001000400100040010dc0001001c01300040010004001000400100040010000001c000a02010000081a000801171d10) else (if i < 427 then 0x6200010000188070000000010000000605 else 0x102fc460000400100040010004001007c00100040010004015007c0010004005004400100040070004001002c00100043700004001004c00b00200800131d071a161900151015030107082212)) else (if i < 430 then (if i < 429 then 0x100000010004001000400700040030004001000400100040c10004001160837000040010004001174000100040010004001000400101001210001411001a0d0f0709070306021f11 else 0x2980000298000000b000100000504) else (if i < 431 then 0xb002c00b00040190004003030c00b001c00b002c001002c00b000400b0004001000400b002c00b012c00b0dc000b002c00b0100150f12070c051a0b160007011806001f11 else 0x87031c0010004001021c37011a0001032c0010004001000455402b403f021c00100040600324001000400100040c500040010304001000400100043c4000c3e0001c00102445d80004001024c001007c00100140010004001000458200040191a2f2f29182a24311032232f1522000d0a092f25011600002303200006381d)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0xcd03440cd021c0cd021c0870180087022c0cd0334087033c0cd03340cd03340cd033408703340cd034c06003340cd0334087021c060033400003340cd03340cd03340cb03340cd24041d16171202181918000a1c000014110100121a062916 else 0x8703540dd021c0e10354017035c0d9021c087021c087021c087036c090021c09801200d5021c08b0334087021c06001800cd021c087021c0870180087021c0d1021c08700d8060021c0871c18060021c0d102a0087021c08701400870160087020008b01800b0022c06802200cd01e00e303540cb01c0087037c08702e0087021c060021c0d50280087004a424b4947413d47454343413d3b38221d1b3733311900152e110d2d2b3c24260c0708342c2303045029) else (if i < 435 then 0x106201880000000403 else 0x1063018c0000000403)) else (if i < 438 then (if i < 437 then 0x10a602980000000403 else 0x401f0004001001400b005400100040010dc0001000400100040010004019000437000040010004001000400100170d0b0d150e0c0e06000800000803041d11) else (if i < 439 then 0x118c06300000000403 else 0x118d06340000000403))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x118c86320000000403 else 0x10004001000400100040010004000017c01f0054001000400100040010004005002c001000400100040010dc00190004001000d0100000a021b00020a19000000161d10) else (if i < 443 then 0x40010004001000400100040050054001007c001006400100043700004001000400b000400100040010004001000400f0018000900170c17000f0015000002011d10 else 0x7c001000000100040010004001001400b000400100540010004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10)) else (if i < 446 then (if i < 445 then 0xe40010000001000400100040010014051000400103940110004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10 else 0xe7000447800044ee000400117800af0004001000c5e200040010f60087000400f0004130030400100040010004001000400700040010dc00010004001000400100044ec00040010004001091e0a1c20020521231d001b240d170010130f1e00000d2c17) else (if i < 447 then 0x2d40af000400100040010064001000400b0004005002c01f006401f00044ee000400100540010014001000437000040010004015000400100040010004001000400100040010004001191d0a22182306240e21002216100b002300161a1b0e052b17 else 0x3900000010004001004400100040010dc001500044d6007c00100440010064001000400100040010044001004400100040e500fc0010004001000400b0014011000400100040191c260023121d12220f1a200000221e170808000005022916)))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x41e006201e2000018800020004000705 else 0x11460007000400100140010004001000400100040010dc0001000c001015c001000400100040010004001001451a000400100040010004001001018190010001a00031200000d0008001103022414) else (if i < 451 then 0x10004568000400700040010004001000400100040010004001001c00100040010004001000402f00040170c13000d0b1201000103000b000b1a0e else 0x40010004001000400f0000001007c001000400100540010014001000405100040010004001000400100040010dc00190004001000604000001071c00020b1a000000121e10)) else (if i < 454 then (if i < 453 then 0x100bc0010004001002c001004400100040010004007008c0010004001000400100040010dc0001000400100040010c19031304000012000a060f0507021c0f else 0x100040b10004001000400100040010dc000100040010034001000400116e80010004001000400500040010004007000400d00140010004001001c0010004001000400100040011520251c001a24140815192507020f0001240e2100032a16) else (if i < 455 then 0x40010004011018c0110004001004400d001c01100440630044011004400103a401100040110dc00110044011004401100000d0f0015090c00150100001100021d10 else 0x100140010dc000100040010004007030458200040010004001021c00d001400100040010004001000400100040010004001000400d0004007000400101800010004001000400100040011d26160020100224000e0d1d251c180424000b0f0116002c17))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x106201880000000403 else 0x10a602980000000403) else (if i < 459 then 0x40000004001006400100040010004001007c02f00540010dc00010004001000400b001400100040010dc0001000400100040010000090b00190d1500150100000b00021e10 else 0x118c06300000000403)) else (if i < 462 then (if i < 461 then 0x10004001000400100040030004001003c0011200001001c007000400100040010004001000400100040010e150012000c0b160102090006031a0e else 0x4001004400100040010004001005c0010dc000100440010004524000400100040010004001000400100040010084007005c0010004001024c021001c0010004001000400000040010925002508231a200200141e1001101a0317001500142a16) else (if i < 463 then 0x4013000400b0000001002c00b0004001002c00b000400b000400b002c00b003c00b002c00b002c00711000d000c0203000a05000404180d else 0x62000106200000100000403)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x63000106300000100000403 else 0xa600010a600000100000403) else (if i < 467 then 0x1006403900040010004370010400100040af000400100040e500040010004001005c00100040010004001000400700040010dc000100fc0150004001001611152113171800031306110000041611072413 else 0x10004130000c05f03ac00003ac069000003903b40ef000c07f0400000009000300000f09)) else (if i < 470 then (if i < 469 then 0x18c000118c00000100000403 else 0x106201880200000403) else (if i < 471 then 0x106201880200000403 else 0x18806200010000000403))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x18806200010000010403 else 0x58018c058015805b0160058016805a8160058018805b8160080c050b040a0108000f09) else (if i < 475 then 0x1000101 else 0xb000101)) else (if i < 478 then (if i < 477 then 0x5c029805c015808f017005c017805e817005c018808f8170080c050b040a0108000f09 else 0x1000101) else (if i < 479 then 0x9f0208082818809f818800040000000328000000030302010a07 else 0x9d0210084818809d81a0004c0000000000000000000302010a07))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x1000101 else 0x18806200010000000403) else (if i < 483 then 0x18806200010000000403 else 0x18806200010000010403)) else (if i < 486 then (if i < 485 then 0x18806200010000000403 else 0x40000000188000000000404) else (if i < 487 then 0x1880dc018809b016005c01880620188080026e06201880004202080d000c070b040a031009 else 0x106201880200000403))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x18800040000620000000000000504 else 0x1880620048001400000000000000000100000706) else (if i < 491 then 0xc000001880308001062000000000100000705 else 0x106201880200000403)) else (if i < 494 then (if i < 493 then 0x400100040010000001000400700040010004001000400100040010004001000c0010004001000400711000d000c0203000a05000404180d else 0x620000000000d000100000404) else (if i < 495 then 0x3c1880000000303 else 0x5406200150000010403)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 0x1000101 else 0x306001880200000403) else (if i < 499 then 0x6200000000188062018806200010620188010000000000000a07 else 0x80063008001681f4020008001782160200080018823a8200080c050b040a0108000f09)) else (if i < 502 then (if i < 501 then 0x1000101 else 0xc0010dc0017000401100040010004001001c02100040010004001000400100040010004001000400100040011905021000110505000303040000001b0f) else (if i < 503 then 0xa6000100002980100000403 else 0x100040010dc00010004001000400100040010004001005c00100040010dc0007000400700840010004001004402f000400100040011618151814170c001302070001010004002011))) else (if i < 508 then (if i < 506 then (if i < 505 then 0xf103cc01100bc000000c003000007f0004001000000000301000b07 else 0x18c000100006300100000403) else (if i < 507 then 0x4001000400100e4001039401700040010004001001c0010dc002f00040010004001000437000040010dc0001000400100640010004001011a00030b00110c0004101600020a0e08012112 else 0x400100040010004001000400100040010034001000400100040010004007001c001000437003d400100040030004001000201000005001a00120116000e00031d10)) else (if i < 510 then (if i < 509 then 0xa6000100002980100000403 else 0x40000000000000c0010004003000437000040010004001000400100040010004007000400100040010004001000400100040010d0718030c020c0005010a0000030600011e11) else (if i < 511 then 0x1000101 else 0x9a063009a01681f5026809a023821e026809a018c23b0268080c050b040a0108000f09))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0xc0010004001000000100040070004001000400100040010004001000400100040010004001000400111000d000c0203000a05000404180d else 0xb0a602980200000403) else (if i < 515 then 0x2980340000002c298000300000504 else 0xbd02e80ba82980bd82b000040000000000000000000302010a07)) else (if i < 518 then (if i < 517 then 0x1000101 else 0xc013000400b0000001002c0070004001002c00b000400b000400b002c00b000400b002c00b002c01311000d000c0203000a05000404180d) else (if i < 519 then 0x42980000000303 else 0x10a602980200000403))) else (if i < 524 then (if i < 522 then (if i < 521 then 0x2980a600010000000403 else 0x2980a600010000000403) else (if i < 523 then 0x142980a60058000000003000000000605 else 0x29800040000000000303)) else (if i < 526 then (if i < 525 then 0x2980a6000b0000000403 else 0x2980dc02980b9017005d02980a602980b802e60a60298002c2e2080d000c070b040a031009) else (if i < 527 then 0x298000c0000a60280000000000504 else 0xa6000000002980a602980a600010a60298010000000000000a07)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 0xb000101 else 0xb806300b801781fc02e00b8023822602e00b8029823c82e0080c050b040a0108000f09) else (if i < 531 then 0x40d800040130004370002c04b002c041002c001002c0010004007004c00b002c00b002c00b002c003002c00b002c0010f150014111205000700100003040000021e11 else 0x4001000400100040110004001000c12e000400100040010004001007c001000423000040e00388001000400704b000100000010004001004c001111f13001610001500140a051403080104002212)) else (if i < 534 then (if i < 533 then 0x10004001000471000043701c5800500040070004001000471200040011c50001000400100140010004003000400100040010dc00010004005000000100000010dc00011b180f1d0418001c0200120017151d1b130b1908002715 else 0x100040010004001000400101e40030004001000437000040f700040010004001001c005000400100040010004001000400000130b1100000a0100040506000201041d10) else (if i < 535 then 0x7f03e407f01fc07f01fc0f903ec5ea01fc0f901fc07f01fc0f903e407f01fc0f901fc07f0cc05ec01fc07f17b807f01fc07f17a007f01fc07f0000160f141b0f031506110e08050a0006022212 else 0x100040050004003000407f001474c00040070004005000400100043700004718000400100040011c6800100040010f20001000437000040fb00040011d38000000400100040012210170000030021201a1a1d1401100d1b0b160101172916))) else (if i < 540 then (if i < 538 then (if i < 537 then 0x100040050004003000407f0014774000401d0004005000400100043c80004720000400100040011c8800100040010f2000100043c800040fb00040011dd8000000400100040012210170000030021201a1a1d1401100d1b0b160101172916 else 0x3fc000101) else (if i < 539 then 0xc03d03f400103fc005000400100140010004001001447400040010004005000477c00040011e180010004001000400100040010d000012001a0a160c030b0400040e0004022012 else 0x1e7879c0100000303)) else (if i < 542 then (if i < 541 then 0x40010004003000400100040010004001001c00100040000dc0001000400100040051ca071a000400100040010004001000400100140c16000a0200000c0f06000407021e10 else 0x2700340010004001000401d000400100040010014001001c71a000400100040010dc0001000400100040000004001000400100040010e050f0e00140c0900000f110002040009032012) else (if i < 543 then 0xdc00011d3800100040010004001001401f000407f00540fb0004001000400100040070004001000400100040010004081000400100010f121c000e140905110f05020301041f11 else 0x40010074005000400100043d0003c001000400100040fb1ce80010004001000400100040050dc001d112074c1cc075e01fc00500040010004001000400100040070004001000400300040010026252a001a2318001c1d030000110b001a02000016080c2d18))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 0x1000474e0014001000401f00040150004001001400101a400101fc005000400b0004001007c3700004001001402d00040190004001000400100040010014001002c00100040010404001002112200e0f211e1523042408010000151b09000118022c17 else 0x40010004103000400100040010004001003401b000400100143700004001001c001000400100040050004001000400500040010004005000471a0004001001400100040011e20100b1827021900021b1d14120e030200180e080e2916) else (if i < 547 then 0x300040010074001003c013002c001000400100040010004105003c0010004001000437000040010004744000000100040010004001004c001101f0f0b001e001503100a05000309010a002112 else 0x4001000000100040bb00040010004001000400100040050004001000400100040010004001000408317070700070401090402000001180d)) else (if i < 550 then (if i < 549 then 0x40010000001000400700040010004001000400100040210004001000400100040010004001000401b17070700070401090402000001180d else 0x4003000c013000c0030dc001b000c017000c009004c001004401f00040010004001000c003000c003000c003001c00000020c160007020600040704000006021d10) else (if i < 551 then 0x40010000001000400100040010004001000400100040070004001000401300040010004001000400317070700070401090402000001180d else 0x40010000001000400100040010004001000400100040070004001000400300040010004001000401b17070700070401090402000001180d))) else (if i < 556 then (if i < 554 then (if i < 553 then 0xd0074750000c000004c013004c109042407f004c01101fc01301fc001004c01301fc0010dc00131d50013004c0010f200130f300131d580131d480fb004c013004c0130004001042c330004c001000407f042401f004c013004c107000c270f0000002e00082811002e192d00231c03001b001800151b01351c else 0x1ba01800cc018401fc3300c4033018800fb0cc033018886ec1ba807f03f407f0ce00fd01fc07f044407f189007f01fc33003f407f01fc07f03ec07f043407f01fc33c046410f01fc6ee189807f01fc11301fc07f01fc0fb01fc0fb03ec0fb045407f01fc07f01fc03d0cc007f01fc07f01fc07f01fc07f01fc0fd03f407f01fc11701fc07f1800000013004800330000000e4a3b490748474600453a442e43424129331f40253f3c301e21280f4d28) else (if i < 555 then 0xfd01f40fd03f433003f40fd03f411b03f40fd03f40fd03f40fd046c10f0cc00fd03f433001fc07f01fc0fb01fc0fd03ec0fd03ec0fd03f411b03f407f03f407f03f40fd1f1800181c16141018110c03000b000008001206032815 else 0x401300040010004001000400f007400100043700004001000437000040010004001000000100040010004001002c000000f0c15000a0a0400050706000001021c10)) else (if i < 558 then (if i < 557 then 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110a00010004001007400100040000004001002c00100121610001f1d1800021c151705110b1606190207002916 else 0x400f0004013000400100040010004001000437000040010004001000401d0004000000400100040010004001002c00f0004001000d07060005091400020b0400000d001e10) else (if i < 559 then 0x8c001004c00f00040010004001004c00100040510004001000400100740010dc00010004001000400100000000004000000400100040010015151500120c070c050b020a00060900092012 else 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110c0001000400103ec00100040000004001002c00100121610001f1d1800021c151705110b1606190207002916)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 0x4001002c00100040010004001003c01d0004001004c001000400f000401d004c37000040010004001112001d00740010004001000400b00040010004001000400100040010004001271e0e1f0a1b092314141900101702000d0401000b02002b17 else 0x10004001003c001000c0010004001000400100040010dc0001000401b000000100040070004001000400100040010a0308070d000705070400030002021b0f) else (if i < 563 then 0x1000000100540050004001000400100040010dc00010004001002c001006000100040010004003000400100040070004001000810070004060900010c00000a12031d10 else 0x1004c00100040010004001000400100043700474001000400f0dc00010064013001405100040010004005000402d00040000004001007c00100040011a0016130e1115150d04040900000010000a022313)) else (if i < 566 then (if i < 565 then 0x100040010004003000402f0004001001c0010004001000437000040000004001013c0010004001000400100040010e00080c0c0806100404040a0102001b0f else 0x100040030474001000402f0004370000400100040010014001000400100043700004001014437000040000000001001400100040190004001001b001c00170d0f0706090311010e0812002112) else (if i < 567 then 0x40000004105001c0010dc00bd006c0bd0004003000400100040010004001001c00100040010004023000400100040010004001071000001d000012180312180904010c001f11 else 0x400100040130004001000400f0004001000437000040010004007000403b0004000000400b00040010004001000c00f0004001000d07060005091400020b0400000d001e10))) else (if i < 572 then (if i < 570 then (if i < 569 then 0x400f00040050dc000104840010004001004c013000411d000400f00040010004001001400100040010c6000100040010dc011f0dc0001001c00100b4000012c00100040010064001000f0c06032023241c1d0021101907021a18161311002a16 else 0x122000400100040010004001001c0010004003000435a0c800010004001000400100040010460001000400100a0001006c00000040010004001000400017191c010c0814180a001114000308061104022313) else (if i < 571 then 0x1402100040010dc00010004001000437001dc0010004001048c0010004007000437000040010000001000400100bc001000400100040011d1d00001903110018130b051200040b002011 else 0x40070dc00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f)) else (if i < 574 then (if i < 573 then 0x101 else 0x700040010004001000400300043700004001000400100040010004000000000100040010004001000400100040010e00080c0b0d07030a0206020001051b0f) else (if i < 575 then 0x40070ee00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f else 0x1000c001000400100040010f200010004001000437000040070004001000400103ec0010004001000400100040010004001000c090600000802000e0404000201001e10)))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 0x400b0004001007c001000400100540050004001000400100140010dc00010004001000401900040010004001000400100040011500040e0d09010f09051200000111070a04002113 else 0x10004001001c00100040030004001000400100043700dc00010014001000000100040010004001000400100040010b000815151400090e0e05040002021b0f) else (if i < 579 then 0x7d0004001000400100040010dc000101b40050000007000400100040010004001000c0010004001000400100040010004001000c000b0000130700080d05000408021d10 else 0x440010084001017c0010004001000400b0dc00010004001000000100040010004001000400100040070004001000400114010a0a06060014020005090905031c0f)) else (if i < 582 then (if i < 581 then 0x11007c00100040010dc001f007c0010004001007c01f001c06500000070194003007c01f007c019007c01f007c01f007c01f000e001500050003000a1207000013011d10 else 0x40010494001009c001000c00500040010dc00010004001000000100040010004001000400100040010004001000400118010a080a0700120200050a0905041c0f) else (if i < 583 then 0x405f0004071000400100040030004370000400100040010000001000408100040010004001000401f00040010004001180009090b040013050107080802061c0f else 0x1c0010004001000400100040010014127001c005000c005000400100040010dc00050004005000400100143c4000c001024c00103340600004001000400100040010014005027c065000000500140050014005272421090828261c04250017021813211a120c0f0102130e003019))) else (if i < 588 then (if i < 586 then (if i < 585 then 0x5f0004001000401f0004001000400100040190dc00010dc000b00040010004001001400100040010004001000000100040010004001070c110f0a02041302080c020803070c001f11 else 0x140050004001001c00100043700004001001c0010004003000400100040010004003000400100040010004001000400100040010ef80010004001000400000040000004001000400109261a201321191e0f00151d1d0d0517191202001607002a17) else (if i < 587 then 0x24001000400100040010dc0001001c00500040010004001000400100040000004001000c00100040010004001000400100040010004001b00001405000a0e07000609021e10 else 0x1001400300040010004001001400500040010004001000406d00040050004001003400504a40050dc00cd01800010000005001400500040050014370001400500080207001513060013051c00180a03000a01002514)) else (if i < 590 then (if i < 589 then 0x4ac0b1005c00103cc00000003f000140170004005005c02f0100000801070002000e09 else 0x7c001002c001000402f00040010004001000400100043700dc03700004001000400100040010004001006400000040010004001001700020004000b000c0900000604091e10) else (if i < 591 then 0x100040010328001000c0010dc0007000400301c4001000400102fc00100440c8000000100040010004001000400100040010004001000e1c110a06001808020e080503090d021f11 else 0x400100040010004001001c0010dc000100040010dc037000040010004000017c00100040010004001000400100040390404001000c10030000000900080c05000415071e10)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 0x4001000400104a40ad000400100440070dc00010004001000400103c037000840010dc00010004001000400100bc001000400100140010004000001f1815140b00081002000710050d00071b2212 else 0x3c0010004001000400100040010004001000400101c400100040010004000000400100740010dc000100040010004001002c013000b15160000001b00050a04000209021e10) else (if i < 595 then 0x130074001004c013007c3700004001004c013004c003004c0750044013004c013004c013004c0010f30013004c0130cc0013004c013004c00301fc0010004013004c001004c000004c013004c01323251f0001242215032100141b121c1b180d0b0d10010705002e19 else 0x13003c0010004370000400100040010dc0001000400301c400100040010004000000400b000400100040010004001000400100040010d0b0c19090400090600140603010b0f001f11)) else (if i < 598 then (if i < 597 then 0x405f000c0010d0000f000400100043700004001000400100040010004001001c000001c00100000010004001000400100040010c0a0b170803000805000e0503010800001e11 else 0xf004c0010dc0001000400100040510dc0001000400100040010dc00010004000006400100000010004001000400100040010004001030c0d190a04000a0805110604010a0f001f11) else (if i < 599 then 0xbc001000400100040010004071000400104000030004001000437000040030dc037000040010004001002c00100040010004001000400100040c5141104120e01180c12000708070505100501032313 else 0x1000400100040010004007000400100040fc00040010000000000400100040010004001000400300040010004001160808090a060010040402010800031b0f))) else (if i < 604 then (if i < 602 then (if i < 601 then 0xb0004001004c00b000400b002c0070dc00410004001000000b0004001002c00b002c00b004c00b000c00b002c00b160b080909060007020009101001041b0f else 0x37001b400301b4071000406d01b406d001c06d01b406d01b4013000400101b400b004c001001406d0dc006d03a000001b412f03a806d04b4001008437001b406d000b2321001d1e060014181c000f1218000701002514) else (if i < 603 then 0x400100540010014001002c013003c0010dc0007002c001000418800040090004370000400100040010dc0001000401100040070a60630000400118d0007007401b0dc00010004005000400318c8017000418c00040010004007000400d000463600040010dc0001008401f000c37000040010004001006437042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x1b000401b00540010dc001b00040000004131017c003006c01b003c001006c001006c01b006c01b00bc007006c01b16190c140f000713120505100003001b0f)) else (if i < 606 then (if i < 605 then 0x1c001000c0030024013000c003017c01d004406b000c00f01a40fd017c3300dc0370000401f000c01d000c003000c0000034003000c001000c003000c0031a141d0012100003110a0d000e04020b0600032413 else 0x40070004003000400100043700dc000f003c00f003c000003c00f003c00f002c00f003c00f003c00f000402f003c00f0dc000f000a0b0c0011000e00061402000000071e10) else (if i < 607 then 0x4001000400100040010004001000400100040010d2000300040010004007000436e000410c002c36a001c1080004001000000000000010004001000400100100021000d0004000a140800061200000300022414 else 0x34354000400d003401f003400d000c3700dc002f003402f00340070dc01030034069004c00d00040110440000003400d003400d000401304cc000003402f003400d2100001b1e1716160a0e1306080a00130300100d002615))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x10004001000400b000436200040010000000000400300040010004001001c0010004001000400b000400100040011607071414020012120505101000021b0f) else (if i < 611 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x4001000400100040010004001000400100040010004370000c0010004001001c0010dc0370000437000040010dc000100040000dc00010dc0001000400100040010012001e000e1e23000b1b0900071400000416022614)) else (if i < 614 then (if i < 613 then 0x400100540010014001002c013003c0010ee0007002c0010004142000400900043b8000400100040010ee0001000401100040070a8063800040011a10007007401b0ee0001000400500040031948017000419e00040010004007000400d000466e00040010ee0001008401f000c3b80004001000400100643b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x56601d013a0f0019400143c00aa03c019003c019903c000e865a0004762001c5ae0004001000400100040130f000010004676003c0010004001006c001000455a00040030004009000476e00040010004019004400100040070004017001c0550084001003400100040070f00001000401f0004001002c001000400300540050004005000400b1800000013004b00330046000e4a264907484746004539442e433b4229411f40253e3d331e30210f4e28) else (if i < 615 then 0x150f0000001a406901a406901a406901a406904dc06904d411d01a406901a40ed01a4069003406901a40690e12000e000e040b010501000300190e else 0x7400100040010034001000401f0f200010004476008400100f4001000400505200010004001069000f00040010f202b00004001000401d00046480004001000401d0ff00010f203c800040010f20003006401d005400b19f800300043c8013433819f00010004011000400b00740010074001000401300043c811d00051928001463b3b444444404040393d353716143433002f0c2e2c412928242127110d201e01081d1b1705044b27))) else (if i < 620 then (if i < 618 then (if i < 617 then 0x301ac10b01ac06b000006b01ac06b04e4000007401d01ac06b01ac06b01ac00f01ac3c801ac06b01ac06b000000040d150001000801060001190e else 0x6901a4069000c3ba01a4069047406900540fd0fc806901a406b047406904ec13703b406901a406901a406901a406901a40691c000f0d000506000206050504000605031f11) else (if i < 619 then 0x400100540010014001002c013003c00110a0007002c00100041a8000400900044280004001000400110a0001000401100040070a4868800040011a90007007401b10a0001000400500040031a8801700041ae00040010004007000400d000468e000400110a0001008401f000c42800040010004001006442842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x400100540010014001002c013003c00110c0007002c00100041b0000400900044300004001000400110c0001000401100040070a2869000040011a5000703ec01b10c0001000400500040031ae801700041b400040010004007000400d00046be000400110c0001008401f000c43000040010004001006443042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 622 then (if i < 621 then 0x1b811201ce11201541120698112000100040151b10001001c001003400100040010004001007c794000401d11200010004007000402b00046aa0004001006c44800040011ad8001002c001000402100440130004005000400b0004001003c02b0004001001400100040011e3000711200070024001000401d00180010004019340032002e002a00390014482a470d4626451f441d4301423b41153d3a2f0c280524002119094a26 else 0x400100140010004091003c103001401f0004003047400100040550004430000400100400010004001000400102440010004001060f150f1a0011060503001008010401001f11) else (if i < 623 then 0x4001047400111280000004001000400100140010004001000413d007c0010004001000c001004c001100e00030e0301000601030300180d else 0x13d0154055002c0fb00b442a00b40fb013402d017405500b402d00b402d00b402d00b402d04fc02d00b402d00b402d0600060403020000000904000001091c0f)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 0x1000401500040130004005000400700040010740001000400b13404d00004009000400100444d000040010ae000100046180004007001c01d00044d01ed0001003c14121c8001002c005000400321a8017000424000040010004007000400d00048dc00040011340001008401f000c4d00004001000400100644d043413f3c403c001b3c3d3b1a3735162e30382d2b362c2a120b25230f2422190a06010e02004825 else 0x1d809204e80b004e818404e81f304e8220801f0004001000400813a0007050c0010004003000400100040070004001005c4e800040012390001002c0090004007000400700840010004001000489200040030004005005400b000400122280010044001000c00f0004001000400513a0001005c001000403d000400100040193200170039002e00120014480f3908472e4627452544204338420b413640013f1f2c00291e094a26) else (if i < 627 then 0x100540010014001000400b2330013003c0011480007002c00100041e800040090004520000400100040051480001000401100040070b2060800040011eb0007007401b1480001000400500040032188017000425000040010004007000400d00048d400040011480001008401f000c5200004001000400100645203e424038413f00373f38361a322f162e2d4027243b3126120b25230f1f1d190a06010e02004825 else 0x14007020c00100040050014069001400500140051480005001400100141450014005010400500140050014005000119050c050e09030204000d00001b0f)) else (if i < 630 then (if i < 629 then 0x18c00000000007000000000404 else 0x524007002414b02bc4d0001c007001c14d051c007001c0aa0004007001c0070524007001c007053c0230014007026c007001c00700170a000d09050b0300090000080c0307022012) else (if i < 631 then 0x10024037001c0000134009054415300240090024009027400900240090024009002400913a0009001c0090912080605051207000a0b050000190e else 0x59007c058009605800b4058017e0580007c7e4000400100540010004580001c00d00040010004001000401d00040010004007000402b00048420004001006c58000040012148001002c001000402100440130004005000400b0004001003c02b0004001001400100040011fb000716000070024001000401d0288001000401931002d443a002a00360014472a460d4526441f431d4201413740153e35380c280524002119094a26))) else (if i < 636 then (if i < 634 then (if i < 633 then 0x63000000210000000303 else 0x7001c01d008c15700740230084580008c0230554000008c005008c023008c000008c023008c023008c0230002080000040400010800040000021a0f) else (if i < 635 then 0x100040150014001002c83a004c001003c001001c5b8002c00100041f8000400900045b80004001000400116e0001000401100040070b605f000040011f7000700b401b16e00010004005000400320a8017000426000040010004007000400d0004832000400116e0001008401f000c5b80004001000400100645b843413f393b3f00373f38361a322f162e2d4127243a3126120b25230f1f1d190a06010e02004825 else 0x18c00050001000303)) else (if i < 638 then (if i < 637 then 0x55c0af01a4005001c00516e0005056400500000050014005001400501040050014149001400500140050014005080e000c120504020a04040000001a0e else 0x18c000100006300100000403) else (if i < 639 then 0x242864818c063000047f822806f00002000200000906 else 0xfb00040011c8007f0004001000400100040010004001000404f00040011c60001200071822a00010004718000400123e800100040010004001000400100040010000001000c001100a001f1e0f1e1d00121d1800091d1a0019011016002916))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 0x241063018c0678004c80822c06d00002000200000906 else 0x1d20013004c013004c01d004c013004c013000c770004c013004c8c0004c013004c013004c8fc004c01301fc0131d20013004c0131d20013004c804004c013004c013004c0131303001d1c1419110016151a000e0600001a050100002916) else (if i < 643 then 0x8100004630000063000000000000605 else 0x63018c00000000003000100000504)) else (if i < 646 then (if i < 645 then 0x118c06300200000403 else 0x63018c00010000000403) else (if i < 647 then 0x118c06300200000403 else 0x63018c00000004020000300000504))) else (if i < 652 then (if i < 650 then (if i < 649 then 0x118c06300200000403 else 0x118c06300200000403) else (if i < 651 then 0x400018c0630000000000504 else 0x63018c00010000000403)) else (if i < 654 then (if i < 653 then 0x63018c00010000010403 else 0x118c06300200000403) else (if i < 655 then 0x63018c00010000000403 else 0x63018c00010000000403)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 0x1463018c0088000000003000000000605 else 0x63000040000000630000000000504) else (if i < 659 then 0x63018c00010000010403 else 0x118a000018c0630000100000504)) else (if i < 662 then (if i < 661 then 0xba001c0000000630000000000504 else 0x6300dc0630206020009a063018c06300b8091218c063000048b8080d000c070b040a031009) else (if i < 663 then 0x318c06300200000403 else 0x6c00018c0630000000000504))) else (if i < 668 then (if i < 666 then (if i < 665 then 0x63018c000d0000010403 else 0x63018c000f0000010403) else (if i < 667 then 0x9c18c0630005400000000000000000100000706 else 0x1000101)) else (if i < 670 then (if i < 669 then 0x630000c62018c0000000000000504 else 0x1000101) else (if i < 671 then 0x1718c000018c0600000100000504 else 0x19000101))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 0x746300000000303 else 0x246300000000303) else (if i < 675 then 0x18c0000000063018c063018c000118c0630010000000000000a07 else 0x40010054001013c0050004001000c00b1c6000100040010004208000400f0014718002c001000404f1c6004f0004011000401d09c02e80004001203000100040131c6004f000400100040032288017000422800040010084001000400d0004902055c0011c60001000401f04c471800040010004001006471842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 678 then (if i < 677 then 0x1d000001d001404d007404f007401d008c7180574149007401d02c801d007401d056c01d03ec01d00b401d007401d007401d007401d08110002061002080503000000000b04021f11 else 0x4c013004c01300f401d004c0131d201631ff001d1e60003004c013004c0130034040004c013004c210004c013004c0030074278004c013004c013004c2f0004c0031d20013004c10b1d2090c1d2015f1d2004d1e000130584013004c01d004c748004c8b2000c01d1de00131d20013004c01300740e902ec5e8004c013004c013463917444444404040383d3836141233320f0b302c27412a262523403f081f3110011d051e001b4b27) else (if i < 679 then 0x4d1d2004d056c000000001d013404d059404d013410f013404d013401d013404d013404d007404d013404d000d020d0e040009000501000000190e else 0x20607f0206063018d081820607d0246081820607d42470818080c050b040a0108000f09))) else (if i < 684 then (if i < 682 then (if i < 681 then 0x22e089822e063018c88b822e085824608b822e087824688b8080c050b040a0108000f09 else 0x24408ee244063423c09102440632246091024408e82478910080c050b040a0108000f09) else (if i < 683 then 0x40010004001018000101b0021005444e1e0008820800010004001000400300040010004001000400b022000300040050004001001c0880004001002c08800040010004001001400102200b80064001003c83c23a00070004070006c0010024001000407800040800004001022008800040110160013000400102800070220007005c007007499802c00a80004001000402a022000100043e0022000102603c40220001000441623a00010034090000c08800040c0007c00100e000100048d26a616b0068665f6565055e3a6600596463005759462c25201e593a54555334504e4b32362e292724110c1e174a48420f4341061b19400002156f39 else 0x400101a8001000c0d80f088e8000c001000400100540131de0968000406c20a0001000400120b8007001c00100840d8000400b000400300040d800140010004001001c0010360017002c001000400103e00d80004001000400500040d803f8019003c00103800f600040c8006c001002400100040ce00040d0000401d03600d800040110158001000400103a00070360007000400d0f100d8000400103b80010004050036000100043f623a0001007c0010108001000492200040f00fc00d8315d5c006a685967676558536700535166656062605e5b54234d304e4c462a4945432840241f1d1a160a3f203e3937153836132c0f0d0406006f39)) else (if i < 686 then (if i < 685 then 0x4c012004803c223a0108000c1200440001048011804801280480138000412004a805c00c0011000400100040030004120000486c20c000104c8003001c00100840010148050000443a10e0007013013a04800011e201200f00001004c0010004001003c0010074007000400100041202470001003400500048e80480001006c001000400b00040010024007000400500040010044001000400b000400b005c00100040230004001007c00100040010004019005400100040010004001520054004e6a4a004700690045686766320000002e0000001e666564186362611260435f0c5e405d2a5c5b5a24595450063e3c3a002b38256d38 else 0x108432054000305a015800041680580168060000105a01900004168009803824a88e8000400105a0001009c0010004001000c0070004021000404805a000105c016805a017805a019805200011dc01680fa0001004c0010004001003c001007400706203fe0f100070004001000484c2100001003400500048e805a00010094001000400b000400100240070004005000400100440010004001000400b005c00100040070004001007c00100040010004019005400100040010004001530057004f0028004c006a004a00690036000000320000001e69686718666564126348620c4430252a61605f245e5d460642403e00593c556d38) else (if i < 687 then 0x80020023a023c052021025c023808703c01e4023400a820c120000307d0850251002e001420026b0001080000108002400f1000123a02000150218000490a12109a800042000004001250000107b01e808000500034001082000107c0228088001300040010800001003c00700041f8000401b0004001000400900040010004011000400100040170014001000401f00040070800001005400500840010004001000400b000c224001c0010004854080023008b0007000400b000400100a40050004001000400100040010910019000c0010004007080000140007b003b7a727936000000320076002e0075002a746f734f004b0047726c6426476c41216b67661e3c64271945144d101c62170c605e5c06075901005855547d40 else 0xba02a825e000d0a408e80a402900a2029000042b80a8003000049a6000402b00040010004001007c0010a4029000041ea23a00660004278000402b001c00b002c0010b6029027a82e00ac00090bc00010004001000440800442c000040011e6000100ac2c80004866000429800040010004280000400100049d0001c29000642d0001402000040150a400070f0800120800210004001007493800040070004290001406c000401d0a40001001c001000400100040011100001004c7e40004028003c0010004452006c001000429000040016a00487746684100660062002a0061743f7370005f005d00567226715a6e225856703b36381c536f346e526c1e5f193e13500e4e08172f4b0430110c0002793e)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 0x4001007c08c00540da000c01321d0001002c005000400f174829205b00010004001000400111a03b000043c000040170004007001c3c00f2000700b43c0000402100040010f4000100040010f000010f6000700043c000048e800043c01d588e8000400100142000ea0009006c3c021600010044001000c001000400b00040010f0000100341200f0000100047b000040010f000010ee04a80f0001956525200514d50524c4c00494d4646441d1505464216401203113a3d39383633312f2d2c2b070f0a2725240023211a5b2f else 0x34001007c00100040150004021000c00527885e80004001279800b001c0010004001051000711a0001000400b11a00010004001000437811a0001006400111a0001003c5ec004c001000445800043c4000c001001446811a0001006c03123a0001000445c002400711a00010004460002c3c00004001000446811a08e8000400511a0007005c37c1f0000100bc47411a000100049da0004001050001f006400127780111ce81b8000400111c0880000400108a00012210001000400108b046861696000696769006664665b00005b640000605c4f57403b3544423f3b36343057542e2b27250b2253511c1a4d4b0f4a1b09180600131102496f39) else (if i < 691 then 0xf088e812a09cc09a09c417a03c012a08e812a049012a049800044a800044a812a074c12a08e426f04a812a09ce09a8015271800117a803308d8001005c9b412807d804c04b800049b61000001000400500040010034001078000104c803300440010004001005c0010004001007c00100cc00100dc0010004350224000112e823400040150004001000400100044a80004021000400100d4033000400526f800100e400100044a8000401912c000100b4001000400b004c00100040330004001003c001000400b000401924725a7139706d00356e6a00436c00003f6b6a693168570054005300526851671e6665640c4f6362064c3e6100604b5f185d485c2c2b452212192914753c else 0x1168150156011414c049c1460072158815c15204d80da04e807c04e0032856814a054815e04d213c052015205320d60278092853816c08e816603b6185036a1368418152015e14684ca054855016c855a11604f801c00c814a84c013405600ea8616142010815203b4132027a15c054807c849009203a8166854842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 694 then (if i < 693 then 0x24c025216405f2130000315e000115e000116a007e164837217002500a1858001f05f00dc05c20054007001c00115005a015e057814404ec140036016205b8001c2841f408241608001183000100145ba000400d00044200004010222000115e00010004011000400100040170004001000401f00040070004009000400115e0578000400100040010004001000457800040210004001006c007000400500000010004001000460e0004019000c00100ec001000400b004c00100040070004001003c001000400b000400324656f003664000032630000445f0000405e00002e5d7000596d6e005a6f6e6d1e546c6b0c536a5706504f56004c4a3d18493c2b29463e2a12143b22753c else 0x17403c423a05d0007c27017a0021001c4d000044d60004005000400100040010054001001c276000400117405d817b800103c05d027f0001172000100349fa17405d00004001008400500040010bf800122780010f0800117980010004013000403d0064001005c001178000103d8001003c8e800045d0000400100041d8001c732002c0071fa000b002400100045d0000400700442f800049b4174000100bc89800049f4004400100045d00004001006c9f200049b20004001005c5d000045d000040014d6e61005f6d496c5e6b67005b695900586866005300650051004566355230642a57254f064b20331c174426161e3e12100e3c0a0c04373d002c713a) else (if i < 695 then 0x23706a80e206ac0e386aa13c0003190000b190064019000491900013001c162002c64e13d063018800081a4000b1a60770059864a180069c1a6800b002c160002c0411a7800b003400b19d000b24c0604236000b193038a002c03f002c00b002c017002c00b002c04b002c007002c63419c001005906ae001c009002c00b192038c002c013002c00b002c00b002c640004c047002c00b006c007002c041190000b000c00b002c640002c045000c00b010c00b002c00b004c00b002c007002c00b000c00b002c00b002c00b24416f003c2f0000382900004b71000047700000346f6d0062006c00616d6c6b1e5f6a690c5d5a6806592f67005844651854522229535119124d4114753c else 0x118808019b011c19a04a418e028c199828a1a006280e0050007e04f8034867c198068019005ca14106581a0066a17e00860e186781a808e818f03be1a9038218a85fc1a0028818e862c020865c1a8866e11804fc0a380d0198862017206640ee86a619401181a003bc18b80841a2068007e84a00e103b818f868042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725))) else (if i < 700 then (if i < 698 then (if i < 697 then 0x6b8000401d1b60001000404d008400100040110004001000400500f400b000400d00140011c88a1014200032cc00201b4051400040010004950002c71a2d106301b400381b406b41ba06d02cc86ea1b4001d1b407180004a0a000400300640011b4000122b001d287801d007c015007400100040011b4000123a000123a07201b40a0800046e000040220004a1c0004a2400040010004b4600046d000040010004770000403a00040131bc001d1b200010004001000c0010004a12000401d003c6d00004a260004001000482000046d00004001740040713b54724d70006e006c006a0068004600670041006400621804003761605d365c5a025754245332501e4e192e0c4b2928134910460620433d002f7a3e else 0x908b20276013c26e00fc00609302ca0003005475000040010c6000114607c81ca059c1d4000107007a018e075000047b806483c60ce000128e00010014750013c00d0004750002c6c02c6074022e004f1d40b0200048f002e82cc2ae07a80004af40004011000400100840170004001000401f0004001001401b000400100409f0000404d0004001013c001000475000040010004001000c00100040012c58001006c04f00047500004019000c0010004001000400b004c0010004001000404f003c0010074001000400124726e0036700000326f00004e6e00004a6d00002e296b00656a690064636a681e605e5f0c5b595a065654500053464c183c434529443d2212193b14753c) else (if i < 699 then 0x400500040010004001148001f000c0011ed0001000401300047b000046d40004003000477000040011dc052422d077000048e81dc08e8000401d002ca4400040151dc001d05b00011dc00211b400010004001290864000040011dc08b0000401d0004a46290000d000477005a000f00040011dc001d0134001000416a000401100047701ed803d007401d000416e002c00100047701ec80050064001004e4d55004b2f5400554852000054475346444240143e394b2c3837280f25351f0a1c273605331929000e012018045b2f else 0x100040010004005015400d00043c00084053002c7b000048e81ec00012d38001001400114a000114d0001003c019000400b007c7b000040011f6000129b000129e82601dc0001000400300048e8004cb3e000402d00047b01bf08cc0144005000434e19207ea0004001000418c1bb0001000404d0004a5800b40011ec0001000423c2c787c000b4011000401500040011ec000300647b026400011ec07121ec0001000400123001a2000400f000402d26000011ec00131ec000105d00011ec098806c8001000402d6f6f6864626e616b6b006c6868006651382d5e1e00401900001303015d4819435b1440583a0f0b56393505322e0054534f4e09294d492b1d27231f743b)) else (if i < 702 then (if i < 701 then 0x1fe07fc1ae00031fc00011fc00011fc00011fc00571fc00011fc00011fc00011fc00621fc07f0150081e019881a1510618194006020700642a00a842a08818007c0012a1800100540010004057000c001002c01d00147f01fc08a000040010004001000c0010004001004400100048242080001016400100048e823a0001004c00100040010004001003c001015c0010004001006c00100040010004001016c0570004001000400b000400100040570004001003400500040210004019430000003f0000003c0000003a666500326652002e3527211e55686718516665125064630c4f62612a4b605f244a5e5d06495c5b00455a596d38 else 0x401f000400500047f00004001000485a0004088000401523e0820000c001000429200045500004820000482023a0001000457c208000b001482000040012080001000400723a00010004001004c8700004858000400f000c820006400700246d000048200004658000401122c001d20800072a20007007408a000400d002cacc000487200040012080a8a0a40001000401b2b3882000140210014001564d5300544b47005329544e504351454427424d46222d3d3c003b3a1e1d383317163530100f202e0a011925050c0b5b2f) else (if i < 703 then 0x1000400123a0001002c001017400d220001f0f008582010007007c015216091400140010004820216005f00048e800040010004001000c0012160001000400700040192160001000400100040012160001002c0010004001002c8580014001000485800048580004858273885800040072d380010004009226802100040012a400110c2000125300012b7000100042a2000c85800640070004558004c708003c8c000041d60004584006c102018489000046600004aa200042580b080010004b266b626c0069605f68675a686600005a655c005125571c5453504e164f4d48104947420e43413b083e302b25183a381f02361e062c34190026327039 else 0x89821c08e821c03900e603a02200560000c87010b88700c008700b589e201a49c2019c005203800520808e821c000516508702ce8870001470023206680014a982bb00b00014005001400700340050c5004123800902ae88702c380630014005008c878001400500140650014005001491021c000521c09fa001406b00140050f1094c00140090014005001c005001487000140050014005004c00500140052590005006c06d00140070014019003400500140050014005001400500140050014041000c005001c0050014005246400003c7100003828706f496e6100456d6c6b346a00005f0000005e6c6b6a1e695a680c592f58065255660050145b184f51422943323112414b22763c)))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 0x1000400101cc001002c0010074814003c00101cc00d232001f0cc801300548c0240000500040011b808b0000400100040010004003002c0010004001000400100048b0000400b000400101c400122c0005000400122c00730004001000400100048b022c000120806f023a0001262895c000400100048b022c0001006400123a0073000498822c08b001d48ca00443300084aa80004ae4000c8b0004c7700004570000448c003c8b001bc1aa000458c000467000748c200041a80004aaa0004ae66b5e6c00695c6a0067596866000059656100606256542f522d511250294f102621490a4c48460845203f1a63413e182d3d37023a36270019357039 else 0x1ec808821d016821c07b419006d422d029223a04ac0368578080054805b085e21608e81d407b015f082023a08b0022808e05a88721a00ac01d507702b102021ed829423a02901d485d21b408242b0887611a054c0a580d821683c6174085c0f08ac61fc012023a03c411a808c23e08e805b84a804903c01d588e842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725) else (if i < 707 then 0x245832e244091411e000323e08f8007491223e09640ca0962000c003007482423e000323a000316800031ff08f820808f8000c8e81da0688000c76023e001d000c00323e04b4000c00323e000325987582560af80ca89602bf001d0074003007407b000c003000c003000c00317688f81fe095c23e09001690003007407b2be8003000c04d01dc0030074003000c8f8000c01d000c003000c00300740030cb0003007404d000cafe000c003000c003000c0031760003000c00301e4003000c003000c003007400312c0003246600003c630000386f00004b6e0000476d0000343f0000616c00005e6f6e6d1e5d5c5a0c2f576c0654535100446b691841504d292b643112142a22753c else 0x29e00a02ba01782a60a681a60a182b802e22b00a600d005b808805b00610ad02a40ac01d40a581820a882b00aa828000c628a0ab01a808e82bc0a402d403202920a302b002b82c00a502820ac82d60b0811c06100bd80e82a80a381780ad80f68b622a001282b003d429c00ac2be0ac006784b807203c82c40ac042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 710 then (if i < 709 then 0x22800002b001802a008c018007402d002a02e00440028050008004800700a602800b801e0088015009802e00b0000800600680aa01a00c801f00800330022023802c02e002801e805a01c009c03280ae00e004c00b8008028803601600a400c80ce024001002e003400e800403000b80078040005003001f80b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0) else 0)) else 0) else 0) else 0))) else 0))

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

lemma root_restricted (C : Circuit) (hc : C.size ≤ 12)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ k ≤ 12, ∃ t ≤ 5, Restricted k t raw.toFinset := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  subst S
  have sz := live_size ht
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length = 8 := rfl
  change C.gates.length ≤ 12 at hc
  have h12 : k ≤ 12 := hk.trans hc
  exact ⟨k,h12,t,by omega,restrict_live ht (project_bound_root h12)⟩

-- A frontier contains the distinct values still needed by gates that follow it.
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

def wireRecipes : Nat := 0xb8bb325805ddc511abc000026968ca0000017706f000000bb82780005dc511bc02e2de9688e001716f452b00000000b87800005cd194400002e689620000000017c0000bb6a35880005dc511b4000000002f400000176b0700000b3b89280000005c494000002ee14a0001771446b00000000b858000000005e0000000002ec0000000017400000b2b89380000005c49c00002e26cca00017714469000000bb23880005c59d12c00000002e0e00000000172000000000b80000595c529c0002e28ec96000001714a7000000000b700000005c4ac02e2ad288ce01715694a4700b8ab4a583800000005c1400002e28a4e0000171452b000000000b6000005c4d9ac000000002d4000000001680000b8a2b358000005c5294000002e288e000000001660000b8a5a328000000000440002ede88da00000000164000000000b1005dbd4159ac000002decd60000016f6a500bb7a2b38580005bd45a940002ded68ca0176f51464b00bb7a85a3280000000058000000002dd6016f571464b000000b7a85800004d1d2c400002e694ca0000001346b000000000af000000000570000000002b4000000001580000bb7a23480000000055800002dece560000016f6650000bb7a8238005dbd14a9c00000002dce00000000154000000000a9005dbd4151ac000000002a0016f5694b070000b7a3b25805bd5952c1c0000000029c0000016f46b00b7ab82a3580005bd1d42c000000002980000000014a000000000a40005dbcd9a9400002de6cd60000000014600000b7b298800000005b940000000028800016f4567100b7a2b8a53800000000508000002dea0a0000000014000000b7a2958000000004f8000000002780000000013a0000000009c0000000004d80000000026800000000132000000000980000000004b800000000258016f569446700b7ab4a5238005bdd194c4000002de88e016f570b4470000000009500005bd45194002de8a8e6200016f4b447000b7a29b858005bcddc29c0000000001e00000016527000009a8a23800005cd11ac000000268ca00001534651000009a3b2580000004d1c4000026ad60e000000001270000bb3a58680005b5ad1940000000025000016d4b70700b6ab8a3258000005b52c40000000024c0017350b66500000b9a5828000000594ac0002daca8d6000000016c5000000000920000000004880000268aa160000001344b0000000009000000000047800000000238000017350a70000000b39580000004d42c000000002340015350b70b00000ba23958000000004ac0000002a256000176d46490000000008c0000000004580026ea168ca000000001140000000008900000000044000000002d8e00016d4764b00b6a3b5a82805b55952c1c0000000021c016d5694467000000000860000005b519402daad628ca00016d5146500b6ab4a5838005b55acc1c000002da8d6016d570546b0000b6a3a858055b51adc1402daad2948e0000000010a00000b6a398800000000420002da8a8e6200016d4b44700000000006855b51acd1ac00000002d0a00000000106000b9a82b3580000005ac94000000002080000173504700000000081000000059c940000000020000000013505000009a2b38800000000494002a6a0ae0a000000151250000000007f0000000003f0000000001f40013570b6650000000007c0005cd45a91c000026a2d4a000000000f60000000007a00005a59d42c0002d2d68ca000000016a90000b4a5b828000005a52c40002ad29622000000000f20000b4b3a2580005a5159ac000000001e00000016944b00000000077000055a512c400000002d0e000000000ec000000000750005a5159cc4000002d288e0001695144700b4ab28a5380005a51d2c400002d26ce200001694531000b4a29b838005a4ddac1c002d2968a62001694745310000b4a5a328000000000242ad26ce2ce356d46569447000000b1a858000000003a0000000001cc00000163471000000000720058d5a5119c000002c68ca01635694b0700b1ab4a52380058d1d14c40002c6968ca0000000000300000000071000000000380000000001bc000000000dc0000000006d000595ad9cc4000002ecc96000000000d80000b5b2a3880005d9d2c1400002d6ca62000000016a5000000b5a8280005952dc1c0002ad4ace20000016550b000000a8b52800000000358000000001a8000000000d200000b2b3988005959d2cc4002cace6e1600000001665000000b3a2880005955ac1c0002ae16cca00000165471000000ab2388005954d429c02caad2960e0000016546b0000ba82a3580005951d2c402caad288ce0000001653100000000068000005952cc400002ca6e0e0000165473100000b29b5880000000001400002a694ca000001570a5000000a2b388000515c529c00000002a0a0015346566500000000067000000000330002a6a16cca00001534b050000000a2958000000003282e6da8d68d6000136d473100000000064000004db51ac0000000018c0000136d46500000b5b3988005ad9d14c4002d6ce6e0a0000000166b000000b5a83800059d2dc14000002ce9620001570566b000000a8b5380054d1ad9ac00000000188000000000c200000000060005ad5b5191c02d6ad288ce00176b31465000b5a2b3988000005ad1940002d6a288e0156b4656510000ba85a328000000002f802d6ad2960e00000016b31000b5ab32988005acdc511c00002d68a62000016b3671000b5a3a29880000000002c00002a688d60000014b707000ba859b8580000052dc140002ae288d60000000150b0000000005e0000000002e800000000170000000000b6000bb398a258000000002d0000000001640000016744b0000b3a2a858055c2d9d12c02ae0ace896000174a5471ab4a2b35b358055ad19591c0000028acd6000000000b0000bab3259880055995acc4000002acc96000000014a5000000000570000059d2c9400000000158000000000aa000a9a82b358000000002a00000000014c000000000a4000000000510000000002800000000013c0000000009c0000000004d0000000002600000000012c00000000094000009b6a58800000000248000000001200000000008e00000000046000000000228002ce6dea0a000000000880000000004300059cdbd42c0000002ce6200167564b31000000000420000059d2cc400002ce6e0a00000000082000ab85b3988005d41cd9c400002ce8a620000167370b000b3a29b5880059d2d14c4000000001000000000000700000a9a5238000000001f8000000000f8000147770a5000000ab5838000000001e8002ea0e8a620000014765100000000a838055bdad191c000000000f0000000000760000000003a00054d42d9ac00002a6a14e0000147652b000000000390000000001c0000000000dc0156d46566b00ab4a23b358000000001b0000000000d4000000000680000ab6a323800000000198000000000c800174764b31000ab52b3988000000001880000028ec960001476b5050000ab2a853800055a5119c00002e8ca6200174654b31000ba329b388005d194dc2c000028ace620014567370b000a2b3a5988000000051940002ae168ca000001514470000000003000054d41599400002a6a08e0000000005e000a9a8b523800000000170000000000b40000136f4470000000002c000000000158000026dea0a000136f366b00ab6a35b35800000000150000000000a4000000000500000000002700051cdbd4140002ada94ce0000000004c0000a3b6a588000000001280000000009000000000046000000000220000000001080000000008000015694b0700000ba35988000000000f8002e8d66ce2000014b6731000ba359b858000055acc1c00000000078001746b4531000a5b3a2988000000000e8000000028d60001570546b000000a3a588000000000e0000026dea1600000000036000a39b7a85800514dbd42c000000000680000000003200000000018000055a5291c0000000005c0000000002c0000000009880055d992cc40026e2968ca0000137144700000ab25988000000000a8002ad68ca6200000014b31000a59b8a23800004dc529c00000000050000000000260000000001200000004d9c4002ad4a6ce20000000002200000000010000000000078000000000380000000001a0000000000c00000000005800002acca62000000147310000000000a000559952cc4000000000240000001370b000ab329b858004ddc511ac00000028a62001453714a700000a29b8380000514dac4000026ed60e00145376b0700000000008000000000038000000000180000000000a000ab35a2988000052d14c4002968a6e0e00001474531000a3a29b58800000000020002966dea160013771446f000a29b7a8280000000001802ada8d68ca014756d4b050000000000200000052d194000000000040013717664b
def wireFallback0 : Nat := 0xfffffffffffffffffffffffffff9e7ffd8fffcffffffffed9bffdfff8000000fffffffffffffffffffffffffff80000000000ffffffffe0000000000000000ffffffffffffffffffffffff8007ffffc000000200000010600000000000000ffffffffffffffffffffffff8007ffffc000000000000000000000000000000ffffffffffffffffffffffff8001e7ffc00000cd9800000d9bffc0000000000ffffffffffffffffffffffc463c0200039fffc02000c0010600020001fff000ffffffffffffffffffffffc463c0200039fffc0000000000000000000000000ffffffffffffffffffffffc07ff800003fffff0207fffff060003ffffffffffffffffffffffffffffffffc01c38000021000032607ffff0600020001fff000ffffffffffffffffffffffc01c38000000000032607ffff0600000000000000ffffffffffffffffffffffc01c38000000000032607fffe0000000000000000ffffffffffffffffffffffc00000000021000000000c0000000020001fff000fffffffffffe00000000073fffffffffffffff0000000000000000000000000ffffffff7ffef3fff9ffff3fffffffffffffffcf9f8c001dfbffffff9fff000ffffffc00001ffffe000073fffffffffffffff0000000000000000000000000ffffff70ffff8fffe7ffffffffffffffffffff3e787ffff3e7ffe0007ffffffffffff70ffff8fffe7fff8ffffffffffffffff0000000000000000000000000ffffff707ffe83ffe1fff83fffffffffffffff0000000000000000000000000ffffff3000018c001ffff83fffffffffffffff0000000000000000000000000ffffff30000180001fffff3fffffffffffffff0000000000000000000000000fffffe8f000070001800073fffffffffffffff02000c0010600020001fff000fffffe8f000070001800073fffffffffffffff0000000000000000000000000fffffe8000017c000000003fffffffffffffff0000000000000000000000000fffffe80000070000000073fffffffffffffff0000000000000000000000000fffffe3fffff0c001fffffffffffffffffffff0007ffffe000003fffffffffffffffe3ffffe00001fffffffffffffffffffff0207fffff060003fffffffffffffffe3ffffe00001fffffffffffffffffffff0007ffffe000003fffffffffffffffe307ffe000001fff83fffffffffffffff0000000000000000000000000fffffe0080010c00060007ffffffffffffffff3260000012640000000000000fffffe0080010c00060007ffffffffffffffff00007fffe0000020007fffffffffffe0080000000060007ffffffffffffffff02007ffff0600020007fffffffffffe0080000000060007ffffffffffffffff0000000000000000000000000fffffe0080000000060000ffffffffffffffff000073ffe0000000006000ffffffffe00800000000000073fffffffffffffff32607ffff0600020001fff000fffffe00800000000000003fffffffffffffff32607ffff0600000000000000fffffe0000010c000000073fffffffffffffff32600c0012640020001fff000fffffe0000010c000000073fffffffffffffff02000c0010600020001fff000fffffe0000010c000000073fffffffffffffff0000000000000000000000000fffffe0000010c000000003fffffffffffffff3260000012640000000000000fffffe0000010c000000003fffffffffffffff0200000010600000000000000fffffe0000010c000000003fffffffffffffff0000000000000000000000000fffffe00000000000000073fffffffffffffff00000c0000000020001fff000ffc081ffffffffffe000073ffff80000000000ffffffffe0000000000000000ffc001ffffffffffe000003f8007ffffc00000fff800001fffffc0000000000ff0081ffffff0c000000073ffff80000000000ffffffffe0000000000000000ff0001ffffff0c000000003ffff80000000000ffffffffe0000000000000000feffff7ffffe83ffffffffffffffffffffffffffffffffffffffffffffffffffeff7ffffffef3fffffff8ffffffffffffffffffffffffffffffffffffffffffec001fffffef3ffe000003ffff9e7ffc00000ffffffffed9bffc0000000000fe3ffe3ffffe00001ffffffffffffffffffffffdffffffef9fffffffffffffffe3f81ffffff80001fffff3ffff80000000000ffffffffe0000000000000000fe3f7e3ffffe00001ffff8ffffffffffffffffffffffffffffffffffffffffffe3f06b0fffe700007fff8c41c382000060003c38073fffc780000006000ffffe3f0630fffe000007fff8ffffffffffffffffffffffffffffffffffffffffffe3f01fffffff0001ffff8387c07c0003e0000fc07f0001f80003fffe000000fe0081fffffe70000000073ffff80000000000ffffffffe0000000000000000fe0081fffffe00000000073ffff8200039fffcfffffffffc78003fff9fff000fe0001fffffe00000000003ffff9e7ffd8fffcffffffffed9bffdfff8000000fe0001fffffe00000000003ffff82000000000fffffffffc780000000000000e03f0130800180001ffff8387c3fc0003e0000fe67ffffffe0003fffe000000dfcf79ff7ffffffff9fff83fe3c1e7ffd8fffccd9f80000d9bffdfff8000000decff9ff7ffef3fff9ffff3ffff9e7ffffffffcf9ffffffdfbfffffffffffffdecf81707ffe83ffe1ffff3b8001c7ffe100000e180c0011e3ffe0001fff000decf797f7ffe83fff9fff83ffffffffffffffffffffffffffffffffffffffffdecf797f7ffe83fff9fff83bffffdfffffffff3c7fffffe387fffffffffffffdecf01707ffe83ffe1fff83ffffffffffffffffffffffffffffffffffffffffde8f7e3f7ffe420019fffce273e104001effff0d9fca00039fffdffff000fffde0f783f7ffe000019fff83bffffdfffdeffff3c7ff3ffe387ffdfffe000fffde0f00307ffe000001fff83ffffffffffffffffffffffffffffffffffffffffc1ff017000018ffffffff83bfc07dffffe0000fc7ff0001f87ffffffe000000c13f813000018c001fffff387c07c0003e0000fc07f0001f80003fffe000000c13f013000018c001ffff8387c07c0003e0000fc07f0001f80003fffe000000c03ff930000180001fffff3c7fc7e0003ffffcfc07f0001f80003fffe000000c03f81b00001f0001fffff387c07c0003e0000fc07f0001f80003fffe000000998cfeaf60017e00198007e25321040016c0030d9e4a00039fffd8007000fff998c662c60014e00118004e25321040016c0030d9e4a00039fffd8007000fff988ce6ac60007200118007e25321040016c0030d9e4a00039fffd8007000fff988c662c60004200118000e25321040016c0030d9e4200039fffd8006000fff988c062060000200018000e25321040016c0030d9e4a00039fffd8007000fff980c662c60000000118004e25321040016c0030d9e4a00039fffd8007000fff9800802c6000000000000722532000002100000f9e4e0010600020001fff000800c80200000000011800720500100003700000e064c0013e00038007fff00021f0ffcf8001fffffe0007ffe3c7fffff9fffcffff8c001fffffffff9fff00021f0860080010c00060007ff9c3fffffe7000332607ffff2640020007ffffff21c001c08001ffffe000003f9c3fffffc00000fff87fffffffffc000000000021b0860080014e00060007e21c3f1c002700033ff87ffff3ffffe0007ffffff2130860080010c00060007ffe3c1e7ffd8fffccd9f80000d9bffdfff800000020f087c08000f3ffe60007ff9c39e7ffe70003cd987fffed9bffe0007ffffff2030fe8f800070001e0007c47ffe38003ffffff3e7fffffe7c003ffffffffff01fffe8f0001ffffffffffc463c7ffffffffffc3878c001ffffffffffffffff01fffe0000018ffffffffffffffffffffffffffffffffffffffffffffffffff01ff7e000001fffffffff8fffffffffffffffffffffffffffffffffffffffff01c0e1cc0001fffff000073fc307fffff1c000fffe0c001ffffff8001fff00001c087c00001ffffe00007ff9027ffffe70003fff84e001fffffe0007ffffff01c087c00001ffffe00007ff9027ffffc60003fff84a001fffffc0007000fff01c007c00001ffffe00004ff9027ffffc60003fff84a001fffffc0007000fff0130f88f00017c001e0007047fc638003ffffcf3e7fc001e7c003fffffff0000130f88f00017c001e0007047fc620003ffffcf387fc001e78003fffffff0000100fe8f00017c00180007c473e020003fffffc387ce001e7c003ffffffffff0100f98f0001fc001800073c63c7f80039fffcffe78c001ffc003fff9fff0000100f88f00017c001800073fe3c7fffff9fffcffff8c001fffffffff9fff0000100f88f00017c00180007047ffe38003ffffff3e7fffffe7c003ffffffffff0100668c00017c00100004c05320000016c00301864a00021c0018007000fff00c0f9cf0000f3fff800073fe3c7fffff9fffcffff8c001fffffffff9fff00000c0f9cf0000f3fff800070463c0200039fffcc3878c001c78003fff9fff00000c081c00000f3ffe000073f8001e7ffe10000cf980c001dfbffe0001fff00000c001c00000f3ffe000003ffffffffffffffffffffffffffffffffffffffff00c001c00000f3ffe000003f9c3fffffe70003fff87fffffffffe0007ffffff0080f88f000072001800072663c1240039fffccf9f8c001fffffffff9fff0000080f88f00007200180007224301040010c0000d9e0800039fffd80010000000080e00c00004200100007224301040031c0000f9e0c0013fffff8001fff0000080868000007200000007e2102104000600030d984a00039fffc0007000fff0080860000004200000007e2102104002700030f984e0013ffffe0007ffffff008080000000420000000722000104002100000f980c0013ffffe0001fff0000080060000004200000004e2102104000600030d984a00039fffc0007000fff003ffe8f000070001fffffc463c7ffffffffffc3878c001ffffffffffffffff003ffe00000000001ffffffffffffffffffffffffffffffffffffffffffffff0030f88f000170001e0007047fc620003ffffcf387fc001e78003fffffff0000000fe8f00007000180007c473e020003fffffc387ce001e7c003ffffffffff0000fe8f00007000180007c05320000016c00301864a00021c0018007000fff0000fe8f00007000180007c01020000006000300004a0002040000007000fff0000f9ffffffffffffffffc463c0200039fffcfffffffffffffffffffffffff0000f9cf000070001800073fe3c0200039fffcffff8c001c78003fff9fff0000000f98f0001f0001800073c63c7e00039fffcff878c001ff8003fff9fff0000000f88f000070001800073ffff9e7ffffffffcf9ffffffdfbfffffffffffff0000f88f000070001800073fe3c1e7fff9fffccf9f8c001dfbffffff9fff0000000f88f000070001800070463c0200039fffcc3878c001c78003fff9fff0000000f88f000070001800070463c0200018fffcc38780001c78001fff80000000000f88f00007000180007044300200010c000c38608001c7800180010000000000f88f000070001800070063c0000039fffc00078c000000003fff9fff0000000f880000070000000070463c0200039fffcc38000001c7800000000000000000f880000070000000000463c0200039fffcc38000001c7800000000000000000f80f000000001800073ffffffffffffffffffffffffffffffffffffffff0000e60c00004000100007c05320000037c00303864e00127c0038007ffffff0000e08c00007000100007044300200031c000c3860c001c780038001fff000000081ffffffffffffffffc000000000210000fffffffffffffffffffffffff0000810000018000000007380007c000210000fe000c001fe00020001fff0000000808f000070000000070463c02000210000c3878c001c780020001fff0000000808f000070000000070463c00000210000c3878c0010600020001fff00000008080000070001800070460002000390000c3878c001c78003fff9fff00000008080000070001800070060000000390000c2078c001c60003fff9fff00000008080000070000000070463c0200039fffcc3878c001c78003fff9fff0000000788f000070001800003ffffffffffffffffffffffffffffffffffffffff0000788f000070001800000463c0200039fffcc1878c000c18003fff9fff0000000060000000000000004c01020000006000302004a0012640000007000fff000001fffffffffffffff8fffffffffffffffffffffffffffffffffffffffff000001fffffef3ffffffffc000000000000000fffffffffffffffffffffffff000001ff7ffef3fff9fff83ffffffffffffffffffffffffffffffffffffffff000001800001f0000000003c0007e000000000ff8000001ff80000000000000000001800001f000000000380007c000000000fc0000001f8000000000000000000017fffff8fffffffffc000000000000000fffffffffffffffffffffffff0000008f000070001800070000000000000000fffffffffffffffffffffffff0000008f000070000000000463c02000000000c3878c000c1800000000000000000008f000000000000000463c0200039fffcc3878c001c78003fff9fff0000000008f000000000000000463c0200018fffcc3878c000c18001fff80000000000008f000000000000000463c00000000000c3878c00106000000000000000000008f000000000000000463c00000000000c3878c000000000000000000000000080000070001800000460002000380000c38780001c78003fff800000000000080000070001800000060000000380000c20780001c60003fff800000000000080000070000000003fe3c1e7ffd8fffccf9f80001dfbffdfff800000000000080000070000000000463c0200018fffcc38780001c78001fff800000000000080000070000000000400002000210000c3800c001c780020001fff0000000003ffffe00001ffffffffffffffffffffffffffffffffffffffffffffff0000003f7ffe000019fff80000000000000000fffffffffffffffffffffffff00000000000100000000000000060000000000320000001260000000000000000000000000040000000000000000000000000038000001078000000000000000000000000000001800000060000000390000c2078c001c60003fff9fff00000000000000000001800000060000000380000c00780001c00003fff800000000000000000000000000040000000000000000020008001060000000100000000000000000000000000003f9c3fffffc60003fff873ffffffffc0006000fff00000000000000000000003bffffdfffdeffff3c7ff3ffe387ffdfffe000fff00000000000000000000003bfff9c7ffffffff0c1fffffe183fffffffffffff00000000000000000000003b9c3fdfffe700033e787ffff3e7ffe0007ffffff00000000000000000000003b9c39c7ffc600030c1873ffe183ffc0006000fff0000000000000000000000387c3fd8003f0003fe67ffffffe4003ffffffffff0000000000000000000000387c07d8003e0000fe67f0001fe4003fffe0000000000000000000000000000387c07c0003f0000fe07fc001fe0003fffffff0000000000000000000000000387c07c0003e0000fc07f0001f80003fffe0000000000000000000000000000225321040037c0030f9e4e0013fffff8007ffffff0000000000000000000000225321040016c0030d9e4a00039fffd8007000fff0000000000000000000000041c3e3800270003f3e07ffffe7c0020007ffffff0000000000000000000000007ffe18003fffff3267fffff264003ffffffffff0000000000000000000000000007ffffffffff000000001ffffffffffffffff0000000000000000000000000007ffffdeffff000000000f9fffdfffe000fff0000000000000000000000000007ffffc00000000000001fffffc00000000000000000000000000000000000007dfffffffff000000000387fffffffffffff00000000000000000000000000000000000000fffffffffffffffffffffffff000000000000000000000000000000000000003260000010600000000000000000000000000000000000000000000000000000200000012640000000000000000000000000000000000000000000000000000000000002040000000000000000000000000000000000000000000000000000000000000000000000000000
def wireFallback1 : Nat := 0xffefffffff7afbf77dfddffffbf1e7dedafdedefdfefef2ddbdddfbbbf75f73ffeaffffff786bf71d7dc7fffbf003ce003ce0efdfefef0003dc07b80f70f7035eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eaffcade60fbe65d7987cc8000638c8038c0eb5001cc0d539907300e60e6035eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eafe0ade006be01d7807c000000380003800000001c000038007000e00e00fffffe3fff9a6bf93ffe5ff37ffd97f27fff2f048ffff3608be4ffcbff97f9735eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eafe0ade006be01d7807c000000380003800000001c000038007000e00e0035eafe0ade006be01d7807c000000380003800000001c000038007000e00e00ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffffff7ffaf3ff79ffde7ffffdf7feffffefefdfefff2ddbfddffbbff5ff3ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd770fbcf8fbce7ef39fbfebfdf79ffb797bc7d73b9fba773f6e6edcbdcfffffd600db800bb8056e01f37ebd97703fb703000001b000036006c00d80d80ffffd6005b8003b8016e00737ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80fffffe0a1d8061d8187606337ebd97f03fbf03000001f00003e007c00f80f80fffffe0a1d8061d8187606337ebd97f03fbf03000001f00003e007c00f80f80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80fffffe3fff9a6bf93ffe5ff37ffd97f27fff2f048ffff3608be4ffcbff97f97fffffe3fff9a6bf93ffe5ff37ffd97f27fff2f048ffff3608be4ffcbff97f97fffffe3fff9a6bf93ffe5ff37ffd97f27fff2f048ffff3608be4ffcbff97f97ffffd6307b8a03b821ee18737ebd97707fb707040d63b1208360d6c2ad81d83ffffd60099850d98846621b37ebf9f713fb713102001b092276206c40d88d88ffffd60099800998066601b37ebd97703fb703000011b040036026c04d82d84ffffd60099800998066601b37ebd97703fb703000011b040036026c04d82d84ffffd60099800998046601b37ebd97703fb703000001b000036006c00d80d80ffffd60099800998066601b37ebd97703fb703000011b040036026c04d82d84ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019850598806620337ebf9f713fb713102001b092276206c40d88d88ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019850598806620337ebf9f713fb713102001b092276206c40d88d88ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80ca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170000001c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068ca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170ca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffca0001f5217890174005c03ffbf0604e8004e0efdfee2f0d505d00b80170170fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd6b0fbaa1bba27ee99f77ebdb7747fb747470d73b564d368f6d2eda3da7ffffd7f5fbff9fbfe7eff9ffffffff7ffff7ffffffffbfffff7ffefffdffdffc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8ca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170ca0001f5217810170005c03ffbf0204e0044e8efdfee2f04585c08b91174170ca0501f5217a90176085d83ffbf1e45edac5edefdfee2f2dd85dd8bbb175173ca0001f5217810170005c03ffbf0204e0004e0efdfee2f04505c00b80170170c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8decf7bff6f7af2f779bdde7ffbf1e5dedaddedefdfeeef2dd9dddbbbb775773dedf7bff6ffaf2ff7bbfde7ffffdf5feffdfefefdffeff6dd9fdfbfbf7f77f7decf53706b4a82b461ad187bfab1c558da9585ac5d62a9298151d2a2a541543dedf7bff6ffff6fffbbffe7ffffffdffffdffffffffefffffdfffbfff7ff7ffdedf7b7f6fdfe6fdfbbf7e7bffffddfbffdfbfbcfffefbfbadf7fbeff7df7dfdedf53f56bff96bfe3aff87ffffffd7fffd7fffffffebffffd7ffafff5ff5ffdecf7a3f6f1a62f139bc5e737bf185d25add2d048feee32089c4db8bb715713dedf7b7f6fdfe6fdfbbf7e7bffffddfbffdfbfbcfffefbfbadf7fbeff7df7dfdedf53f56bff96bfe3aff87ffffffd7fffd7fffffffebffffd7ffafff5ff5ffc015017001c5841cc2873038fc07c869be0690bc7570389ba47330e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8988c6a2e6d1062d119b44662532105c212dc21048e4ae20089c49b883710712988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712988c42246910029101a440625321054212d421048e4aa20089449a883510512988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b88371071288000024211000110004402253200042000420048e4a22000044008801101108004002001000010008400205001004012040004044020008040108021001002120adcf9475fd47dc51e78c81426a8f8068f8fbf28d4e9f7e9f0d3d1a7ca782130840090850d0886422180040e1a2125221210201110d226222444488a88c000001c000659406c001a00c8002680d8000d0fb70000c9f741b003400680682130840090850d0886422180040e1a2125221210201110d226222444488a88ceb2585f5b17a991764c5d9bffbf1e65edae5edefdfef2f2dda5ddcbbb975973213085c090e0990e4643818c840c722ca522c2eb50111c4d5239247048e28e42130ac8f94b57d4b9e52e784054e3aa7256a7a53a29d56d67eae2d5d5abeabc35fffe8fdeb7ffebfffaffc4054fffb7fffb7f53a29dd6ffffafff5ffebfebfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000021cc0475d447d011e40c8102688f8048f0fbf2084e9f7c9f093c1278278000001c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068000001c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068000001c000659406c001a00c8002680d8000d0fb70000c9f741b003400680680010288f04b5744b9a12e604054628a7244a7853a29c56967cae295d52bc2b80010288f04b5704b9a12e604054620a7244a7853829c569658ae295d52bc2b80000288f043070431810c6040140208600486843828c4604588c091912342300000298f0475f4479811e60c0142688f0048f8fba28c4e9f7c9e093d127c278000029cf0475f447d811e60c8142688f8048f8fbf28c4e9f7c9f093d127c2780010288f04b5744b9a12e604054e38a7254a7a53a29c56d67cae295d52be2bc0000200c0410404110104400010000820048200082084200088409081210210000029cf0475f447d811e60c8142688f8048f8fbf28c4e9f7c9f093d127c2780000288f043070431810c6040140208600486843828c4604588c09191234230000001c0006090064001800c8000600c8000c0eb50000c0d501900300060060ca1501f521ff941fe287f83ffffffc7fffc7fffffffe3ffffc7ff8fff1ff1ff001001c000e5940ec203a00c840e782da502d2fb70101cdf743b207440ea0ec0000288f043070431810c6040140208600486843828c4604588c091912342300000280e04106041181046000100008200482000820842000884090812102100000200c041040411010440001000082004820008208420008840908121021000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000035fffe8fdeb7ffebfffaffc4054fffb7fffb7f53a29dd6ffffafff5ffebfebffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0010288f04b5704b9a12e604054620a7244a7853829c569658ae295d52bc2b80000288f043070431810c6040140208600486843828c4604588c091912342300000280e04106041181046000100008200482000820842000884090812102100000280a0400604018100600000000800008000000004000008001000200200000029ffe67ffe67ff99ffcc8142688fc048fcfffffe4ffffc9ff93ff27f27f000029cf047070471811c60c8140208e0048e8ebd28c4e04589c093912742700000298f0475f0479811e60c0142608f0048f8fb828c4e9f589e093d127c278ca1529ff25faf05f7a97de3ffffdf4feffcfefefdffe7f6dd8fdf9fbf3f73f7000029cf0470f0475811c60c8140608e8048e8ebd28c4e0d589d09391274270ca0528bf253a70533894de377bf1a4d65acd6d478fee6724d8ccd99bb3353330000288f043070431810c6040140208600486843828c4604588c091912342300000288e043070431810c604010020860048604382084604588c091812302300000280f04106041181046000140008200482800828c4200088409091214210000000800020100200008004000020040000404300000404500800100020020000000800020100200008004000020040000404300000404500800100020020ca1529ff25fff45ffa97fe3ffffffcffffcffffffffe7ffffcfff9fff3ff3ff0000200c04104041101044000100008200482000820842000884090812102100000208c043050431010c404010020860048604382084604588c09181230230000029ffe67ffe67ff99ffcc8142688fc048fcfffffe4ffffc9ff93ff27f27f00000100004580048001200800024009000090b80000089b00120024004804800000085003010030000c0040140200600006043828c0604500c0018003003000000085003000030000c0040140000600006043828c0600000c0018003003000000080002010020000800400002004000040430000040450080010002002000000000000000000000000000000000000000000000000000000000000000000000085003010030000c0040140200600406843828c0604580c08191034030ca1529ff25fff45ffa97fe3ffffffcffffcffffffffe7ffffcfff9fff3ff3ff0000288f043070431810c6040140208600486843828c4604588c09191234230000000000000000000000000000000000000000000000000000000000000000ca1529ffe7fffe7fff9ffffffffffcffffcffffffffe7ffffcfff9fff3ff3ff000029ffe67ffe67ff99ffcc8142688fc048fcfffffe4ffffc9ff93ff27f27fca1529ff67fff67ffb9ffe7ffffffcffffcffffffffe7ffffcfff9fff3ff3ff00000180006590068001a00c0002600d0000d0fb00000c9f501a0034006806800000100004580048001200800024009000090b80000089b001200240048048000029ffe67ffe67ff99ffcc8142688fc048fcfffffe4ffffc9ff93ff27f27f000029ff247ff447fa91fe0c8142688fc048fcfffffe4ffffc9ff93ff27f27f00000085003010030000c0040140200600006043828c0604500c0018003003000000085003010030000c0040140200600406843828c0604580c0819103403000000085003010030000c0040140200600406843828c0604580c0819103403000000085003000030000c0040140000600006043828c0600000c0018003003000000085003000030000c0040140000600006043828c0600000c00180030030000000800020100200008004000020040000404300000404500800100020020000000000000000000000000000000000000000000000000000000000000000ca0501f5217a90176085d83ffbf1e45edac5edefdfee2f2dd85dd8bbb17517300000085003010030000c0040140200600406843828c0604580c08191034030000000800020100200008004000020040000404300000404500800100020020ca1529ffe7fffe7fff9ffffffffffcffffcffffffffe7ffffcfff9fff3ff3ff000029ff667ff667fb99fe4c8142688fc048fcfffffe4ffffc9ff93ff27f27f000000000005000080002000000200010000101000000092000200040008008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ca1501f021ef941ee287b83ffebffc7dff87d7ff7d723dfff47bf0f6e1eb1efca15017521df841de287783bffffdc7bffc7bfbcfffe3bfbac77f8eff1df1dfca15017521da801d6287583bfffdd47affc7afacdffe3b698875f8ebf1d71d7ca15017021cf841ce287383bfebfdc79ff8797bc7d7239fba473f0e6e1cb1cfca15017021ca801c6287183bfebdd478ff8787ac5d7239698071f0e2e1c31c7c015013001c5841c828730387c0fd8693f0692bc257038dba47230e661ca1ccc015013001c5841c828730387c07c8693e0690bc2570389ba47230e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8c015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c88804002421100011008440225321044212c421048e4a22008844988831101128804002421100011008440225321044212c421048e4a22008844988831101120010008000a5140a8202a004040e382525025253201014d6742a205440aa0acca150035219f0419a28678337fff9c737fc73f14affe33f2ac66f8cff19f19f0015000000879408e2823800040ffc31ffc31f10201010fffc23f847f08f08f0015000000879408e2823800040ffc31ffc31f10201010fffc23f847f08f08f0000000000059400c000200000026801800010102000009f7403000400080080015000000878408e2823800040fdc31ffc31f10201010fbac23f847f08f08f000001f5207f9407e281f80c8142680fc040fcfffffe0ffffc1ff83ff07f07f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def readWire (i : Nat) : Sig :=
  let code := (wireRecipes >>> (45*(i-1))) &&& 0x1fffffffffff
  if code &&& 1 = 1 then recipeValue sourceSignals (code >>> 1) else
    (BitVec.ofNat 252 (wireFallback0 >>> (252*(code >>> 1))),
      BitVec.ofNat 252 (wireFallback1 >>> (252*(code >>> 1))))

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

def frontierData : Nat → Nat → Nat
  | 8, 0 => 0x2077497850d3542cdb2646281df85e1434d50b36c9910a077697850d3542cdb2646181df35e1434d50b36c99171ba6d57850d3542cdb2647681dba5e16150d3542cdb266076e97850d3542cdb2642e81dff5e1434d50b36c99106076e99f5e1434d50b36c9981dba5e16750d3542cdb266077497850d3542cdb2640b81dd25e1434d50b36c9918e076e98250d3542cdb2641181dba609434d50b3f0db266076e97850d3542cdb2642981dba5e16850d3542cdb266076e978595434d50b36c9981dba5e1434d50b36c99006076e978581434d50b36c9981dba5e1434d50b36c990b6076e9a05e1434d50b36c9981dba6497850d3542cdb266077097850d3542cdb2640981dc25e1434d50b36c9919a077e17850d3542cdb2640b81df85e1434d50b36c9910e076e98750d3542cdb2641381dba61d434d50b3e8db266076e9ab50d3542cdb2641481dba6ad434d50b36cb1266076e97850d3542cdb2641b81dba64d7850d3542cdb2660a6e97850d3542cdb2641b829ba6697850d3542cdb266076e97850d3542cdb26436821ba5e1434d50b36c990da077197850d3542cdb2646481ddf5e1434d50b36c99176076e978599434d50b36c996e9b55e1434d50b36c990e2076e97850d3542cda2643881dba5e1434d50b36c990d6076e978589434d50b36c9981dba5e1434d50b36c9905a077697850d3542cdb2643881dba6897850d3542cdb266076e97850d3542cdb2642f81df35e1434d50b36ca6266076ed7850d3542cf536c9981dba5e1474d50b3d4db266077fd78589434d50b36c99829ba5e16c50d3542cdb266076e97858d434d50b36c9981dba5e1434d50b36c991a2076e98250d3542cfe36c9981dba609434d50b3fcdb266077497850d3542cdb2640881dd25e1434d50b36caa266077497850d3542cdb2645b81dba609434d50b36c990be076e97850d3542cdb2909981dba5e1434d50b36c9906607749a25e1434d50b36c9981dd95e1434d51d42cdb266077657850d354b90b36c9981dbb5e1434d50b36c990580081dbb5e1434d50b36c9981dba5e1434d50b36c9a266076e97850d3542cdb2641581dba5e17050d3542cdb266076e97850d3542cdb2646981df86ad434d50b36c9910a077e17856d3542cdb2644281df85e1435010b36c9910a077e17850d35494db2644281df85e1434d50b3c8db10a077097850d3542cdb2648681dba61d434d50b3fcdb266076e9ab50d3542cdb2641281dba6ad434d50b36cb2266077e17850d3542cdb2643f81dc25e1434d50b36cab266077e17850d3542cdb2640a81df85e1434d50b36ca7266077e17850d3542cdb26440829ba5e1434d50b36c990d6076e98750d3542cdb2643581dc25e1434d50b36c990d6076e97850d3542ce72643581dba5e1434d50b37cdb266076e97850d3542cdb26430829ba61d434d50b36c990d60a7097850d3542cdb26435829ba5e1434d50b39c990d60a6e97850d3542cdf36c99829ba5e1434d50b36c990c20a6e97850d3542cdb26418829ba6e17850d3542cdb2663a81dc25e1434d50b36c9981df86897850d3542cdb2663a829ba5e1434d50b36c998ea086e97850d3542cdb26607719a25e1434d50b36c998ea076f57850d3542cdb266077ddba5e1434d50b36c8a81dba5e1434d50b36c8a0e2076e97850d3542cdb2641e81dba5e1434d50036c9906a076e97850d3542cdb2648c81dd05e1434d50b36c990e2076e97d50d3542cdb2643881dba5e14a4d50b36c990ac0081dda5e1434d50b36c9981df35e1434d50b36c990e2076e97850d3542cdb2642c81dba5e1434d50b36c991b2076e97850d3542cdb2643381dba5e1434d50b36cbb266076e99e50d3542cdb2643881dba61d434d50b36c990e2077097850d3542cdb2643881dba609434d50b36c990e2077557850d3542cdb2642b81dba5e1434d50b36ca2266076e9785093542cdb2642b81dba5e16450d0b36cb3266076e97850d2942cdb2cc99002076e97850d0b36cb3266077697850d354b90b36c9981dba5e16450d0b36c991ea1e84dba5f5434d50b36c998c6136e97d50d3542cdb2662d83dba5e1434d50b36c9987a136e97850d35438db266076e97850d35420db2641881dce5e1434d50b3d4db266076e97850d3542cdb2642b8ae136e97d50d3542cdb2662b84dba5e1434d51136c9981dba5e1434d50b36c990aa076e9785553542cdb2642b81dba5e1434d50b36c9913e076e97850d3d42cdb2642b81dba5e1434d50b36c9f2660a6e97850d3542cdb2642b81dc25e1434d50b36c990ae077e17850d3542cdb2642b81dba5e14e4d50b36c990ae076e97850d3a42cdb2642b81dba5e1434d52536c990ae076e97850d3542cdb2647481dba5e1434d50b36c99062077497850d3542cdb2642b81dba5e1434d50b36c9913a076e97d50d3542cf536c9981dba5f5434d50b36c9911a0776dda5e1434d50b36c9981dba5f5434d50b36c9915a076e9785293542cf536c9981dba5e14a4d50b36c9911a077b9da5e1434d50b36c9981dba5e14a4d50b36c990ea077697850d354750b36c9981dda5e1434d50b36c991be077697850d3542cf536c9981dda5e1434d50b36c9911a076e97d50d3542cdb2889981dba5e1434d50b3d8db266076e97850d3542cdb2644a87a0f6e97850d3542cdb2662883dba5e1434d50b36c9981dba5e14a4d50b36c99062076e97850d35438db2641881dba5e1484d50b36c990ae076e9785213542cdb26418002077397850d3542cdb266076e97850d3542cdb2849981dba5e1434d50b36c9903a076e9785293542cdb298996e9785a5434d50636c9906a076e9785b5434d50b36c9981dba5dd434d50b36c9911a076e97850d3d4cd0b36c9981dba6cd7850d3342cdb2640081dba5e1434cd0b36c9981dd25e17150d3542cdb266077497850d3542cdb2646a8ca0b6e97850d3542cdb266076e97850d3542cdb26003821ba6857850d3542cdb266076f5a15e1434d50b36c9981dc66857850d3542cdb266076fd785b5434d50b36c9981dba6156d50d3542cdb266076e97850d3542cef36c9981dd25e16d50d3542cdb26607741a15e1434d50b36c9981dba5e1434d50b36cba26607749a15e1434d50b36c9981dba5e1434d50b36c991aa076e9785c5434d50b36c6a81dba5e1434d50b36c9811a076e97850d3542cdb3009981dba5e1434d50b36c991ae076e97850d3542cdb1bc6a829ba5e16d50d3542cdb26607709785b5434d50b36c9981dba61d6d50d3542cdb266076e9785c5434d50b36c9981dc26857850d3542cdb266077e1a15e1434d50b36c99829ba6857850d3542cdb266076e9785d1434d50b36c9981dba5e1434d50b36cbc266076e97850d3542cf536c6a81dba6096d50d3542cdb266076e97850d3542cdb2749981dba5e1434d50b36c990762885dba5e1434d50b3849988a206e97850d3542cdb266076e97850d35424db2641781df25e1434d51d42cdb266077e17850d3542cdb2641d81dba5e1434d52536c99076076e97850d3542cdb3609981dba5e1434d50b36c99072077097850d3542cdb2641d829ba5e1434d50b36c99076076e97850d3542cdb2647381dba5e1434d50b36c9905e077497850d3542cdb2641d81dba5e1434d50b36c99132076e97850d354790b36c9981dba5e1434d50b36c991c62284dba5e1434d50b36c9981dba5e1434d50c36c9905e076f17850d3542cdb2641d81dbc5e1434d50b36c9905c0081dbc5e1434d50b36c9981dba5e1434d50b36c9c266076e97850d3542cdb2640c6e9b55e1434d50b368991bdba6597850d3542cd52643181dba5e1434d50b3548a0c6076e99b5e1434d50b36c9981dba61d434d50b368991be076e97850d3442cdb2646f81dc25e1434d50b368991be07709b661d434d50b36c9981dc26d9785393542cdb266076e9b661d4e4d50b36c9981dba6ad9b50d3542c990c6076e97850d404c90b36c9981dba66d7850d3242cdb2640081dba5e1434c90b36c9981df86a17850d3542cdb266076e9ab66d434d50b36c8a81dba6ad434d50b36c992280081dba6ad434d50b36c8a81df86757850d3542cdb266077e19b5e1434d50b36c8a81df85e1434d50b36c992280081df85e1434d50b36c8a81dba5e1434d52542cdb22a33829ba5e1434d50b36c99829ba5e1434d50b368991be0a6e9b661d434d50b36c99829c26d97850d3542cdb2660a6e9b65e1434d50b39c9981dba5e1434d50b3c8db22a0a6e9b75e1434d50b36c9981dba66d7850d35494db22a076e97850d35494db2648a002076e97850d35494db229ba6d57850d3542cdb2640381dba5e1434d50b3689900e086e9b65e1434d50b36c9981dc666d7850d3542cdb2660777d9b5e1434d50b36c9981dba5e1434d50b414db266077e19b5e1434d50b36c99829ba6d97850d3542cdb266076e99b5e1434d50b36c8a81dba5e1434d50b36c992280081dba5e1434d50b36c8a81dba6757850d3542cdb22a076e9a85e1434d50b36c8a81dba66d7850d35404db22a076e97850d35404db2648a002076e97850d35404db22a076e97850d3542cdb2283181dba5e1434d50b40cdb2662881dba5e1434d50b36c8a81dba5e1434d50b368991be076e97850d3545d0b36c8a81dba5e1434d50136c9903e076e9a95e1434d50b36c9981dba5e1434d50b408db266076e97850d354750b36c8a81dba5e1434d50b36c8a1be077099b5e1434d50b36c99829ba66d7850d3542cdb266076e97850d354a50b36c8a81dba5e1434d50b36c9922e076e97850d3542cf536c8a81dba5e1434d50136c9911a076e97850d3542cdb2284681dba6757850d3542cdb266077499b5e1434d50b36c9981dba6ad5b4d50b36c990e22881dba6ad434d50b2643881df47097850d3542cdb266076e97856d3542cdb2642581df86ad434d50b36c990e2077e17856d3542cdb2643881df85e1435010b36c990e207811c25e1434d50b36c9981dba5e1435010b36c9908e077e17850d35494db2643881dba6ad434d52536c990e2076e97856d35494db2643881dba5e1435012536c990e2076e97850d35494f236c388920a6e97850d3542cdb266076e9ad50d3542cdb2643881dd55e1434d50b36c990e2076e97c50d3542cdb26438002077417850d3542cdb26607761d25e1434d50b36c9981dba5e1434f50b36c9908e076e97850d3542cdb3109981dba5e1434d50b380db266076e97850d3542ce62643881dbf5e1434d50b36c990e2076e98550d3542cdb26438829ba61d434d50b36c990e2076e9875393542cdb2643881ddd7097850d3542cdb266076e9785393542cdb26426829c25e1434d50b36c990e2077098750d3542cdb2643881dc25e14e4d50b36c990e2077097850d3a42cdb2643881dc37097850d3542cdb266076e97850d3a42cdb2642481dba5e1434d50b36c990ca0a6e97850d3542ce72643881dba61d434d50b39c990e2077097850d3542ce7264388620a6e97850d3542cdb266076e97850d3542ce726432829ba5e1434d50b36c991da076e98750d3542cdb2647681dc25e1434d50b36c991da076e97850d3542ce72647681dba61d434d50b36c99036077097850d3542cdb2640d81dba5e1434d50b39c99036077017850d3542cdb2646f81dbe5e1434d50b36c991be096e97850d3542cdb2646f81dff5e1434d50b36c990e2076e97850d3542cdb2643781dba635434d50b36c990e2076e97850d3542cdb2647d81dba5e1434d50b39c990e2076e97850d3542cdb2949981dba5e1434d51336c990e20777d7850d3542cdb2643881dba601434d50b36c990e2077197850d3542cdb2643881dba68d434d50b36c990e207779d25e1434d50b36c9981dba5e1554d50b36c9909e076e97850d3542cdb26420821ba5e1434d50b36c990e2076e97950d3542cdb2643881dbd5e1434d50b36c990e2076e98250d3542cdb2645081dba5e1554d50b36c9903e076e97b50d3542cdb2644681dba6ad434d50b36c990e2077e17850d3542cdb2643881dba5e1434d52536c990e2076e98350d3542cdb2643881df85e1434d50b384db266076e9ab50d3542ce136c9981dba5e1434d525384db266077497850d3542ce136c9985e0b6e97850d3542cdb266076e97850d3542cdb30c99829ba5e1434d50b384db266076e98750d3542ce136c9981dc25e1434d50b384db266076e97850d3542ce936c9985e0a6e97850d3542cdb266076e97850d3542cf836c4b81dba60d434d50b384db266076e97850d3542cdb24c4681dba60d434d50b36c9912c0081dd35e1434d50b36c9981dba5e1434d50b36cce266076e97850d3542cdb2fc9981dba5e1434d50b3d4db12e076e98250d3542ce136c9981dba6ad434d50b264380c6076e97850d3542ce12643181dba5e1434d50b354990c62885dba5e1434d50b36c9981dba6ad434d50b36c990c6077e17850d3542cdb2643181dba5e1434d52536c990c6076e9ab50d3542cd526431002076e9ab50d3542c990c6077e17850d3542cd52643181dba5e1434d525354990c6076e97850d3542cd72643181dd25e1434d50b36c990c6076e97850d3542cdb2641f829ba5e1434d50b36c990c6076e98750d3542cdb2643181dc25e1434d50b36c990c6076e97850d3542ce72643181dba5e1434d50b36c991d6076e98250d3542cdb2643181dba5e1434d51f42cdb266076e97850d3542cdb2647081dba5e1434d50b36c991361e849ba5e1434d50b36c9981dba5ed434d50b36c990c6077497850d3542cdb2643881dba621434d50b36c990e2076e97850d3542cdb2643181dba5e1434d50b36c991da076e97850d35444db2647281dba5e1434d50b36c99142076e97850d3542ce12644d81dba5e1434d50b36ca612e077497850d3542cdb298998ae0b6e97850d3542cdb266076e97850d3542cdb2809981dba5e1434d52536ca6266077e17850d3542cdb2989981dba6ad434d50b36ca6266076e97850d4042cdb2989981dba5e15b4d50b36ca626623829ba5e1434d50b36c9981dba5e1434d50b36c991f2076e9785553542cdb2989981dba5e1434d50b36cd0266076e97850d3542cdb2649781dba5e1434d52036c991ca076e97853d3542cdb2989981dba5e1434d50b36c8911a076e97850d354a4db2647281dba5e14f4d50b36c991c80081dd15e1434d50b36c9981dba5e1434d50b3a0db266076e97850d354bd0b36c9981dba5e1434d50b36c991ee076e97850d3542cd52644d81dba5e1434d50b36ccf2661e84dba5e1434d51136c998b2136e97850d3542cdb266076e97850d3d42cdb2989981dba5e1434d52042cdb266076e97850d3542cdb2789981dba5e1434d51d36c991ca0a6e97850d3542cdb2989981dc25e1434d50b36ca6266076e98750d3542cdb2989981dba5e14e4d50b36ca6266076e97850d3a42cdb2989981dba5e1434d50b39ca6266076e97850d3542cf836c9981dba5e1434d50b36ca3266076e98250d3542cdb2989981dba5e1434d51136c9906a076e97850d3542cdb2643881dba5e1434d50636c9906a076e97850d354a8db2641a81dba5e1434d50f36c9906a2b84dba5e1434d50b36c9981dba5e1494d51136c9906a07771d05e1434d50b36c9981dba5e1494d50b36c990a2076e9785253542cdb2989981dba5f1434d50b36c9906a076e97c50d3542ce136c9981dba5f1434d50b36c990c6076e97c50d3542cdb2989981dba5e1494d50b36c9906a076e97850d3542ce136c9981dba5e1434d50b36c990d2076e97850d3542cde2643181dba5ed434d50b36c990e2076e97850d3542cdb2989981dba5e1434d50b36c9908a076e97850d35434db2641a829ba5e1434d50b36c990e2076e97a50d3542cdb2643881dbe5e1434d50b36c990e2076e97850d3542cdc2643881dd25e1434d50b36c9906a077497850d35418db2641a81dba5e1434d52836c9906a076e97850d3542cdb2641a002076e97850d3542cdb266076e97850d35424db2641a81df85e1434d50b36c9906a076e9ab50d3542cdb2641a81dba5e15b4d50b36c9906a076e97850d4042cdb2641a81dba5e1434d52536c9906a076e97850d3542cf236c1a81dba5e1434d50b36cbd266076e97850d35490db2641a81dba5e1554d50b36c9906a076e97850d3542cdb2640f81dba5e1434d50836c9906a076e97850d3d42cdb2641a81dba5e1434d50b36c9924a077097850d3542cdb2641a81dba61d434d50b36c9906a076e9785393542cdb2641a81dba5e1434e90b36c9906a076e97850d3542ce72641a81dba5e1434d50b36c99036076e97850d354a4f52641a81dba5e1434d50b36c99042076e98250d3542cdb2641a81dba5e1434d51536c9906a076e97850d3542cdb2644981dba5e1494d50636c9906a076e9785d9494d4db2641a81dba5e1494d52936c9906a3581dd05e1434d50b36c9981dba679434d50b36c99166076e97c50d3542cf536c9981dba5f1434d50b36c9911a0775dd05e1434d50b36c9981dba5f1434d50b36c9915e077cd7850d354750b36c9981df35e1434d50b36c991be07805d05e1434d50b36c9981dba5e1594d50b36c990ea076e9785653542cf536c9981dba5e1594d50b36c9911a076e9785253542cf536c9981dba5e1494d50b36c9911a077add05e1434d50b36c9981dba5e1494d50b36c990f2077417850d354750b36c9981dd05e1434d50b36c991be077417850d3542cf536c9981dd05e1434d50b36c9911a076e97850d354a4db2641a81dba679434d50b36cbf266076e97850d3542cdb2644781dba5e1434d50b36c9912e1e845ba5e1434d50b36c998a2116e97850d3542cdb266076e9785253542cdb2640f81dba5e1464d50b36c9906a076e9785193542cdb2640f0020773d7850d3542cdb266076e97850d3542cdb26c9981dba5e1494d50b36c9e266076e97850d3542cdb2647281dba5e1434d50b3dcdb266076e97850d3542cdb26448896136e97850d3542cdb266076e97c50d3542cdb2640d829ba5e1434d50b36c9906a076f97850d3542cdb2641a81dba5e9434d50b36c9906a076e9785153542cdb2641a81dba5e1434dd0b36c9906a076e97850d3542cdc2641a829ba5e1434d50b36c99036076e97a50d3542cdb2640d002077017850d3542cdb266076f97850d3542cdb2640d002076f97850d3542cdb266076e97850d3542cdb2f89981dba5e1434d50b3709903400825ba5e1434d50b36c9981dba5e1434d50b3c4db266077fd7850d354b90b36c9981dff5e1434d50b36c991ea3981dd55e1434d50b36c9981dba5e1574d50b36cc8266076e98d50d354b90b36c998de1e7557850d3542cdb266076e97855d3542cf536c7787a0a7557850d3542cdb266076e97850d3542ce62647a81dba5e1504d50b36c991ea076e97850d3c42cdb2647a81de25e1434d50b36c991ea076e98a50d3542cdb2647a81dba5e1434d51336c991ea076e9785713542cf336c9981dba5e15c4d50b36c991163781dd55e1434d50b36c9981dba6b5434d50b36c9916a0775dd55e1434d50b36c9981dba635434d50b36c9920a07801d55e1434d50b36c9981dba5e15c4d50b36c9914a076e9785713542cf536c9981dba5e1574d50b3d4db266077b1d55e1434d50b36c9981dba5e1574d50b36c991de077557850d3542cf536c9981dba635434d50b3d4db2661e831ba5e1434d50b36c9987a136e97850d3549cdb2661e84dba6b5434d50b36c9987a137557850d3542cdb2661e84dba5e1434d5293d4990021e84dba5e1434d5293d6076e9785713542cdb2644681dba691434d50b3d4db266077257850d3542cf536c9981dba5e1564d50b3d4db266077817850d3542cdb2644681dba605434d50b36c9911a076e9785313542cdb2644681de05e1434d50b36c991140081de05e1434d50b36c9981dba605434d50b36c991140081dc95e1434d50b36c9981dba5e14c4d50b36c991140081dc75e1434d50b36c9981dd55e1434d50b36c9911a0a6e97850d3542cdb2644681dba5e1574d50b36c9911a076e97f50d3542cdb2644681dba609434d50b36c99116076e9785553542cdb32499839ba609434d50b36c9911a076e98f6093542cdb2644681dba609754d50b36c9911a077318250d3542cdb2644681dba6a98250d3542c9911a076e98250d354890b2644681dba609434d50b36c99182076e9785553542cdb2647a8e2077497850d3542cdb266076e98250d3542cdb2645a8d20775d7850d3542cdb266076e9785553542cdb2645381dba5e1554d50b36c991de076e9785553542cdb3449981dba5e1554d50b36cd4266076e98250d3542cdb2a49981dd25e1434d50b36c991ea076e97850d3d42cdb2e0998d21e7497850d3542cdb2661e84dd25e1434d50b36c9981dba609554d50b36c991180081dd25e1554d50b36c9981dd67497850d3542cdb26607805d25e1434d50b36c9981dba5e1434f50b36c9925a076e98250d3542cdb2648281dec75d7850d3542cdb266077497850d3542cdb2648e81dba5e1534d50b36c990ee076e9785753542cdb2643b81dba5e1434f50b3b0db266156e9785553542cdb2643b0020e6e98250d3542cdb26607711785553542cdb2643b00207749785453542cdb266076e97e5553542cdb2643b002077c5785553542cdb266076e9785553842cdb2643b002077318250d3542cdb266076e97850d3d42cdb2b89981dba5e1554d51236c990ec00899d25e1434d50b36c9981dba5e1434f50b36cb9266076e9785553542ce22643b0021c7497850d3542cdb266076e98250d3542cdb2640781e037497850d3542cdb266076e97850d3d42cdb2d89981dba5e1434a50b36cb62640081dba5e14342cdb2d89981dba5e1434f50b36c991ea1e84dba609434d50b36c998c2136e98250d3542cdb2660779dd25e1434d50b36c9981dba5e1434f50b36c9900a077498250d3542cdb26446002077498250d3542cdb266077517850d3542cdb2644681dba5e1434d50b36cc92661984dba5e1434d51536c9981dba5e1434f52c42cdb266077497850d3542cdb2647981dec7497850d3542cdb266076e97850d3d42cdb2b09981dba5e1554d50b3d4db2661984dba609434d50b36c9981dba5e1434d50b36cca266077497850d3542cdb334998660b6e97850d3542cdb266076e9785553542cdb3349981dba5e1434fd0b36ccd266076e98c50d3542cdb26479002077517850d3542cdb266076e97855d3542cdb3349987a136e97850d35454db266076e97850d3d42cdb3349981dba609434d50b36ccd266077497850d3542cdb3309981dba5e1434d51336c9900e086e98250d3542cdb2640382e086e97850d3542cdb266086e97850d3542cdb26445821ba609434d50b36c9911800821ba609434d50b36c99821ba5e1434d50b36ccd266076f58250d3542cdb26403821bd5e1434d50b36c9911a076e97850d3e42cdb3349981ddf5e1434d50b36c9900e07785bd5e1434d50b36c9981dba5e1434d90b36c99012076f58250d3542cdb26446002076f58250d3542cdb266076e97850d3642cdb33499821ba5e5434d50b36c9911a076f57950d3542cdb2644681dba5e1544d50b36ccd266076e98050d3542cdb2640381dd26fd7850d3542cdb266076e9785113542cdb2643e81dba5e1444d50b36ccd266076e9825113542cdb26403821ba5e1444d50b36c9911a076f5785113542cdb2644681dba5e5444d50b36c9911a077197850d3542cdb3349981dc65e1434d50b36c9900e076e9825113542cdb26446002076e9825113542cdb266077a1bf5e1434d50b36c9981dba5e5434d50b36c9901e076e97950d3542cdb3349981dbd5e1554d50b36c9900e086e97850d3642cdb2644681ddf5e14b4d50b36c9911a076e98052d3542cdb2644681dba5e1444d90b36c9911a076f57850d3542cdb3349981dba6094b4d50b36c991180081dba6094b4d50b36c9981dc86f57850d3542cdb266076e97850d3642cdb2643d81dba68d434d50b36ccd266076e9a350d3542cdb2640381dba5e1434d51a42cdb266077497850d354750b36c9981dc15e1434d50b36c99252076e98650d3542cdb26494821ba5e1434d50b36c99252076e98250d3542cdb26446002077497850d3542cdb266076e97850d3546d0b36c9981dff5e1434d51d42cdb2663c81dba5e1434d50b36c9981dba5e1434d52c42cdb266076e97850d3542cdb2649481dd55e1434d51d42cdb2660a6e97850d354750b36c9987a0b6e97850d3542cdb26628829ba5e1434d50b36c9981dba5e1434d50b36ccb266076e98250d354b90b36c9981dba609434d50b36c99252077b5d25e1434d50b36c9981dba5e1434f50b36cad266348a1d25e1434d50b36c9981dd25e1434d52e42cdb266077497850d3542cdb2649481de65e1434d51d42cdb266077057850d3542cdb2646f81dc15e1434d50b36c991b80081dc15e1434d50b36c9981dfc5e1434d50b390db266077fd7850d3542cdb2646f81dd57497850d3542cdb266076e98250d3542cdb2640681dba609434d50b36c991e80081dbf5e1434d50b36c99002076f57850d3542cdb266077097850d3542cdb2646e81dc25e1434d50b390db266076e97850d3a484db2646f81dba6514e4d50b36c991be077bd785393542cdb2646f81e0561d434d50b36c991be277097850d3542cdb2646f81dc25e1434d52336c991be07749785393542cdb2646f81dba6094e4d50b36c991be106e98750d3542cdb2646f81dc55e14e4d50b36c991be076e9895393542cdb2646f81dcd61d434d50b36c991be076e97853935448db2646f875c25e1434d50b36c991be076e97850d0b36cb52646f81dc2609434d50b36c991be07819c261d434d50b36c9981dba5e14e4e93042cdb266077e1ab50d354750b36c9981df86ad434d50b36c991be077f9c261d434d50b36c9981dba5e15b5010b36c9914607709af61d434d50b36c9981df86ad434d50b36c99162076e9785393a42cf536c9981dba5e14e4e90b36c9911a07709a561d434d50b36c9981dba5e14e4e90b36c991de077098e61d434d50b36c9981dc261d434d50b36c99202077098750d354750b36c9981dc261d434d50b3d4db266077098750d3542cdb2644681df0709785393542cdb266076e98750d3a4c50b36c9981dc25e1765393542cdb266076e98750d3a42cdb2648081dba6ad5b4d51d42cdb266076e9ab56d3542cdb2646f81dfe709785393542cdb266076e9ab56d3542cdb2645181dc25e15e5393542cdb266076e9ab56d3542cdb2645881dba6ad5b4d50b3d4db266076e9ab56d3542cdb2644681dc25e1525393542cdb26607709785393542cdb2647781dc25e14e4d51d42cdb26607709785393542cf536c9981dc25e14e4d50b36c9911a07709875393542cdb2646f00207709875393542cdb2662181dba61d4e4d50b36c9981df85e15b4d50b36c99146076e99561d4e4d50b36c9981dba61d4e5053542cdb266077e17856d354750b36c9981df85e15b4d50b36c991be076e9875794e4d50b36c9981dba6ad435010b36c99162077e17856d3542cf536c9981df85e15b4d50b36c9911a076e9875d94e4d50b36c9981dba61d4e4d50b36c99202076e9875494e4d50b36c9981dba61d4e4d50b36c991de076e987539354750b36c9981dba61d4e4d50b3d4db266076e9875393542cdb2644681dba61d434d50b36c9920a076e97856d3542cdb2647e81dba5e14e4d50b36c991fe076e9785393542cdb2a09981dba5e15b4d50b36cd3266076e98750d3542cdb2a49981dba5e15b4d50b36c991ea076e98750d3542cdb2648581dba5e15b4d50b36ccd26607755c25e1434d50b36c9981dba635434d50b36c9911a076e9785393542cdb334998e2077097850d3542cdb266076e9ab50d3542cdb2645a8de0775d7850d3542cdb266076e97856d3542cdb2645381dba5e14e4d50b36c991de076e97850d3a42cee36c9981dba5e14e4d50b36caf266076e98750d3542ceb36c9981dba5e14e4d50b36c990fa076e98750d3542cdb2649481dba5e1435010b36cc5266378a1c25e1434d50b36c9981dc25e1434d50b36c99252077f1c25e1434d50b36c9981dfc5e1434d50b36c991bc0081dfc5e1434d50b36c9981df861d434d50b36c991bc0081df861d434d50b36c9981df85e14e4d50b36c991be076e9ab5393542cdb2646f002077e1785393542cdb2663b81dc25e1434d50b36c9981dba6ad434d50b36c992063781dfe5e1434d50b36c9981dba5e1434e90b36c9921e077097850d3542cdb2648f81dba5e15d4d50b36c99146076e97850d4042ce336c99851ba5e15b4d50b36c9914400835ba6ad434d50b36c9981de55e15b4d50b36c991440081dba6514e4d50b36c9981dba6115b4d50b36c991440081def5e14e4d50b36c9981dba5e15b4e50b36c991440081e0561d434d50b36c9981dba5e1435010b36cd2266076e97856d35458db26451002277097850d3542cdb266076e9ab50d3542cdb2640581dba5e1434e90b36cb9266076e97856d3542ce2264510021c7e17850d3542cdb26607805c25e1434d50b36c9981dba5e1434e90b36cb7266076e9ab50d354b90b36c9981dba6ad434d50b36c991ea34879f85e1434d50b36c9987a137e17850d3542cdb266077097850d3542cdb3349981dba6095b4d50b36c991180081dd25e14e4d50b36c9981dcb7097850d3542cdb266076e97850d3a42cdb2643d81dba6ad434d50b36ccd266077e17850d3542cdb2647a81dba5e14e4d50b36c9921237879c25e1434d50b36c9987a137097850d3542cdb266077e17850d3542cdb3349981dba6094e4d50b36c991180081dba6094e4d50b36c9981de97097850d3542cdb266076e98750d3542cdb334998e6077097850d3542cdb266076e9785393542cdb2645f81dba61d434d50b36c99202077a9d75e1434d50b36c9981df85e1434d50b36c99236076e9785693542cdb2645181dba5e15e4d50b36c991de076e9785393542cf536c7781dba5e1434e90b3b4db266166e9785393542cdb26477002106e98750d3542cdb26607715785393542cdb2647700207715785393542cdb266076e9895393542cdb26477002076e9895393542cdb266076e9785393b42cdb26477002077358750d3542cdb266076e97850d3a42cdb2b89981dba5e14e4d51236c991dc00899f85e1434d50b36c9981dba5e14e4d50b3a8db266076e9785393542cea264770021d7097850d3542cdb266076e98750d3542cdb2640781dba61d434d52e42cdb266076e9ab50d3542cdb2649481ded7097850d3542cdb266076e97850d3a42cdb264888d2287e17850d3542cdb266077e17850d3542cdb2649481dc261d434d50b36c991bc0081dc261d434d50b36c9981dc25e14e4d50b36c991bc0081dc25e14e4d50b36c9981dba61d4e4d50b36c991bc0081dba61d4e4d50b36c9981df85e1434d52e42cdb266076e97850d4042cdb2647a81e027097850d3542cdb266076e97850d3a42cdb2d49981dba5e1434a50b36cb52640081dba5e14342cdb2d49981dc25e1434d52e42cdb2662f84dba61d434d50b36c9987a136e98750d3542cdb2661e84dba6ad434d50b36c998ba136e9ab50d3542cdb266076e97850d4042cdb3349981de47097850d3542cdb266076e97850d3a42cdb2640481dc2609434d50b36c991180081dc2609434d50b36c9981dba5e1434e90b36ccd266077ed7850d3542cdb2646f81df95e1434d50b36c991be076e97850d35494db2647881dba5e1434d50b36c9900e0a6e97850d3542cdb2646e829ba6ad434d50b36c991be0a7e17850d3542cdb2646f84e0a6e97850d3542cdb266077557850d3542cdb2646f829d25e1434d50b36c991be076e97850d3542ce436c9981dba5e1434d50b3c8db1e228829ba5e1434d50b39c9981dba5e1434d5253c8db1be076e9875393542ce736c9981df85e1434d50b36c991e23781dc25e1434d50b36c9981dba5e14e4d50b36c9920e076e9785393542cf536c9981dba5e14e4d50b36c991ea28829c25e1434d50b36c9981df85e1434d52536c991be076e9ab50d3542cf236c5881dba5e14e4d50b39c9911a076e98750d3542cf536c9981dba61d434d50b36c991ea076e98750d3542ce72644681dc261d434d50b39cdb26607709785393542ce736c9981dc25e1434e90b39cdb266077e17850d354ad0b36c9981dba6ad434d50b36c991e2077f9c25e1434d50b36c9981dba5e1434e90b36cb4266076e97856d3542cf536c9981dba5e1434e90b36c991ea28829ba61d434d50b36c9981dba6ad434d52536c991be076e97856d3542cf236c5181dba5e1434e90b39c9911a077097850d3542cf536c9981dc25e1434d50b36c991ea077097850d3542ce72644681dba5e1434d50b36c99256076e9ae50d3542ce736c9981dfb5e1434d50b39cdb266076e97850d35494db2646f81de35e1434d50b36c991e00081de35e1434d50b36c9981dba62d434d50b36c991e00081dca5e1434d50b36c99829ba5e1434d50b36c991e2076e97850d354ad0b36c9981dba5e1434d50b36ccc26400821ba5e1434d50b36c99829ba5e1434d50b36c99252077e17850d3542ce736c9981dba6ad434d50b39cdb266077097850d35494db2646f0020a7e17850d3542cdb266076e98750d35494db2646f0020a6e9ab50d3542cdb266076e97850d3542ce536c9981dba5e1434d50b3c8db1ea077497850d3542ce736c9982e0a6e97850d3542cdb266076e97850d3542cdb31c9981dba5e1434d50b3c8db252076e98750d3542ce736c9981dc25e1434d50b39cdb266076e97850d354b90b36c9981dba5e1434d50b36c991ea076e98d50d3542ce736c9981dba5e1434d50b39c9911a076e97850d3542cf336c9981dba5e1434d50b36c99116076e98d50d3542cdb2647a002077557850d3542cdb266076e97850d3542cdb3349981dba5e1434d50b36c991be076e97850d3542cdb2644681dba609434d50b39cdb266076e97850d35494db3349981dba609434d50b39c9911800829d25e1434d50b36c99829ba6b1434d50b36c991be0a7e57850d3542cdb2646f829ba5e1434d52536c991be0a7557850d3542cdb2646f829ba609434d50b36c991be0a6e9875393542cdb2646f0020a6e9875393542cdb2662f829ba61d434d50b36c9981dba5e1434e90b39cb426613829ba61d434d50b36c9981dc25e1434d50b39c991ea0a6e9a561d434d50b36c99829ba5e14e4d50b36c991de29829ba61d434d50b36c9981dba6ad434d52536c991e20a6e9af61d434d50b36c9981dba6ad434d52536c991620a6e9785393542cf536c99829ba5e14e4d50b36c9911a1e829ba61d434d50b36c9981dba5e1434e90b39c991ea0a6e98e61d434d50b36c99829ba61d434d50b36c992020a6e98750d354750b36c99829ba61d434d50b3d4db2660a6e98750d3542cdb26446829c261d434d50b36c991bc00829c261d434d50b36c99829c25e14e4d50b36c991bc00829c25e14e4d50b36c99829c25e1434e90b36c991bc00829c25e1434e90b36c998de0a7097850d3542cdb266076e9785393542ce72648384e0a7097850d3542cdb266076e98750d3542ce72647a829d77097850d3542cdb266076e98750d3542ce7264808a60a7097850d3542cdb266077e17850d35494db26478829fe7097850d3542cdb266076e97856d35494db26451829ba5e1434e90b3d4db2660a6e97850d3a42cdb2644687a0a7097850d3542cdb266076e9785393542ce72647a829ea7097850d3542cdb266076e9785393542ce726477829c25e1434d51d42cdb2660a7097850d3542cf536c99829c25e1434d50b36c9911a0a6e98750d3542ce736c99829c25e1434d50b39cdb26629829ba5e1434d50b36c99829ba5e1434d50b390db266076e97850d35494f236c78829ba5e1434d50b3d4db2660a6e97850d3542ce726446829c25e1434d50b39c991bc00829c25e1434d50b39c998a60a6e97850d3542ce72660a6e97850d3542ce739099829ba5e1434d51d42ce72660a6e97850d3542cf539c99829ba5e1434d50b39c991ea0a6e97850d3542cdb2649581de35e1434d52536c991e000829f95e1434d50b36c9981dba62d434d52536c991e000829ba6b1434d50b36c9981dba5e1434d52539cdb2660a6e97850d35494db264780020a6e97850d35494db266076e97850d35494db2647a81dba5e1434d50b39c991ea1e84dba5e1434d50b36c9981dba5e1434d5253ccdb266076e98d50d3542ce72647a0020a7557850d3542cdb266076e97850d3542ce7334998820a6e97850d3542cdb266076e97850d3542ce731c9981dba5e1434d52536c992520a6e98750d3542cdb2646f0020a6e98750d3542cdb2660a7097850d3542cdb2646f0020a7097850d3542cdb2660a6e97850d3542ce736c99829ba5e1434d50b39c991bc00829ba5e1434d50b39c998aa0a6e97850d3542cdb266076e97850d35494e536c99829ba5e1434d52e42cdb2660a6e97850d3542cdb2647a87a136e97850d3542ce72661e84dba5e1434d52536c998320a6e97850d3542cdb2660a6e97850d3542cdb26445829ba609434d50b36c9911800829ba609434d50b36c99829ba5e1434d50b36ccd2660a6e98750d3542cdb2640381dba61d4e4d50b36c9900e0a7097850d3542cdb2640381dc261d434d50b36c9900e07709785393542cdb2640381dc25e1434e90b36c9900e0a6e97850d3542ce72640381dba61d434d50b39c9900e077097850d3542ce72640381dba5e1434d52536ccc266076e9ab50d3542cdb3309981df85e1434d50b36ccc266076e97850d3542ce736c9981dba5e1434d50b36c991ba076e97850d3542ce626403821ba61d434d50b36c9900e087097850d3542cdb26403821ba5e1434d50b39c9900e0a821ba5e1434d50b36c99829ba5e1434d50b36c991bc00829ba5e1434d50b36c99821ba5e1434d50b36c991ba086e98750d3542cdb2646f002086e98750d3542cdb266087097850d3542cdb2646f002087097850d3542cdb266086e97850d3542ce736c99829ba5e1434d50b398991bc00829ba5e1434d50b39899821ba5e1434d50b36c9900e0a6e97950d3542cdb2640381dc25e5434d50b36c9900e076e9875113542cdb2640381dc25e1444d50b36c9900e076e97950d3542ce726403821ba5e5434d50b36c991be076e9795113542cdb2646f81dba5e5434d50b39cdb2660a6fd7850d3542cdb2646f0020a6fd7850d3542cdb266076e97950d3542cdb2640381dc26fd7850d3542cdb266076e97950d3542cdb2640681dc25e5434d50b36c991bc0081dc25e5434d50b36c9981dc25e1444d50b36c991bc0081dc25e1444d50b36c9981dba61d444d50b36c991bc0081dba61d444d50b36c9981dbf5e1434d50b39cdb2660a6e97950d3542cdb2646f0020a6e97950d3542cdb266076fd7850d3542cdb26403829bd5e1434d50b36c9900e076f58750d3542cdb2640381dbd5e14e4d50b36c9900e077097850d3642cdb2640381dbd5e1434d50b39c9900e086f57850d3542cdb2646f81dbd5e5434d50b36c991be076f5785113542cdb2646f81dba6154d4d50b36c991be076e98550d3542ce736c99829bd5e1434d50b36c991bc00829bd5e1434d50b36c9981dba615434d50b36c9900e07709bd5e1434d50b36c9981dc25e1434d50b36c991bc0081dc25e1434d50b36c9981dba5e1434d90b36c990e6077098550d3542cdb2646f002077098550d3542cdb26607709785353542cdb2646f002076e9ab52d3542cdb266076e9875353542cdb2646f002077e17852d3542cdb266076f57850d3542ce736c99829ba615434d50b36c991bc00829ba615434d50b36c9981dbd5e1434d50b36c9900e076e9ab50d3542cdb2640381df85e1434d50b36c9900e076e97850d35494db2640381dd25e1434d50b36c9900e0a6e97850d3542cdb2640381dba61d434d50b36c9900e077097850d3542cdb2640381dba5e1434d50b39c9900e076e98250d3542cdb2640381dba5e1434d51d42cdb266076e97850d3542cdb2647881dba5e1434d50b3d4db266076e97850d3542cdb2647981dba5e1434d51336c991be076e97850d3542ce6264468a2086e97850d3542cdb266076e97850d3544cdb2647884e086e97850d3542cdb266076e97850d3542ce626479821ba5e1434d51d42cdb266086e97850d3542cdb2646f821ba5e1434d50b3d4db266086e97850d3542cdb2644681dc65e1434d50b36ccc266086e97950d3542cdb26403002086e97950d3542cdb266076e9795113542cdb26403002076e9795113542cdb2663481dbf5e1434d50b36c9981dba601434d50b36c99162076e97950d3542cf536c9981dba5e5434d50b36c9911a0775dbf5e1434d50b36c9981dba5e5434d50b36c99156077197850d354750b36c9981dc65e1434d50b36c991be077f5bf5e1434d50b36c9981dba5e1544d50b36c990ea076e9785513542cf536c9981dba5e1544d50b36c9911a076e9785113542cf536c9981dba5e1444d50b36c9911a077a9bf5e1434d50b36c9981dba5e1444d50b36c990ee076fd7850d354750b36c9981dbf5e1434d50b36c991be076fd7850d3542cf536c9981dbf5e1434d50b36c9911a076e9a350d3542cdb33099821bd5e1434d50b36c9900c00821bd5e1434d50b36c9981dbd5e5434d50b36c9900c0081dbd5e5434d50b36c9981dbd5e1444d50b36c9900c0081dbd5e1444d50b36c9981dbd5e1434d90b36c9900c0081ddf5e14b4d50b36c998da076f57850d3542cdb266076e9a350d3542cdb2645481dba615434d50b3d4db266076e98550d3542cdb2644681dd76f57850d3542cdb266076e97852d3542cdb2645e81ddf5e1434d51d42cdb2660777d7850d3542cdb2646f81dfa6f57850d3542cdb266076e97852d3542cdb2645181dba5e14b4d50b3d4db266076e97852d3542cdb2644681dba5e14d4d50b3d4db266076e9785353542cdb2644681dea6f57850d3542cdb266076e97850d3642cdb2646781dbd5e1434d51d42cdb266076f57850d3542cdb2646f81dbd5e1434d50b3d4db266076f57850d3542cdb26446
  | 8, 1 => 0x6e9b165d785ad434d4386e9975e1434d50b264386e9785ad434d4db2643881d7850d3542cdb264616e9434d50b36cb0264385e1434d50b36c99108386e9785ad434d4db264355e1434d50b36c991883881d7850d3542cdb2645c6e9434d50b3e4db264385e1434d50b36c99194386e9975e1434d50b264356e9434d50b3ecdb264386e9434d50b3f4db2643881d7850d3542cdb264416e97850d3542cdb2643681d7850d3542cdb2646481d7850d3542cdb2645d6e9785ad434d4d52641d6e97850d3542cda264386e9b65e1434d51d36c386e97850d3542cdb264356e9785ad434d4db2402b7697850d3542cdb264386e9a15e1434d5292643884dba5e16250d3536c9981dba50d3542cfb3d44681dba50d3542cfe36c9981dbb5e1434d50b36c998a17850d3542cd52644281dab50d3542cdb2644281d7856d3542cdb2644281d7850d4042cdb2644281d7850d35494db2644281d7850d3542cf236c4281d7850d3542cdb264868a17850d3542cdb264426e97850d35474db1bc356e98750d3542cdb264357097850d3542cdb264356e97850d3542ce7264357e1975e1434d50b264386e9975e1434d52526438749785ad434d4db2643881dda5e1434d50b36c997cd7850d3542cdb264387417850d3542cdb26438749975e1434d50b264386e97850d3542cdb228386e9975e1434d51d1bc38709975e1434d50b264386e9985e1434d50b264386e9975e1434d50b228386e99b5e1434d50b2641d6e9975e1434d5112641a741975e1434d50b264386e99e50d3542cdb264386e9785ad554d4db26438709785ad434d4db264386e9875ad434d4db264386e9785ad4e4d4db264386e9785ad5b4d4db264386e9785ad434d4e7264386e9785c9434d4db264386e97d50d3542cdb264386e9785ad494d4db264386e9785ad434d4f5118386e9825ad434d4db264386e9b35e1434d50b36c2b6e97d5ad434d4db264386e9b15e1434d51136c1a6e97c5ad434d4db2643884dba5e1434d51036c9981dba5e14342cdb2cc9981dda5e1434d50b3d4466e97850d3542cdb27c996e97850d3d42cdb2402b81dba6457850d3542c466e97850d3542cdb27c2b001ba5e1434d51036c996e97850d3542cdb2442b6e9785293542cdb2402b81dce5e1434d50b36c996e97850d3542cdb2402b8adba5e1434d51136c9981dba5e1434d50b3bc4681dba5e1434cd0b36c9984dd25e16d50d3536c9981dba5e1434d50436c9984dba5e16a50d3536c996e9785b56a50d3536c99001ba5e16a50d3536c996e9785a5434d4db2641a84dba5e16d50d3536c998a1ba5e1434d50b360997e17850d3542cdb2641d6e97850d3542cdb360997e17850d3542cd52641d6e97850d35494d52641d81dba5e16e50d3536c6f6e97850d3542cd82641d6e97850d3542cd52641d81dbc5e1434d50b36c9981dba5e1434d50536c6f81dba5e1434d51d3686f81dba5e1434c90b36c9981dba6ad434d50b36c8a8a1f866d7850d3542c9981df85e1434d50b36c8a81dba5e1434d52536c8a8a1ba66d7850d354949981dba5e1434d50536c998a1ba6657850d3542c996e99b6657850d3542c998a1ba66d7850d3542c9981dba5e1434d50b36c8a81dba5e1434d50136c8a8a1ba66d7850d3542c8a8a1ba6ad434d50b264386e9ab56d3542cdb264387e1ab50d3542cdb264387e17856d3542cdb264387e17850d4042cdb264387e17850d35494db264386e9ab50d35494db264386e97856d35494db264386e97850d40494db264386e97850d35494f236c3881dd05e1434d50b36c996e9ad50d3542cdb264387557850d3542cdb264386e97c50d3542cdb264386e97850d3542ce6264386fd7850d3542cdb264386e98550d3542cdb264387fd7850d3542cdb264386e97850d354a4d7264386e97850d3544cdb2643877d7850d3542cdb264386e98050d3542cdb264387197850d3542cdb264386e9a350d3542cdb264386e9ab50d3542cdb264387e17850d3542cdb264386e97850d35494db264387e17850d3542ce136c9981dd35e1434d50b36c996e9ab50d3542c990e03181dba6ad434d50b264317497850d3542cdb2643881dd15e1434d50b36c996e97850d35444db2641a6e97850d3542cdb2643881dba5e1434d50b36c9981dcf5e1434d50b36c9981dc05e1434d50b36c9981dbe5e1434d50b36c99825ba5e1434d50b36c996e98750d35474db1bc386e9875393542cdb264386e97853935474db264387097850d35474db1bc387098750d3542cdb26438709785393542cdb264387097850d3a42cdb264387097850d35474db264386e97850d35474e71bc386e98750d3542ce7264387097850d3542ce7264386e97850d35474db1d86f6e98750d3542cdb264767097850d3542cdb264766e97850d3542ce7264766e98d50d3542cdb264386e97850d3542ce7264386e97850d3542cf51e8386e98250d3542cf5118386e97950d3542cdb264386f57850d3542cdb264386e98350d3542cdb264386e98850d3542cdb264386e97850d3542cdb264766e97850d35444db264726e97852535444db2641a6e97b50d3542cdb264386e97a50d3542cdb264386f97850d3542cdb264386e97850d3542cdc2643881dba635434d50b3d47a84dba5e1434d52636c9987a136e97850d354a4f581de05e1434d50b36c9981dc95e1434d50b36c9981dc75e1434d50b36c9984dba5e1434d5063d44681dba5e1434d5293249981dba5e1434d52e3184681dba609434d50b3d44681dba639434d50b36c5a81dba5e1554d50b3d44681dd25e1554d50b36c9981dba5e1584d50b36c3b839ba609434d50b36c9981dd25e1514d50b36c9981df15e1554d50b36c9981dcc609434d50b36c99899d25e1434d50b36c99871d25e1434d50b36c9981dba5e14342cdb2d89981dd25e1434d50b3d44681dd2609434d50b36c9981dba5e1554d5293349981dd45e1434d50b36c9981dba5e1434d50b3d47982dd25e1434d50b36c9981dba5e1434d52933403821ba5e1434d50b3d446821ba609434d50b36c99865ba5e1434d51336c9981dbd5e1434d50b3d44681dbd609434d50b36c99865df5e1434d50b36c9981dba5e5434d50b3d44681dba5e1444d50b3d44681dba609444d50b36c9982dc65e1434d50b36c9981dba5e14b4d50b3d44682dba68d434d50b36c9981dba6094b4d50b36c9981dd25e1434d50b36c998a1ff5e1434d50b36c9981dc15e1434d50b36c998a1ba5e1434d51d3546f8a1ba5e1434d50b3909981dba5e1434d52e3086f81dd25e1434d51d36c6f81dba5e1434d51d36c6f81dba5e1434d5293346f81dbf5e1434d50b36c9981dbd5e1434d50b36c9981dc261d434d51d36c6f8a1f86ad434d50b36c99002287e1ab50d3542c9981dc25e14e4d51d36c6f8a1f85e1435010b36c9981dba61d4e4d51d36c6f81dc261d4e4d50b36c998a1f85e15b4d50b36c99002287e17856d3542c9981dba6c1434d50b36c5881dba61d434d50b3d44681dba639434d50b36c8081df85e1434d51d36c6f81dfc5e1434d50b36c9981df861d434d50b36c9981df85e14e4d50b36c9981dba5e15f4d50b36c51835ba6ad434d50b36c9981dba6514e4d50b36c9981def5e14e4d50b36c9981e0561d434d50b36c9989dc25e1434d50b36c99871f85e1434d50b36c9981dba5e15b4d50b3d44682dba6ad434d50b36c9981dd25e14e4d50b36c9981dba6094e4d50b36c9982df85e1434d50b36c9981dba5e1524d50b36c77841ba61d434d50b36c9981dc55e14e4d50b36c9981dba6254e4d50b36c9981dcd61d434d50b36c99899f85e1434d50b36c99875c25e1434d50b36c9981dba5e14e4d51d36c7781dc25e1434d51d36c6f81dc261d434d50b36c9981dc25e14e4d50b36c9981dba61d4e4d50b36c9981dba5e14342cdb2d4998a1f85e1434d50b3d49981dc25e1434d50b3d44681dc2609434d50b36c99865f85e1434d50b36c998a1f85e1434d50b3c89981de35e1434d50b36c9981dca5e1434d50b36c99821ba5e1434d50b36c9981dba5e1434d51d36c7881dba5e1434d52b36c6f829f85e1434d50b36c99829ba6ad434d50b36c9981dd55e1434d50b36c9981dba5e1434d50b3d446829d25e1434d50b36c99829ba61d434d51d36c6f829ba61d4e4d50b36c99829ba5e14e4d51d36c99829ba61d434d51d36c99002286e9ab50d3549499829c25e1434d51d36c6f829c261d434d50b36c99829c25e14e4d50b36c99829c25e1434e90b36c99829c25e1434d51d36c998a1ba5e1434d5253c899829ba5e1434d51d39c6f829c25e1434d50b39c99829ba5e1434d51d39c990020a6e97850d35474e781dba5e1434d52b36c78829f95e1434d50b36c99829ba6b1434d50b36c99829ba5e1434d52536c9981dba5e1434d50b3d47a829d55e1434d50b36c99829ba5e1434d51d36c6f829ba61d434d50b36c99829c25e1434d50b36c99829ba5e1434d50b39c99829ba5e1434d50b3d446829ba609434d50b36c99829ba5e1434d51536c9981dba5e1434d51d39c03821ba5e1434d51d36c6f829ba5e1434d50b36c99821ba61d434d50b36c99821c25e1434d50b36c99829ba5e1434d50b3989981dbf5e1434d51d36c6f829bf5e1434d50b36c9981dc25e5434d50b36c9981dc25e1444d50b36c9981dba61d444d50b36c99829ba5e5434d50b36c9981dbd5e1434d51d36c6f829bd5e1434d50b36c9981dc25e1434d50b36c9981dc2615434d50b36c9981dba6ad4b4d50b36c9981df85e14b4d50b36c99829ba615434d50b36c99821ba5e5434d50b36c9981dba5e5444d50b36c99821bd5e1434d50b36c9981dbd5e5434d50b36c9981dbd5e1444d50b36c9981ddf5e14b4d50b36c99
  | 8, 2 => 0x6e97850d35440db265ba5e16a50d3536c998a1f86ad434d50b266287e17856d3542c998a1ba6ad434d5252660a6e97850d35474e7
  | 9, 0 => 0x81dba65d7850d3542cdb2643881dba5e16b50d3542cdb26438002076e97850d3542cdb2643881dba5e16b50d3542cdb2641d81dba6d97850d3542cdb2643881dba5e16b50d3542cdb2642b81dba6857850d3542cdb2643885e076e97850d3542cdb264318ae076e97850d3542cdb2641a81dba5e1434d50b3d4db2641681dba6417850d3542cf536c9981dba6d17850d3542cdb2647a002076e978589434d50b36c9981dba609434d50b3ecdb26446002077497850d3542cdb2646281dba5e1434d50b36c991182f866076e97850d3542cdb2642f002076e97850d3542cdb2642f81df76e97850d3542cdb264468a2076e97850d3542cdb264168b6076e97850d3542cdb26416002076e97850d3542cdb2641681dba5e16650d354750b36c9981dba6c97850d3542cdb26494002076e978599434d50b36c9981df85e1434d50b36cd526442002077e17850d3542cdb2644281dba5e1434d50b36c991bc3582a076e97850d3542cdb26435002076e97850d3542cdb26435829ba5e1434d50b36c991bc350020a6e97850d3542cdb2643581dba6e17850d3542cdb2646f8ea076e97850d3542cdb26403002076e9a25e1434d50b36c9981dba66d7850d3542cdb26438002076e99b5e1434d50b36c9981dba5e1434d50b36c990e01d002076e97850d3542cdb2641d85e076e97850d3542cdb2643881dba65d7850d3542cdb2643181dba6717850d3542cdb2643881dba65d7850d3542cdb2641a81dba5e16d50d3542cdb26438002076e9785b5434d50b36c9981dba5e1434d50b36c990e02b002076e97850d3542cdb2642b88e076e97850d3542cdb2643881dba5e16b50d3542cdb2641a81dba5e16f50d3542cdb2643881dba5e16b50d3542cdb2643181dba5e17350d3542cdb2643881dba6c57850d3542cdb2641a81dba5e1434d51d42cdb2643881dba5e1434d50b36c991bc3881dba5e1434d50b3d4db2643881dba5e1434d50b36c9911838882076e97850d3542cdb2642b81dba5e1434d50b36cd92642b87a136e97850d3542cdb2642b87a076e9785293542cdb2642b002077697850d3542cf536c9984e076e97850d3542cdb2889987a076e97850d3542cdb2641888e1e6e97850d3542cdb2642b81dba5e1434d52942cdb2642b81dba5e1434d50b36cc12642b87a076e97850d3542cdb2642b81dba5e1434d50b36c992402b81dba5e1434d51d42cdb2642b81dba5e1434d50b36c991bc2b81dba5e1434d50b3d4db2642b81dba5e1434d50b36c991182b002076e9785293542cdb2642b0000081dda5e1434d50b36c9981dba5e1434d50b374db2642b002076e97850d3542cdb2889981dba5e1434d50b36c990ac18002076e97850d3542cdb2641881dba5e1434d50b36ca62642b81df66e97850d3542cdb2644681dba5e1434d50b428db2644681dba5e16d50d35418db2641a81df56e98250d3542cdb2644600207749785b5434d50b36c9981dba6857850d3542cdb3349981dba6857850d3542cdb2640381df56e97850d3542cf536c9981df56e97850d3542cdb2644681dba5e16d50d3542cdb2641a81dba6857850d3542cf536c9981dba6857850d3542cdb2644681dba5e1715b5434d50b36c99002076e9785c5434d50b36c9981dba5e16d50d3542cdb2646a002076e97850d3542cdb2646a81dba5e16d50d354750b36c9981dba5e16d50d3542cdb2646f81dba5e16d50d3542cf536c9981dba5e16d50d3542cdb264468aa076e97850d3542cdb2641d81dba5e1434d50b36c992501d8a2176e97850d3542cdb2641d8a2076e97850d3542cdb274998a2076e97850d3542cdb264178a2076e97850d3542cdb2641d81dba5e1434d50b36cd52641d81dba5e1434d51d42cdb2641d81dba5e1434d50b36c991bc1d81dba5e1434d50b3d4db2641d81dba5e1434d50b36c991181d81dba5e1434d50b384db2641d81dba5e1434d50b36c9d2641d002076e97850d3542cdb2749981dba5e1434d50b36c9907417002076e97850d3542cdb2641781dba6dd7850d3542cdb2646f81dba6d97850d3542cda2646f81dba5e1434d50b36cda2646f002076e97850d3542cda2646f81dba66d7850d3542cd52643181dc26d97850d3542cdb2646f002077e19b5e1434d50b36c9981dba6d97850d3542ce736c99829ba6d97850d3542cdb2646f0020a6e9b65e1434d50b36c9981dba6d97850d3542cdb2640381dba6d97850d354750b36c9981dba6d97850d3542cdb2646f81dba66d7850d3542cdb2643181dba6759b5e1434d50b36c99002076e99d5e1434d50b36c9981dba66d7850d3542cdb2648a002076e99b5e1434d50b36c8a002076e97850d3542cdb2648a0000081dba5e1434d50b36c8a81dba66d7850d354750b36c9981dba66d7850d3542cdb2646f81dba66d7850d3542cf536c9981dba66d7850d3542cdb2644681dba5e1434d50b36c992503881dba5e1434d50b36c990e031002076e97850d3542cdb264318a2076e97850d3542cd52643881dba6ad434d50b36cd526438002076e9ab50d3542cdb2643881df85e1434d50b36cd526438002077e17850d3542cdb2643881dba5e1434d52536cd52643881dba5e1434d50b3c8db26438002076e97850d35494db2643881dba5e1434d50b384db26438002076e97850d3542ce136c9981dba5e1434d50b36cd72643881dba5e1434d50b36c992443887a136e97850d3542cdb2643881dba5e1434d50b36c990e01a002076e97850d3542cdb2641a87a076e97850d3542cdb2403881dba5e1434f50b36c9924038002077497850d3542cdb2643881dba5e1434d51942cdb2643881dba5e1434d50b3d0db2643881dba5e1434d50b36ca626438002076e97850d3542cdb29899882076e97850d3542cdb2643881dba5e1434d51842cdb2643881dba5e1434d50b36cc22643881dba5e1434d5204750b36c9981dba5e1434d51d42cdb2642281dba5e1434d50b36c990e022002076e97850d3542cdb2642282a076e97850d3542cdb26438829ba5e1434d50b36c991bc380020a6e97850d3542cdb2643881dba65d7850d3542cdb2640381dba61d434d50b36c991bc38002076e98750d3542cdb2643881dc25e1434d50b36c991bc38002077097850d3542cdb2643881dba5e1434d50b39cdb2643881dba5e1434d50b39c991bc38002076e97850d3542ce72643881dba5e1434d50b36c991d86f81dba5e1434d50b36c991d838002076e97850d3542cdb2647681dba5e1434d50b36c991bc0d8aa076e97850d3542cdb2643881dba5e1434d50b3c0db2643881dba5e1434d52e42cdb2643881dba5e1434d50b36c991e83881dba5e1434d52942cf52643884e076e97850d354a4db2643881dba5e1434d50b3e0f536c9981dba5e1434d52942cdb2643481dba5e1434d50b36c990e034002076e97850d3542cdb2643482e076e97850d3542cdb2643881dba5e16b50d3542cdb2640381dba609434d50b36c9911838002076e98250d3542cdb2643881dba5e1434d50b36ccd2643881dba5e1434d50b36c990e00381dba5e1434d50b36c991404681dba5e1434d50b36c9914038002076e97850d3542cdb2645081dba5e1434d50b36cc12640f81dba5e1434d50b36cd5264388a2076e97850d3542ce12643881dba5e1434d50b36c9912c388a2076e97850d3542ce136c990022885dba5e1434d50b36c9981dba5e16f50d3542cdb2646f84e076e97850d3542ce136c9981dba6e57850d3542cdb2644681dba5e1434d51d42ce136c9981dba5e1434d50b384db2646f81dba5e1434d50b3e0e136c9981dba5e1434d50b384db2644b002076e97850d3542cdb2644b81dba5e1434d50b3d4e136c9981dba5e1434d50b384db2644681dba5e1434d50b354990e03181dba5e1434d50b384db2643181dba5e1434d50b384990e031002076e97850d3542ce1264318a2076e97850d3542cdb2643881dba5e1434d50b36ca32643881dba5e1434d50b36cd526431002076e97850d3542cd52643184e076e97850d3542cdb2643181dba5e1434d50b36c992403181dba5e1434d51d42cdb2643181dba5e1434d50b36c991bc3181dba5e1434d50b3d4db2643181dba5e1434d50b36c99118318a2076e97850d3542cdb2643181dba5e1434d50b36ca326431002076e97850d3542cdb28c9981dba5e1434d50b36c990c40f81dba5e1434d50b36c992403881dba5e1434d52042cdb2643881dba5e1434d50b36c991c83881dba5e1434d50b3e0db2643881dba5e1434d50b36c991343884e076e97850d35444db2643881dba5e1434d51142cdb2989981dba5e1434d50b384db2989981dba5e1434d50b36ca62643184e076e97850d3542cdb2989981dba69d7850d3542cdb264468a2076e97850d3542cdb2989981dba5e17350d3542cdb2646f81dba5e1434d52942cdb2989981dba5e1434d51142cdb2644681dba5e1434d52042cdb29899002076e97850d354810b36c9981dba5e1434d50b36ca626472002076e97850d3542cdb2647281dba5e1434d50b3e0db29899002076e97850d3542cf836c9981dba5e1434d50b36ca62644d002076e97850d3542cdb2644d87a076e97850d3542cdb298990022b84dba5e1434d50b36c9981dba6717850d3542cdb2644681dba5e1434d51d42cdb2989981dba5e1434d50b36ca62646f81dba5e1434d50b3d4db2989981dba5e1434d50b36ca62644681dba5e1434d50636c990e01a81dba5e1434d52936c990e01a81dba5e1434d51142cdb2641a81dba5e1434d51136c990e01a002076e97850d35444db2641a81dba5e1434d50b384db2641a81dba5e1434d50b36c990c41a81dba5e1434d50b36ca62641a81dba5e1434d50b36c990841a84e076e97850d3542cdb2643881dba5e1494d50b36c990e01a002076e97c50d3542cdb2643881dba5e1434d50b378db2643881dba5e1434d50b36c990e00f81dba5e1434d50b36c9e2643881dba5e1434d50b36c990e00d81dba5e1434d50b418db2641a002076e97850d35418db2641a8a2076e97850d3542cdb2641a81dba5e1434d50b36cd52641a81dba5e1434d52942cdb2641a002076e97850d354a4db2641a81dba5e1434d50b36cc12641a87a076e97850d3542cdb2641a81dba5e1434d50b36c992401a81dba5e1434d51d42cdb2641a81dba5e1434d50b36c991bc1a81dba5e1434d50b3d4db2641a81dba5e1434d50b36c991181a84e076e97850d3542cdb2641a002076e9785253542cdb2641a0000081dd05e1434d50b36c9981dba5e1434d50b378db2641a002076e97850d3542cdb2fc9981dba5e1434d50b36c990680f002076e97850d3542cdb2640f81dba5e1434d50b36c9e2641a002076e97850d3542cdb2789981dba5e1434d50b36c990680d002076e97850d3542cdb2640d81dba5e1434d50b3d4f136c99002076e97850d3542cf136c998f2076e97850d3542cf536c9981dba5e1434d52942cdb264958aa076e97850d354b90b36c998aa076e97850d3542cdb2647a81dba5e1434d52442cdb2647a81dba5e1434d52e42cdb2647a84e076e97850d3542cf336c9981dba635434d52942cdb2647a002076e97855d3542cf536c9981dba5e1434d52942ce72647a81dba5e1434d52942cdb2647a87a076e97850d3542cdb2647a86a076e97850d3542cdb2647a002076e97850d3542cf336c9981dba5e1434d50b36c9924445002076e98d50d3542cdb2647a0000081dd55e1434d50b36c99002076e97850d3542cdb2646f84e076e97850d3542cdb2647a002076e97850d3542ce736c9981dba5e1434d50b3d4db2647a87a13829ba5e1434d50b36c9900000829ba5e1434d50b36c998aa1e84dba5e1434d50b36c9984e076e97850d354a4db2647a8821e84dba5e1434d50b36c9981dba5e1434d52942cf52647a87a136e97850d3542cf536c990021e84dba5e1434d52936c9981dba5e1434d50b36c992444681dba5e1434d52d42cf536c9984e076e97850d3542cdb2644581dba5e1434d50b36c9911845002076e97850d3542cdb2644581dba5e1434d51442cdb26446002076e97850d3542cdb3249981dba5e1434d50b420db2644687a136e97850d3542cdb2644681dba5e1434d50b36cc62644681dba5e1434d52942cf52644684e076e98250d3542cdb2644681dd25e1434d50b418db2644681dba6998250d3542cdb2644681dba5e1554d50b36cc12643b81dba609434d52942cdb2644681dba609434d50b36c992404681dba6398250d3542cdb2644681dba609434d50b36c991684681dba609434d50b3d4db26446002076e98250d3542cf536c99002076e98250d3542cdb264460020775dd25e1434d50b36c99002076e98250d3542cdb2645a002076e9785553542cf536c99002076e9785553542cdb26446002077b1d25e1434d50b36c99002076e9785553542cdb2643b002077497850d3542cf536c99002077497850d3542cdb2644686e076e97850d3542cdb2644681dba5e1434d50b41cdb26446866136e97850d3542cdb2644681dba5e1434d52942cdb2644682e076e97850d3542cdb3349981dba609434d51542cdb26446002076e9785553542cdb3349984e076e97850d3542cdb3349981dba5e1434d51942cdb2644681dba5e1434d52942cdb3349981dba5e1434d51542cdb2644687e076e97850d3542cdb33499002076e97850d354b10b36c9981dba5e1434d52842cdb26479002076e97850d3542cdb26479002076e97850d354750b36c9981dba5e1434d51542cdb2647a002076e97850d3542cdb2649487a076e97850d3542cdb334990021e82dba5e1434d50b36c9981dba5e1434d51c42cdb2644681dba5e1434d50b36ccd2644682e076e97850d3542cdb2640381dba5e1434d50b36c991100381dba609434d50b36c9911803002076e98250d3542cdb2640381dba5e1434d50b36ccd2640381dba5e1434d51342cdb26446821ba5e1434d50b36c9911803002086e97850d3542cdb2644681dbd5e1434d50b36c9911803002076f57850d3542cdb2644681dba5e5434d50b36c9911803002076e97950d3542cdb2644681dba5e1444d50b36c9911803002076e9785113542cdb2644681dba5e1434d90b36c9911803002076e97852d3542cdb2644681dba5e1434d51d4690b36c99002076e97850d354690b36c998f2076e97850d354750b36c998a2076e97850d3542cdb26495882076e97850d354b90b36c998f2076e97850d354b90b36c990023c81dba5e1434d50b36c998aa076e97850d3542cdb26495002076e97850d3542cdb264958aa076e97850d3542cdb2649481dba5e1434d50b424db264948b6076e97850d3542cdb264948a2076e97850d3546d0b36c9981dba5e1434d51d42cdb264468a2076e97850d3542cdb2649481dba5e1434d51d42cdb2649481dba5e1434d51b42cdb26494002076e97850d3546d0b36c9981dba5e1434d50b36c992506e81dba5e1434d50b3d0db26494002076e97850d3542cdb26446882076e97850d3542cf536c9981dba5e1434d52942cdb264948aa076e97850d354750b36c998a2076e97850d3542cdb2647a002076e97850d354b90b36c9981dba5e1434d50b3d4db33499002076e97850d3542cdb3349981dba5e1434d52e4750b36c9981dba5e1434d51d42cdb2647a81dba5e1434d52e42cf536c9981dba5e1434d50b3d4db2649487a136e97850d354750b36c998a21e84dba5e1434d50b36c99882076e97850d3542cdb2644681dba5e1434d50b424db2644681dba5e1434d52e42cdb2644681dba5e1434d50b36c99250468a2076e97850d3542cdb3349981dba609434d51d42cdb26446002077497850d354750b36c9981dba5e1434d51d42cdb3349981dba5e1434d50b36c992506f81dba5e1434d52b4750b36c998a2076e97850d3542cdb2646e81dba5e1434d50b36c991bc6e002076e97850d3542cdb2646e81dba5e1434d50b390db2646f002076e97850d3542ce436c9981dba5e1434d50b36cc22646f8aa076e97850d3542cdb2646f81dba5e1434d50b36cd72646f81dba5e1434d52e42cdb2646f87a136e97850d3542cdb2646f84e076e97850d354a4db2646f81dba5e1434d50b3d0db2646f81dba609434d50b36c991bc46002077497850d3542cdb2646f81dba5e1434d50b36ccd2646f81dba5e1434d50b36c991e846002076e97850d3542cdb264038de077097850d3542cdb2646f81dba6ad434d50b36cd52645881dba61d434d50b3d4db2646f81dba61d434d50b36c991bc4681dd77097850d3542cdb2646f81dba61d434d50b36c992006f8a2077097850d3542cdb2646f81dc25e1434d50b36cd52646f81dfe7097850d3542cdb2646f81dba5e15b4d50b36cd52645181dba5e1434e90b3d4db2646f81dba5e1434e90b36c991bc4681dba5e14e4d50b3d4db2646f81dba5e14e4d50b36c991bc4681dea7097850d3542cdb2646f81dba5e14e4d50b36c991dc6f81dc25e1434d51d42cdb2646f81dc25e1434d50b3d4db2646f81dc25e1434d50b36c991bc46002077098750d3542cdb2646f0000081dc261d434d50b36c9900207709785393542cdb2646f0000081dc25e14e4d50b36c99002076e9875393542cdb2646f0000081dba61d4e4d50b36c990023781dc25e1434d50b36c99002076e9ab50d3542cdb26458002076e98750d3542cf536c99002076e98750d3542cdb264460020775dc25e1434d50b36c99002076e98750d3542cdb26480002077e17850d354750b36c99002077e17850d3542cdb2646f002077f9c25e1434d50b36c99002076e97856d3542cdb26451002076e97856d3542cf536c99002076e97856d3542cdb26446002076e9785393542cf536c99002076e9785393542cdb26446002077a9c25e1434d50b36c99002076e9785393542cdb26477002077097850d354750b36c99002077097850d3542cdb2646f002077097850d3542cf536c99002077097850d3542cdb264468a6076e97850d3542cdb2646f81dba5e1434d50b36cd62646f8a20a6e97850d3542cdb2646f829ba5e1434d50b36cd52646f81dba5e1434d50b3d4db2646f81dba5e1434d50b36c991e86f81dba5e1434d50b39c991bc4682a076e97850d3542ce736c9981dba61d434d50b39cdb2646f002076e98750d3542ce736c9981dc25e1434d50b39cdb2646f002077097850d3542ce736c998a6076e97850d3542ce736c99002076e97850d354ad0b36c9981dba5e1434d52542cdb26478002076e97850d3542cdb264788a2076e97850d3542ce736c9900228829ba5e1434d50b36c9981dba5e1434d50b3c8db2646f002076e97850d35494db2646f84e076e97850d3542ce736c9981dba5e1434d52542cdb2644681dba5e1434d51d42ce736c9981dba5e1434d50b39cdb2646f002076e97850d3542cf536c9981dba5e1434d50b39cdb2647a002076e97850d3542cdb2647a81dba5e1434d50b3d4e736c9981dba5e1434d50b39cdb26446002076e97850d3542ce7264468a60a6e97850d3542cdb2646f829ba5e1434d50b36cd62646f84e0a6e97850d3542cdb2646f81dba5e1434d50b39c991e86f829ba5e1434d51d42cdb2646f829ba5e1434d50b3d4db2646f829ba5e1434d50b36c991bc460020a6e98750d3542cdb2646f00000829ba61d434d50b36c990020a7097850d3542cdb2646f00000829c25e1434d50b36c99829ba5e1434d50b39cdb2646f0020a6e97850d3542ce736c990020a6e97850d3542ce72646f00000829ba5e1434d50b39c9900229829ba5e1434d50b36c99002076e97850d35494db2647800213829ba5e1434d50b36c99002076e97850d3542ce72647a0020a6e97850d354750b36c990020a6e97850d3542cdb2646f0020a6e97850d3542cf536c990020a6e97850d3542cdb2644682a076e97850d3542cdb26403829ba5e1434d50b36c991bc030020a6e97850d3542cdb2640381dba5e1434d50b36c991b40381dba61d434d50b36c991bc03002076e98750d3542cdb2640381dc25e1434d50b36c991bc03002077097850d3542cdb2640381dba5e1434d50b39cdb2640381dba5e1434d50b39c991bc03002076e97850d3542ce72640381dba5e1434d50b398db2646f821ba5e1434d50b36c991bc03002086e97850d3542cdb2646f81dba5e5434d50b36c991bc03002076fd7850d3542cdb2646f81dbd5e1434d50b36c991bc03002076f57850d3542cdb2646f8a2076e97850d3542cdb2640381dba5e1434d50b36cd52640384e076e97850d3542cdb2640381dba5e1434d50b36c992400381dba5e1434d51d42cdb2640381dba5e1434d50b36c991bc0381dba5e1434d50b3d4db2640381dba5e1434d50b36c9911803822076e97850d3542cdb26403002076e97850d3542cdb33099002086e97850d3542cdb2640300000821ba5e1434d50b36c99002076e97950d3542cdb264030000081dbf5e1434d50b36c99002076f57850d3542cdb264030000081dbd5e1434d50b36c99
  | 9, 1 => 0x6e9975e16b50d3542c990e1ba65d785ad434d4db26438001ba65d785ad434d4990e1ba65d7850d3542cdb264386e9785ad434d50b36c990e2076e97850d3542cdb26438001ba5e1434d50b36c990e2076e9785ad434d4db2641d6e9b65e1434d50b36c990e2076e9785ad434d4db2642b6e9a15e1434d50b36c990e2076e978589434d50b36c9981dba50d3542cfb36c9911a077497850d3542cdb26462002075e1434d50b36c9918a076e97850d3542cdb2642f81dba5e1434d50b36c9905a076e978599434d50b36c9981d7850d3542cdb3549910a077e17850d3542cdb26442002075e1434d50b36c9910a076e97850d3542cdb264356e97850d3542cdb2646f0d60a6e97850d3542cdb26435001ba5e1434d50b36c990d6076e9a25e1434d50b36c998a1ba65d7850d3542c990e1ba65d7850d3542cd52643881dba66d7850d3542cdb266076e97850d3542cdb2641d85dba5e1434d50b36c990e2076e9975e1434d50b2643184dba5e16b50d3536c990e1ba6c57850d3542cdb2403881dba5e16d50d3542cdb266076e97850d3542cdb2642b88dba5e1434d50b36c990e2076e9785ad434d4db2641a6e99c5e1434d50b36c990e2076e9975e1434d50b2641a6e9975e1434d50b3d4990e1ba65d7850d3542c99118386e99b5e1434d50b36c990e1ba5e1434d50b36c990e01d6e9975e1434d50b384990e1ba65d7850d3542c990e0316e9975e1434d51d42c990e1ba65d7850d3542c991bc386e99b65d7850d3542c990e1ba65d7850d3542c990e01d6e9975e1434d50b298990e1ba65d7850d3542c990e01a6e9785cd434d50b36c990e2076e9b15e1434d50b36c1a6e9785ad434d52936c990e1ba6c57850d3542cdb118386e9785bd434d50b36c990e2076e9785ad434d4db264316e9785ad434d51d36c990e1ba5e16b50d3536c991bc386e9785b5434d50b36c990e1ba5e1434d50b36c990e02b6e9785ad434d51136c990e1ba5e16b50d3536c990e01a6e9785ad434d4f536c990e1ba5e16b50d3536c99118386e9785b56b50d3536c990e1ba6c57850d3542cdb0e02b6e9785ad434d4e136c990e1ba5e16b50d3536c990e0316e9785ad434d4db298990e1ba6c57850d3542cdb0e01a879ba5e1434d50b36c900ae077697850d3542cf536c996e97850d3542cdb264900ac006e97850d3542cdb2402b84dba5e1434d50b36c990ae076e9785293542cdb2642b002077697850d3542cdb266076e97850d3542cdb2889981dba5e1434d50b36c99062236e97850d3542cdb2642b81df56e97850d3542cf511a07749785b5434d50b36c9984dba5e16d50d3542cdb2640084dba5e16d50d3536c9981dba5e16d50d3536c9906a076e9785c5434d50b36c9981dba5e1434d50b36c991aa286e97850d3542cd52641d6e97850d3542cdb35499074006e97850d3542cd52641d85dba5e1434d50b36c99076076e97850d3542cdb2749981dba5e1434d50b36c9905e076e97850d3542cda2646f81dba6d97850d35474db1be077e19b5e1434d50b36c99829ba6d97850d3542cdb266286e99b5e1434d50b36c99002286e99b5e1434d50b266076e99b5e1434d50b2643181dba6757850d3542cdb266076e99b5e1434d50b36c8a81dba5e1434d50b36c992280081dba5e1434d50b36c8a81dba5e1434d50b36c990c5ba5e1434d50b36c99250386e97850d3542cdb264380c6286e97850d3542cd52643881dba6ad434d50b36c990e2077e17850d3542cdb2643881dba5e1434d52536c990e2076e97850d3542ce136c996e9ab50d3542cdb354990e0006e9ab50d3542cdb264387e17850d3542cdb354990e0007e17850d3542cdb264386e97850d35494db354990e1ba5e1434d50b3c8db26438001ba5e1434d52536c990e1ba5e1434d50b384db2643881dba5e1434d50b36c99069ba5e1434d50b36cd7264386e97850d3542cdb264910e1ba5e1434d50b36c990e01a879ba5e1434d50b36c900e2077497850d3542cdb2643881dba5e1434d50b36ca6265ba5e1434f50b36c9924038001d25e1434d50b36c990e1ba5e1434d51942cdb264386e97850d3542cf436c990e1ba5e1434d50b36ca626438881ba5e1434d50b36c990e1ba5e1434d51842cdb2643881dba5e1434d50b36c9908a076e97850d35474db1bc38829ba5e1434d50b36c990e2076e9975e1434d50b2640381dba61d434d50b36c990e2077097850d3542cdb2643881dba5e1434d50b39c990e2076e97850d3542cdb264768a9ba5e1434d50b36c990e1ba5e1434d50b3c0db2643884dba5e1434d52936c990e2076e97850d3542cdb2643481dba5e1434d50b3d4460e20b6e97850d3542cdb2643881dba5e16b50d3536c9900e076e98250d3542cdb2643881dba5e1434d50b36c99141ba5e1434d50b36cd5264388a1ba5e1434d50b384990e22885dba5e1434d50b36c9981dba5e16f50d3536c991be076e97850d3542cdb2644b6e97850d3542cd5264380c6076e97850d3542ce1264318a1ba5e1434d50b36c990e2076e97850d3542cd5264318a1ba5e1434d50b36c990c6076e97850d3542cdb28c996e97850d3542cdb264900e2136e97850d35444db2643884dba5e1434d50b36ca6266076e97850d354810b36c9981dba5e1434d50b36c991ca076e97850d3542cf836c9981dba5e1434d50b36c991362b84dba5e1434d50b36c9981dba6717850d3542c99119ba5e1434d50636c990e01a81dba5e1434d51136c9906a136e97850d3542cdb2643881dba5f1434d50b36c990e2076e97850d35418db2641a81dba5e1434d52936c9906a136e97850d3542cdb2641a81dba5e1494d50b36c990680081dd05e1434d50b36c9981dba5e1434d50b36cbf266076e97850d3542cdb2640f81dba5e1434d50b36c9e266076e97850d3542cdb2640d6e97850d3542cdb308990e1ba5e1434d50b36c990e0226e97850d35474db2646f0e0006e97850d35474db1bc386e98750d3542cdb2646f0e0006e98750d3542cdb264387097850d3542cdb2646f0e0007097850d3542cdb264386e97850d3542ce736c990e1ba5e1434d50b39c991bc38001ba5e1434d50b39c990e1ba5e1434d50b36c991d86f6e97850d3542cdb264760e0006e97850d3542cdb264766e97850d354b90b36c990e1ba5e1434d50b36c991e8386e97850d354a50b3d4990e1ba5e1434d50b36c990e0346e97850d3542cf536c460e1ba5e1434d50b3d49911838001ba5e1434d50b3d4460e1ba609434d50b36c9911838001ba609434d50b36c990e1ba5e1434d50b36ccd264386e97850d3542cdb2643800dba5e1434d50b36c99140386e97850d3542cdb2644b0e1ba5e1434d50b384db264316e97850d3542ce1264380c5ba5e1434d50b36ca3264386e97850d354810b36c990e1ba5e1434d50b36c991c8386e97850d3542cf836c990e1ba5e1434d50b36c99134386e97850d354450b36ca6265ba5e1434d52936c990e01a6e97850d354450b36c99069ba5e1434d51136c990e01a001ba5e1434d51136c99069ba5e1494d50b36c990e01a001ba5f1434d50b36c990e1ba5e1434d50b378db264386e97850d3542cdb2643803dba5e1434d50b36c9e264386e97850d3542cdb26438036076e97850d3542cf136c9981dba5e1434d52e42cdb1ea076e97855d3542cf536c9981dba5e1434d50b3ccdb266076e98d50d3542cdb2647a002077557850d3542cdb266076e97850d3542cdb2646f81dba5e1434d50b39cdb266076e97850d3542cf536c7a0020a6e97850d3542cdb266076e97850d354a50b3d47a81dba5e1434d50b3d4991e80081dba5e1434d50b3d47a87a136e97850d354a4db266076e97850d3542cdb2644581dba5e1434d50b36cc9266076e97850d354a50b3d446879ba5e1434d50b36c9011a1381dba5e1434d50b3d44684dba5e1434d50636c9911a076e97850d354b90b3d44681dba5e1434d50b3d4c611a076e98250d3542cf526446002076e98250d3542cf511a076e98250d3542cf536c9981dba609434d50b36c9911a0775dd25e1434d50b36c9981dba609434d50b36c9916a076e9785553542cf536c9981dba5e1554d50b36c9911a077b1d25e1434d50b36c9981dba5e1554d50b36c990ee077497850d3542cf536c9981dd25e1434d50b36c9911a076e97850d354550b3d44681dba5e1554d50b36ccd266076e97850d354a50b3349981dba5e1434d52c42cdb266076e97850d3542cdb2647981dba5e1434d51d42cdb266076e97850d3542cdb2649487a0b6e97850d3542cdb266076e97850d3542cf42644681dba5e1434d50b3d44600e076e98250d3542cdb2640381dba5e1434d51536c9900e086e97850d3542cdb2644681dbd5e1434d50b36c9911a076e97950d3542cdb2644681dba5e1444d50b36c9911a076e97852d3542cdb2644681dba5e1434d51a42cdb2663c81dba5e1434d50b36c9981dba5e1434d50b36c992562d81dba5e1434d50b36c9481dba5e1434d51b42cdb266076e97850d3542cdb2644681dba5e1434d52e42cdb266076e97850d3542cdb3349981dba5e1434d51d42cdb1ea076e97850d3542cf536c9481dba5e1434d51d42cf511a077497850d354750b36c9981dba5e1434d50b36c991ba076e97850d3542ce436c998a2076e97850d35474db1be286e97850d3542cd52646f81dba5e1434d52e474db1be076e97850d35474db3086f81dba5e1434d51d3d4db1be076e97850d35474db1bc4681dba5e1434d50b3d46f11a077497850d3542cdb2646f81dba5e1434d51536c991be076e97850d3542cdb2640381dba61d434d51d36c991be077097850d35474db2646f002077097850d35474db1be077098750d3542cdb2646f002077098750d3542cdb26607709785393542cdb2646f00207709785393542cdb266076e9875393542cdb2646f002076e9875393542cdb2663781dc25e1434d50b36c9981dba6ad434d50b36c99162076e98750d3542cf536c9981dba61d434d50b36c9911a0775dc25e1434d50b36c9981dba61d434d50b36c99202077e17850d354750b36c9981df85e1434d50b36c991be077f9c25e1434d50b36c9981dba5e15b4d50b36c99146076e97856d3542cf536c9981dba5e15b4d50b36c9911a076e9785393542cf536c9981dba5e14e4d50b36c9911a077a9c25e1434d50b36c9981dba5e14e4d50b36c991de077097850d354750b36c99002287e17850d3542cdb266077097850d3542cdb2646f81dc25e1434d50b3d4db266077097850d3542cdb2644681dba5e1434d51d39cdb1be076e98750d3542ce736c9981dc25e1434d50b39cdb266076e97850d354ad0b36c9981dba5e1434d50b36c991e228829ba5e1434d50b36c9981dba5e1434d52536c991be076e97850d3542cf536c9981dba5e1434d50b36c991ea076e97850d3542ce726446829ba5e1434d51d36c991bc00829ba5e1434d51d36c6f829ba61d434d50b36c991bc00829ba61d434d50b36c99829c25e1434d50b36c991bc00829c25e1434d50b36c99829ba5e1434d50b39cdb2660a6e97850d3542ce72646f0020a6e97850d3542ce726629829ba5e1434d50b36c9981dba5e1434d52536c991e213829ba5e1434d50b36c9981dba5e1434d50b39c991ea0a6e97850d354750b36c99829ba5e1434d50b36c991be0a6e97850d3542cf536c99829ba5e1434d50b36c9911a076e97850d35474db1bc03829ba5e1434d50b36c9900e076e98750d3542cdb2640381dc25e1434d50b36c9900e076e97850d3542ce726403821ba5e1434d50b36c991be076fd7850d3542cdb2646f81dbd5e1434d50b36c991be076e97850d3542cdb33099821ba5e1434d50b36c9900c00821ba5e1434d50b36c9981dba5e5434d50b36c9900c0081dbf5e1434d50b36c9981dbd5e1434d50b36c9900c0081dbd5e1434d50b36c99
  | 9, 2 => 0x6e9975e16b50d35264386e97850d3542cdb2643881d7850d3542cdb2646281d7850d3542cdb264426e97850d3542cdb264356e97850d3542cdb2402b81dda5e1434d50b36c9984dba5e16d50d3536c996e97850d3542cd52641d8a1ba66d7850d3542c9981dba5e1434d50b36c8a6e9ab50d3542cdb264387e17850d3542cdb264386e97850d35494db264387497850d3542cdb2643881dd05e1434d50b36c996e97850d35474db1bc386e98750d3542cdb264387097850d3542cdb264386e97850d3542ce7264386e97850d3542cdb264766e97850d3542cf5118386e98250d3542cdb264386e97850d35444db2641a6e97c50d3542cdb2643881dd55e1434d50b36c99829ba5e1434d50b36c9981dba5e1434d50b3d47a81dba609434d50b3d44681dc25e1434d51d36c6f81dc261d434d50b36c9981dc25e14e4d50b36c9981dba61d4e4d50b36c998a1f85e1434d50b36c99829ba5e1434d51d36c6f829ba61d434d50b36c99829c25e1434d50b36c99829ba5e1434d50b39c99821ba5e1434d50b36c9981dbf5e1434d50b36c9981dbd5e1434d50b36c99
  | 10, 0 => 0x2076e9975e1434d50b36c990e00081dba5e16b50d3542cdb264380000081dba5e1434d50b36c990e0000000081dba5e1434d50b36c990021e81dba5e1434d50b36c990ac00002076e97850d3542cdb2642b002077d5ba5e1434d50b36c9911800002076e9785b5434d50b36c990022881dba5e1434d50b36c9907400002076e97850d3542cdb2641d002076e9b65e1434d50b36c991bc00002076e99b5e1434d50b36c990022881dba5e1434d50b36c990e00081dba5e1434d50b36cd5264380021381dba5e1434d50b36c990e00081dba5e1434d50b36c9924038002076e97850d354750b36c990e00081dba5e1434d50b36c991bc38002076e97850d3542cf536c990e00081dba5e1434d50b36c9911838002076e97850d3542ce136c990e000002076e97850d3542ce136c99002076e97850d3542cdb264380c400002076e97850d3542cdb26431002076e97850d3542cdb298990e000002076e97850d3542cdb29899002076e97850d3542cdb2643806800002076e97850d3542cdb2641a0021381dba5e1434d50b3d4db2640081dba5e1434d52e42cf536c99002076e97850d354a50b36c991e800002076e97850d3542cdb2647a002076e97850d354a50b3d4db264000021e84dba5e1434d50b36c990021381dba5e1434d50b36c991180081dba5e1434d50b418db26446002076e97850d354a50b36c991180081dba5e1434d50b36c9924046002076e97850d3542cf536c9911800002076e98250d3542cdb2644600000002077497850d3542cdb2640081dba5e1434d51542cdb264460000081dba5e1434d50b36ccd2640081dba5e1434d50b36c99118030022881dba5e1434d51d42cdb2640081dba5e1434d52e4750b36c990000081dba5e1434d52e42cdb264008a2076e97850d3542cdb264940000081dba5e1434d50b36c992500081dba5e1434d51d42cf536c99002076e97850d354750b36c99118008a2076e97850d3542cdb2646f002076e97850d3542cdb354991bc0081dba5e1434d51d42cdb2646f002076e97850d3542cf536c991bc0081dba5e1434d50b36c991bc460000081dc25e1434d50b36c991bc000000081dc25e1434d50b36c99002076e97850d3542ce736c991bc00002076e97850d3542ce736c9900000829ba5e1434d50b36c991bc0000000829ba5e1434d50b36c99002076e97850d3542cdb2646f00c00002076e97850d3542cdb26403
  | 10, 1 => 0x81dba65d7850d3542cdb2643881dba5e16b50d3542cdb26438001ba65d7850d3542cdb26438000006e9975e1434d50b26438001ba5e16b50d3542cdb26438000006e9785ad434d4db26438002076e97850d3542cdb264380000081dba5e1434d50b36c9987a076e97850d3542cdb2642b002076e97850d3542cdb2642b81df56e97850d3542cdb26446002076e9785b5434d50b36c998a2076e97850d3542cdb2641d002076e97850d3542cdb2641d81dba6d97850d3542cdb2646f002076e99b5e1434d50b36c998a2076e97850d3542cdb26438002286e97850d3542cdb2643881dba5e1434d50b36cd526438001ba5e1434d50b36cd52643884e076e97850d3542cdb26438002136e97850d3542cdb2643881dba5e1434d50b36c9924038001ba5e1434d50b36c992403881dba5e1434d51d42cdb2643881dba5e1434d50b36c991bc3881dba5e1434d50b3d4db2643881dba5e1434d50b36c991183881dba5e1434d50b384db26438002076e97850d3542ce136c9981dba5e1434d50b36c990e031002076e97850d3542cdb2643181dba5e1434d50b36ca626438002076e97850d3542cdb2989981dba5e1434d50b36c990e01a002076e97850d3542cdb2641a001ba5e1434d51d42cdb26438001ba5e1434d50b36c991bc38001ba5e1434d50b3d4db26438001ba5e1434d50b36c9911838001ba5e1434d50b384db26438001ba5e1434d50b36c990e031001ba5e1434d50b36ca626438001ba5e1434d50b36c990e01a84e076e97850d3542cf536c9981dba5e1434d52e42cf536c9981dba5e1434d52942cdb2647a002076e97850d3542cdb2647a81dba5e1434d52942cf536c990021e84dba5e1434d50b36c9984e076e97850d3542cdb2644681dba5e1434d50b418db2644681dba5e1434d52942cdb2644681dba5e1434d50b36c992404681dba5e1434d50b3d4db26446002076e97850d3542cf5264460000081dba5e1434d50b3d446002076e98250d3542cdb264460000081dd25e1434d50b36c9981dba5e1434d51542cdb26446002076e97850d3542cdb3349981dba5e1434d50b36c99118038a2076e97850d354750b36c9981dba5e1434d52e4750b36c99002076e97850d354b90b36c998a2076e97850d3542cdb26494002076e97850d3542cdb2649481dba5e1434d51d42cf536c9981dba5e1434d51d42cdb264468a2076e97850d3542cdb2646f81dba5e1434d50b36cd52646f81dba5e1434d51d42cdb2646f002076e97850d35474db2646f0000081dba5e1434d51d36c6f81dba5e1434d50b3d4db2646f81dba5e1434d50b36c991bc46002077097850d3542cdb2646f0000081dc25e1434d50b36c9981dba5e1434d50b39cdb2646f002076e97850d3542ce736c990020a6e97850d3542cdb2646f00000829ba5e1434d50b36c9981dba5e1434d50b36c991bc03002076e97850d3542cdb26403
  | 10, 2 => 0x1ba65d7850d3542cdb26438001ba65d7850d3542c990e1ba5e16b50d3542cdb26438001ba5e16b50d3536c990e2076e97850d3542cdb26438002076e97850d3542cdb266076e97850d3542cdb2642b81dba5e16d50d3542cdb266076e97850d3542cdb2641d81dba66d7850d3542cdb266286e97850d3542cdb264386e97850d3542cdb354990e2136e97850d3542cdb264386e97850d3542cdb264900e2076e97850d3542ce136c9981dba5e1434d50b36c990c6076e97850d3542cdb2989981dba5e1434d50b36c99069ba5e1434d51d42cdb264386e97850d3542cdb2646f0e1ba5e1434d50b3d4db264386e97850d3542cdb264460e1ba5e1434d50b384db264386e97850d3542cdb264380c5ba5e1434d50b36ca6264386e97850d3542cdb2643806a076e97850d3542cdb2647a87a136e97850d3542cdb266076e97850d3542cf526446002076e97850d3542cf511a076e98250d3542cdb26446002077497850d3542cdb266076e97850d3542cdb3349981dba5e1434d52e42cdb266076e97850d3542cdb2649481dba5e1434d51d36c991bc0081dba5e1434d51d36c6f81dc25e1434d50b36c991bc0081dc25e1434d50b36c9981dba5e1434d50b39cdb2660a6e97850d3542cdb2646f0020a6e97850d3542cdb266076e97850d3542cdb26403
  | 10, 3 => 0x6e9975e1434d50b264386e9785ad434d4db2643881dba5e1434d50b36c9981dba5e1434d50b3d44681dd25e1434d50b36c9981dba5e1434d51d36c6f81dc25e1434d50b36c99829ba5e1434d50b36c99
  | 11, 0 => 0x2076e97850d3542cdb2643800000002076e97850d3542cf536c9900000002076e97850d3542cdb2644600000002076e97850d354750b36c9900000002076e97850d3542cdb2646f
  | 11, 1 => 0x81dba5e1434d50b36c990e000000006e97850d3542cdb264380000081dba5e1434d50b3d4db26400002076e97850d3542cdb264460000081dba5e1434d51d42cdb26400002076e97850d3542cdb2646f
  | 11, 2 => 0x2076e97850d3542cdb26438000006e97850d3542cdb26438002076e97850d3542cf536c99002076e97850d3542cdb26446002076e97850d354750b36c99002076e97850d3542cdb2646f
  | 11, 3 => 0x81dba5e1434d50b36c990e0006e97850d3542cdb2643881dba5e1434d50b3d4db266076e97850d3542cdb2644681dba5e1434d51d42cdb266076e97850d3542cdb2646f
  | 11, 4 => 0x6e97850d3542cdb26438
  | _, _ => 0

def frontierState (k t i : Nat) : List Sig :=
  let n := k+1-t
  let width := wireBits*n
  readWires n ((frontierData k t >>> (width*i)) &&& (2^width-1))

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

lemma finalBound : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12 := by
  rintro ⟨C, hf, hs, he⟩
  obtain ⟨k,hk,t,ht,h⟩ := root_restricted C hs hf he
  exact rootImpossible t ht k hk h
end PEqualNP.Outside.L_meta_670_aux.Base1007
