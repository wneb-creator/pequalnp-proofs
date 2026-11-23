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
end PEqualNP.Outside.L_meta_670_aux.Base1007

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


end PEqualNP.Outside.L_meta_670_aux.LiveCheck

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

lemma feasible_const (pt : p LiveCheck.target = target)
    (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {k t : Nat} {S : Finset LiveCheck.Sig} (h : LiveCheck.Live k t S)
    (a : LiveCheck.Sig) (ha : a ∈ S) (hc : ¬ proper (p a)) :
    ∃ q < k, Feasible p q S := by
  induction h with
  | stop =>
    have ht : a = LiveCheck.target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, pt]; exact target_proper)).elim
  | @unary k t U b hp hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary pn hc (feasible_live pt pn pb tail)⟩
    · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q+1,by omega,pull_unary pn h⟩
  | @binary k t U b c d hb hc' hbc hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left pb hc (feasible_live pt pn pb tail)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right pb hc (feasible_live pt pn pb tail)⟩
      · obtain ⟨q,hq,h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q+1,by omega,pull_binary pb h⟩

lemma represented_of_constant_or_old {S : Finset LiveCheck.Sig} {g : LiveCheck.Sig}
    (h : p g = zero ∨ p g = one ∨ p g ∈ S.image p) :
    represented (S.image p).toList (p g) := by
  rcases h with hz | ho | hm
  · exact Or.inr (fun hp => hp.1 hz)
  · exact Or.inr (fun hp => hp.2 ho)
  · exact Or.inl (Finset.mem_toList.mpr hm)

lemma not_feasible_free {q : Nat} {S S' : Finset LiveCheck.Sig} {g : LiveCheck.Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image p).toList (p g))
    (h : ¬ Feasible p q S) : ¬ Feasible p q S' :=
  fun h' => h (feasible_free hs hr h')

lemma not_feasible_pull {q : Nat} {S S' : Finset LiveCheck.Sig} {g : LiveCheck.Sig}
    (hq : 0 < q) (hs : S' ⊆ insert g S)
    (hr : represented (S.image p).toList (p g) ∨ witness (S.image p).toList (p g))
    (h : ¬ Feasible p q S) : ¬ Feasible p (q-1) S' := by
  intro h'
  apply h
  have hh := feasible_pull hs hr h'
  simpa [Nat.sub_add_cancel (show 1 ≤ q by omega)] using hh

end PEqualNP.Outside.L_meta_670_aux.Projection

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

lemma exclude_by_constantCount
    (pt : p LiveCheck.target = target)
    (pn : ∀ a, p (LiveCheck.neg a) = neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = bin d (p a) (p b))
    {k t r : Nat} {S : Finset LiveCheck.Sig}
    (hbound : ¬ Feasible p r S) (hslack : k < r + constantCount p S + 1) :
    ¬ LiveCheck.Live k t S := by
  intro h
  obtain ⟨q,hq,hf⟩ := feasible_count pt pn pb h
  exact hbound (feasible_mono hf (by omega))

end PEqualNP.Outside.L_meta_670_aux.Projection

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

lemma prefix_pull {p : LiveCheck.Sig → Base1007.Sig}
    (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {q : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs Base1007.raw)
    (hf : Feasible p q S) :
    ∃ m ≤ q + gs.length, ∃ t, Base1007.Live m t Base1007.raw.toFinset := by
  obtain ⟨m,hm,t,T,hl,hT⟩ := hf
  have hsub : ∀ a ∈ T, a ∈ Base1007.execute gs Base1007.raw := by
    intro a ha
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (hT ha)
    subst a
    exact hcover b hb (Base1007.live_proper hl _ ha)
  obtain ⟨m',t',T',hm',hl',hT'⟩ := old_extract_from gs Base1007.raw legal hl hsub
  have he := Base1007.necessary hl' hT'
  refine ⟨m',by omega,t',?_⟩
  rw [he]
  exact hl'

lemma exclude_by_prefix {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {k t budget : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs Base1007.raw)
    (hbase : ∀ m ≤ budget, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset)
    (hcost : gs.length + k ≤ budget + constantCount p S) :
    ¬ LiveCheck.Live k t S := by
  intro h
  obtain ⟨q,hq,hf⟩ := feasible_count pt pn pb h
  obtain ⟨m,hm,u,hl⟩ := prefix_pull gs legal hcover hf
  exact hbase m (by omega) u hl

end PEqualNP.Outside.L_meta_670_aux.Projection

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

end PEqualNP.Outside.L_meta_670_aux.ProjectionData

namespace PEqualNP.Outside.L_meta_670_aux.Projection

open Base1007 PEqualNP.CircuitLowerBounds

def prefixInputs : List Base1007.Sig :=
  Base1007.raw ++ [Base1007.zero, Base1007.one]

lemma prefix_pull_constants {p : LiveCheck.Sig → Base1007.Sig}
    (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {q : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs prefixInputs)
    (hf : Feasible p q S) :
    ∃ m ≤ q + gs.length, ∃ t, Base1007.Live m t Base1007.raw.toFinset := by
  obtain ⟨m,hm,t,T,hl,hT⟩ := hf
  have hsub : ∀ a ∈ T, a ∈ Base1007.execute gs prefixInputs := by
    intro a ha
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (hT ha)
    subst a
    exact hcover b hb (Base1007.live_proper hl _ ha)
  obtain ⟨m',t',T',hm',hl',hT'⟩ := old_extract_from gs prefixInputs legal hl hsub
  have hin : ∀ a ∈ T', a ∈ Base1007.raw := by
    intro a ha
    have hm := hT' a ha
    have hp := Base1007.live_proper hl' a ha
    simpa only [prefixInputs, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, hp.1, hp.2, or_false] using hm
  have he := Base1007.necessary hl' hin
  refine ⟨m',by omega,t',?_⟩
  rw [he]
  exact hl'

lemma exclude_by_prefix_constants {p : LiveCheck.Sig → Base1007.Sig}
    (pt : p LiveCheck.target = Base1007.target)
    (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
    (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))
    (gs : List Gate)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {k t budget : Nat} {S : Finset LiveCheck.Sig}
    (hcover : ∀ a ∈ S, Base1007.proper (p a) →
      p a ∈ Base1007.execute gs prefixInputs)
    (hbase : ∀ m ≤ budget, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset)
    (hcost : gs.length + k ≤ budget + constantCount p S) :
    ¬ LiveCheck.Live k t S := by
  intro h
  obtain ⟨q,hq,hf⟩ := feasible_count pt pn pb h
  obtain ⟨m,hm,u,hl⟩ := prefix_pull_constants gs legal hcover hf
  exact hbase m (by omega) u hl

end PEqualNP.Outside.L_meta_670_aux.Projection

namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds
open Projection ProjectionData

def legalOp : GateOp → Bool
  | .and | .or | .not => true
  | _ => false

def legalPrefix (gs : List Gate) : Bool := gs.all fun g =>
  legalOp g.op && decide (g.inputs.length ≤ 2)

def coversPrefix (i : Fin 3) (gs : List Gate) (v : List LiveCheck.Sig) : Bool :=
  let w := Base1007.execute gs prefixInputs
  v.all fun a =>
    let z := project i a
    z == Base1007.zero || z == Base1007.one || w.contains z

def prefixCheck (i : Fin 3) (k : Nat) (gs : List Gate) (v : List LiveCheck.Sig) : Bool :=
  legalPrefix gs && coversPrefix i gs v &&
    decide (gs.length + k ≤ 12 + constantCount (project i) v.toFinset)

lemma legalPrefix_sound {gs : List Gate} (h : legalPrefix gs = true) :
    ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  have hh := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  refine ⟨?_,hh.2⟩
  have hop := hh.1
  cases hgo : g.op <;> simp_all [legalOp, hgo]

lemma coversPrefix_sound {i : Fin 3} {gs : List Gate} {v : List LiveCheck.Sig}
    (h : coversPrefix i gs v = true) :
    ∀ a ∈ v.toFinset, Base1007.proper (project i a) →
      project i a ∈ Base1007.execute gs prefixInputs := by
  intro a ha hp
  have hc := List.all_eq_true.mp h a (List.mem_toFinset.mp ha)
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
  exact hc.resolve_left (by simpa only [Base1007.proper, not_or] using hp)

lemma prefixCheck_sound {i : Fin 3} {k : Nat} {gs : List Gate} {v : List LiveCheck.Sig}
    (hbase : ∀ m ≤ 12, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset)
    (hc : prefixCheck i k gs v = true) :
    ∀ m ≤ k, ∀ t, ¬ LiveCheck.Live m t v.toFinset := by
  have hchecks : (legalPrefix gs = true ∧ coversPrefix i gs v = true) ∧
      gs.length + k ≤ 12 + constantCount (project i) v.toFinset := by
    simpa only [prefixCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
  intro m hm t
  apply exclude_by_prefix_constants (project_target i) (project_neg i) (project_bin i)
    gs (legalPrefix_sound hchecks.1.1) (coversPrefix_sound hchecks.1.2) hbase
  omega

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma emptyPrefix13 : prefixCheck 0 13 [] LiveCheck.raw = true := by decide +kernel

lemma target_lower14
    (hbase : ∀ m ≤ 12, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset)
    (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = LiveCheck.edgeF x) :
    14 ≤ C.size := by
  by_contra! hs
  obtain ⟨k,t,S,hk,ht,hsub⟩ := LiveCheck.extract C.gates LiveCheck.raw hf
    (LiveCheck.circuit_target C hf he)
  have eq := LiveCheck.necessary ht hsub
  have hk13 : k ≤ 13 := by change C.gates.length < 14 at hs; omega
  apply prefixCheck_sound hbase emptyPrefix13 k hk13 t
  rw [eq]
  exact ht

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

namespace PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate

open LiveCheck

def star4State : List Sig :=
  [bin false raw4 (bin true raw0 raw3), raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma star4Prefix : prefixCheck 0 13 [] star4State = true := by decide +kernel

lemma star4_excluded
    (hbase : ∀ m ≤ 12, ∀ u, ¬ Base1007.Live m u Base1007.raw.toFinset) :
    ∀ m ≤ 13, ∀ t, ¬ Live m t star4State.toFinset :=
  prefixCheck_sound hbase star4Prefix

end PEqualNP.Outside.L_meta_670_aux.ProjectionCertificate
