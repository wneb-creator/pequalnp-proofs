import PEqualNP.Defs
-- The bit-vector evaluation and coverage lemmas are adapted from L-meta-1447,
-- building on work of ljste and jfsantoropereira, under Apache-2.0.
namespace PEqualNP.Outside.L_meta_5056_aux
abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
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
def raw : List Sig := [(0x801ff60707c043c8649f03823c104e09c05afc2000c051a0011e421162fc0049,0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049),
  (0x240807ffc2b0508861041cc401b2f64da10dc00101866306038cf08d0c0183,0xc000000000b0008860041c800090f60480018001018601060084400c000080),
  (0x380ffbf8000cb8010639e37c220d00823df66086060844082c0122f1f40206,0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d40206),
  (0xffc00ffc000953e10278420588cc303ff3c63b8308082f8030c031cf1e383034,0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010),
  (0xfffff0000001bd3e13809c79f30fc1c73c07c3e030303000c0f03e0c1fc00038,0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020),
  (0x142e381c00e07e03f001f83ff803e4403fc018ff01c00fe000cc40,0x300004020000c380000e02c016001503fb003e0401a80085a01800ec0004400),
  (0x22cfffe000ff8003fffe003ffffc187fc0001f0001fff000030180,0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100),
  (0x4f7c7ffff000003ffffffc000001f8000001ffffe000000000e00,0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da000000000800),
  (0x38f807fffffffffc0000000000001fffffffe0000000000003f000,0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a000)]
def fixed : Sig := (0x803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f,0x803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f)


def forceN (x : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (n+1)) x

lemma forceN_eq (x : Nat) (f : Nat → Bool) : forceN x f = f x := by cases x <;> rfl


def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def Covers (S : Finset Sig) : Prop := ∀ i < 256, ∃ a ∈ S, (sep true a).getLsbD i = true

def Live : Nat → Finset Sig → Prop
  | 0, S => S.card ≤ 6 ∧ fixed ∈ S ∧ Covers S ∧ ∀ a ∈ S, proper a
  | k+1, S => ∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ fixed ∈ U ∧ Live k (insert (bin d a b) U)

private lemma live_proper {k S} (l : Live k S) : ∀ a ∈ S, proper a := by
  induction k generalizing S with
  | zero => exact l.2.2.2
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,pa,pb,_,_,_,t⟩ := l
    simp only [Finset.forall_mem_insert]
    exact ⟨pa,pb,fun x hx => ih t x (Finset.mem_insert_of_mem hx)⟩

private lemma live_fixed {k S} (l : Live k S) : fixed ∈ S := by
  cases k with
  | zero => exact l.2.1
  | succ k =>
    obtain ⟨U,a,b,d,rfl,_,_,_,_,hf,_⟩ := l
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hf)

private lemma live_size {k S} (l : Live k S) : S.card ≤ k+6 := by
  induction k generalizing S with
  | zero => exact l.1
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,hn,_,t⟩ := l
    have hc := ih t
    have hu : bin d a b ∉ U := fun h => hn (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem hu] at hc
    have ha := Finset.card_insert_le (a := a) (s := insert b U)
    have hb := Finset.card_insert_le (a := b) (s := U)
    omega
private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h


private lemma live_sep {k S} (l : Live k S) : Covers S := by
  induction k generalizing S with
  | zero => exact l.2.2.1
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,_,_,t⟩ := l
    intro i hi
    obtain ⟨x,hx,h⟩ := ih t i hi
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases sep_binary true d a b i h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k S} {v : List Sig} (h : Live k S) (he : v.toFinset=S) :
    unionSep true v = top := by
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

private lemma pull {w : List Sig} {g : Gate} {k S}
    (l : Live k S) (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (nn : g.op ≠ .not) (fx : fixed ∈ w) (sub : ∀ a ∈ S, a ∈ w++[gv w g]) :
    ∃ m T, m ≤ k+1 ∧ Live m T ∧ ∀ a ∈ T, a ∈ w := by
  let z := gv w g
  by_cases hsub : ∀ a ∈ S, a ∈ w
  · exact ⟨k,S,by omega,l,hsub⟩
  push_neg at hsub
  obtain ⟨x,hx,hnx⟩ := hsub
  have eq : x = z := by simpa [hnx,z] using sub x hx
  subst x
  have hp := live_proper l z hx
  rcases gate_rep w g hg with hr | ⟨hon,_⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,hz⟩
  · exact False.elim ((hr.resolve_left hnx) hp)
  · exact False.elim (nn ((isNot_iff g.op).1 hon))
  · change z = bin d a b at hz
    let U := S.erase z
    have hu : ∀ v ∈ U, v ∈ w := by
      intro v hv
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
      simpa [show v ≠ gv w g from hne] using sub v hm
    have fresh : bin d a b ∉ insert a (insert b U) := by
      rw [← hz]
      intro hm
      rcases Finset.mem_insert.mp hm with e | hm
      · exact hnx (e.symm ▸ ha)
      rcases Finset.mem_insert.mp hm with e | hm
      · exact hnx (e.symm ▸ hb)
      · exact hnx (hu _ hm)
    have hfix : fixed ∈ U := Finset.mem_erase.mpr ⟨fun e => hnx (e ▸ fx),live_fixed l⟩
    have ht : Live k (insert (bin d a b) U) := by simpa [← hz,U,Finset.insert_erase hx] using l
    refine ⟨k+1,insert a (insert b U),le_rfl,⟨U,a,b,d,rfl,pa,pb,hab,fresh,hfix,ht⟩,?_⟩
    simpa using And.intro ha (And.intro hb hu)

private lemma extract (gs : List Gate) (w : List Sig) (F : Finset Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (nn : ∀ g ∈ gs, g.op ≠ .not) (fx : fixed ∈ w) (term : Live 0 F)
    (sub : ∀ a ∈ F, a ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live k S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,F,by simp,term,sub⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,l,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun a ha => nn a (by simp [ha])) (by simp [fx]) sub
    obtain ⟨m,T,hm,ht,hT⟩ := pull l (legal g (by simp)) (nn g (by simp)) fx hs
    exact ⟨m,T,by simp; omega,ht,hT⟩
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

def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 9) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]


-- Store the positive and negative columns in one natural number for the kernel's
-- bitwise operations. The second coordinate caches their separating rows.
def pack (s : Sig) : Nat := (s.2 ++ s.1).toNat
def fixedN : Nat := pack fixed
def allSig : Nat := pack one
abbrev W := Nat × Nat
def full : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def delta (x : Nat) := Nat.land full (Nat.xor x (Nat.shiftRight x 256))
def code (s : Sig) : W := (pack s,(sep true s).toNat)
def masks : List W → Nat
  | [] => 0
  | a::v => Nat.lor a.2 (masks v)
def absent (x : Nat) : List W → Bool
  | [] => true
  | a::v => cond (Nat.beq x a.1) false (absent x v)
def combine (r : List W → Bool) (rest : List W) (kextra : Nat) (c : Nat) (a b : W) (g : Nat) : Bool :=
  forceN g fun g =>
  cond (Nat.beq g a.1 || Nat.beq g b.1 || Nat.beq g 0 || Nat.beq g allSig) false (
    forceN (delta g) fun s =>
    forceN (Nat.lor s c) fun base =>
    let go := fun v => absent g rest && r ((g,s)::v)
    let da := !(Nat.beq a.1 fixedN)
    let db := !(Nat.beq b.1 fixedN)
    (da && db && Nat.beq base full && go rest) ||
    (Nat.ble 1 kextra &&
      ((db && Nat.beq (Nat.lor base a.2) full && go (a::rest)) ||
       (da && Nat.beq (Nat.lor base b.2) full && go (b::rest)) ||
       (Nat.ble 2 kextra && Nat.beq (Nat.lor base (Nat.lor a.2 b.2)) full && go (a::b::rest)))))
def inner (r : List W → Bool) (ex : Nat) (a : W) (pre : List W) (pc : Nat) : List W → Bool
  | [] => false
  | b::t =>
    (forceN (Nat.lor pc (masks t)) fun c =>
      let rest := pre ++ t
      combine r rest ex c a b (Nat.land a.1 b.1) || combine r rest ex c a b (Nat.lor a.1 b.1)) ||
    inner r ex a (b::pre) (Nat.lor pc b.2) t
def outer (r : List W → Bool) (ex : Nat) (pre : List W) (pc : Nat) : List W → Bool
  | [] => false
  | a::t => inner r ex a pre pc t || outer r ex (a::pre) (Nat.lor pc a.2) t
def go : Nat → List W → Bool
  | 0, v => Nat.ble v.length 6
  | k+1,v => Nat.ble v.length 6 || outer (go k) (k+7-v.length) [] 0 v

lemma pack_injective : Function.Injective pack := by
  intro a b h
  have e : a.2 ++ a.1 = b.2 ++ b.1 := BitVec.eq_of_toNat_eq h
  apply Prod.ext
  · simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun x : BitVec 512 => x.extractLsb' 0 256) e
  · simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun x : BitVec 512 => x.extractLsb' 256 256) e

lemma pack_and (a b : Sig) : Nat.land (pack a) (pack b) = pack (bin false a b) := by
  change ((a.2 ++ a.1).toNat &&& (b.2 ++ b.1).toNat) = _
  rw [← BitVec.toNat_and,BitVec.and_append]
  rfl

lemma pack_or (a b : Sig) : Nat.lor (pack a) (pack b) = pack (bin true a b) := by
  change ((a.2 ++ a.1).toNat ||| (b.2 ++ b.1).toNat) = _
  rw [← BitVec.toNat_or,BitVec.or_append]
  rfl

lemma delta_pack (a : Sig) : delta (pack a) = (sep true a).toNat := by
  have lo : (pack a) % 2^256 = a.1.toNat := by
    simpa only [BitVec.extractLsb',BitVec.toNat_ofNat,Nat.shiftRight_zero,pack] using congrArg BitVec.toNat (BitVec.extractLsb'_append_eq_right (a:=a.2) (b:=a.1))
  have hi : ((pack a) >>> 256) % 2^256 = a.2.toNat := by
    simpa only [BitVec.extractLsb',BitVec.toNat_ofNat,pack] using congrArg BitVec.toNat (BitVec.extractLsb'_append_eq_left (a:=a.2) (b:=a.1))
  change (2^256-1) &&& ((pack a) ^^^ ((pack a) >>> 256)) = (a.1 ^^^ a.2).toNat
  rw [Nat.and_comm,Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow,lo,hi,BitVec.toNat_xor]

lemma masks_eq (v : List Sig) : masks (v.map code) = (unionSep true v).toNat := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.map_cons,masks,code,unionSep,BitVec.toNat_or,ih]; rfl

lemma masks_append (l t : List W) : masks (l++t) = Nat.lor (masks l) (masks t) := by
  induction l with
  | nil => simp [masks]
  | cons a v ih => simp only [List.cons_append,masks,ih]; exact (Nat.or_assoc ..).symm

lemma absent_ok {g : Sig} {v : List Sig} (h : g ∉ v) : absent (pack g) (v.map code) = true := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have na : pack g ≠ pack a := fun e => h (List.mem_cons.mpr (Or.inl (pack_injective e)))
    have nt : g ∉ v := fun e => h (List.mem_cons_of_mem _ e)
    simp [absent,code,na,ih nt]

private lemma natbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr (by simpa using h)

lemma combine_ok {k m : Nat} {v rest : List Sig} {U : Finset Sig} {a b : Sig} {d : Bool}
    {r : List W → Bool} (perm : (a::b::rest).Perm v) (hv : v.Nodup)
    (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (fx : fixed ∈ U)
    (l : Live m (insert (bin d a b) U))
    (ih : ∀ w : List Sig, w.Nodup → w.toFinset = insert (bin d a b) U → r (w.map code) = true) :
    combine r (rest.map code) (k+7-v.length) (masks (rest.map code)) (code a) (code b) (pack (bin d a b)) = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  have e0 := (List.toFinset_eq_of_perm _ _ perm).trans he
  have nd := perm.symm.nodup_iff.mp hv
  have clean : dropped [a,b] (a::b::rest) = rest := by
    have na := (List.nodup_cons.mp nd).1
    have nb := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    have eq : rest.filter (fun x => !([a,b].contains x)) = rest := by
      apply List.filter_eq_self.mpr
      intro x hx
      have xa : x ≠ a := fun e => na (List.mem_cons_of_mem _ (e ▸ hx))
      have xb : x ≠ b := fun e => nb (e ▸ hx)
      simp [xa,xb]
    unfold dropped
    rw [List.filter_cons,List.filter_cons]
    simp only [List.contains_cons,beq_self_eq_true,Bool.true_or,Bool.or_true,Bool.not_true,cond_false]
    simp only [Bool.false_eq_true,if_false]
    simpa only [List.contains_cons] using eq
  obtain ⟨nn,e⟩ := edit_list (del := [a,b]) (U := U) nd (by simp [hab]) (by simpa using e0)
  rw [clean] at nn e
  change (h++rest).Nodup at nn
  change (h++rest).toFinset=U at e
  have nU : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have nnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nU (e ▸ List.mem_toFinset.mpr hm),nn⟩
  have eh : (g::(h++rest)).toFinset = insert g U := by rw [List.toFinset_cons,e]
  have next := ih _ nnd eh
  have size := live_size l
  rw [← eh,List.toFinset_card_of_nodup nnd] at size
  have len := perm.length_eq
  simp only [List.length_cons,List.length_append] at len size
  have extra : h.length ≤ k+7-v.length := by omega
  have cover := congrArg BitVec.toNat (live_cover l eh)
  have cov : Nat.lor (Nat.lor (sep true g).toNat (masks (rest.map code))) (masks (h.map code)) = full := by
    rw [masks_eq,masks_eq]
    change ((sep true g).toNat ||| (unionSep true rest).toNat) ||| (unionSep true h).toNat = top.toNat
    rw [←cover,unionSep,union_append,BitVec.toNat_or,BitVec.toNat_or]
    ac_rfl
  have pg := live_proper l _ (Finset.mem_insert_self _ _)
  have na : pack g ≠ pack a := by
    intro eq
    apply fresh
    change g ∈ _
    rw [pack_injective eq]
    exact Finset.mem_insert_self _ _
  have nb : pack g ≠ pack b := by
    intro eq
    apply fresh
    change g ∈ _
    rw [pack_injective eq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have nz : pack g ≠ 0 := fun eq => pg.1 (pack_injective (show pack g = pack zero from eq))
  have no : pack g ≠ allSig := fun eq => pg.2 (pack_injective eq)
  have abs : absent (pack g) (rest.map code) = true := absent_ok (fun hm => nU (e ▸ List.mem_toFinset.mpr (List.mem_append_right _ hm)))
  have discard {z : Sig} (hz : z ∉ U) : Nat.beq (pack z) fixedN = false :=
    natbeq_false (fun e => hz (pack_injective e ▸ fx))
  change combine r _ _ _ (code a) (code b) (pack g) = true
  simp only [combine,forceN_eq,code,natbeq_false na,natbeq_false nb,natbeq_false nz,natbeq_false no,
    Bool.false_or,cond_false,delta_pack,abs,Bool.true_and,Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq,Nat.ble_eq]
  by_cases A : a ∈ U <;> by_cases B : b ∈ U
  · right; refine ⟨?_,Or.inr ⟨⟨?_,?_⟩,?_⟩⟩
    · simp [h,keepOf,A,B] at extra; omega
    · simpa [h,keepOf,A,B] using extra
    · simpa [h,keepOf,A,B,masks,code] using cov
    · simpa [h,keepOf,A,B,code] using next
  · right; refine ⟨?_,Or.inl (Or.inl ⟨⟨by simp [discard B],?_⟩,?_⟩)⟩
    · simpa [h,keepOf,A,B] using extra
    · simpa [h,keepOf,A,B,masks,code] using cov
    · simpa [h,keepOf,A,B,code] using next
  · right; refine ⟨?_,Or.inl (Or.inr ⟨⟨by simp [discard A],?_⟩,?_⟩)⟩
    · simpa [h,keepOf,A,B] using extra
    · simpa [h,keepOf,A,B,masks,code] using cov
    · simpa [h,keepOf,A,B,code] using next
  · left
    refine ⟨⟨⟨by simp [discard A],by simp [discard B]⟩,?_⟩,?_⟩
    · simpa [h,keepOf,A,B,masks,code] using cov
    · simpa [h,keepOf,A,B,code] using next

private def pairHit (r : List W → Bool) (ex : Nat) (a b : Sig) (t : List Sig) :=
  combine r (t.map code) ex (masks (t.map code)) (code a) (code b) (Nat.land (pack a) (pack b)) ||
  combine r (t.map code) ex (masks (t.map code)) (code a) (code b) (Nat.lor (pack a) (pack b))

private lemma lor_comm (a b : Nat) : Nat.lor a b = Nat.lor b a := Nat.or_comm a b

private lemma inner_hit {r ex a b v} (t pre : List Sig) (hb : b ∈ t)
    (p : (a::(pre++t)).Perm v)
    (h : ∀ rest, (a::b::rest).Perm v → pairHit r ex a b rest = true) :
    inner r ex (code a) (pre.map code) (masks (pre.map code)) (t.map code) = true := by
  induction t generalizing pre with
  | nil => simp at hb
  | cons x t ih =>
    rw [List.map_cons,inner,Bool.or_eq_true]
    rcases List.mem_cons.mp hb with e | mem
    · subst x
      left
      rw [forceN_eq,← masks_append,← List.map_append]
      exact h (pre++t) ((List.Perm.cons a List.perm_middle.symm).trans p)
    · right
      have pp : (a::((x::pre)++t)).Perm v := (List.Perm.cons a List.perm_middle.symm).trans p
      simpa only [List.map_cons,masks,lor_comm] using ih (x::pre) mem pp

private lemma outer_hit {r ex a b v} (t pre : List Sig) (ha : a ∈ t) (hb : b ∈ t)
    (ne : a ≠ b) (p : (pre++t).Perm v)
    (h1 : ∀ rest, (a::b::rest).Perm v → pairHit r ex a b rest = true)
    (h2 : ∀ rest, (b::a::rest).Perm v → pairHit r ex b a rest = true) :
    outer r ex (pre.map code) (masks (pre.map code)) (t.map code) = true := by
  induction t generalizing pre with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.map_cons,outer,Bool.or_eq_true]
    have pp : (x::(pre++t)).Perm v := List.perm_middle.symm.trans p
    by_cases ea : a=x
    · subst x
      exact Or.inl (inner_hit t pre ((List.mem_cons.mp hb).resolve_left ne.symm) pp h1)
    by_cases eb : b=x
    · subst x
      exact Or.inl (inner_hit t pre ((List.mem_cons.mp ha).resolve_left ne) pp h2)
    right
    simpa only [List.map_cons,masks,lor_comm] using
      ih (x::pre) ((List.mem_cons.mp ha).resolve_left ea) ((List.mem_cons.mp hb).resolve_left eb) pp

private lemma pair_hit_ok {k m : Nat} {v : List Sig} {U : Finset Sig} {a b : Sig} {d : Bool}
    {r : List W → Bool} (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U)) (fx : fixed ∈ U)
    (l : Live m (insert (bin d a b) U))
    (ih : ∀ w : List Sig, w.Nodup → w.toFinset = insert (bin d a b) U → r (w.map code) = true)
    (rest) (p : (a::b::rest).Perm v) : pairHit r (k+7-v.length) a b rest = true := by
  have f := combine_ok p hv he hle hab fresh fx l ih
  rw [pairHit,Bool.or_eq_true,pack_and,pack_or]
  cases d
  · exact Or.inl f
  · exact Or.inr f

lemma go_complete {m S} (l : Live m S) (k : Nat) (hk : m ≤ k) (v : List Sig)
    (hv : v.Nodup) (he : v.toFinset = S) : go k (v.map code) = true := by
  induction k generalizing m S v with
  | zero =>
    obtain rfl : m = 0 := by omega
    have hs := live_size l
    rw [← he,List.toFinset_card_of_nodup hv] at hs
    simpa only [go,Nat.ble_eq,List.length_map] using hs
  | succ k ih =>
    rw [go,Bool.or_eq_true,List.length_map]
    cases m with
    | zero =>
      have hs := live_size l
      rw [← he,List.toFinset_card_of_nodup hv] at hs
      exact Or.inl (Nat.ble_eq.mpr hs)
    | succ m =>
      right
      obtain ⟨U,a,b,d,rfl,_,_,hab,hf,fx,t⟩ := l
      have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
      have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
      have hf' : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a,Finset.insert_comm b a]
      have t' : Live m (insert (bin d b a) U) := by rwa [bin_comm d b a]
      exact outer_hit v [] ah bh hab (List.Perm.refl v)
        (pair_hit_ok hv he (show m ≤ k by omega) hab hf fx t (fun w hn e => ih t (by omega) w hn e))
        (pair_hit_ok hv e' (show m ≤ k by omega) hab.symm hf' fx t' (fun w hn e => ih t' (by omega) w hn e))

private lemma combine_mono {r t : List W → Bool} (h : ∀ w, r w = true → t w = true)
    (rest : List W) (ex c : Nat) (a b : W) (g : Nat) :
    combine r rest ex c a b g = true → combine t rest ex c a b g = true := by
  simp only [combine,forceN_eq]
  cases gcase : (Nat.beq g a.1 || Nat.beq g b.1 || Nat.beq g 0 || Nat.beq g allSig)
  · simp only [Bool.cond_false,Bool.or_eq_true,Bool.and_eq_true]
    intro step
    rcases step with ⟨c1,c2,hr⟩ | ⟨space,((⟨c1,c2,hr⟩ | ⟨c1,c2,hr⟩) | ⟨c1,c2,hr⟩)⟩
    · exact Or.inl ⟨c1,c2,h _ hr⟩
    · exact Or.inr ⟨space,Or.inl (Or.inl ⟨c1,c2,h _ hr⟩)⟩
    · exact Or.inr ⟨space,Or.inl (Or.inr ⟨c1,c2,h _ hr⟩)⟩
    · exact Or.inr ⟨space,Or.inr ⟨c1,c2,h _ hr⟩⟩
  · exact id

private lemma inner_mono {r t : List W → Bool} (h : ∀ w, r w = true → t w = true)
    (ex : Nat) (a : W) (pre : List W) (pc : Nat) (xs : List W) :
    inner r ex a pre pc xs = true → inner t ex a pre pc xs = true := by
  induction xs generalizing pre pc with
  | nil => exact id
  | cons b tail ih =>
    simp only [inner,forceN_eq,Bool.or_eq_true]
    exact Or.imp (Or.imp (combine_mono h _ _ _ _ _ _) (combine_mono h _ _ _ _ _ _)) (ih _ _)

private lemma outer_mono {r t : List W → Bool} (h : ∀ w, r w = true → t w = true)
    (ex : Nat) (pre : List W) (pc : Nat) (xs : List W) :
    outer r ex pre pc xs = true → outer t ex pre pc xs = true := by
  induction xs generalizing pre pc with
  | nil => exact id
  | cons a tail ih =>
    simp only [outer,Bool.or_eq_true]
    exact Or.imp (inner_mono h _ _ _ _ _) (ih _ _)

def layer (k : Nat) (r : List W → Bool) (v : List W) : Bool :=
  Nat.ble v.length 6 || outer r (k+7-v.length) [] 0 v

lemma cutGo (k : Nat) (v : List W) (kids : List (List W))
    (closed : layer k (fun w => !(kids.contains w)) v = false)
    (smaller : kids.all (fun w => !(go k w)) = true) : go (k+1) v = false := by
  have h (w) (hw : go k w = true) : (!(kids.contains w)) = true := by
    by_contra hn
    have hm : w ∈ kids := by simpa using hn
    have no := List.all_eq_true.mp smaller w hm
    simp [hw] at no
  cases hs : go (k+1) v with
  | false => rfl
  | true =>
    simp only [go,Bool.or_eq_true] at hs
    have hit : layer k (fun w => !(kids.contains w)) v = true := by
      simp only [layer,Bool.or_eq_true]
      exact hs.imp_right (outer_mono h _ _ _ _)
    exact hit.symm.trans closed


def start : List Sig := raw ++ [fixed]
def edge (x : Fin 9 → Bool) : Bool :=
  [1,12,23,34,40,5,16,27,38,57,68,85].any fun (e : Nat) => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10))

lemma rows (s : Bool) (i : Fin 256) : edge (sample raw s i) = s := by
  revert s i
  decide +kernel

lemma root_eq {k S} (l : Live k S) (hs : ∀ a ∈ S, a ∈ start) : start.toFinset=S := by
  have necessary : start.all (fun a => a == fixed || unionSep true (start.erase a) != top) = true := by decide +kernel
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have ne : a ≠ fixed := fun e => hn (e ▸ live_fixed l)
  have fail := List.all_eq_true.mp necessary a hr
  have cov : unionSep true (start.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [ne,cov] at fail

private lemma prefix_exec (gs : List Gate) (w : List Sig) : ∃ t, execute gs w = w++t := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨t,et⟩ := ih (w++[gv w g])
    refine ⟨gv w g::t,?_⟩
    change execute gs (w++[gv w g]) = _
    simpa only [List.append_assoc,List.singleton_append] using et

lemma frontier (C : Circuit) (leg : PEqualNP.MetaComplexity.FanInTwo C) (sz : C.size = 8)
    (nn : ∀ g ∈ C.gates, g.op ≠ .not)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (S : Finset Nat) (card : S.card = 6) (included : 9 ∈ S)
    (ob : ¬ ∃ x y : Fin 9 → Bool, edge x ≠ edge y ∧
      ∀ j ∈ S, (C.wires (List.ofFn x)).getD j false = (C.wires (List.ofFn y)).getD j false) :
    go 7 (start.map code) = true := by
  classical
  have rid : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := by decide +kernel
  let w := execute C.gates raw
  have proj (s i j) : bit s i (w.getD j zero) = (C.wires (List.ofFn (sample raw s i))).getD j false := by
    rw [← b_read]
    change ((execute C.gates raw).map _).getD _ _ = _
    rw [execute_bits _ _ _ _ (fun g hg => (leg g hg).1),sample_list raw rid]
    rfl
  have firstEq : w.getD 9 zero = fixed := by
    have fo : bin true (raw.getD 0 zero) (raw.getD 2 zero) = fixed := by decide +kernel
    have bitEq (s : Bool) (i : Fin 256) : bit s i (w.getD 9 zero) = bit s i fixed := by
      rw [proj, first, ←fo, bit_bin]
      rfl
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    · exact bitEq true ⟨i,hi⟩
    · exact bitEq false ⟨i,hi⟩
  let F := (S.image (fun j => w.getD j zero)).filter proper
  have fx : fixed ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨9,included,firstEq⟩,by
    unfold proper fixed zero one top
    decide⟩
  have term : Live 0 F := by
    refine ⟨(Finset.card_filter_le ..).trans ((Finset.card_image_le).trans card.le),fx,?_,fun _ ha => (Finset.mem_filter.mp ha).2⟩
    intro i hi
    let i' : Fin 256 := ⟨i,hi⟩
    have distinct : ∃ j ∈ S, bit true i' (w.getD j zero) ≠ bit false i' (w.getD j zero) := by
      by_contra hh
      push Not at hh
      apply ob
      refine ⟨sample raw true i',sample raw false i',by simp [rows],?_⟩
      intro j hj
      simpa only [←proj] using hh j hj
    obtain ⟨j,hj,hd⟩ := distinct
    let z := w.getD j zero
    have p : proper z := by
      constructor
      · intro e
        exact hd (by change bit true i' z = bit false i' z; rw [e,bit_zero,bit_zero])
      · intro e
        exact hd (by change bit true i' z = bit false i' z; rw [e,bit_one,bit_one])
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,p⟩,?_⟩
    change z.1.getLsbD i ≠ z.2.getLsbD i at hd
    simp only [sep,ite_true,BitVec.getLsbD_xor]
    cases hp : z.1.getLsbD i <;> cases hn : z.2.getLsbD i <;> simp_all
  have sub : ∀ a ∈ F, a ∈ w := by
    intro a ha
    obtain ⟨h,p⟩ := Finset.mem_filter.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact (get_rep w j).resolve_right (fun np => np p)
  cases hg : C.gates with
  | nil => simp [Circuit.size,hg] at sz
  | cons g gs =>
    have wg : w = execute gs (raw++[gv raw g]) := by simp [w,execute,hg]
    obtain ⟨t,et⟩ := prefix_exec gs (raw++[gv raw g])
    have fg : gv raw g = fixed := by
      rw [wg,et,List.getD_append _ _ _ _ (by simp [raw])] at firstEq
      exact firstEq
    have ws : w = execute gs start := by simpa only [fg,start] using wg
    obtain ⟨k,T,hk,l,hT⟩ := extract gs start F
      (fun h hh => leg h (by simp [hg,hh])) (fun h hh => nn h (by simp [hg,hh]))
      (by simp [start]) term (ws ▸ sub)
    have len : gs.length + 1 = 8 := by simpa [Circuit.size,hg] using sz
    exact go_complete l 7 (by omega) start (by decide +kernel) (root_eq l hT)

def q0 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049801ff60707c043c8649f03823c104e09c05afc2000c051a0011e421162fc0049,0x10441a08000008000000002000000000108020000000000000000040800000)

def q1 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240807ffc2b0508861041cc401b2f64da10dc00101866306038cf08d0c0183,0xe40807ffc20050000100004401220049210c4000000062000308b0810c0103)

def q2 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d4020600380ffbf8000cb8010639e37c220d00823df66086060844082c0122f1f40206,0x8521100400080000400000000080080002000000000000008000000200000)

def q3 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffc00ffc000953e10278420588cc303ff3c63b8308082f8030c031cf1e383034,0xea802fec0089102002500001880800042204130200002d000080210a18102024)

def q4 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff0000001bd3e13809c79f30fc1c73c07c3e030303000c0f03e0c1fc00038,0x957fb02010010100008000001004400310024080000010000050120406400018)

def q5 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec00044000000000000142e381c00e07e03f001f83ff803e4403fc018ff01c00fe000cc40,0x3000040201422001c000052029000a80048000400254010a500400120008840)

def q6 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100000000000022cfffe000ff8003fffe003ffffc187fc0001f0001fff000030180,0xc00808041228004c00015000000900004800010258000010000844000020080)

def q7 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da000000000800000000000004f7c7ffff000003ffffffc000001f8000001ffffe000000000e00,0x30010000020404000102000001620550000000008000000c5a24000000000600)

def q8 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a000000000000038f807fffffffffc0000000000001fffffffe0000000000003f000,0x40020100843848032028eaac00000000000000095a5a82800000000000015000)

def q9 : W := (0x803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f,0x0)

def q10 : W := (0x4000707c00040000100000400020040000c000000002000020010000c0001,0x4000707c00040000100000400020040000c000000002000020010000c0001)

def q11 : W := (0x80cfb21d0fc0f3c0ecff079e9c10deffc4ca7d8001c1d7a1071ec6512e7c00c9803ffe07ffc2f3d8ecff079efc11feffcdfbfde001c1d7e3071fcef1effc01cb,0xf04c1af002001800000000600120000931806000000042000108a0c1800102)

def q12 : W := (0x100808400000000201821c0004000008540000000000000400002054000000380e03f8000098000601827c000c008039f46000000040000c0020e1f40002,0x381e0bf040009800040000600008008031a0600000004000080020c1a00002)

def q13 : W := (0x80ffffffffc0fff8edff3ffffc32dfffc6ffffe087c7dfe50f3ec773fffc02cf803fffffffc2fff8edff3ffffc33ffffcfffffe087c7dfe70f3fcff3fffc03cf,0xc0000000020000000000000001200009000000000000020001088000000100)

def q14 : W := (0x402010008043c0002802040000103bc0c2288000000280000000410628000080000e04000053c0007802048800303fc1c2398000000780000000c10e380000,0x80402e1400801000005000008800200401001100000005000000008008100000)

def q15 : W := (0x95cfb21d0fc0f3c1ecff479e9cd4feffd5ca7d8109c9d7a1375ed6d52e7c10d9ffffffffffcbf3f9eeff479ffcddfeffffffffe309c9ffe337dffffffffc31ff,0x6a304de2f00b003802000001600900002a358262000028420081292ad1802126)

def q16 : W := (0x8000000000b00000000418800080c404000100000000000000040008000000803ff0000000b11800800418f001c0c70c03c1e00000100000100e000fc00008,0x80bff0000000011800800000700140030803c0e00000100000100a0007c00008)

def q17 : W := (0xeacff23d1fc0fffeffff9fffff1bdfffeccfffe031f1f7a1c7beee593ffc00e9fffffe07ffc3fffeffff9fffff1ffffffdffffe031f1f7e3c7fffefdfffc01fb,0x15300c3ae003000000000000000420001130000000000042004110a4c0000112)

def q18 : W := (0xc000000500480018000008000020080000000000000000000000022180c00001e001000f80df801e00001c0000701c001e0000040,0x22180c000012001000a8097800600001400005014001e0000040)

def q19 : W := (0x83cfb25d2fc0fff8ecffe7be9d70dffffffa7fe041dbd7a95f1fc65fee7c44c9803ffe07ffd6fff8fcffe7fefff1fffffffbffe441ffd7fbff1fceffeffccdcb,0x3f04c5ad016000010000040628120000001800400240052a00008a001808902)

def q20 : W := (0x8000010043c02000028000104e00004a7c00004000000000421000000000000000000002c3d8e00007800011fe000dfbfc0001c000030001cef000000180,0x800001028018c00005000001b0000db180000180000300018ce000000180)

def q21 : W := (0x8ccfb29d4fc0fffbecffef9e9ffffefffffffd885bc1d7bf071ffff12e7d01c9803ffe07ffe2ffffecffff9efffffefffffffdf87fc1d7ff071ffff1efff01cb,0xcf04c9ab02200040000100060000000000000702400004000000000c1820002)

def q22 : W := (0x100000200f3c0ecfd00000010daafc000000000000001051a000000000000000000000000f3c0ecff00000011feffc000000000000003071e000000000000,0x1000002000000000200000001245000000000000000020204000000000000)

def q23 : W := (0xb0cfb21d0fc0f3c7feff079e9e9dfeffc4ca7d9f01c1d7b3a7dec6512e7c08c9803ffe07ffc6f7dfffff079effffffffcdfbfdff81c1d7ffffffcef1effc0fcb,0x30f04c1af00604180100000061620100093180608000004c582108a0c1800702)

def q24 : W := (0x200000400b000ccd705129c00000000000000018155200000000000000000000000000000f000ecff079efc0000000000000001c1d7e00000000000000000,0x20000040040002028028c6000000000000000004082c00000000000000000)

def q25 : W := (0xc0cfb31d8fc0f3c4ffff17dffc10deffc4ca7d96a5e5ffe1071ec6512e7ea0c9803ffe07fffafbdffffffffffc11feffcdfbfdffffffffe3071fcef1effff1cb,0x40f04d1a703a081b0000e82000012000093180695a1a0002000108a0c1815102)

def q26 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049803ffe07ffc043d8649f03827c104e09c07bfc6000c051e0011e4231e3fc004b,0x304c1af00000180000000060000000003180600000004000000020c1800002)

def q27 : W := (0x200803f8000010000000004400000000210440000000400000002081040002,0x200803f8000010000000004400000000210440000000400000002081040002)

def q28 : W := (0xf05deaf840bc3889623dfffc2295f606bdd7e087078e450e248562fdd40286003c0fffffc2bcf889673dfffc23bff6cfbdffe087078e670e2f8df2fdfc0387,0xcc5215078200c00005000000012a00c900280000000022000b089000280101)

def q29 : W := (0x40000000000000002000040000103200800080000002000000004004000000000008040000104000600004800030364180098000000600000000c00c080000,0x40080400001040004000008000200441000900000004000000008008080000)

def q30 : W := (0x15c020100080f3c18868461c80c4b0ffd5c2298109098681364094c50e281090ffe40fffffcbf3f18a79461dcccdb2ffffe73fc30909afe336c3bdff9f3c31b7,0xea242fefff4b0030021100014c0902002a251642000029620083293a91142127)

def q31 : W := (0x8000000000b00000000418800080c404000100000000000000040008000000002400000000b01000000418c00180c60c0101c00000000000000c000d000000,0xa40000000000100000000040010002080100c0000000000000080005000000)

def q32 : W := (0x6ac040201000bc3e9b609c7de30b91f62c8583e03131a601c6a0ac481d8000a0fffff807ffc3bd7e9be19c7df70ff3f77da7cfe03131b663c6f3befc9fcc01bb,0x953fb827efc30140008100001404620151224c0000001062005312b4824c011b)

def q33 : W := (0xc000000500480018000008000020080000000000000000000000020100800001c000000f00da001c0000180000601800080000000,0x201008000010000000a009200040000100000401000080000000)

def q34 : W := (0x3c000402000bc388860e43c816091f63fb003e0411b86095e01844ecc00448000240807ffd6be789c61e47ec7f1b3fe7ff90fe4413fc67bff03ccffed0ccdc3,0x3e40847dfd60240140100424691220840490c0400244072a10248b1210c8943)

def q35 : W := (0x28050800004000001b2000da10c000100000300018cf000000180,0x28050800004000001b2000da10c000100000300018cf000000180)

def q36 : W := (0xcc080804100fffba860ee9c83fffef63ffffd885b41861f0601fff00c01018000240807ffe2ffffe861ff9cc7fffef67ffffdd87fc1867f0603fff08d0f0183,0xce48887bee200044001110044000000400000502480006000020000810e0003)

def q37 : W := (0xb00088600000000090a600000000000000010400000000000000000000000000b040886100000001b2f640000000000000030602000000000000,0x40000100000001225040000000000000020202000000000000)

def q38 : W := (0x30c100000200f3c7fefd041c829dfaffc480019f01018613a7da84400c00088000240807ffc6f7d7ffff041cc7ffffffcda10ddf8101867fffff8cf08d0c0f83,0x30e50807fdc60410010200004562050009210c408000006c582508b0810c0703)

def q39 : W := (0xb000884004108000000000000000010104000000000000000000000000000000b0008861041cc400000000000000010186600000000000000000,0x21000c4400000000000000000082600000000000000000)

def q40 : W := (0x40c201008400b004dff7155ffc0090f604800196a5a5ff61060084400c02a08000240807fffaf857fffffffffc01b2f64da10ddfffffffe306038cf08d0ff183,0x40e609077bfa48532008eaa00001220049210c495a5a0082000308b0810d5103)

def q41 : W := (0x240807ffc00050000100004400020040210c400000006000020030810c0003,0x240807ffc00050000100004400020040210c400000006000020030810c0003)

def q42 : W := (0xff8000000a0000000010800000082043200000008000000010210300004,0xff8000000a0000000010800000082043200000008000000010210300004)

def q43 : W := (0x15707dfaf8c04ff9012a7be77ce6353bd3fffee18e0e0ac4386411e7f7fc1216fff80ffff8095ff9037e7be7fcee3d3ff3ffffe38e0e2fc438ec31effffc3236,0xea88720500c91000025400008008080420000102000025000088200808002020)

def q44 : W := (0x402010000c380100186160020100000582600000000000200000118000000038000000000c3801001861700201000005c260000000000020000011c00000,0x38402010000000000000001000000000004000000000000000000000400000)

def q45 : W := (0x6ab05deaf840bc3e1302bdfbff2b85c42e3dd760b6362844c8a42d2af9d40226fffffffbf801bdbe1386bdfbff2fcdc7be3ff7e0b6363844c8fc3f2efff4023e,0x954fa21100410180008400000004480390022080000010000058120406200018)

def q46 : W := (0x4020000c380000202000200100023002600002000008000002c00000000000000000000c380000206200200100023802600006000008000002e0000000,0x4020000000000000420000000000080000000400000000000020000000)

def q47 : W := (0x3305deaf8400c380102f9ef7d6205503fbdd7e0c61e884c5a25812ef1d4460600380ffbf8142eb81d06f9ff7ff20df8bffdf7e4c63fc85cff2dc12ff1f4ce46,0x3085211005422801c040010029008a88040200400214010a508400100208840)

def q48 : W := (0x8040000c380000288000220400023dd4000200000400000120000000000000000000000cb80000398000220c00023df400060000040000012000000000,0x8040000080000011000000080000002000040000000000000000000000)

def q49 : W := (0xc30ddeaf9404ffb2102fbe37fff6f003b7ffe68de46085e08257bb2f1d5030600380ffbf822cfffe106ffe37fffff00bffffe78ffc6085f082dfff2f1f70386,0xc08d21101628004c00404000000900084800010218000010008844000220080)

def q50 : W := (0x4800106000000220d008000000080000004082c000000000200,0x4800106000000220d008000000080000004082c000000000200)

def q51 : W := (0x30315deafa40ffffffff39e37ebfffafc23dd67f86060857adfe0122f1d40a0600380ffbf804ffffffff39e37fffffffc23df67f8606085ffffe0122f1f40e06,0x3009521102440000000000000140005000002000000000085200000000200400)

def q52 : W := (0x10080000000010211437c000000000000008404084000000000000000000000000000000800010639e37c00000000000000860608400000000000000000,0x10080000800000428a00000000000000000020200000000000000000000)

def q53 : W := (0x40325deafc40bc3cdfd73df3fc220500023dd676a7a77d6408240122f1d6a20600380ffbf838fcbffffffffffc220d00823df67fffffffe4082c0122f1f7f206,0x400a5211047840832028c20c0000080080002009585882800008000000215000)

def q54 : W := (0xffc000000001112002000001800c0007300603800000200000c0300c1e000030,0xffc000000001112002000001800c0007300603800000200000c0300c1e000030)

def q55 : W := (0x7fc060301080ffff1328de7de3cfb1fffdc7abe138382280f0e03ccd1fa81030fffffffc0009ffff13f8de7dfbcff1ffffc7fbe338383f80f0f03fcf1ff8303c,0x803f9fcc1089000000d00000180040000200500200001d00001003020050200c)

def q56 : W := (0x10000000000000000004004004000101180008000080000100000040000000000000000000002200000400400c0003833c00380000800003000000f00000000,0x100000000000220000000000080002822400300000000002000000b00000000)

def q57 : W := (0x1740205020804ff90028e22c01e4317bfff22be1481a82887a4190cfc6285410ffc00ffc001d7ff91e78e27f8bfc31fffffe3be7483fef98ffc1f1cffe38fc74,0xe8802fac209d30001e5000538a180084000c100600256d10858061003810a864)

def q58 : W := (0x4000000000043c10000420000c420001142280008000000000010800000000000000000000043e10000420000cc300033c6380008000000000031c000000000,0x400000000000020000000000008100022841000000000000000214000000000)

def q59 : W := (0x1d40a09041804ffb2028ea8403ff7e3bfbfffc895a48029e30417bf506291110ffc00ffc002bdfffe278ff858bfffe3fffffff9b7fc82f9f30c1ffff1e3b31b4,0xe280af6c41ab9004c2501501880080040400031225802d010080840a181220a4)

def q60 : W := (0x10000000000043c1002800000084302bc000000100000000204000000000000000000000000053c10278000000cc303fc00000030000000030c0000000000000,0x1000000000001000025000000048001400000002000000001080000000000000)

def q61 : W := (0x354120100280f3c7fefd420402ddfabfd1c2289f08080293b5da10c506281810ffc00ffc000df7e7ffff42058bfffffff3c63b9f88082f9ffffe31cf1e383e34,0xca812fec028d042001020001892205402204130080002d0c4a24210a18102624)

def q62 : W := (0x8500102784205880000000000000308082f800000000000003000,0x8500102784205880000000000000308082f800000000000003000)

def q63 : W := (0x554221108480f3c5dfff5757fcc4303bd1c22897adad7fe0304010c5062ab010ffc00ffc0039fbe7fffffffffccc303ff3c63b9fffffffe030c031cf1e3bf034,0xaa822eec84b908222000a8a80008000422041308525280000080210a18114024)

def q64 : W := (0x2010008043c00008020000000009c042280000000080000000010228000080000ffc000043e00018020108000009c2463a00000009800000010312380004,0x80002fec00800020001000010800000002041200000009000000010210100004)

def q65 : W := (0x957fffffffc04ff965bf7be77cf67f3bd3fffee18ece5be4397e53f7f7fc125fffffffffffc95ff967ff7be7fcfe7f3ff3ffffe38ece7fe439fe73fffffc327f,0x6a80000000091000024000008008000420000102000024000080200808002020)

def q66 : W := (0x200000000000c3800008028010001402c0003600010000040000008000000000000000000002c3810008078030001c03c0003e000300000c000000c00000000,0x200000000002000100000500200008010000080002000008000000400000000)

def q67 : W := (0x6b8040603000bc3e1300fc7de36b81d43fb583e0703aa008daa1ac0ed9804420fffff0000015bf3e1f80fc7ff3ffc1ff3fffc3e4703ff018fff1fe0fffc0cc78,0x947fb060301503000c8000021094402b004a4004000550102550520126408858)

def q68 : W := (0x800000000000c3a00008800030b0000280580001000000000002800000000000000000000008d3e00009c00030fc0003c07c0003000000000003e0000000000,0x800000000008104000014000004c00014024000200000000000160000000000)

def q69 : W := (0x6e80c0a05100ffff3300fef9e3ffefc43f7fff687a70201ec0a17fb819810120fffff0000023fffff380fff9f3ffffc73ffffff87ff0301fc0f1fffc1fc301b8,0x917f30a051230000c08001001000100300800090058010010050804406420098)

def q70 : W := (0x200000000000b006120000000209808400000000000000008080000000000000000000000000b50613800000030fc1c70000000000000000c0f0000000000000,0x2000000000000500018000000106414300000000000000004070000000000000)

def q71 : W := (0x7a8140201200fffffffd9c79e39ffbefec05837f30302013e5fa2c0819800820fffff0000005ffffffff9c79f3fffffffc07c3ffb030301ffffe3e0c1fc00e38,0x857eb020120500000002000010600410100240808000100c1a04120406400618)

def q72 : W := (0x400000000000b00413001451e000000000000000202020000000000000000000000000000000b80613809c79f000000000000000303030000000000000000000,0x4000000000000802008088281000000000000000101010000000000000000000)

def q73 : W := (0x6a8241209400bc3edfd79d7bff0b81c42c058376b5b57d60c0a02c081982a020fffff0000039fd3fffffffffff0fc1c73c07c3ffffffffe0c0f03e0c1fc3f038,0x957db120943941012028628400044003100240894a4a82800050120406415018)

def q74 : W := (0x402010000c38010018616002010000058260000000000020000011800000803ff00000000d3801801861700241010007c260000010000030020013c00008,0x803fb02010000100008000001000400100024000000010000010020002400008)

def q75 : W := (0xeabfffffffc0fffe779fbffbff3bcfcdee7fff60b6f679e4c9be6f3bfbfc026fffffffffffc1fffe779fbffbff3fcfcffe7fffe0b6f679e4c9fe7f3ffffc027f,0x1540000000010000000000000004000210000080000000000040100404000010)

def q76 : W := (0xc380000e000016000003b3000004000000800010000000000000000000000000e380000e00003f000003ff80000400000180001c00000000000,0x200000000000290000004c80000000000100000c00000000000)

def q77 : W := (0xf0080c061004ffb2000eaac03ff6f503fffffe85a5a801e5a01fbbec0014500000000000036effffc00fffe03fffff83ffffffc7fffc01fff01ffffe003cdc0,0xf0080c06136a004dc001552000090a80000001425a54001a5000441200288c0)

def q78 : W := (0x426001c00000003f001f80000000400000018ff00000000000c00,0x426001c00000003f001f80000000400000018ff00000000000c00)

def q79 : W := (0x330100402200fffffefde02c03fdfbffffb003ff401a801bffdb800ec0004c00000000000014ffffffffe07e03fffffffff803ffc03fc01fffffc00fe000ce40,0x3301004022140000010200520002040000480000802540040024400120008240)

def q80 : W := (0x1028001c00e07e0000000000000004403fc000000000000000c000,0x1028001c00e07e0000000000000004403fc000000000000000c000)

def q81 : W := (0x43020140a400bc3cdfd7f57ffd6001503fb003f6e5bffd685a01800ec002e40000000000003cfe3ffffffffffff001f83ff803fffffffff8ff01c00fe003fc40,0x43020140a43c420320280a80029000a8004800091a400290a500400120011840)

def q82 : W := (0x4020000c380000202000200100023002600002000008000002c00000000000000000000e380400206200300108027802600006400009004003e0000040,0x4020000200040000420010000800480000000440000100400120000040)

def q83 : W := (0x833fffffffc04ff8659ffbef7d724f59ffffffe0c6ded9ec5b3fc33ff3fc464f803fffffffd46ff87d9ffbff7ff24ff9ffffffe4c6ffd9fcff3fc33ff3fcce4f,0x30000000014200018000010028000a00000000400210010a400000000008800)

def q84 : W := (0x43c320000000029d6a0000000008000000120000000000000000000000000000c7c7e000000003fffe00000000180000001f0000000000000000,0x8404c000000001629400000000100000000d0000000000000000)

def q85 : W := (0x3c0180804300fffffefdea8003fffeaffb7ffc1f5a40001fa5db7bb000010900000000000026ffffffffff8003fffffffffffc1fffc0001ffffffff000030f80,0x3c01808043260000010215000000015004800000a58000005a24844000020680)

def q86 : W := (0x20c807e000ff8000000000000000187fc000000000000000030000,0x20c807e000ff8000000000000000187fc000000000000000030000)

def q87 : W := (0x4c028180c500ffffffd7ffd3ffff6e003b7ffc1effe57d7e00017bb00003a10000000000003afffffffffffffffffe003ffffc1fffffffff0001fff00003f180,0x4c028180c53a00000028002c0000900004800001001a82810000844000005080)

def q88 : W := (0x808041004ff820002a8000324e00027ffc000240000400004330000000000000000000004ff860003b8000324e00027ffc0006c000040000433000000000,0x808041000000400011000000000000000000048000000000000000000000)

def q89 : W := (0x8c3fffffffc04ffb659ffbe37fff6f09fb7ffe68dec659fe093f7bb3f3fd034f803fffffffe2cfffe59fffe37fffff09fffffe78ffc659ff093ffff3f3ff03cf,0xc00000000228004800004000000900004800010210000010000844000020080)

def q90 : W := (0xb004ded500000000000000000016000000000000000000000000000000000000f007ffff0000000000000000001f800000000000000000000000,0x4003212a00000000000000000009800000000000000000000000)

def q91 : W := (0x700301008600f3c7ffff1553fe9dfaafc000001fa5a57d73a5da00000002a80000000000003cffc7ffffffffffffffffc000001ffffffffffffe00000003fe00,0x70030100863c0c000000eaac01620550000000005a5a828c5a24000000015600)

def q92 : W := (0x10000020043c0649d000000104a09c000000000000000011a00000000000000000000000047c0659f000000324f09c000000080000004093e000000000200,0x1000002000400010200000022050000000000800000040824000000000200)

def q93 : W := (0xb03fffffffc0ffffffff3be37ebfffafc27ffe7f86c659f7adfe4333f3fc0a4f803fffffffc4ffffffff3be37fffffffc27ffe7f86c659fffffe4333f3fc0e4f,0x3000000000040000000000000140005000000000000000085200000000000400)

def q94 : W := (0x2010084000000459711437c000000000000008484596000000000000000000000000000004800659f3be37c0000000000000086c659e00000000000000000,0x201008400480020082aa00000000000000000024200800000000000000000)

def q95 : W := (0xc03fffffffc0fffcffdf3ff3fc324f09c27ffe76a7e77de4093e4333f3fea24f803ffffffff8fffffffffffffc324f09c27ffe7fffffffe4093e4333f3fff24f,0x40000000003800030020c00c0000000000000009581882000000000000015000)

def q96 : W := (0x100808400000000201821c000400000854000000000000040000205400000018060300000088000601823c000c008018f42000000000000c000060f40000,0x18160b0840008800040000200008008010a020000000000008000040a00000)

def q97 : W := (0x300000000000000000400000000000400000000000000000000040000,0x300000000000000000400000000000400000000000000000000040000)

def q98 : W := (0xc010080840b0008862059e9c0094f60488558001018601060484402c540080003c0e07ffc2b0d88867059efc01bef6cdb9fde001018663060f8cf0edfc0183,0xfc1e0ff78200d80005000060012a00c931a86000000062000b08b0c1a80103)

def q99 : W := (0x60000000080000000000800000080003000000000000000000000300000,0x60000000080000000000800000080003000000000000000000000300000)

def q100 : W := (0x1540301808c043c1002a43861cc4343bd1ca7c8108080280304410c5267c1010ffd80fff000953e9027e4387bccc3c3ff3deffa308082f8030cc31cf7efc3034,0xea983fe708c9102802540001a00808042214832200002d000088210a58802024)

def q101 : W := (0x1800000000000800000000300000000000c020000000000000000000c00000,0x1800000000000800000000300000000000c020000000000000000000c00000)

def q102 : W := (0x6a8050281840bc3e13029dfbff0b85c42c0dd76030302000c0a42c0839d40020fffff6030001bdbe13869dfbff0fcdc7bc1ff7e030303000c0fc3e0c7ff40038,0x957fa62b18410180008400000004480390122080000010000058120446200018)

def q103 : W := (0x8000000020000000000180020000000000000000060000000,0x8000000020000000000180020000000000000000060000000)

def q104 : W := (0x300104828400c380002e1ae1d6005503fb857e0401a80085a05800ee05444000018060300142eb81c06e1fe3ff00df8bff8f7e4403fc018ff0dc00fe0f4cc40,0x318164b285422801c040050229008a88040a00400254010a508400100a08840)

def q105 : W := (0x80000004000008540000000000000000000000000000000000000000880000018000000c000018f400000000000000000000000000,0x8800000100000008000010a000000000000000000000000000)

def q106 : W := (0xc00908849404ffb2002eb821fff6e003b7ffc085a40001e00057bb020550100001806030022cfffe006ff823ffffe00bffffc387fc0001f000dfff060f70180,0xc18968b49628004c00414002000900084800030258000010008844040a20080)

def q107 : W := (0x800006000000000c008000000000000000000c000000000000,0x800006000000000c008000000000000000000c000000000000)

def q108 : W := (0x300110080a40f3c7feff01821e9dfeafc008541f00000013a5de000020540800001806030004f7cfffff01823fffffffc018f43f8000001ffffe000060f40e00,0x3019160b0a44040801000000216201500010a0208000000c5a20000040a00600)

def q109 : W := (0x201021c000000000000000000000000000000000000000000000000000000000601823c00000000000000000000000000000000000000,0x400802000000000000000000000000000000000000000)

def q110 : W := (0x400211088c40b004dfd715d3fc00040000085416a5a57d60000400002056a000001806030038f88ffffffffffc000c008018f43fffffffe0000c000060f7f000,0x401a170b8c78488b2028ea2c000008008010a0295a5a82800008000040a15000)

def q111 : W := (0x2010008043c00008020000000009c042280000000080000000010228000080000604000043c00018020008000009c0423800000001800000000102380000,0x8000261400800000001000000800000000001000000001000000000000100000)

def q112 : W := (0x954fb21d0fc043c164bf43861cd47e3bd1ca7c8108c853a0315e52d5267c1059ffdfffff07c953e966ff4387bcdc7e3ff3deffa308c87fa031de73df7efc307d,0x6a904de20809102802400001a00800042214832200002c000080210a58802024)

def q113 : W := (0x801ff0000000010800800000300040010002c020000010000010020002c00008,0x801ff0000000010800800000300040010002c020000010000010020002c00008)

def q114 : W := (0xea8ff23d1fc0fffe779f9ffbff1bcfcdec4fff6030f071a0c1be6e193bfc0069fffff60707c1fffe779f9ffbff1fcfcffc5fffe030f071a0c1fe7e1d7ffc0079,0x1570043a18010000000000000004000210100080000000000040100444000010)

def q115 : W := (0x208040000020010000800580020000040000100400160000040,0x208040000020010000800580020000040000100400160000040)

def q116 : W := (0x830fb25d2fc04ff8649fe3ae1d704f59fffa7fe040dad1a85b1fc21fe27c4449801ff60707d46ff87c9fe3fe3ff04ff9fffaffe440ffd1b8ff1fc21fe2fccc49,0x310445a2814200018000050228000a00000800400250010a400000000808800)

def q117 : W := (0x8000010043c02000028000104e00004a7c0000400000000042100000000000000000000043c86000038000104e00005afc0000c000000000421000000000,0x800001000008400001000000000000108000008000000000000000000000)

def q118 : W := (0x8c0fb29d4fc04ffb649feb821fff6e09fb7ffc085ac051be011f7bb1227d0149801ff60707e2cfffe49fff823ffffe09fffffc387fc051bf011ffff162ff01c9,0xc10449a48228004800014002000900004800030250000010000844040820080)

def q119 : W := (0x10000020043c0649d000000104a09c000000000000000011a00000000000000000000000043c0649f000000104e09c000000000000000011e000000000000,0x1000002000000000200000000040000000000000000000004000000000000)

def q120 : W := (0xb00fb21d0fc0f3c7feff03821e9dfeafc04a7c1f00c051b3a5de4211227c0849801ff60707c4f7cfffff03823fffffffc05afc3f80c051bffffe421162fc0e49,0x3010441a080404080100000021620150001080208000000c5a20000040800600)

def q121 : W := (0x2000004000000449701021c000000000000000080512000000000000000000000000000004000649f03823c0000000000000000c051a00000000000000000,0x2000004004000200802802000000000000000004000800000000000000000)

def q122 : W := (0xc00fb31d8fc0f3c4ffdf17d3fc104e09c04a7c16a5e57de0011e4211227ea049801ff60707f8fbcffffffffffc104e09c05afc3fffffffe0011e421162fff049,0x4010451a8838080b0020e82c00000000001080295a1a82000000000040815000)

def q123 : W := (0x100808400000000201821c0004000008540000000000000400002054000000180ffb000000a8000601833c000c00821cf62000000800000c010270f40004,0x181ff3084000a800040001200008008214a220000008000008010250a00004)

def q124 : W := (0x400000000000000020000400001032008000800000020000000040040000000004080707c01040006100048400323641800d8000000620000200d00c0c0001,0x44080707c01040004100008400220441000d000000042000020090080c0001)

def q125 : W := (0xffdff0000001112802800001b00c40073006c3a00000300000d0320c1ec00038,0xffdff0000001112802800001b00c40073006c3a00000300000d0320c1ec00038)

def q126 : W := (0xffcff23d1fc0ffff77bfdfffffdffffffdcfffe138f873a0f1fe7edd3ffc1079ffffffff07c9ffff77ffdfffffdfffffffdfffe338f87fa0f1fe7fdf7ffc307d,0x300dc21809000000400000000000000210000200000c000000010240002004)

def q127 : W := (0x10000000000000000004004004000101180008000080000100000040000000000000000000002280400400600d0003833d803a0000840003100400f60000040,0x100000000000228040000020090002822580320000040002100400b60000040)

def q128 : W := (0x974fb25d2fc04ff964bfe3ae1df47f7bfffa7fe148dad3a87b5fd2dfe67c5459ffdfffff07dd7ff97effe3ffbffc7ffffffeffe748ffffb8ffdff3dffefcfc7d,0x68904da2281d30001a400051a20800840004800600252c10848021001880a824)

def q129 : W := (0x4008000010043c12000428000d46e00114a7c0008400000000052900000000000000000000043e96000438000dc7e0033defc0008c00000000073d000000000,0x400800001000028400001000008100022948000008000000000214000000000)

def q130 : W := (0x9d4fb29d4fc04ffb64bfeb861fff7e3bfbfffc895ac853be315f7bf5267d1159ffdfffff07ebdfffe6ffff87bffffe3fffffffbb7fc87fbf31dfffff7eff31fd,0x62904d62482b900482401401a00080040400033225002c010080840a588220a4)

def q131 : W := (0x10010000020043c164bd000000947a2bc000000100000000215a00000000000000000000000053c166ff000000dc7e3fc00000030000000031de000000000000,0x1001000002001000024200000048041400000002000000001084000000000000)

def q132 : W := (0xb54fb21d0fc0f3c7feff43861eddfebfd1ca7c9f08c853b3b5de52d5267c1859ffdfffff07cdf7efffff4387bffffffff3deffbf88c87fbffffe73df7efc3e7d,0x4a904de2080d042801000001a12201402214832080002c0c4a20210a58802624)

def q133 : W := (0x2000004000000449701021c00000000000000008051200000000000000000000000000008500166ff4387bc0000000000000308c87fa00000000000003000,0x200000408500122684285a00000000000000308482e800000000000003000)

def q134 : W := (0xd54fb31d8fc0f3c5ffff57d7fcd47e3bd1ca7c97aded7fe0315e52d5267eb059ffdfffff07f9fbeffffffffffcdc7e3ff3deffbfffffffe031de73df7efff07d,0x2a904ce28839082a0000a8280008000422148328521280000080210a58814024)

def q135 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049801fffff07c043e8649f03833c104e09c25efe2000c059a0011e431372fc004d,0x104de208000028000000012000000002148220000008000000010250800004)

def q136 : W := (0x8000000000000100000000000000000100020000000000000000000002000000,0x8000000000000100000000000000000100020000000000000000000002000000)

def q137 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffdffffc000953e902f84205b8cc703ff3c6fba308083f8030d033cf1ef8303c,0xea9fdfec0089102802d00001b80840042204d32200003d000090230a18d0202c)

def q138 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d40206803ffffbf8000db8018639e37c224d01823ff66086061844083c0322f3f4020e,0x800fa21100400180008400000000480180022000000010000018020002200008)

def q139 : W := (0x4000000000000000000000000000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000000000000000000000)

def q140 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c000080803ff807ffc2b15888e1041cf401f2f74da3cde00101966306138ef08fcc018b,0x80fff807ffc2015800810000740162014923cc600000106200130ab083cc010b)

def q141 : W := (0x8000000000000000000000020000000000000000000000000,0x8000000000000000000000020000000000000000000000000)

def q142 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec0004400801ff00000142f381c80e07e33f041f93ffac3e4403fd018ff11c20fe2c0cc48,0x831ff040201423001c800052329040a9004ac00400255010a510420122c08848)

def q143 : W := (0x10800000000000040000002c000000000000000020000000000,0x10800000000000040000002c000000000000000020000000000)

def q144 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100801ff0000022cfffe080ff8033fffe013ffffc387fc0101f0011fff002c30188,0x8c1f708041228004c08015003000900104800030258010010010844002c20088)

def q145 : W := (0x100008000000000400100000000000000000010000000000000,0x100008000000000400100000000000000000010000000000000)

def q146 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da000000000800801ff0000004f7cfffff000033ffffffc002c03f8000101ffffe020002c00e08,0xb01ef0000204040801020000316205500002c0208000100c5a24020002c00608)

def q147 : W := (0x8000003000000000000000000010000000000000000000,0x8000003000000000000000000010000000000000000000)

def q148 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a000801ff0000038f90ffffffffffc0040010002c03fffffffe00010020002c3f008,0xc01df1008438490b2028eaac000040010002c0295a5a82800010020002c15008)

def q149 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff0000001bf3e17809c7bf31fc1cf3c5fc3e030307000c1f07e0d7fc00078,0x957fb02010010300048000021014400b105a4080000050000150520566400058)

def q150 : W := (0x200000000000000000800400000000000000000000100000000,0x200000000000000000800400000000000000000000100000000)

def q151 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffc00ffc000953e90678420788dc303ff3de3ba308086f8031c071cf7e383074,0xea802fec008910280650000388180004221c132200006d000180610a78102064)

def q152 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d4020600380ffbf8000eb8050639e37c320d08827df66086064844092c4123f1f40246,0x8521100400280040400000010080880402000000040000108400100200040)

def q153 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240807ffc2b2588c61041ec411b2fe4df90de00101c6630703ccf1ed0c01c3,0xe40807ffc20258040100024411220849790c6000004062010348b1e10c0143)

def q154 : W := (0x208000000000010000000580000000000000000400000000000,0x208000000000010000000580000000000000000400000000000)

def q155 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100000000000022cfffe400ff8203fffe083ffffc387fc0401f0101fff1600301c0,0xc00808041228004c400150200009008048000302580400101008441600200c0)

def q156 : W := (0x200040000000010000800000000000000000100000000000000,0x200040000000010000800000000000000000100000000000000)

def q157 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da000000000800000000000004f7cfffff000203ffffffc058003f8000401ffffe400160000e40,0x30010000020404080102000201620550005800208000400c5a24400160000640)

def q158 : W := (0x40000020000000000000000000040000000000000000000,0x40000020000000000000000000040000000000000000000)

def q159 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a000000000000038fa0ffffffffffc1000080058003fffffffe0010040016003f040,0x4002010084384a0b2028eaac00100008005800295a5a82800100400160015040)

def q160 : W := (0x8000010043c320000280029d6e00004a7c08004000120000421000000000000000000000c7cfe000038003fffe00005afc1800c0001f0000421000000000,0x80000100840cc000010001629000001080100080000d0000000000000000)

def q161 : W := (0xbc0fb29d4fc0fffffeffeb821ffffeaffb7ffc1f5ac051bfa5df7bb1227d0949801ff60707e6ffffffffff823ffffffffffffc3fffc051bffffffff162ff0fc9,0x3c10449a48260000010014002000015004800020a50000005a20844040820680)

def q162 : W := (0x426081c00000203f001f80058002400004018ff00400160000c40,0x426081c00000203f001f80058002400004018ff00400160000c40)

def q163 : W := (0xb30fb25d2fc0fffffeffe3ae1ffdfffffffa7fff40dad1bbffdfc21fe27c4c49801ff60707d4ffffffffe3fe3ffffffffffaffffc0ffd1bfffffc21fe2fcce49,0x3310445a28140000010000502002000000008000802500040020000000808200)

def q164 : W := (0x200000000000b006120000000209808400000000000000008080000000000000801ff0000000b50e13800000330fc1c70002c02000001000c0f0020002c00008,0xa01ff0000000050801800000310641430002c020000010004070020002c00008)

def q165 : W := (0xfa8ff23d1fc0ffffffff9ffbff9fffefec4fff7f30f071b3e5fe6e193bfc0869fffff60707c5ffffffff9ffbfffffffffc5fffffb0f071bffffe7e1d7ffc0e79,0x570043a180500000000000000600010101000808000000c1a00100444000610)

def q166 : W := (0x10002010008043c1002802000084302bc042280100000080204000010228000080000604000053c10278020008cc303fc04238030000018030c0000102380000,0x9000261400801000025000000848001400001002000001001080000000100000)

def q167 : W := (0x100808400000000201821c000400000854000000000000040000205400000018060300000488010601823c220d008018f42080000004082c000060f40200,0x18160b0840048801040000202209008010a020800000040828000040a00200)

def q168 : W := (0xb00088600000000090a6000000000000000104000000000000000004000707c0b040886100000401b2f640000c000000002306020010000c0001,0x4000707c00040000100000401225040000c000000002202020010000c0001)

def q169 : W := (0x200000400b004ded701021c00000000000016008051200000000000000000000000000000f007ffff03823c0000000000001f80c051a00000000000000000,0x2000004004003212802802000000000000009804000800000000000000000)

def q170 : W := (0xf00fb31d8fc0f3c7ffff17d3fe9dfeafc04a7c1fa5e57df3a5de4211227ea849801ff60707fcffcfffffffffffffffffc05afc3ffffffffffffe421162fffe49,0x7010451a883c0c080000e82c01620150001080205a1a820c5a20000040815600)

def q171 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049801ff60707c047c8659f03823c324f09c05afc2080c051a4093e421162fc0249,0x10441a08000408010000002022010000108020800000040820000040800200)

def q172 : W := (0x100808400000000201821c00040000085400000000000004000020540000001c060707c000c8000701823c000e00c018fc2000000020000e001060fc0001,0x1c160f0f8000c80005000020000a00c010a82000000020000a001040a80001)

def q173 : W := (0x4000000000000000200004000010320080008000000200000000400400000000000ffc000010e00060000588003036c3843b8000000e00000001c21c380004,0x400ffc000010e00040000188002004c3043b0000000c000000018218380004)

def q174 : W := (0x15f07dfaf8c0fff9896a7ffffce6b5ffd7ffffe18f0f8ec53e6495e7fffc1296fffc0fffffcbfff98b7f7ffffcefbfffffffffe38f0fafe73eefbdfffffc33b7,0xea0c7205070b00000215000000090a002800000200002122008b281800002121)

def q175 : W := (0x8040201000bc3801001c79e00281c404058360000000000020040019800000003c00000000bc3801001c79f00381c60c05c3e00000000000200c001dc00000,0xbc402010000000000000001001000208004080000000000000080004400000)

def q176 : W := (0x6af05deaf840bc3e9b62bdffff2b95f62ebdd7e0b737ae45cea4ad6afdd402a6ffffffffffc3bdfe9be7bdffff2ffff7ffbfffe0b737be67ceffbffefffc03bf,0x950fa215078301c00085000000046a01d102280000001022005b129402280119)

def q177 : W := (0x4020000c380000202c0020015006b003e0000280000a008002c00000000000000000002c380800207e002001f00fb803e0000780000e018002e0000000,0x402000200008000052000000a009080000000500000401000020000000)

def q178 : W := (0x3f05deaf840bc388962fdfffd6295f63fbdd7e0c71f8e4d5e25856efdd44686003c0fffffd6bef89d67fdfffff3bffefffdffe4c73fce7fff2fcdfffdfccfc7,0x3cc5215079602c01405000002912a08c040280400204032a10a489100288941)

def q179 : W := (0x8040000c380000288000220400023dd4000200000400000120000000000000000000028cf880003d800023be000fbdfc000700000700018df000000180,0x80400280c0800015000001ba000d8028000500000300018cd000000180)

def q180 : W := (0xcf0ddeaf940fffba962fffffffffff63fffffe8df478e5f0e25fff2fdd50386003c0fffffe2ffffe967fffffffffff6fffffff8ffc78e7f0e2ffff2fdff0387,0xcccd21506a200044005000000000000c000001020800020000a0000002a0001)

def q181 : W := (0xb00088600000000090a600000000000000010400000000000000000000000000b4c0896700000023bff6c0000000800000070e2e000000000200,0x4c00107000000232f50c0000000800000060a2e000000000200)

def q182 : W := (0x30f15deafa40ffffffff3dfffebfffffc6bdd7ff87078e57affe8562fdd40a86003c0fffffc6ffffffff3dffffffffffcfbdffff87078e7fffff8df2fdfc0f87,0x30cd521505860000000000000140000009002800000000285001089000280501)

def q183 : W := (0x1008000b00089421553fc0000000000000085050c400000000000000000000000000000b80089673dfffc0000000000000087078e600000000000000000,0x10080000800002528ac0000000000000000020282200000000000000000)

def q184 : W := (0x40f25deafc40bc3cdff73dfffc2295f606bdd7f6a7a7ff650e248562fdd6a286003c0ffffffafcfffffffffffc23bff6cfbdffffffffffe70e2f8df2fdfff387,0x40ce521503ba40c32008c20000012a00c900280958580082000b089000295101)

def q185 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d40206003c0fffffc00cf8010739e37c220f00c23dfe6086060864082e0132f1fc0207,0xc5215078000c00005000000000a00c000280000000020000a001000280001)

def q186 : W := (0x100004400000000000000000000600000000000000000,0x100004400000000000000000000600000000000000000)

def q187 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a00000240807fff8f857fffffffffc00020040210c5fffffffe000020030810ff003,0x402609077bf848532028eaac0000020040210c495a5a828000020030810d5003)

def q188 : W := (0x40000100000000020040000000000000000002000000000000,0x40000100000000020040000000000000000002000000000000)

def q189 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da00000000080000240807ffc4f7d7ffff000047ffffffc0210c5f8000007ffffe0030810c0e03,0x30250807fdc40410010200004562055000210c408000006c5a240030810c0603)

def q190 : W := (0x50000000000000020000210c00000000000000003000000000,0x50000000000000020000210c00000000000000003000000000)

def q191 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb00001010000240807ffe2cfffe001ff8047fffe007ffffc587fc0007f0003fff0810f0183,0xc248887bee28004c001150044009000448000502580006100028440810e0083)

def q192 : W := (0x10000000000000000000200040000000000000000080000000,0x10000000000000000000200040000000000000000080000000)

def q193 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec000440000240807ffd42e781c01e07e47f003f87ff90fe4403fc078ff03c03fe10ccc43,0x3240847dfd422401c010052469002a840490c0400254070a5024031210c8843)

def q194 : W := (0x24000000000010000000004000000000010040000000000000000001000000,0x24000000000010000000004000000000010040000000000000000001000000)

def q195 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff807ffc1bd7e13819c79f70fc3c77c27cfe030303060c0f23e3c9fcc003b,0x957fb827efc10140008100001404420350224c800000106000521234864c001b)

def q196 : W := (0x80400000040000000000000000040000800000000000000000000080000,0x80400000040000000000000000040000800000000000000000000080000)

def q197 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffe40fffffc953f102794205cccc323ff3e73fc308082fe030c231ff9f3c3037,0xeaa42fefff49103002510001cc0802042225174200002d600082213a99142027)

def q198 : W := (0x80000000000000000000000000000000000000000000000000000000000,0x80000000000000000000000000000000000000000000000000000000000)

def q199 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240fffffc2b0f08861041dcc01b2f6cfa53fc001018e6306038df29d3c0187,0xe40fffffc200f0000100014c012200cb253e4000000862000309b2913c0107)

def q200 : W := (0x20000000010000000000040200000000000000000010000000,0x20000000010000000000040200000000000000000010000000)

def q201 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffffff80001bdbe13809c79fb0fc1c7be07f3e030303800c0f03f0e1ff0003c,0x957fbfd81001018000800000180440039202708000001800005013060670001c)

def q202 : W := (0x20000000000000000002000200000000000000000200000000,0x20000000000000000002000200000000000000000200000000)

def q203 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec000440000000ff800142eb81c00e07f0bf001f8bffc33e4403fc818ff01c10ff030cc44,0x3000fb8201422801c0000530a9000a8804c300400254810a500410130308844)

def q204 : W := (0xa0000000000000000002043000000000000000010000000000,0xa0000000000000000002043000000000000000010000000000)

def q205 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb00001010000000ff80022cfffe000ff810bfffe00bffffe187fc0081f0001fff210330184,0xc008f7841228004c00015010800900084800210258008010000844210320084)

def q206 : W := (0x80000000000000000080000000000000000000000000000000,0x80000000000000000080000000000000000000000000000000)

def q207 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da00000000080000000ff80004f7e7ffff00010bffffffc204321f8000081ffffe010210300e04,0x30010ff8020404200102000109620550020432008000080c5a24010210300604)

def q208 : W := (0x10800000000000000000008000000000000000000,0x10800000000000000000008000000000000000000)

def q209 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a00000000ff80038f8a7fffffffffc0000008204321fffffffe0000001021033f004,0x40020ef8843848a32028eaac00000000820432095a5a82800000010210315004)

def q210 : W := (0xffc00ff8000111a002000001880c0007b20633800000280000c0310e1e300034,0xffc00ff8000111a002000001880c0007b20633800000280000c0310e1e300034)

def q211 : W := (0x7ff07dfaf8c0ffff132affffffefb5ffffffffe1be3e2ac4f8e43deffffc1236fffffffff809ffff13feffffffeffdffffffffe3be3e3fc4f8fc3feffffc323e,0x800f820500c9000000d400000000480000000002000015000018020000002008)

def q212 : W := (0x8000000000b00000000418800080c40400010000000000000004000800000000240803f800b01000000418c40180c60c2105c00000004000000c208d040002,0xa40803f80000100000000044010002082104c0000000400000082085040002)

def q213 : W := (0x100808400000000201821c00040000085400000000000004000020540000801ff60300000188008601823c004c01801af42000001000001c020062f40008,0x801fe60b0840018800840000200048018012a020000010000018020042a00008)

def q214 : W := (0x200004020000c380000a028012001402e300360001200004800000ac00000000000000000002c381000a07a032001c03e3803e000360000c800000ee0000000,0x200004020002000100000520200008010080080002400008000000420000000)

def q215 : W := (0x6bb05deaf840bc3e1302fdffff6b85d43fbdd7e0f63ea84cdaa5ad2ef9d44626fffffffbf815bfbe1f86fdffffffcdffbffff7e4f63ff85cfffdff2ffff4ce7e,0x944fa211005503800c8400000094482b80422004000150102558520106208858)

def q216 : W := (0x800008040000c3a0000a880032b04002a3dd4001200000400002920000000000000000000008dbe0000bd80032fcc003e3ff4003600000400003f2000000000,0x800008040008184000015000004c80014022000240000000000160000000000)

def q217 : W := (0x6eb0ddeaf940ffff3302fffbffffefc43f7fff68fe76285ec8a57fbaf9d50326fffffffbf823fffff386fffbffffffc7bffffff8fff6385fc8fdfffefff703be,0x914f221101630000c08400000000100380800090018010010058804406220098)

def q218 : W := (0x200000000000b006120000000209808400000000000000008080000000000000000000000000b58613860000032fcdc78000000080000004c8fc000000000200,0x20000000000005800186000001264d438000000080000004487c000000000200)

def q219 : W := (0x7ab15deafa40ffffffffbdfbffbfffefee3dd77fb6362857edfe2d2af9d40a26fffffffbf805ffffffffbdfbfffffffffe3ff7ffb636385ffffe3f2efff40e3e,0x854ea21102450000000000000040001010022080000010081200120406200418)

def q220 : W := (0x400001008000b00413021553fc00000000000000a42428400000000000000000000000000000b8061386bdfbfc00000000000000b63638400000000000000000,0x40000100800008020084a8a80000000000000000121210000000000000000000)

def q221 : W := (0x6ab25deafc40bc3edfd7bdfbff2b85c42e3dd776b7b77d64c8a42d2af9d6a226fffffffbf839fdbfffffffffff2fcdc7be3ff7ffffffffe4c8fc3f2efff7f23e,0x954da21104794181202842040004480390022089484882800058120406215018)

def q222 : W := (0x200402010000c3801009869610201402c0583600010000040200008118000000038000000002c3811009879730201c03c05c3e000300000c020000c11c00000,0x238402010002000100000101200008010004080002000008000000400400000)

def q223 : W := (0x10000000000000000004004004000101180008000080000100000040000000000000ff8000002a00000400508c00038b3c43380000808003000010f10300004,0x1000ff8000002a00000000108800028a2443300000008002000010b10300004)

def q224 : W := (0x17707dfaf8c04ff9012afbef7de6357bffffffe1ce1e8acc7a6591eff7fc5616fff80ffff81d7ff91f7efbfffffe3dffffffffe7ce3fefdcffedf1effffcfe76,0xe888720500dd30001e540010821808840000000600216510858860000800a860)

def q225 : W := (0xc000000500480018000008000020080000000000000200803f80020100800001c440000f00da105c0000180400601802081040002,0x200803f800201008000010440000a009210440000100400401002081040002)

def q226 : W := (0x100808400000000201821c000400000854000000000000040000205400000018060300000288040601823c100c088058f42000004000010c400160f40040,0x18160b0840028804040000201008088050a020000040000108400140a00040)

def q227 : W := (0x8040000c380000e880016204003b3dd4004200000c00010120000000000000000000000eb80000f98003f20c003ffdf4004600001c0001c12000000000,0x8040000280000011000290080004c02000040000100000c00000000000)

def q228 : W := (0xf30ddeaf9404ffb2102fbef7fff6f503fffffe8de5e885e5a25fbbef1d5470600380ffbf836effffd06ffff7ffffff8bffffffcffffc85fff2dfffff1f7cfc6,0xf08d2110176a004dc040410000090a88000001421a14001a5080441002288c0)

def q229 : W := (0x426801d06000003f20df8800000048000001cff2c000000000e00,0x426801d06000003f20df8800000048000001cff2c000000000e00)

def q230 : W := (0x33315deafa40fffffffff9ef7fffffffffbdd7ffc61e885fffff812ef1d44e0600380ffbf814fffffffff9ff7ffffffffffdf7ffc63fc85fffffc12ff1f4ce46,0x3309521102540000000000100000000000402000002140000000400100208040)

def q231 : W := (0x10080000000010211437c0000000000000084040840000000000000000000000000001028001d06f9ff7c00000000000004c63fc840000000000000c000,0x100801028001c04e8bc0000000000000004423bc000000000000000c000)

def q232 : W := (0x43325deafc40bc3cdfd7fdfffd6205503fbdd7f6e7bffd6c5a25812ef1d6e60600380ffbf83cfebffffffffffff20df8bffdf7fffffffffcff2dc12ff1f7fe46,0x430a5211047c428320280200029008a88040200918400290a508400100211840)

def q233 : W := (0x4800000000000220c0000000000000000040000000000000000,0x4800000000000220c0000000000000000040000000000000000)

def q234 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100000000000022cfffe106ff8003ffff00bffffc18ffc0001f082dfff000030380,0xc00808041228004c10615000000910084800010a5800001082c844000020280)

def q235 : W := (0x400000000000020010000000000000000000800000000000000,0x400000000000020010000000000000000000800000000000000)

def q236 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec00044000000000000142eb81d06e07e03f20df8bff803e4c03fc01cff2dc00fe000ce40,0x3000040201422801d06005202920ca88048000480254014a52c400120008a40)

def q237 : W := (0x400010000000002010000000000000000000020000000000000,0x400010000000002010000000000000000000020000000000000)

def q238 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff0000001bdbe13869c79f32fcdc7bc07c3e0b0303004c8fc3e0c1fc00238,0x957fb020100101800086000010244c039002408080001004085c120406400218)

def q239 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffc00ffc000957e1037e420588ee3d3ff3c63b8388082f8438ec31cf1e383234,0xea802fec0089142003560001882a0d042204130280002d0408ac210a18102224)

def q240 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240807ffc2b4d08967041cc423bff6cda10dc0810186670e2f8cf08d0c0383,0xe40807ffc204d00107000044232f00c9210c4080000066082f08b0810c0303)

def q241 : W := (0x10600000000000000000000800000000000000000000000,0x10600000000000000000000800000000000000000000000)

def q242 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a000000000000038fc87fffffffffc220d008000001fffffffe4082c00000003f200,0x4002010084384c832028eaac00220d00800000095a5a8284082c000000015200)

def q243 : W := (0x4000000000043c32000420002dd6a0011422808080000120000108000000000000000000000c7e7e000420003fffe0033c638180800001f000031c000000000,0x400000000008424c000000001229400228410100000000d0000214000000000)

def q244 : W := (0x3d41a0904380fffffefdea8403fffebffbfffc9f5a48029fb5db7bf506291910ffc00ffc002fffffffffff858bffffffffffff9fffc82f9fffffffff1e3b3fb4,0xc281af6c43af0000010215018800014004000300a5802d004a24840a181226a4)

def q245 : W := (0x10000000000000000004004004000101180008000080000100000040000000000000000000426201c00400403f001f833c0038400080018ff00000f00000c00,0x1000000000426201c00000003b001e82240030400000018ef00000b00000c00)

def q246 : W := (0x374120502280fffffefde22c03fdfbfffff22bff481a829bffdb90cfc6285c10ffc00ffc001dffffffffe27f8bfffffffffe3bffc83fef9ffffff1cffe38fe74,0xc8812fac229d00000102005388020400000c100080256d04002461003810a264)

def q247 : W := (0x200000000000b006120000000209808400000000000000008080000000000000ffc000000001b52613800001830fc1c73006038000002000c0f0300c1e000030,0xdfc0000000010520018000018106414330060380000020004070300c1e000030)

def q248 : W := (0x7fc160301280fffffffdde7de3dffbfffdc7abff38382293f5fa3ccd1fa81830fffffffc000dffffffffde7dfbffffffffc7fbffb8383f9ffffe3fcf1ff83e3c,0x803e9fcc128d000000020000182004000200500080001d0c0a0403020050260c)

def q249 : W := (0xff8000004a00106000108220d008204320080000804082c010210300204,0xff8000004a00106000108220d008204320080000804082c010210300204)

def q250 : W := (0x35717dfafac0ffffffff7be77effffbfd3fffeff8e0e0ad7bdfe11e7f7fc1a16fff80ffff80dffffffff7be7fffffffff3ffffff8e0e2fdffffe31effffc3e36,0xca89720502cd0000000000008100004020000100000025084200200808002420)

def q251 : W := (0x4000000000b00088600004000090b600800080000002010400004004000000000008040000b040886100048001b2f64180098000000603060200c00c080000,0x40080400000040000100008001224041000900000004020202008008080000)

def q252 : W := (0x35c120100280f3c7fefd461c82ddfaffd5c2299f09098693b7da94c50e281890ffe40fffffcff7f7ffff461dcfffffffffe73fdf8909afffffffbdff9f3c3fb7,0xca252feffd4f0430010200014d2205002a2516408000296c4825293a91142727)

def q253 : W := (0x12010028043c0649d020000104a09c042280000000080011a00010228000080000604000043c0649f020008104e09c042380000000180011e000102380000,0x8001261402800000000200000800040000001000000001000004000000100000)

def q254 : W := (0xb004ded500000000000000000016000000000000000000000000000000000008f007ffff4205880000000000001f88082f800000000000003000,0x84003212a4205880000000000000988082f800000000000003000)

def q255 : W := (0x754321108680f3c7ffff5757feddfabfd1c2289fadad7ff3b5da10c5062ab810ffc00ffc003dffe7fffffffffffffffff3c63b9ffffffffffffe31cf1e3bfe34,0x8a832eec86bd0c200000a8a801220540220413005252800c4a24210a18114624)

def q256 : W := (0x12010028043c0649d020000104a09c042280000000080011a00010228000080000ffc000047e0659f020108324f09c2463a0080000984093e010312380204,0x80012fec02800420010200010822050002041200800009040824010210100204)

def q257 : W := (0xb57fffffffc0ffffffff7be77effffbfd3fffeff8ece5bf7bdfe53f7f7fc1a5fffffffffffcdffffffff7be7fffffffff3ffffff8ece7ffffffe73fffffc3e7f,0x4a800000000d0000000000008100004020000100000024084200200808002420)

def q258 : W := (0x100000000000000000040040040001011800080000800001000000400000000ffc00000000113200200400580cc003f33c603800008200030c0300f1e000030,0xfec000000001132002000001808c002f224603000000200020c0300b1e000030)

def q259 : W := (0x7fc060703080ffff1328fe7de3efb1fffff7abe1783aa288fae1bccfdfa85430fffffffc001dffff1ff8fe7ffbfff1fffffffbe7783fff98fff1ffcffff8fc7c,0x803f9f8c309d00000cd00002181040000008500600055d10051043002050a84c)

def q260 : W := (0x406030000c380100386160220100023582600002000008200002d18000000038000000000c380100386370220100023dc2600006000008200002f1c00000,0x38406030000000000000021000000000084000000400000000000020400000)

def q261 : W := (0x8000000000b0000000041c800080d404800180000080000200840008000000002400000000b0100800041cc00180f60da101c00001800006018c008d000000,0xa4000000000010080000004001002209210040000100000401080085000000)

def q262 : W := (0x6bc040603000bc3e9b60fc7de36b91f63fb583e0713ba609dea1ac4edd8044a0fffff807ffd7bf7e9fe1fc7ff7fff3ff7fffcfe4713ff67bfff3feffffcccdfb,0x943fb867cfd703400481000214946209404a4c0400045072215252b1224c895b)

def q263 : W := (0x801ff000000003080480000230104009005ac020000050000110420162c00048,0x801ff000000003080480000230104009005ac020000050000110420162c00048)

def q264 : W := (0xeb8ff27d3fc0fffe779fffffff7bcfddffffffe070faf1a8dbbfee1ffbfc4469fffff60707d5fffe7f9fffffffffcfffffffffe470fff1b8fffffe1ffffccc79,0x1470047a38150000080000000084002200000004000500102440100004008810)

def q265 : W := (0x800000000000c3a0000e800036b00003b3580005000000800012800000000000000000000008f3e0000fc0003ffc0003fffc000700000180001fe0000000000,0x800000000008304000014000094c00004ca4000200000100000d60000000000)

def q266 : W := (0x6f80c0e07100ffff3300fefde3ffefd43fffffe87a7aa01edaa1ffbed9814520fffff0000037ffffff80fffff3ffffff3ffffffc7ffff01ffff1ffffffc3cdf8,0x907f30e071370000cc8001021000102b000000140585500125500041264288d8)

def q267 : W := (0x200000000000b006120000000209808400000000000000008080000000000000000000000004b7061f80000003ffc1ff0000000400000018fff0000000000c00,0x20000000000407000d80000001f6417b00000004000000187f70000000000c00)

def q268 : W := (0x7b8140603200fffffffdfc7de3fffbffffb583ff703aa01bfffbac0ed9804c20fffff0000015fffffffffc7ff3ffffffffffc3fff03ff01ffffffe0fffc0ce78,0x847eb060321500000002000210000400004a4000800550040004520126408258)

def q269 : W := (0x400000000000b00413001451e000000000000000202020000000000000000000000000000010b8061f80fc7ff000000000000004703ff000000000000000c000,0x40000000001008020c80e82e1000000000000004501fd000000000000000c000)

def q270 : W := (0x6b824160b400bc3edfd7fd7fff6b81d43fb583f6f5bffd68daa1ac0ed982e420fffff000003dff3fffffffffffffc1ff3fffc3fffffffff8fff1fe0fffc3fc78,0x947db160b43d4301202802800094402b004a40090a4002902550520126411858)

def q271 : W := (0x406030000c380100386160220100023582600002000008200002d1800000803ff00000000f380580386370324109027fc2600006500009304203f3c00048,0x803fb060300003000480000210104009004a4000000450000110420122400048)

def q272 : W := (0xebbfffffffc0fffe779fffffff7bcfddffffffe0f6fef9ecdbbfef3ffbfc466fffffffffffd5fffe7f9fffffffffcfffffffffe4f6fff9fcffffff3ffffcce7f,0x1440000000150000080000000084002200000004000100102440100004008810)

def q273 : W := (0x6000000000003f0000000000000000000180000000000000000,0x6000000000003f0000000000000000000180000000000000000)

def q274 : W := (0xc00808041004ffb2000ea8003ff6e003b7ffc085a40001e00017bb000010100000000000026effffc00ff8003fffff83ffffc1c7fc0001fff01fff000030d80,0xc0080804126a004dc001500000091f80480001425800001ff00844000020c80)

def q275 : W := (0x240010000000030001c00000000000000000c000000000000000,0x240010000000030001c00000000000000000c000000000000000)

def q276 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff0000005bf3e1f809c79f3ffc1ff3c07c3e430303018fff03e0c1fc00c38,0x957fb020100503000c80000010f4403b10024084000010183f50120406400c18)

def q277 : W := (0x2000000000000c0003800000000000000003000000000000000,0x2000000000000c0003800000000000000003000000000000000)

def q278 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffc00ffc000d77e11e7842058bfc31fff3c63b8708082f98ffc031cf1e383c34,0xea802fec008d34201e5000018b3801c42204130600002d18cf80210a18102c24)

def q279 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d4020600380ffbf8042eb81d0639e37ff20df8823df6648606085cff2c0122f1f40e06,0x85211004422801c04000003d008f88000200400000018f708000000200c00)

def q280 : W := (0x200008000000000000f000000000000000000600000000000000,0x200008000000000000f000000000000000000600000000000000)

def q281 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240807ffc6b6509c61041cc7f1b3fe4da10dc40101867bff038cf08d0c0d83,0xe40807ffc606501401000047f1230849210c440000007af90308b0810c0d03)

def q282 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049801ff60707c467c87c9f03823ff04ff9c05afc2400c051b8ff1e421162fc0c49,0x10441a080424081800000023e001f00010802400000018fe00000040800c00)

def q283 : W := (0x20001c0000000000000000000004000000000000000000000000,0x20001c0000000000000000000004000000000000000000000000)

def q284 : W := (0x400201008400b004dfd71553fc00000000000016a5a57d60000000000002a00000000000003cfe07fffffffffff001f80000001ffffffff8ff0000000003fc00,0x40020100843c4e032028eaac03f001f8000000095a5a8298ff00000000015c00)

def q285 : W := (0x600040000000030010800000000000000000900000000000000,0x600040000000030010800000000000000000900000000000000)

def q286 : W := (0x803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f803fffffffc46ff87d9f3be37ff24ff9c27ffe6486c659fcff3e4333f3fc0e4f,0x420001800000003c000f00000000400000018f600000000000c00)

def q287 : W := (0xc007e00000000000000000000018000000000000000000000000,0xc007e00000000000000000000018000000000000000000000000)

def q288 : W := (0x300100000200f3c7fefd0000029dfaafc000001f00000013a5da000000000800000000000024ffc7ffffff8003ffffffc000001fffc0001ffffe000000030e00,0x3001000002240c000102ff800162055000000000ffc0000c5a24000000030600)

def q289 : W := (0x8000000e0000000000000000000400000000000000000000000,0x8000000e0000000000000000000400000000000000000000000)

def q290 : W := (0x300004020000c380000e02c016001503fb003e0401a80085a01800ec0004400000000000034ee3ffc00fffe03f001f83ff803fc7fffc018ff01c00fe003cc40,0x30000402034e207fc001fd2029000a80048001c3fe54010a500400120038840)

def q291 : W := (0x880600009c000000000000000000300000000000000000000000,0x880600009c000000000000000000300000000000000000000000)

def q292 : W := (0x6a8040201000bc3e13009c79e30b81c42c05836030302000c0a02c0819800020fffff0000021fd3ff380fff9f30fc1c73c07c3f87ff03000c0f03e0c1fc30038,0x957fb02010214101e080638010044003100240984fc010000050120406430018)

def q293 : W := (0x4001000042000000000000000000080000000000000000000000,0x4001000042000000000000000000080000000000000000000000)

def q294 : W := (0x15402010008043c10028420400c4303bd1c2288108080280304010c506281010ffc00ffc0029dbe7e278ff8588cc303ff3c63b9b7fc82f8030c031cf1e3b3034,0xea802fec00a99826e250bd81880800042204131a77c02d000080210a18132024)

def q295 : W := (0x800000039800000000000000000060000000000000000000000,0x800000039800000000000000000060000000000000000000000)

def q296 : W := (0x305deaf8400c38010239e37c220500023dd6608606084408240122f1d4020600380ffbf820ccbfe106ffe37c220d00823df678ffc60844082c0122f1f70206,0x852110060c087e004c600000008008000201879c000000008000000230000)

def q297 : W := (0x8000800004000000000000000000010000000000000000000000,0x8000800004000000000000000000010000000000000000000000)

def q298 : W := (0xc000000000b0008860041c800090f60480018001018601060084400c00008000240807ffe2f857e861ff9cc401b2f64da10dd87fc1866306038cf08d0f0183,0xe40807ffe248576001fb804401220049210c587ec00062000308b0810f0103)

def q299 : W := (0x400060000380000000000000000000c000000000000000000000,0x400060000380000000000000000000c000000000000000000000)

def q300 : W := (0x800fb21d0fc043c0649f03821c104e09c04a7c0000c051a0011e4211227c0049801ff60707e0cbcfe49fff823c104e09c05afc387fc051a0011e421162ff0049,0x10441a0820880f8000fc0020000000001080387f0000000000000040830000)

def q301 : W := (0x480060003b80000000000000000006c000000000000000000000,0x480060003b80000000000000000006c000000000000000000000)

def q302 : W := (0x803fffffffc04ff8659f3be37c324f09c27ffe6086c659e4093e4333f3fc024f803fffffffe0cfffe59fffe37c324f09c27ffe78ffc659e4093e4333f3ff024f,0x2080078000c4000000000000000018790000000000000000030000)

def v0 : List W := [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v1 : List W := [q10,q0,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v2 : List W := [q11,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v3 : List W := [q12,q11,q1,q3,q4,q5,q6,q7,q8,q9]

def v4 : List W := [q12,q2,q1,q3,q4,q5,q6,q7,q8,q9]

def v5 : List W := [q12,q11,q2,q1,q3,q4,q5,q6,q7,q8,q9]

def v6 : List W := [q13,q11,q2,q1,q3,q4,q5,q6,q7,q8,q9]

def v7 : List W := [q14,q11,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v8 : List W := [q15,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v9 : List W := [q15,q11,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v10 : List W := [q16,q11,q4,q3,q2,q1,q5,q6,q7,q8,q9]

def v11 : List W := [q17,q11,q4,q3,q2,q1,q5,q6,q7,q8,q9]

def v12 : List W := [q18,q11,q5,q4,q3,q2,q1,q6,q7,q8,q9]

def v13 : List W := [q19,q11,q5,q4,q3,q2,q1,q6,q7,q8,q9]

def v14 : List W := [q20,q11,q6,q5,q4,q3,q2,q1,q7,q8,q9]

def v15 : List W := [q21,q11,q6,q5,q4,q3,q2,q1,q7,q8,q9]

def v16 : List W := [q22,q11,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v17 : List W := [q23,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v18 : List W := [q23,q11,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v19 : List W := [q24,q11,q8,q7,q6,q5,q4,q3,q2,q1,q9]

def v20 : List W := [q25,q11,q8,q7,q6,q5,q4,q3,q2,q1,q9]

def v21 : List W := [q26,q9,q8,q7,q6,q5,q4,q3,q2,q1]

def v22 : List W := [q26,q11,q9,q8,q7,q6,q5,q4,q3,q2,q1]

def v23 : List W := [q13,q11,q9,q8,q7,q6,q5,q4,q3,q2,q1]

def v24 : List W := [q27,q1,q2,q11,q3,q4,q5,q6,q7,q8,q9]

def v25 : List W := [q28,q1,q11,q3,q4,q5,q6,q7,q8,q9]

def v26 : List W := [q28,q1,q2,q11,q3,q4,q5,q6,q7,q8,q9]

def v27 : List W := [q29,q1,q3,q2,q11,q4,q5,q6,q7,q8,q9]

def v28 : List W := [q30,q1,q3,q2,q11,q4,q5,q6,q7,q8,q9]

def v29 : List W := [q31,q1,q4,q3,q2,q11,q5,q6,q7,q8,q9]

def v30 : List W := [q32,q4,q3,q2,q11,q5,q6,q7,q8,q9]

def v31 : List W := [q32,q1,q4,q3,q2,q11,q5,q6,q7,q8,q9]

def v32 : List W := [q33,q1,q5,q4,q3,q2,q11,q6,q7,q8,q9]

def v33 : List W := [q34,q5,q4,q3,q2,q11,q6,q7,q8,q9]

def v34 : List W := [q34,q1,q5,q4,q3,q2,q11,q6,q7,q8,q9]

def v35 : List W := [q35,q1,q6,q5,q4,q3,q2,q11,q7,q8,q9]

def v36 : List W := [q36,q1,q6,q5,q4,q3,q2,q11,q7,q8,q9]

def v37 : List W := [q37,q1,q7,q6,q5,q4,q3,q2,q11,q8,q9]

def v38 : List W := [q38,q1,q7,q6,q5,q4,q3,q2,q11,q8,q9]

def v39 : List W := [q39,q1,q8,q7,q6,q5,q4,q3,q2,q11,q9]

def v40 : List W := [q40,q1,q8,q7,q6,q5,q4,q3,q2,q11,q9]

def v41 : List W := [q41,q9,q8,q7,q6,q5,q4,q3,q2,q11]

def v42 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q3,q2,q11]

def v43 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q3,q2,q11]

def v44 : List W := [q42,q2,q3,q1,q11,q4,q5,q6,q7,q8,q9]

def v45 : List W := [q43,q2,q3,q1,q11,q4,q5,q6,q7,q8,q9]

def v46 : List W := [q44,q2,q4,q3,q1,q11,q5,q6,q7,q8,q9]

def v47 : List W := [q45,q4,q3,q1,q11,q5,q6,q7,q8,q9]

def v48 : List W := [q45,q2,q4,q3,q1,q11,q5,q6,q7,q8,q9]

def v49 : List W := [q46,q2,q5,q4,q3,q1,q11,q6,q7,q8,q9]

def v50 : List W := [q47,q5,q4,q3,q1,q11,q6,q7,q8,q9]

def v51 : List W := [q47,q2,q5,q4,q3,q1,q11,q6,q7,q8,q9]

def v52 : List W := [q48,q2,q6,q5,q4,q3,q1,q11,q7,q8,q9]

def v53 : List W := [q49,q2,q6,q5,q4,q3,q1,q11,q7,q8,q9]

def v54 : List W := [q50,q2,q7,q6,q5,q4,q3,q1,q11,q8,q9]

def v55 : List W := [q51,q2,q7,q6,q5,q4,q3,q1,q11,q8,q9]

def v56 : List W := [q52,q2,q8,q7,q6,q5,q4,q3,q1,q11,q9]

def v57 : List W := [q53,q2,q8,q7,q6,q5,q4,q3,q1,q11,q9]

def v58 : List W := [q54,q3,q4,q2,q1,q11,q5,q6,q7,q8,q9]

def v59 : List W := [q55,q3,q4,q2,q1,q11,q5,q6,q7,q8,q9]

def v60 : List W := [q56,q3,q5,q4,q2,q1,q11,q6,q7,q8,q9]

def v61 : List W := [q57,q3,q5,q4,q2,q1,q11,q6,q7,q8,q9]

def v62 : List W := [q58,q3,q6,q5,q4,q2,q1,q11,q7,q8,q9]

def v63 : List W := [q59,q3,q6,q5,q4,q2,q1,q11,q7,q8,q9]

def v64 : List W := [q60,q3,q7,q6,q5,q4,q2,q1,q11,q8,q9]

def v65 : List W := [q61,q3,q7,q6,q5,q4,q2,q1,q11,q8,q9]

def v66 : List W := [q62,q3,q8,q7,q6,q5,q4,q2,q1,q11,q9]

def v67 : List W := [q63,q3,q8,q7,q6,q5,q4,q2,q1,q11,q9]

def v68 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q2,q1,q11]

def v69 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q2,q1,q11]

def v70 : List W := [q66,q4,q5,q3,q2,q1,q11,q6,q7,q8,q9]

def v71 : List W := [q67,q4,q5,q3,q2,q1,q11,q6,q7,q8,q9]

def v72 : List W := [q68,q4,q6,q5,q3,q2,q1,q11,q7,q8,q9]

def v73 : List W := [q69,q4,q6,q5,q3,q2,q1,q11,q7,q8,q9]

def v74 : List W := [q70,q4,q7,q6,q5,q3,q2,q1,q11,q8,q9]

def v75 : List W := [q71,q4,q7,q6,q5,q3,q2,q1,q11,q8,q9]

def v76 : List W := [q72,q4,q8,q7,q6,q5,q3,q2,q1,q11,q9]

def v77 : List W := [q73,q4,q8,q7,q6,q5,q3,q2,q1,q11,q9]

def v78 : List W := [q74,q4,q9,q8,q7,q6,q5,q3,q2,q1,q11]

def v79 : List W := [q75,q4,q9,q8,q7,q6,q5,q3,q2,q1,q11]

def v80 : List W := [q76,q5,q6,q4,q3,q2,q1,q11,q7,q8,q9]

def v81 : List W := [q77,q5,q6,q4,q3,q2,q1,q11,q7,q8,q9]

def v82 : List W := [q78,q5,q7,q6,q4,q3,q2,q1,q11,q8,q9]

def v83 : List W := [q79,q5,q7,q6,q4,q3,q2,q1,q11,q8,q9]

def v84 : List W := [q80,q5,q8,q7,q6,q4,q3,q2,q1,q11,q9]

def v85 : List W := [q81,q5,q8,q7,q6,q4,q3,q2,q1,q11,q9]

def v86 : List W := [q82,q5,q9,q8,q7,q6,q4,q3,q2,q1,q11]

def v87 : List W := [q83,q5,q9,q8,q7,q6,q4,q3,q2,q1,q11]

def v88 : List W := [q84,q6,q7,q5,q4,q3,q2,q1,q11,q8,q9]

def v89 : List W := [q85,q6,q7,q5,q4,q3,q2,q1,q11,q8,q9]

def v90 : List W := [q86,q6,q8,q7,q5,q4,q3,q2,q1,q11,q9]

def v91 : List W := [q87,q6,q8,q7,q5,q4,q3,q2,q1,q11,q9]

def v92 : List W := [q88,q6,q9,q8,q7,q5,q4,q3,q2,q1,q11]

def v93 : List W := [q89,q6,q9,q8,q7,q5,q4,q3,q2,q1,q11]

def v94 : List W := [q90,q7,q8,q6,q5,q4,q3,q2,q1,q11,q9]

def v95 : List W := [q91,q7,q8,q6,q5,q4,q3,q2,q1,q11,q9]

def v96 : List W := [q92,q7,q9,q8,q6,q5,q4,q3,q2,q1,q11]

def v97 : List W := [q93,q7,q9,q8,q6,q5,q4,q3,q2,q1,q11]

def v98 : List W := [q94,q8,q9,q7,q6,q5,q4,q3,q2,q1,q11]

def v99 : List W := [q95,q8,q9,q7,q6,q5,q4,q3,q2,q1,q11]

def v100 : List W := [q11,q0,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v101 : List W := [q96,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v102 : List W := [q97,q96,q1,q0,q3,q4,q5,q6,q7,q8,q9]

def v103 : List W := [q98,q1,q0,q3,q4,q5,q6,q7,q8,q9]

def v104 : List W := [q98,q96,q1,q0,q3,q4,q5,q6,q7,q8,q9]

def v105 : List W := [q99,q96,q3,q1,q0,q4,q5,q6,q7,q8,q9]

def v106 : List W := [q100,q96,q3,q1,q0,q4,q5,q6,q7,q8,q9]

def v107 : List W := [q101,q96,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v108 : List W := [q102,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v109 : List W := [q102,q96,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v110 : List W := [q103,q96,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v111 : List W := [q104,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v112 : List W := [q104,q96,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v113 : List W := [q105,q96,q6,q5,q4,q3,q1,q0,q7,q8,q9]

def v114 : List W := [q106,q96,q6,q5,q4,q3,q1,q0,q7,q8,q9]

def v115 : List W := [q107,q96,q7,q6,q5,q4,q3,q1,q0,q8,q9]

def v116 : List W := [q108,q96,q7,q6,q5,q4,q3,q1,q0,q8,q9]

def v117 : List W := [q109,q96,q8,q7,q6,q5,q4,q3,q1,q0,q9]

def v118 : List W := [q110,q96,q8,q7,q6,q5,q4,q3,q1,q0,q9]

def v119 : List W := [q10,q0,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v120 : List W := [q11,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v121 : List W := [q11,q0,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v122 : List W := [q111,q0,q3,q1,q96,q4,q5,q6,q7,q8,q9]

def v123 : List W := [q112,q0,q3,q1,q96,q4,q5,q6,q7,q8,q9]

def v124 : List W := [q113,q0,q4,q3,q1,q96,q5,q6,q7,q8,q9]

def v125 : List W := [q114,q0,q4,q3,q1,q96,q5,q6,q7,q8,q9]

def v126 : List W := [q115,q0,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v127 : List W := [q116,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v128 : List W := [q116,q0,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v129 : List W := [q117,q0,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v130 : List W := [q118,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v131 : List W := [q118,q0,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v132 : List W := [q119,q0,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v133 : List W := [q120,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v134 : List W := [q120,q0,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v135 : List W := [q121,q0,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v136 : List W := [q122,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v137 : List W := [q122,q0,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v138 : List W := [q29,q1,q3,q0,q96,q4,q5,q6,q7,q8,q9]

def v139 : List W := [q30,q1,q3,q0,q96,q4,q5,q6,q7,q8,q9]

def v140 : List W := [q31,q1,q4,q3,q0,q96,q5,q6,q7,q8,q9]

def v141 : List W := [q32,q1,q4,q3,q0,q96,q5,q6,q7,q8,q9]

def v142 : List W := [q33,q1,q5,q4,q3,q0,q96,q6,q7,q8,q9]

def v143 : List W := [q34,q1,q5,q4,q3,q0,q96,q6,q7,q8,q9]

def v144 : List W := [q35,q1,q6,q5,q4,q3,q0,q96,q7,q8,q9]

def v145 : List W := [q36,q1,q6,q5,q4,q3,q0,q96,q7,q8,q9]

def v146 : List W := [q37,q1,q7,q6,q5,q4,q3,q0,q96,q8,q9]

def v147 : List W := [q38,q1,q7,q6,q5,q4,q3,q0,q96,q8,q9]

def v148 : List W := [q39,q1,q8,q7,q6,q5,q4,q3,q0,q96,q9]

def v149 : List W := [q40,q1,q8,q7,q6,q5,q4,q3,q0,q96,q9]

def v150 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q3,q0,q96]

def v151 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q3,q0,q96]

def v152 : List W := [q54,q3,q4,q1,q0,q96,q5,q6,q7,q8,q9]

def v153 : List W := [q55,q3,q4,q1,q0,q96,q5,q6,q7,q8,q9]

def v154 : List W := [q56,q3,q5,q4,q1,q0,q96,q6,q7,q8,q9]

def v155 : List W := [q57,q3,q5,q4,q1,q0,q96,q6,q7,q8,q9]

def v156 : List W := [q58,q3,q6,q5,q4,q1,q0,q96,q7,q8,q9]

def v157 : List W := [q59,q3,q6,q5,q4,q1,q0,q96,q7,q8,q9]

def v158 : List W := [q60,q3,q7,q6,q5,q4,q1,q0,q96,q8,q9]

def v159 : List W := [q61,q3,q7,q6,q5,q4,q1,q0,q96,q8,q9]

def v160 : List W := [q62,q3,q8,q7,q6,q5,q4,q1,q0,q96,q9]

def v161 : List W := [q63,q3,q8,q7,q6,q5,q4,q1,q0,q96,q9]

def v162 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q1,q0,q96]

def v163 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q1,q0,q96]

def v164 : List W := [q66,q4,q5,q3,q1,q0,q96,q6,q7,q8,q9]

def v165 : List W := [q67,q4,q5,q3,q1,q0,q96,q6,q7,q8,q9]

def v166 : List W := [q68,q4,q6,q5,q3,q1,q0,q96,q7,q8,q9]

def v167 : List W := [q69,q4,q6,q5,q3,q1,q0,q96,q7,q8,q9]

def v168 : List W := [q70,q4,q7,q6,q5,q3,q1,q0,q96,q8,q9]

def v169 : List W := [q71,q4,q7,q6,q5,q3,q1,q0,q96,q8,q9]

def v170 : List W := [q72,q4,q8,q7,q6,q5,q3,q1,q0,q96,q9]

def v171 : List W := [q73,q4,q8,q7,q6,q5,q3,q1,q0,q96,q9]

def v172 : List W := [q74,q4,q9,q8,q7,q6,q5,q3,q1,q0,q96]

def v173 : List W := [q75,q4,q9,q8,q7,q6,q5,q3,q1,q0,q96]

def v174 : List W := [q76,q5,q6,q4,q3,q1,q0,q96,q7,q8,q9]

def v175 : List W := [q77,q5,q6,q4,q3,q1,q0,q96,q7,q8,q9]

def v176 : List W := [q78,q5,q7,q6,q4,q3,q1,q0,q96,q8,q9]

def v177 : List W := [q79,q5,q7,q6,q4,q3,q1,q0,q96,q8,q9]

def v178 : List W := [q80,q5,q8,q7,q6,q4,q3,q1,q0,q96,q9]

def v179 : List W := [q81,q5,q8,q7,q6,q4,q3,q1,q0,q96,q9]

def v180 : List W := [q82,q5,q9,q8,q7,q6,q4,q3,q1,q0,q96]

def v181 : List W := [q83,q5,q9,q8,q7,q6,q4,q3,q1,q0,q96]

def v182 : List W := [q84,q6,q7,q5,q4,q3,q1,q0,q96,q8,q9]

def v183 : List W := [q85,q6,q7,q5,q4,q3,q1,q0,q96,q8,q9]

def v184 : List W := [q86,q6,q8,q7,q5,q4,q3,q1,q0,q96,q9]

def v185 : List W := [q87,q6,q8,q7,q5,q4,q3,q1,q0,q96,q9]

def v186 : List W := [q88,q6,q9,q8,q7,q5,q4,q3,q1,q0,q96]

def v187 : List W := [q89,q6,q9,q8,q7,q5,q4,q3,q1,q0,q96]

def v188 : List W := [q90,q7,q8,q6,q5,q4,q3,q1,q0,q96,q9]

def v189 : List W := [q91,q7,q8,q6,q5,q4,q3,q1,q0,q96,q9]

def v190 : List W := [q92,q7,q9,q8,q6,q5,q4,q3,q1,q0,q96]

def v191 : List W := [q93,q7,q9,q8,q6,q5,q4,q3,q1,q0,q96]

def v192 : List W := [q94,q8,q9,q7,q6,q5,q4,q3,q1,q0,q96]

def v193 : List W := [q95,q8,q9,q7,q6,q5,q4,q3,q1,q0,q96]

def v194 : List W := [q96,q2,q1,q3,q4,q5,q6,q7,q8,q9]

def v195 : List W := [q97,q96,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v196 : List W := [q98,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v197 : List W := [q98,q96,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v198 : List W := [q99,q96,q3,q1,q2,q4,q5,q6,q7,q8,q9]

def v199 : List W := [q100,q3,q1,q2,q4,q5,q6,q7,q8,q9]

def v200 : List W := [q100,q96,q3,q1,q2,q4,q5,q6,q7,q8,q9]

def v201 : List W := [q101,q96,q4,q3,q1,q2,q5,q6,q7,q8,q9]

def v202 : List W := [q102,q96,q4,q3,q1,q2,q5,q6,q7,q8,q9]

def v203 : List W := [q103,q96,q5,q4,q3,q1,q2,q6,q7,q8,q9]

def v204 : List W := [q104,q96,q5,q4,q3,q1,q2,q6,q7,q8,q9]

def v205 : List W := [q105,q96,q6,q5,q4,q3,q1,q2,q7,q8,q9]

def v206 : List W := [q106,q96,q6,q5,q4,q3,q1,q2,q7,q8,q9]

def v207 : List W := [q107,q96,q7,q6,q5,q4,q3,q1,q2,q8,q9]

def v208 : List W := [q108,q7,q6,q5,q4,q3,q1,q2,q8,q9]

def v209 : List W := [q108,q96,q7,q6,q5,q4,q3,q1,q2,q8,q9]

def v210 : List W := [q109,q96,q8,q7,q6,q5,q4,q3,q1,q2,q9]

def v211 : List W := [q110,q96,q8,q7,q6,q5,q4,q3,q1,q2,q9]

def v212 : List W := [q27,q2,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v213 : List W := [q28,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v214 : List W := [q28,q2,q1,q96,q3,q4,q5,q6,q7,q8,q9]

def v215 : List W := [q42,q2,q3,q1,q96,q4,q5,q6,q7,q8,q9]

def v216 : List W := [q43,q2,q3,q1,q96,q4,q5,q6,q7,q8,q9]

def v217 : List W := [q44,q2,q4,q3,q1,q96,q5,q6,q7,q8,q9]

def v218 : List W := [q45,q2,q4,q3,q1,q96,q5,q6,q7,q8,q9]

def v219 : List W := [q46,q2,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v220 : List W := [q47,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v221 : List W := [q47,q2,q5,q4,q3,q1,q96,q6,q7,q8,q9]

def v222 : List W := [q48,q2,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v223 : List W := [q49,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v224 : List W := [q49,q2,q6,q5,q4,q3,q1,q96,q7,q8,q9]

def v225 : List W := [q50,q2,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v226 : List W := [q51,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v227 : List W := [q51,q2,q7,q6,q5,q4,q3,q1,q96,q8,q9]

def v228 : List W := [q52,q2,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v229 : List W := [q53,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v230 : List W := [q53,q2,q8,q7,q6,q5,q4,q3,q1,q96,q9]

def v231 : List W := [q29,q1,q3,q2,q96,q4,q5,q6,q7,q8,q9]

def v232 : List W := [q30,q1,q3,q2,q96,q4,q5,q6,q7,q8,q9]

def v233 : List W := [q31,q1,q4,q3,q2,q96,q5,q6,q7,q8,q9]

def v234 : List W := [q32,q1,q4,q3,q2,q96,q5,q6,q7,q8,q9]

def v235 : List W := [q33,q1,q5,q4,q3,q2,q96,q6,q7,q8,q9]

def v236 : List W := [q34,q1,q5,q4,q3,q2,q96,q6,q7,q8,q9]

def v237 : List W := [q35,q1,q6,q5,q4,q3,q2,q96,q7,q8,q9]

def v238 : List W := [q36,q1,q6,q5,q4,q3,q2,q96,q7,q8,q9]

def v239 : List W := [q37,q1,q7,q6,q5,q4,q3,q2,q96,q8,q9]

def v240 : List W := [q38,q1,q7,q6,q5,q4,q3,q2,q96,q8,q9]

def v241 : List W := [q39,q1,q8,q7,q6,q5,q4,q3,q2,q96,q9]

def v242 : List W := [q40,q1,q8,q7,q6,q5,q4,q3,q2,q96,q9]

def v243 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q3,q2,q96]

def v244 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q3,q2,q96]

def v245 : List W := [q54,q3,q4,q1,q2,q96,q5,q6,q7,q8,q9]

def v246 : List W := [q55,q3,q4,q1,q2,q96,q5,q6,q7,q8,q9]

def v247 : List W := [q56,q3,q5,q4,q1,q2,q96,q6,q7,q8,q9]

def v248 : List W := [q57,q3,q5,q4,q1,q2,q96,q6,q7,q8,q9]

def v249 : List W := [q58,q3,q6,q5,q4,q1,q2,q96,q7,q8,q9]

def v250 : List W := [q59,q3,q6,q5,q4,q1,q2,q96,q7,q8,q9]

def v251 : List W := [q60,q3,q7,q6,q5,q4,q1,q2,q96,q8,q9]

def v252 : List W := [q61,q3,q7,q6,q5,q4,q1,q2,q96,q8,q9]

def v253 : List W := [q62,q3,q8,q7,q6,q5,q4,q1,q2,q96,q9]

def v254 : List W := [q63,q3,q8,q7,q6,q5,q4,q1,q2,q96,q9]

def v255 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q1,q2,q96]

def v256 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q1,q2,q96]

def v257 : List W := [q66,q4,q5,q3,q1,q2,q96,q6,q7,q8,q9]

def v258 : List W := [q67,q4,q5,q3,q1,q2,q96,q6,q7,q8,q9]

def v259 : List W := [q68,q4,q6,q5,q3,q1,q2,q96,q7,q8,q9]

def v260 : List W := [q69,q4,q6,q5,q3,q1,q2,q96,q7,q8,q9]

def v261 : List W := [q70,q4,q7,q6,q5,q3,q1,q2,q96,q8,q9]

def v262 : List W := [q71,q4,q7,q6,q5,q3,q1,q2,q96,q8,q9]

def v263 : List W := [q72,q4,q8,q7,q6,q5,q3,q1,q2,q96,q9]

def v264 : List W := [q73,q4,q8,q7,q6,q5,q3,q1,q2,q96,q9]

def v265 : List W := [q74,q4,q9,q8,q7,q6,q5,q3,q1,q2,q96]

def v266 : List W := [q75,q4,q9,q8,q7,q6,q5,q3,q1,q2,q96]

def v267 : List W := [q76,q5,q6,q4,q3,q1,q2,q96,q7,q8,q9]

def v268 : List W := [q77,q5,q6,q4,q3,q1,q2,q96,q7,q8,q9]

def v269 : List W := [q78,q5,q7,q6,q4,q3,q1,q2,q96,q8,q9]

def v270 : List W := [q79,q5,q7,q6,q4,q3,q1,q2,q96,q8,q9]

def v271 : List W := [q80,q5,q8,q7,q6,q4,q3,q1,q2,q96,q9]

def v272 : List W := [q81,q5,q8,q7,q6,q4,q3,q1,q2,q96,q9]

def v273 : List W := [q82,q5,q9,q8,q7,q6,q4,q3,q1,q2,q96]

def v274 : List W := [q83,q5,q9,q8,q7,q6,q4,q3,q1,q2,q96]

def v275 : List W := [q84,q6,q7,q5,q4,q3,q1,q2,q96,q8,q9]

def v276 : List W := [q85,q6,q7,q5,q4,q3,q1,q2,q96,q8,q9]

def v277 : List W := [q86,q6,q8,q7,q5,q4,q3,q1,q2,q96,q9]

def v278 : List W := [q87,q6,q8,q7,q5,q4,q3,q1,q2,q96,q9]

def v279 : List W := [q88,q6,q9,q8,q7,q5,q4,q3,q1,q2,q96]

def v280 : List W := [q89,q6,q9,q8,q7,q5,q4,q3,q1,q2,q96]

def v281 : List W := [q90,q7,q8,q6,q5,q4,q3,q1,q2,q96,q9]

def v282 : List W := [q91,q7,q8,q6,q5,q4,q3,q1,q2,q96,q9]

def v283 : List W := [q92,q7,q9,q8,q6,q5,q4,q3,q1,q2,q96]

def v284 : List W := [q93,q7,q9,q8,q6,q5,q4,q3,q1,q2,q96]

def v285 : List W := [q94,q8,q9,q7,q6,q5,q4,q3,q1,q2,q96]

def v286 : List W := [q95,q8,q9,q7,q6,q5,q4,q3,q1,q2,q96]

def v287 : List W := [q96,q0,q2,q1,q3,q4,q5,q6,q7,q8,q9]

def v288 : List W := [q111,q0,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v289 : List W := [q112,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v290 : List W := [q123,q112,q3,q1,q4,q5,q6,q7,q8,q9]

def v291 : List W := [q123,q2,q3,q1,q4,q5,q6,q7,q8,q9]

def v292 : List W := [q123,q112,q2,q3,q1,q4,q5,q6,q7,q8,q9]

def v293 : List W := [q65,q112,q2,q3,q1,q4,q5,q6,q7,q8,q9]

def v294 : List W := [q124,q112,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v295 : List W := [q15,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v296 : List W := [q15,q112,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v297 : List W := [q125,q112,q1,q2,q3,q5,q6,q7,q8,q9]

def v298 : List W := [q125,q112,q4,q1,q2,q3,q5,q6,q7,q8,q9]

def v299 : List W := [q126,q112,q4,q1,q2,q3,q5,q6,q7,q8,q9]

def v300 : List W := [q127,q112,q5,q4,q1,q2,q3,q6,q7,q8,q9]

def v301 : List W := [q128,q112,q5,q4,q1,q2,q3,q6,q7,q8,q9]

def v302 : List W := [q129,q112,q6,q5,q4,q1,q2,q3,q7,q8,q9]

def v303 : List W := [q130,q112,q6,q5,q4,q1,q2,q3,q7,q8,q9]

def v304 : List W := [q131,q112,q7,q6,q5,q4,q1,q2,q3,q8,q9]

def v305 : List W := [q132,q7,q6,q5,q4,q1,q2,q3,q8,q9]

def v306 : List W := [q132,q112,q7,q6,q5,q4,q1,q2,q3,q8,q9]

def v307 : List W := [q133,q112,q8,q7,q6,q5,q4,q1,q2,q3,q9]

def v308 : List W := [q134,q112,q8,q7,q6,q5,q4,q1,q2,q3,q9]

def v309 : List W := [q135,q9,q8,q7,q6,q5,q4,q1,q2,q3]

def v310 : List W := [q135,q112,q9,q8,q7,q6,q5,q4,q1,q2,q3]

def v311 : List W := [q65,q112,q9,q8,q7,q6,q5,q4,q1,q2,q3]

def v312 : List W := [q42,q3,q2,q112,q1,q4,q5,q6,q7,q8,q9]

def v313 : List W := [q43,q3,q2,q112,q1,q4,q5,q6,q7,q8,q9]

def v314 : List W := [q29,q3,q1,q2,q112,q4,q5,q6,q7,q8,q9]

def v315 : List W := [q30,q1,q2,q112,q4,q5,q6,q7,q8,q9]

def v316 : List W := [q30,q3,q1,q2,q112,q4,q5,q6,q7,q8,q9]

def v317 : List W := [q54,q3,q4,q1,q2,q112,q5,q6,q7,q8,q9]

def v318 : List W := [q55,q4,q1,q2,q112,q5,q6,q7,q8,q9]

def v319 : List W := [q55,q3,q4,q1,q2,q112,q5,q6,q7,q8,q9]

def v320 : List W := [q56,q3,q5,q4,q1,q2,q112,q6,q7,q8,q9]

def v321 : List W := [q57,q5,q4,q1,q2,q112,q6,q7,q8,q9]

def v322 : List W := [q57,q3,q5,q4,q1,q2,q112,q6,q7,q8,q9]

def v323 : List W := [q58,q3,q6,q5,q4,q1,q2,q112,q7,q8,q9]

def v324 : List W := [q59,q3,q6,q5,q4,q1,q2,q112,q7,q8,q9]

def v325 : List W := [q60,q3,q7,q6,q5,q4,q1,q2,q112,q8,q9]

def v326 : List W := [q61,q3,q7,q6,q5,q4,q1,q2,q112,q8,q9]

def v327 : List W := [q62,q3,q8,q7,q6,q5,q4,q1,q2,q112,q9]

def v328 : List W := [q63,q3,q8,q7,q6,q5,q4,q1,q2,q112,q9]

def v329 : List W := [q64,q9,q8,q7,q6,q5,q4,q1,q2,q112]

def v330 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q1,q2,q112]

def v331 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q1,q2,q112]

def v332 : List W := [q27,q2,q1,q3,q112,q4,q5,q6,q7,q8,q9]

def v333 : List W := [q28,q1,q3,q112,q4,q5,q6,q7,q8,q9]

def v334 : List W := [q28,q2,q1,q3,q112,q4,q5,q6,q7,q8,q9]

def v335 : List W := [q44,q2,q4,q1,q3,q112,q5,q6,q7,q8,q9]

def v336 : List W := [q45,q4,q1,q3,q112,q5,q6,q7,q8,q9]

def v337 : List W := [q45,q2,q4,q1,q3,q112,q5,q6,q7,q8,q9]

def v338 : List W := [q46,q2,q5,q4,q1,q3,q112,q6,q7,q8,q9]

def v339 : List W := [q47,q5,q4,q1,q3,q112,q6,q7,q8,q9]

def v340 : List W := [q47,q2,q5,q4,q1,q3,q112,q6,q7,q8,q9]

def v341 : List W := [q48,q2,q6,q5,q4,q1,q3,q112,q7,q8,q9]

def v342 : List W := [q49,q2,q6,q5,q4,q1,q3,q112,q7,q8,q9]

def v343 : List W := [q50,q2,q7,q6,q5,q4,q1,q3,q112,q8,q9]

def v344 : List W := [q51,q2,q7,q6,q5,q4,q1,q3,q112,q8,q9]

def v345 : List W := [q52,q2,q8,q7,q6,q5,q4,q1,q3,q112,q9]

def v346 : List W := [q53,q2,q8,q7,q6,q5,q4,q1,q3,q112,q9]

def v347 : List W := [q31,q1,q4,q2,q3,q112,q5,q6,q7,q8,q9]

def v348 : List W := [q32,q1,q4,q2,q3,q112,q5,q6,q7,q8,q9]

def v349 : List W := [q33,q1,q5,q4,q2,q3,q112,q6,q7,q8,q9]

def v350 : List W := [q34,q1,q5,q4,q2,q3,q112,q6,q7,q8,q9]

def v351 : List W := [q35,q1,q6,q5,q4,q2,q3,q112,q7,q8,q9]

def v352 : List W := [q36,q1,q6,q5,q4,q2,q3,q112,q7,q8,q9]

def v353 : List W := [q37,q1,q7,q6,q5,q4,q2,q3,q112,q8,q9]

def v354 : List W := [q38,q1,q7,q6,q5,q4,q2,q3,q112,q8,q9]

def v355 : List W := [q39,q1,q8,q7,q6,q5,q4,q2,q3,q112,q9]

def v356 : List W := [q40,q1,q8,q7,q6,q5,q4,q2,q3,q112,q9]

def v357 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q2,q3,q112]

def v358 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q2,q3,q112]

def v359 : List W := [q66,q4,q5,q1,q2,q3,q112,q6,q7,q8,q9]

def v360 : List W := [q67,q4,q5,q1,q2,q3,q112,q6,q7,q8,q9]

def v361 : List W := [q68,q4,q6,q5,q1,q2,q3,q112,q7,q8,q9]

def v362 : List W := [q69,q4,q6,q5,q1,q2,q3,q112,q7,q8,q9]

def v363 : List W := [q70,q4,q7,q6,q5,q1,q2,q3,q112,q8,q9]

def v364 : List W := [q71,q4,q7,q6,q5,q1,q2,q3,q112,q8,q9]

def v365 : List W := [q72,q4,q8,q7,q6,q5,q1,q2,q3,q112,q9]

def v366 : List W := [q73,q4,q8,q7,q6,q5,q1,q2,q3,q112,q9]

def v367 : List W := [q74,q4,q9,q8,q7,q6,q5,q1,q2,q3,q112]

def v368 : List W := [q75,q4,q9,q8,q7,q6,q5,q1,q2,q3,q112]

def v369 : List W := [q76,q5,q6,q4,q1,q2,q3,q112,q7,q8,q9]

def v370 : List W := [q77,q5,q6,q4,q1,q2,q3,q112,q7,q8,q9]

def v371 : List W := [q78,q5,q7,q6,q4,q1,q2,q3,q112,q8,q9]

def v372 : List W := [q79,q5,q7,q6,q4,q1,q2,q3,q112,q8,q9]

def v373 : List W := [q80,q5,q8,q7,q6,q4,q1,q2,q3,q112,q9]

def v374 : List W := [q81,q5,q8,q7,q6,q4,q1,q2,q3,q112,q9]

def v375 : List W := [q82,q5,q9,q8,q7,q6,q4,q1,q2,q3,q112]

def v376 : List W := [q83,q5,q9,q8,q7,q6,q4,q1,q2,q3,q112]

def v377 : List W := [q84,q6,q7,q5,q4,q1,q2,q3,q112,q8,q9]

def v378 : List W := [q85,q6,q7,q5,q4,q1,q2,q3,q112,q8,q9]

def v379 : List W := [q86,q6,q8,q7,q5,q4,q1,q2,q3,q112,q9]

def v380 : List W := [q87,q6,q8,q7,q5,q4,q1,q2,q3,q112,q9]

def v381 : List W := [q88,q6,q9,q8,q7,q5,q4,q1,q2,q3,q112]

def v382 : List W := [q89,q6,q9,q8,q7,q5,q4,q1,q2,q3,q112]

def v383 : List W := [q90,q7,q8,q6,q5,q4,q1,q2,q3,q112,q9]

def v384 : List W := [q91,q7,q8,q6,q5,q4,q1,q2,q3,q112,q9]

def v385 : List W := [q92,q7,q9,q8,q6,q5,q4,q1,q2,q3,q112]

def v386 : List W := [q93,q7,q9,q8,q6,q5,q4,q1,q2,q3,q112]

def v387 : List W := [q94,q8,q9,q7,q6,q5,q4,q1,q2,q3,q112]

def v388 : List W := [q95,q8,q9,q7,q6,q5,q4,q1,q2,q3,q112]

def v389 : List W := [q112,q0,q3,q2,q1,q4,q5,q6,q7,q8,q9]

def v390 : List W := [q113,q0,q4,q3,q2,q1,q5,q6,q7,q8,q9]

def v391 : List W := [q136,q3,q4,q0,q2,q1,q5,q6,q7,q8,q9]

def v392 : List W := [q137,q4,q0,q2,q1,q5,q6,q7,q8,q9]

def v393 : List W := [q137,q113,q4,q0,q2,q1,q5,q6,q7,q8,q9]

def v394 : List W := [q137,q3,q4,q0,q2,q1,q5,q6,q7,q8,q9]

def v395 : List W := [q101,q2,q3,q4,q0,q1,q5,q6,q7,q8,q9]

def v396 : List W := [q138,q3,q4,q0,q1,q5,q6,q7,q8,q9]

def v397 : List W := [q138,q113,q3,q4,q0,q1,q5,q6,q7,q8,q9]

def v398 : List W := [q138,q2,q3,q4,q0,q1,q5,q6,q7,q8,q9]

def v399 : List W := [q139,q1,q2,q3,q4,q0,q5,q6,q7,q8,q9]

def v400 : List W := [q140,q2,q3,q4,q0,q5,q6,q7,q8,q9]

def v401 : List W := [q140,q113,q2,q3,q4,q0,q5,q6,q7,q8,q9]

def v402 : List W := [q140,q1,q2,q3,q4,q0,q5,q6,q7,q8,q9]

def v403 : List W := [q141,q5,q1,q2,q3,q4,q0,q6,q7,q8,q9]

def v404 : List W := [q142,q1,q2,q3,q4,q0,q6,q7,q8,q9]

def v405 : List W := [q142,q113,q1,q2,q3,q4,q0,q6,q7,q8,q9]

def v406 : List W := [q142,q5,q1,q2,q3,q4,q0,q6,q7,q8,q9]

def v407 : List W := [q143,q6,q5,q1,q2,q3,q4,q0,q7,q8,q9]

def v408 : List W := [q144,q5,q1,q2,q3,q4,q0,q7,q8,q9]

def v409 : List W := [q144,q113,q5,q1,q2,q3,q4,q0,q7,q8,q9]

def v410 : List W := [q144,q6,q5,q1,q2,q3,q4,q0,q7,q8,q9]

def v411 : List W := [q145,q7,q6,q5,q1,q2,q3,q4,q0,q8,q9]

def v412 : List W := [q146,q6,q5,q1,q2,q3,q4,q0,q8,q9]

def v413 : List W := [q146,q113,q6,q5,q1,q2,q3,q4,q0,q8,q9]

def v414 : List W := [q146,q7,q6,q5,q1,q2,q3,q4,q0,q8,q9]

def v415 : List W := [q147,q8,q7,q6,q5,q1,q2,q3,q4,q0,q9]

def v416 : List W := [q148,q7,q6,q5,q1,q2,q3,q4,q0,q9]

def v417 : List W := [q148,q113,q7,q6,q5,q1,q2,q3,q4,q0,q9]

def v418 : List W := [q148,q8,q7,q6,q5,q1,q2,q3,q4,q0,q9]

def v419 : List W := [q114,q113,q3,q2,q1,q5,q6,q7,q8,q9]

def v420 : List W := [q114,q0,q113,q3,q2,q1,q5,q6,q7,q8,q9]

def v421 : List W := [q114,q4,q113,q3,q2,q1,q5,q6,q7,q8,q9]

def v422 : List W := [q112,q3,q4,q113,q2,q1,q5,q6,q7,q8,q9]

def v423 : List W := [q96,q0,q3,q4,q113,q1,q5,q6,q7,q8,q9]

def v424 : List W := [q96,q2,q3,q4,q113,q1,q5,q6,q7,q8,q9]

def v425 : List W := [q11,q1,q2,q3,q4,q113,q5,q6,q7,q8,q9]

def v426 : List W := [q115,q5,q1,q2,q3,q4,q113,q6,q7,q8,q9]

def v427 : List W := [q120,q7,q6,q5,q1,q2,q3,q4,q113,q8,q9]

def v428 : List W := [q122,q8,q7,q6,q5,q1,q2,q3,q4,q113,q9]

def v429 : List W := [q54,q3,q0,q113,q2,q1,q5,q6,q7,q8,q9]

def v430 : List W := [q45,q3,q0,q113,q1,q5,q6,q7,q8,q9]

def v431 : List W := [q45,q4,q3,q0,q113,q1,q5,q6,q7,q8,q9]

def v432 : List W := [q45,q2,q3,q0,q113,q1,q5,q6,q7,q8,q9]

def v433 : List W := [q73,q8,q7,q6,q5,q1,q2,q3,q0,q113,q9]

def v434 : List W := [q75,q9,q8,q7,q6,q5,q1,q2,q3,q0,q113]

def v435 : List W := [q28,q1,q3,q4,q0,q113,q5,q6,q7,q8,q9]

def v436 : List W := [q47,q5,q1,q3,q4,q0,q113,q6,q7,q8,q9]

def v437 : List W := [q114,q0,q4,q3,q2,q1,q5,q6,q7,q8,q9]

def v438 : List W := [q115,q0,q5,q4,q3,q2,q1,q6,q7,q8,q9]

def v439 : List W := [q141,q4,q5,q0,q3,q2,q1,q6,q7,q8,q9]

def v440 : List W := [q149,q5,q0,q3,q2,q1,q6,q7,q8,q9]

def v441 : List W := [q149,q115,q5,q0,q3,q2,q1,q6,q7,q8,q9]

def v442 : List W := [q149,q4,q5,q0,q3,q2,q1,q6,q7,q8,q9]

def v443 : List W := [q150,q3,q4,q5,q0,q2,q1,q6,q7,q8,q9]

def v444 : List W := [q151,q4,q5,q0,q2,q1,q6,q7,q8,q9]

def v445 : List W := [q151,q115,q4,q5,q0,q2,q1,q6,q7,q8,q9]

def v446 : List W := [q151,q3,q4,q5,q0,q2,q1,q6,q7,q8,q9]

def v447 : List W := [q103,q2,q3,q4,q5,q0,q1,q6,q7,q8,q9]

def v448 : List W := [q152,q3,q4,q5,q0,q1,q6,q7,q8,q9]

def v449 : List W := [q152,q115,q3,q4,q5,q0,q1,q6,q7,q8,q9]

def v450 : List W := [q152,q2,q3,q4,q5,q0,q1,q6,q7,q8,q9]

def v451 : List W := [q153,q2,q3,q4,q5,q0,q6,q7,q8,q9]

def v452 : List W := [q153,q115,q2,q3,q4,q5,q0,q6,q7,q8,q9]

def v453 : List W := [q153,q1,q2,q3,q4,q5,q0,q6,q7,q8,q9]

def v454 : List W := [q154,q6,q1,q2,q3,q4,q5,q0,q7,q8,q9]

def v455 : List W := [q155,q1,q2,q3,q4,q5,q0,q7,q8,q9]

def v456 : List W := [q155,q115,q1,q2,q3,q4,q5,q0,q7,q8,q9]

def v457 : List W := [q155,q6,q1,q2,q3,q4,q5,q0,q7,q8,q9]

def v458 : List W := [q156,q7,q6,q1,q2,q3,q4,q5,q0,q8,q9]

def v459 : List W := [q157,q6,q1,q2,q3,q4,q5,q0,q8,q9]

def v460 : List W := [q157,q115,q6,q1,q2,q3,q4,q5,q0,q8,q9]

def v461 : List W := [q157,q7,q6,q1,q2,q3,q4,q5,q0,q8,q9]

def v462 : List W := [q158,q8,q7,q6,q1,q2,q3,q4,q5,q0,q9]

def v463 : List W := [q159,q7,q6,q1,q2,q3,q4,q5,q0,q9]

def v464 : List W := [q159,q115,q7,q6,q1,q2,q3,q4,q5,q0,q9]

def v465 : List W := [q159,q8,q7,q6,q1,q2,q3,q4,q5,q0,q9]

def v466 : List W := [q116,q115,q4,q3,q2,q1,q6,q7,q8,q9]

def v467 : List W := [q116,q0,q115,q4,q3,q2,q1,q6,q7,q8,q9]

def v468 : List W := [q116,q5,q115,q4,q3,q2,q1,q6,q7,q8,q9]

def v469 : List W := [q113,q4,q5,q115,q3,q2,q1,q6,q7,q8,q9]

def v470 : List W := [q112,q3,q4,q5,q115,q2,q1,q6,q7,q8,q9]

def v471 : List W := [q96,q0,q3,q4,q5,q115,q1,q6,q7,q8,q9]

def v472 : List W := [q96,q2,q3,q4,q5,q115,q1,q6,q7,q8,q9]

def v473 : List W := [q11,q1,q2,q3,q4,q5,q115,q6,q7,q8,q9]

def v474 : List W := [q120,q7,q6,q1,q2,q3,q4,q5,q115,q8,q9]

def v475 : List W := [q47,q5,q3,q4,q0,q115,q1,q6,q7,q8,q9]

def v476 : List W := [q45,q4,q3,q5,q0,q115,q1,q6,q7,q8,q9]

def v477 : List W := [q28,q1,q3,q4,q5,q0,q115,q6,q7,q8,q9]

def v478 : List W := [q116,q0,q5,q4,q3,q2,q1,q6,q7,q8,q9]

def v479 : List W := [q117,q0,q6,q5,q4,q3,q2,q1,q7,q8,q9]

def v480 : List W := [q118,q0,q6,q5,q4,q3,q2,q1,q7,q8,q9]

def v481 : List W := [q119,q0,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v482 : List W := [q120,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v483 : List W := [q160,q120,q6,q7,q5,q4,q3,q2,q1,q8,q9]

def v484 : List W := [q161,q120,q6,q7,q5,q4,q3,q2,q1,q8,q9]

def v485 : List W := [q162,q120,q5,q6,q7,q4,q3,q2,q1,q8,q9]

def v486 : List W := [q163,q120,q5,q6,q7,q4,q3,q2,q1,q8,q9]

def v487 : List W := [q164,q120,q4,q5,q6,q7,q3,q2,q1,q8,q9]

def v488 : List W := [q165,q120,q4,q5,q6,q7,q3,q2,q1,q8,q9]

def v489 : List W := [q166,q120,q3,q4,q5,q6,q7,q2,q1,q8,q9]

def v490 : List W := [q132,q3,q4,q5,q6,q7,q2,q1,q8,q9]

def v491 : List W := [q132,q120,q3,q4,q5,q6,q7,q2,q1,q8,q9]

def v492 : List W := [q167,q120,q3,q4,q5,q6,q7,q1,q8,q9]

def v493 : List W := [q167,q2,q3,q4,q5,q6,q7,q1,q8,q9]

def v494 : List W := [q167,q120,q2,q3,q4,q5,q6,q7,q1,q8,q9]

def v495 : List W := [q93,q120,q2,q3,q4,q5,q6,q7,q1,q8,q9]

def v496 : List W := [q168,q120,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v497 : List W := [q23,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v498 : List W := [q23,q120,q1,q2,q3,q4,q5,q6,q7,q8,q9]

def v499 : List W := [q169,q120,q8,q1,q2,q3,q4,q5,q6,q7,q9]

def v500 : List W := [q170,q120,q8,q1,q2,q3,q4,q5,q6,q7,q9]

def v501 : List W := [q171,q9,q8,q1,q2,q3,q4,q5,q6,q7]

def v502 : List W := [q171,q120,q9,q8,q1,q2,q3,q4,q5,q6,q7]

def v503 : List W := [q93,q120,q9,q8,q1,q2,q3,q4,q5,q6,q7]

def v504 : List W := [q84,q7,q6,q120,q5,q4,q3,q2,q1,q8,q9]

def v505 : List W := [q85,q7,q6,q120,q5,q4,q3,q2,q1,q8,q9]

def v506 : List W := [q78,q7,q5,q6,q120,q4,q3,q2,q1,q8,q9]

def v507 : List W := [q79,q5,q6,q120,q4,q3,q2,q1,q8,q9]

def v508 : List W := [q79,q7,q5,q6,q120,q4,q3,q2,q1,q8,q9]

def v509 : List W := [q70,q7,q4,q5,q6,q120,q3,q2,q1,q8,q9]

def v510 : List W := [q71,q4,q5,q6,q120,q3,q2,q1,q8,q9]

def v511 : List W := [q71,q7,q4,q5,q6,q120,q3,q2,q1,q8,q9]

def v512 : List W := [q60,q7,q3,q4,q5,q6,q120,q2,q1,q8,q9]

def v513 : List W := [q61,q3,q4,q5,q6,q120,q2,q1,q8,q9]

def v514 : List W := [q61,q7,q3,q4,q5,q6,q120,q2,q1,q8,q9]

def v515 : List W := [q50,q2,q3,q4,q5,q6,q120,q1,q8,q9]

def v516 : List W := [q50,q7,q2,q3,q4,q5,q6,q120,q1,q8,q9]

def v517 : List W := [q51,q7,q2,q3,q4,q5,q6,q120,q1,q8,q9]

def v518 : List W := [q37,q7,q1,q2,q3,q4,q5,q6,q120,q8,q9]

def v519 : List W := [q38,q1,q2,q3,q4,q5,q6,q120,q8,q9]

def v520 : List W := [q38,q7,q1,q2,q3,q4,q5,q6,q120,q8,q9]

def v521 : List W := [q90,q7,q8,q1,q2,q3,q4,q5,q6,q120,q9]

def v522 : List W := [q91,q7,q8,q1,q2,q3,q4,q5,q6,q120,q9]

def v523 : List W := [q92,q9,q8,q1,q2,q3,q4,q5,q6,q120]

def v524 : List W := [q92,q7,q9,q8,q1,q2,q3,q4,q5,q6,q120]

def v525 : List W := [q93,q7,q9,q8,q1,q2,q3,q4,q5,q6,q120]

def v526 : List W := [q76,q6,q5,q7,q120,q4,q3,q2,q1,q8,q9]

def v527 : List W := [q77,q6,q5,q7,q120,q4,q3,q2,q1,q8,q9]

def v528 : List W := [q68,q6,q4,q5,q7,q120,q3,q2,q1,q8,q9]

def v529 : List W := [q69,q6,q4,q5,q7,q120,q3,q2,q1,q8,q9]

def v530 : List W := [q58,q6,q3,q4,q5,q7,q120,q2,q1,q8,q9]

def v531 : List W := [q59,q6,q3,q4,q5,q7,q120,q2,q1,q8,q9]

def v532 : List W := [q48,q6,q2,q3,q4,q5,q7,q120,q1,q8,q9]

def v533 : List W := [q49,q6,q2,q3,q4,q5,q7,q120,q1,q8,q9]

def v534 : List W := [q35,q6,q1,q2,q3,q4,q5,q7,q120,q8,q9]

def v535 : List W := [q36,q6,q1,q2,q3,q4,q5,q7,q120,q8,q9]

def v536 : List W := [q86,q6,q8,q1,q2,q3,q4,q5,q7,q120,q9]

def v537 : List W := [q87,q6,q8,q1,q2,q3,q4,q5,q7,q120,q9]

def v538 : List W := [q88,q6,q9,q8,q1,q2,q3,q4,q5,q7,q120]

def v539 : List W := [q89,q6,q9,q8,q1,q2,q3,q4,q5,q7,q120]

def v540 : List W := [q66,q5,q4,q6,q7,q120,q3,q2,q1,q8,q9]

def v541 : List W := [q67,q5,q4,q6,q7,q120,q3,q2,q1,q8,q9]

def v542 : List W := [q56,q5,q3,q4,q6,q7,q120,q2,q1,q8,q9]

def v543 : List W := [q57,q5,q3,q4,q6,q7,q120,q2,q1,q8,q9]

def v544 : List W := [q46,q5,q2,q3,q4,q6,q7,q120,q1,q8,q9]

def v545 : List W := [q47,q5,q3,q4,q6,q7,q120,q1,q8,q9]

def v546 : List W := [q47,q5,q2,q3,q4,q6,q7,q120,q1,q8,q9]

def v547 : List W := [q33,q5,q1,q2,q3,q4,q6,q7,q120,q8,q9]

def v548 : List W := [q34,q5,q1,q2,q3,q4,q6,q7,q120,q8,q9]

def v549 : List W := [q80,q5,q8,q1,q2,q3,q4,q6,q7,q120,q9]

def v550 : List W := [q81,q5,q8,q1,q2,q3,q4,q6,q7,q120,q9]

def v551 : List W := [q82,q5,q9,q8,q1,q2,q3,q4,q6,q7,q120]

def v552 : List W := [q83,q5,q9,q8,q1,q2,q3,q4,q6,q7,q120]

def v553 : List W := [q54,q4,q3,q5,q6,q7,q120,q2,q1,q8,q9]

def v554 : List W := [q55,q4,q3,q5,q6,q7,q120,q2,q1,q8,q9]

def v555 : List W := [q44,q4,q2,q3,q5,q6,q7,q120,q1,q8,q9]

def v556 : List W := [q45,q4,q3,q5,q6,q7,q120,q1,q8,q9]

def v557 : List W := [q45,q4,q2,q3,q5,q6,q7,q120,q1,q8,q9]

def v558 : List W := [q31,q4,q1,q2,q3,q5,q6,q7,q120,q8,q9]

def v559 : List W := [q32,q4,q1,q2,q3,q5,q6,q7,q120,q8,q9]

def v560 : List W := [q72,q4,q8,q1,q2,q3,q5,q6,q7,q120,q9]

def v561 : List W := [q73,q4,q8,q1,q2,q3,q5,q6,q7,q120,q9]

def v562 : List W := [q74,q4,q9,q8,q1,q2,q3,q5,q6,q7,q120]

def v563 : List W := [q75,q4,q9,q8,q1,q2,q3,q5,q6,q7,q120]

def v564 : List W := [q42,q3,q2,q4,q5,q6,q7,q120,q1,q8,q9]

def v565 : List W := [q43,q3,q2,q4,q5,q6,q7,q120,q1,q8,q9]

def v566 : List W := [q29,q3,q1,q2,q4,q5,q6,q7,q120,q8,q9]

def v567 : List W := [q30,q3,q1,q2,q4,q5,q6,q7,q120,q8,q9]

def v568 : List W := [q62,q3,q8,q1,q2,q4,q5,q6,q7,q120,q9]

def v569 : List W := [q63,q3,q8,q1,q2,q4,q5,q6,q7,q120,q9]

def v570 : List W := [q64,q3,q9,q8,q1,q2,q4,q5,q6,q7,q120]

def v571 : List W := [q65,q3,q9,q8,q1,q2,q4,q5,q6,q7,q120]

def v572 : List W := [q27,q2,q1,q3,q4,q5,q6,q7,q120,q8,q9]

def v573 : List W := [q28,q1,q3,q4,q5,q6,q7,q120,q8,q9]

def v574 : List W := [q28,q2,q1,q3,q4,q5,q6,q7,q120,q8,q9]

def v575 : List W := [q52,q2,q8,q1,q3,q4,q5,q6,q7,q120,q9]

def v576 : List W := [q53,q2,q8,q1,q3,q4,q5,q6,q7,q120,q9]

def v577 : List W := [q39,q1,q8,q2,q3,q4,q5,q6,q7,q120,q9]

def v578 : List W := [q40,q1,q8,q2,q3,q4,q5,q6,q7,q120,q9]

def v579 : List W := [q41,q1,q9,q8,q2,q3,q4,q5,q6,q7,q120]

def v580 : List W := [q13,q1,q9,q8,q2,q3,q4,q5,q6,q7,q120]

def v581 : List W := [q94,q8,q9,q1,q2,q3,q4,q5,q6,q7,q120]

def v582 : List W := [q95,q8,q9,q1,q2,q3,q4,q5,q6,q7,q120]

def v583 : List W := [q120,q0,q7,q6,q5,q4,q3,q2,q1,q8,q9]

def v584 : List W := [q121,q0,q8,q7,q6,q5,q4,q3,q2,q1,q9]

def v585 : List W := [q122,q0,q8,q7,q6,q5,q4,q3,q2,q1,q9]

def v586 : List W := [q27,q1,q2,q0,q3,q4,q5,q6,q7,q8,q9]

def v587 : List W := [q28,q1,q0,q3,q4,q5,q6,q7,q8,q9]

def v588 : List W := [q172,q28,q1,q3,q4,q5,q6,q7,q8,q9]

def v589 : List W := [q172,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v590 : List W := [q172,q28,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v591 : List W := [q13,q28,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v592 : List W := [q173,q28,q3,q0,q1,q4,q5,q6,q7,q8,q9]

def v593 : List W := [q174,q28,q3,q0,q1,q4,q5,q6,q7,q8,q9]

def v594 : List W := [q175,q28,q4,q3,q0,q1,q5,q6,q7,q8,q9]

def v595 : List W := [q176,q4,q3,q0,q1,q5,q6,q7,q8,q9]

def v596 : List W := [q176,q28,q4,q3,q0,q1,q5,q6,q7,q8,q9]

def v597 : List W := [q177,q28,q5,q4,q3,q0,q1,q6,q7,q8,q9]

def v598 : List W := [q178,q5,q4,q3,q0,q1,q6,q7,q8,q9]

def v599 : List W := [q178,q28,q5,q4,q3,q0,q1,q6,q7,q8,q9]

def v600 : List W := [q179,q28,q6,q5,q4,q3,q0,q1,q7,q8,q9]

def v601 : List W := [q180,q28,q6,q5,q4,q3,q0,q1,q7,q8,q9]

def v602 : List W := [q181,q28,q7,q6,q5,q4,q3,q0,q1,q8,q9]

def v603 : List W := [q182,q28,q7,q6,q5,q4,q3,q0,q1,q8,q9]

def v604 : List W := [q183,q28,q8,q7,q6,q5,q4,q3,q0,q1,q9]

def v605 : List W := [q184,q28,q8,q7,q6,q5,q4,q3,q0,q1,q9]

def v606 : List W := [q185,q9,q8,q7,q6,q5,q4,q3,q0,q1]

def v607 : List W := [q185,q28,q9,q8,q7,q6,q5,q4,q3,q0,q1]

def v608 : List W := [q13,q28,q9,q8,q7,q6,q5,q4,q3,q0,q1]

def v609 : List W := [q10,q1,q0,q28,q3,q4,q5,q6,q7,q8,q9]

def v610 : List W := [q11,q1,q28,q3,q4,q5,q6,q7,q8,q9]

def v611 : List W := [q11,q1,q0,q28,q3,q4,q5,q6,q7,q8,q9]

def v612 : List W := [q29,q1,q3,q0,q28,q4,q5,q6,q7,q8,q9]

def v613 : List W := [q30,q3,q0,q28,q4,q5,q6,q7,q8,q9]

def v614 : List W := [q30,q1,q3,q0,q28,q4,q5,q6,q7,q8,q9]

def v615 : List W := [q31,q1,q4,q3,q0,q28,q5,q6,q7,q8,q9]

def v616 : List W := [q32,q1,q4,q3,q0,q28,q5,q6,q7,q8,q9]

def v617 : List W := [q33,q1,q5,q4,q3,q0,q28,q6,q7,q8,q9]

def v618 : List W := [q34,q1,q5,q4,q3,q0,q28,q6,q7,q8,q9]

def v619 : List W := [q35,q1,q6,q5,q4,q3,q0,q28,q7,q8,q9]

def v620 : List W := [q36,q1,q6,q5,q4,q3,q0,q28,q7,q8,q9]

def v621 : List W := [q37,q1,q7,q6,q5,q4,q3,q0,q28,q8,q9]

def v622 : List W := [q38,q7,q6,q5,q4,q3,q0,q28,q8,q9]

def v623 : List W := [q38,q1,q7,q6,q5,q4,q3,q0,q28,q8,q9]

def v624 : List W := [q39,q1,q8,q7,q6,q5,q4,q3,q0,q28,q9]

def v625 : List W := [q40,q1,q8,q7,q6,q5,q4,q3,q0,q28,q9]

def v626 : List W := [q41,q9,q8,q7,q6,q5,q4,q3,q0,q28]

def v627 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q3,q0,q28]

def v628 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q3,q0,q28]

def v629 : List W := [q111,q0,q3,q1,q28,q4,q5,q6,q7,q8,q9]

def v630 : List W := [q112,q3,q1,q28,q4,q5,q6,q7,q8,q9]

def v631 : List W := [q112,q0,q3,q1,q28,q4,q5,q6,q7,q8,q9]

def v632 : List W := [q113,q0,q4,q3,q1,q28,q5,q6,q7,q8,q9]

def v633 : List W := [q114,q0,q4,q3,q1,q28,q5,q6,q7,q8,q9]

def v634 : List W := [q115,q0,q5,q4,q3,q1,q28,q6,q7,q8,q9]

def v635 : List W := [q116,q0,q5,q4,q3,q1,q28,q6,q7,q8,q9]

def v636 : List W := [q117,q0,q6,q5,q4,q3,q1,q28,q7,q8,q9]

def v637 : List W := [q118,q0,q6,q5,q4,q3,q1,q28,q7,q8,q9]

def v638 : List W := [q119,q0,q7,q6,q5,q4,q3,q1,q28,q8,q9]

def v639 : List W := [q120,q7,q6,q5,q4,q3,q1,q28,q8,q9]

def v640 : List W := [q120,q0,q7,q6,q5,q4,q3,q1,q28,q8,q9]

def v641 : List W := [q121,q0,q8,q7,q6,q5,q4,q3,q1,q28,q9]

def v642 : List W := [q122,q0,q8,q7,q6,q5,q4,q3,q1,q28,q9]

def v643 : List W := [q54,q3,q4,q0,q1,q28,q5,q6,q7,q8,q9]

def v644 : List W := [q55,q3,q4,q0,q1,q28,q5,q6,q7,q8,q9]

def v645 : List W := [q56,q3,q5,q4,q0,q1,q28,q6,q7,q8,q9]

def v646 : List W := [q57,q3,q5,q4,q0,q1,q28,q6,q7,q8,q9]

def v647 : List W := [q58,q3,q6,q5,q4,q0,q1,q28,q7,q8,q9]

def v648 : List W := [q59,q3,q6,q5,q4,q0,q1,q28,q7,q8,q9]

def v649 : List W := [q60,q3,q7,q6,q5,q4,q0,q1,q28,q8,q9]

def v650 : List W := [q61,q3,q7,q6,q5,q4,q0,q1,q28,q8,q9]

def v651 : List W := [q62,q3,q8,q7,q6,q5,q4,q0,q1,q28,q9]

def v652 : List W := [q63,q3,q8,q7,q6,q5,q4,q0,q1,q28,q9]

def v653 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q0,q1,q28]

def v654 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q0,q1,q28]

def v655 : List W := [q66,q4,q5,q3,q0,q1,q28,q6,q7,q8,q9]

def v656 : List W := [q67,q4,q5,q3,q0,q1,q28,q6,q7,q8,q9]

def v657 : List W := [q68,q4,q6,q5,q3,q0,q1,q28,q7,q8,q9]

def v658 : List W := [q69,q4,q6,q5,q3,q0,q1,q28,q7,q8,q9]

def v659 : List W := [q70,q4,q7,q6,q5,q3,q0,q1,q28,q8,q9]

def v660 : List W := [q71,q4,q7,q6,q5,q3,q0,q1,q28,q8,q9]

def v661 : List W := [q72,q4,q8,q7,q6,q5,q3,q0,q1,q28,q9]

def v662 : List W := [q73,q4,q8,q7,q6,q5,q3,q0,q1,q28,q9]

def v663 : List W := [q74,q4,q9,q8,q7,q6,q5,q3,q0,q1,q28]

def v664 : List W := [q75,q4,q9,q8,q7,q6,q5,q3,q0,q1,q28]

def v665 : List W := [q76,q5,q6,q4,q3,q0,q1,q28,q7,q8,q9]

def v666 : List W := [q77,q5,q6,q4,q3,q0,q1,q28,q7,q8,q9]

def v667 : List W := [q78,q5,q7,q6,q4,q3,q0,q1,q28,q8,q9]

def v668 : List W := [q79,q5,q7,q6,q4,q3,q0,q1,q28,q8,q9]

def v669 : List W := [q80,q5,q8,q7,q6,q4,q3,q0,q1,q28,q9]

def v670 : List W := [q81,q5,q8,q7,q6,q4,q3,q0,q1,q28,q9]

def v671 : List W := [q82,q5,q9,q8,q7,q6,q4,q3,q0,q1,q28]

def v672 : List W := [q83,q5,q9,q8,q7,q6,q4,q3,q0,q1,q28]

def v673 : List W := [q84,q6,q7,q5,q4,q3,q0,q1,q28,q8,q9]

def v674 : List W := [q85,q6,q7,q5,q4,q3,q0,q1,q28,q8,q9]

def v675 : List W := [q86,q6,q8,q7,q5,q4,q3,q0,q1,q28,q9]

def v676 : List W := [q87,q6,q8,q7,q5,q4,q3,q0,q1,q28,q9]

def v677 : List W := [q88,q6,q9,q8,q7,q5,q4,q3,q0,q1,q28]

def v678 : List W := [q89,q6,q9,q8,q7,q5,q4,q3,q0,q1,q28]

def v679 : List W := [q90,q7,q8,q6,q5,q4,q3,q0,q1,q28,q9]

def v680 : List W := [q91,q7,q8,q6,q5,q4,q3,q0,q1,q28,q9]

def v681 : List W := [q92,q7,q9,q8,q6,q5,q4,q3,q0,q1,q28]

def v682 : List W := [q93,q7,q9,q8,q6,q5,q4,q3,q0,q1,q28]

def v683 : List W := [q94,q8,q9,q7,q6,q5,q4,q3,q0,q1,q28]

def v684 : List W := [q95,q8,q9,q7,q6,q5,q4,q3,q0,q1,q28]

def v685 : List W := [q28,q1,q2,q0,q3,q4,q5,q6,q7,q8,q9]

def v686 : List W := [q29,q1,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v687 : List W := [q30,q1,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v688 : List W := [q31,q1,q4,q3,q2,q0,q5,q6,q7,q8,q9]

def v689 : List W := [q32,q1,q4,q3,q2,q0,q5,q6,q7,q8,q9]

def v690 : List W := [q33,q1,q5,q4,q3,q2,q0,q6,q7,q8,q9]

def v691 : List W := [q34,q1,q5,q4,q3,q2,q0,q6,q7,q8,q9]

def v692 : List W := [q35,q1,q6,q5,q4,q3,q2,q0,q7,q8,q9]

def v693 : List W := [q36,q1,q6,q5,q4,q3,q2,q0,q7,q8,q9]

def v694 : List W := [q37,q1,q7,q6,q5,q4,q3,q2,q0,q8,q9]

def v695 : List W := [q38,q1,q7,q6,q5,q4,q3,q2,q0,q8,q9]

def v696 : List W := [q39,q1,q8,q7,q6,q5,q4,q3,q2,q0,q9]

def v697 : List W := [q40,q1,q8,q7,q6,q5,q4,q3,q2,q0,q9]

def v698 : List W := [q41,q1,q9,q8,q7,q6,q5,q4,q3,q2,q0]

def v699 : List W := [q186,q8,q9,q1,q7,q6,q5,q4,q3,q2,q0]

def v700 : List W := [q187,q9,q1,q7,q6,q5,q4,q3,q2,q0]

def v701 : List W := [q187,q41,q9,q1,q7,q6,q5,q4,q3,q2,q0]

def v702 : List W := [q187,q8,q9,q1,q7,q6,q5,q4,q3,q2,q0]

def v703 : List W := [q188,q7,q8,q9,q1,q6,q5,q4,q3,q2,q0]

def v704 : List W := [q189,q8,q9,q1,q6,q5,q4,q3,q2,q0]

def v705 : List W := [q189,q41,q8,q9,q1,q6,q5,q4,q3,q2,q0]

def v706 : List W := [q189,q7,q8,q9,q1,q6,q5,q4,q3,q2,q0]

def v707 : List W := [q190,q6,q7,q8,q9,q1,q5,q4,q3,q2,q0]

def v708 : List W := [q191,q7,q8,q9,q1,q5,q4,q3,q2,q0]

def v709 : List W := [q191,q41,q7,q8,q9,q1,q5,q4,q3,q2,q0]

def v710 : List W := [q191,q6,q7,q8,q9,q1,q5,q4,q3,q2,q0]

def v711 : List W := [q192,q5,q6,q7,q8,q9,q1,q4,q3,q2,q0]

def v712 : List W := [q193,q6,q7,q8,q9,q1,q4,q3,q2,q0]

def v713 : List W := [q193,q41,q6,q7,q8,q9,q1,q4,q3,q2,q0]

def v714 : List W := [q193,q5,q6,q7,q8,q9,q1,q4,q3,q2,q0]

def v715 : List W := [q194,q4,q5,q6,q7,q8,q9,q1,q3,q2,q0]

def v716 : List W := [q195,q5,q6,q7,q8,q9,q1,q3,q2,q0]

def v717 : List W := [q195,q41,q5,q6,q7,q8,q9,q1,q3,q2,q0]

def v718 : List W := [q195,q4,q5,q6,q7,q8,q9,q1,q3,q2,q0]

def v719 : List W := [q196,q3,q4,q5,q6,q7,q8,q9,q1,q2,q0]

def v720 : List W := [q197,q4,q5,q6,q7,q8,q9,q1,q2,q0]

def v721 : List W := [q197,q41,q4,q5,q6,q7,q8,q9,q1,q2,q0]

def v722 : List W := [q197,q3,q4,q5,q6,q7,q8,q9,q1,q2,q0]

def v723 : List W := [q27,q2,q3,q4,q5,q6,q7,q8,q9,q1,q0]

def v724 : List W := [q185,q3,q4,q5,q6,q7,q8,q9,q1,q0]

def v725 : List W := [q185,q41,q3,q4,q5,q6,q7,q8,q9,q1,q0]

def v726 : List W := [q185,q2,q3,q4,q5,q6,q7,q8,q9,q1,q0]

def v727 : List W := [q10,q0,q2,q3,q4,q5,q6,q7,q8,q9,q1]

def v728 : List W := [q26,q2,q3,q4,q5,q6,q7,q8,q9,q1]

def v729 : List W := [q26,q41,q2,q3,q4,q5,q6,q7,q8,q9,q1]

def v730 : List W := [q26,q0,q2,q3,q4,q5,q6,q7,q8,q9,q1]

def v731 : List W := [q13,q9,q41,q8,q7,q6,q5,q4,q3,q2,q0]

def v732 : List W := [q40,q8,q9,q41,q7,q6,q5,q4,q3,q2,q0]

def v733 : List W := [q35,q6,q7,q8,q9,q41,q5,q4,q3,q2,q0]

def v734 : List W := [q28,q3,q4,q5,q6,q7,q8,q9,q41,q0]

def v735 : List W := [q28,q1,q3,q4,q5,q6,q7,q8,q9,q41,q0]

def v736 : List W := [q28,q2,q3,q4,q5,q6,q7,q8,q9,q41,q0]

def v737 : List W := [q11,q2,q3,q4,q5,q6,q7,q8,q9,q41]

def v738 : List W := [q11,q1,q2,q3,q4,q5,q6,q7,q8,q9,q41]

def v739 : List W := [q11,q0,q2,q3,q4,q5,q6,q7,q8,q9,q41]

def v740 : List W := [q120,q7,q2,q3,q4,q5,q6,q8,q9,q1,q41]

def v741 : List W := [q47,q5,q3,q4,q6,q7,q8,q9,q1,q41,q0]

def v742 : List W := [q45,q4,q3,q5,q6,q7,q8,q9,q1,q41,q0]

def v743 : List W := [q112,q3,q2,q4,q5,q6,q7,q8,q9,q1,q41]

def v744 : List W := [q96,q2,q3,q4,q5,q6,q7,q8,q9,q1,q41]

def v745 : List W := [q96,q0,q3,q4,q5,q6,q7,q8,q9,q1,q41]

def v746 : List W := [q13,q1,q9,q8,q7,q6,q5,q4,q3,q2,q0]

def v747 : List W := [q42,q2,q3,q1,q0,q4,q5,q6,q7,q8,q9]

def v748 : List W := [q198,q1,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v749 : List W := [q199,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v750 : List W := [q199,q42,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v751 : List W := [q199,q1,q3,q2,q0,q4,q5,q6,q7,q8,q9]

def v752 : List W := [q99,q0,q1,q3,q2,q4,q5,q6,q7,q8,q9]

def v753 : List W := [q135,q1,q3,q2,q4,q5,q6,q7,q8,q9]

def v754 : List W := [q135,q42,q1,q3,q2,q4,q5,q6,q7,q8,q9]

def v755 : List W := [q135,q0,q1,q3,q2,q4,q5,q6,q7,q8,q9]

def v756 : List W := [q200,q4,q0,q1,q3,q2,q5,q6,q7,q8,q9]

def v757 : List W := [q201,q0,q1,q3,q2,q5,q6,q7,q8,q9]

def v758 : List W := [q201,q42,q0,q1,q3,q2,q5,q6,q7,q8,q9]

def v759 : List W := [q201,q4,q0,q1,q3,q2,q5,q6,q7,q8,q9]

def v760 : List W := [q202,q5,q4,q0,q1,q3,q2,q6,q7,q8,q9]

def v761 : List W := [q203,q4,q0,q1,q3,q2,q6,q7,q8,q9]

def v762 : List W := [q203,q42,q4,q0,q1,q3,q2,q6,q7,q8,q9]

def v763 : List W := [q203,q5,q4,q0,q1,q3,q2,q6,q7,q8,q9]

def v764 : List W := [q204,q6,q5,q4,q0,q1,q3,q2,q7,q8,q9]

def v765 : List W := [q205,q5,q4,q0,q1,q3,q2,q7,q8,q9]

def v766 : List W := [q205,q42,q5,q4,q0,q1,q3,q2,q7,q8,q9]

def v767 : List W := [q205,q6,q5,q4,q0,q1,q3,q2,q7,q8,q9]

def v768 : List W := [q206,q7,q6,q5,q4,q0,q1,q3,q2,q8,q9]

def v769 : List W := [q207,q6,q5,q4,q0,q1,q3,q2,q8,q9]

def v770 : List W := [q207,q42,q6,q5,q4,q0,q1,q3,q2,q8,q9]

def v771 : List W := [q207,q7,q6,q5,q4,q0,q1,q3,q2,q8,q9]

def v772 : List W := [q208,q8,q7,q6,q5,q4,q0,q1,q3,q2,q9]

def v773 : List W := [q209,q7,q6,q5,q4,q0,q1,q3,q2,q9]

def v774 : List W := [q209,q42,q7,q6,q5,q4,q0,q1,q3,q2,q9]

def v775 : List W := [q209,q8,q7,q6,q5,q4,q0,q1,q3,q2,q9]

def v776 : List W := [q43,q42,q1,q0,q4,q5,q6,q7,q8,q9]

def v777 : List W := [q43,q2,q42,q1,q0,q4,q5,q6,q7,q8,q9]

def v778 : List W := [q43,q3,q42,q1,q0,q4,q5,q6,q7,q8,q9]

def v779 : List W := [q28,q1,q3,q42,q0,q4,q5,q6,q7,q8,q9]

def v780 : List W := [q96,q2,q1,q3,q42,q4,q5,q6,q7,q8,q9]

def v781 : List W := [q96,q0,q1,q3,q42,q4,q5,q6,q7,q8,q9]

def v782 : List W := [q45,q4,q0,q1,q3,q42,q5,q6,q7,q8,q9]

def v783 : List W := [q47,q5,q4,q0,q1,q3,q42,q6,q7,q8,q9]

def v784 : List W := [q50,q7,q6,q5,q4,q0,q1,q3,q42,q8,q9]

def v785 : List W := [q112,q3,q1,q2,q42,q4,q5,q6,q7,q8,q9]

def v786 : List W := [q11,q1,q3,q2,q42,q4,q5,q6,q7,q8,q9]

def v787 : List W := [q120,q7,q6,q5,q4,q1,q3,q2,q42,q8,q9]

def v788 : List W := [q43,q2,q3,q1,q0,q4,q5,q6,q7,q8,q9]

def v789 : List W := [q44,q2,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v790 : List W := [q45,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v791 : List W := [q210,q45,q3,q4,q1,q0,q5,q6,q7,q8,q9]

def v792 : List W := [q211,q45,q3,q4,q1,q0,q5,q6,q7,q8,q9]

def v793 : List W := [q212,q45,q1,q3,q4,q0,q5,q6,q7,q8,q9]

def v794 : List W := [q176,q1,q3,q4,q0,q5,q6,q7,q8,q9]

def v795 : List W := [q176,q45,q1,q3,q4,q0,q5,q6,q7,q8,q9]

def v796 : List W := [q213,q45,q1,q3,q4,q5,q6,q7,q8,q9]

def v797 : List W := [q213,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v798 : List W := [q213,q45,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v799 : List W := [q75,q45,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v800 : List W := [q214,q45,q5,q0,q1,q3,q4,q6,q7,q8,q9]

def v801 : List W := [q215,q5,q0,q1,q3,q4,q6,q7,q8,q9]

def v802 : List W := [q215,q45,q5,q0,q1,q3,q4,q6,q7,q8,q9]

def v803 : List W := [q216,q45,q6,q5,q0,q1,q3,q4,q7,q8,q9]

def v804 : List W := [q217,q45,q6,q5,q0,q1,q3,q4,q7,q8,q9]

def v805 : List W := [q218,q45,q7,q6,q5,q0,q1,q3,q4,q8,q9]

def v806 : List W := [q219,q45,q7,q6,q5,q0,q1,q3,q4,q8,q9]

def v807 : List W := [q220,q45,q8,q7,q6,q5,q0,q1,q3,q4,q9]

def v808 : List W := [q221,q45,q8,q7,q6,q5,q0,q1,q3,q4,q9]

def v809 : List W := [q138,q9,q8,q7,q6,q5,q0,q1,q3,q4]

def v810 : List W := [q138,q45,q9,q8,q7,q6,q5,q0,q1,q3,q4]

def v811 : List W := [q75,q45,q9,q8,q7,q6,q5,q0,q1,q3,q4]

def v812 : List W := [q54,q4,q3,q45,q1,q0,q5,q6,q7,q8,q9]

def v813 : List W := [q55,q3,q45,q1,q0,q5,q6,q7,q8,q9]

def v814 : List W := [q55,q4,q3,q45,q1,q0,q5,q6,q7,q8,q9]

def v815 : List W := [q31,q4,q1,q3,q45,q0,q5,q6,q7,q8,q9]

def v816 : List W := [q32,q1,q3,q45,q0,q5,q6,q7,q8,q9]

def v817 : List W := [q32,q4,q1,q3,q45,q0,q5,q6,q7,q8,q9]

def v818 : List W := [q113,q0,q1,q3,q45,q5,q6,q7,q8,q9]

def v819 : List W := [q113,q4,q0,q1,q3,q45,q5,q6,q7,q8,q9]

def v820 : List W := [q114,q4,q0,q1,q3,q45,q5,q6,q7,q8,q9]

def v821 : List W := [q66,q4,q5,q0,q1,q3,q45,q6,q7,q8,q9]

def v822 : List W := [q67,q5,q0,q1,q3,q45,q6,q7,q8,q9]

def v823 : List W := [q67,q4,q5,q0,q1,q3,q45,q6,q7,q8,q9]

def v824 : List W := [q68,q4,q6,q5,q0,q1,q3,q45,q7,q8,q9]

def v825 : List W := [q69,q4,q6,q5,q0,q1,q3,q45,q7,q8,q9]

def v826 : List W := [q70,q4,q7,q6,q5,q0,q1,q3,q45,q8,q9]

def v827 : List W := [q71,q7,q6,q5,q0,q1,q3,q45,q8,q9]

def v828 : List W := [q71,q4,q7,q6,q5,q0,q1,q3,q45,q8,q9]

def v829 : List W := [q72,q4,q8,q7,q6,q5,q0,q1,q3,q45,q9]

def v830 : List W := [q73,q4,q8,q7,q6,q5,q0,q1,q3,q45,q9]

def v831 : List W := [q74,q9,q8,q7,q6,q5,q0,q1,q3,q45]

def v832 : List W := [q74,q4,q9,q8,q7,q6,q5,q0,q1,q3,q45]

def v833 : List W := [q75,q4,q9,q8,q7,q6,q5,q0,q1,q3,q45]

def v834 : List W := [q29,q3,q1,q4,q45,q0,q5,q6,q7,q8,q9]

def v835 : List W := [q30,q3,q1,q4,q45,q0,q5,q6,q7,q8,q9]

def v836 : List W := [q111,q3,q0,q1,q4,q45,q5,q6,q7,q8,q9]

def v837 : List W := [q112,q3,q1,q4,q45,q5,q6,q7,q8,q9]

def v838 : List W := [q112,q3,q0,q1,q4,q45,q5,q6,q7,q8,q9]

def v839 : List W := [q56,q3,q5,q0,q1,q4,q45,q6,q7,q8,q9]

def v840 : List W := [q57,q3,q5,q0,q1,q4,q45,q6,q7,q8,q9]

def v841 : List W := [q58,q3,q6,q5,q0,q1,q4,q45,q7,q8,q9]

def v842 : List W := [q59,q3,q6,q5,q0,q1,q4,q45,q7,q8,q9]

def v843 : List W := [q60,q3,q7,q6,q5,q0,q1,q4,q45,q8,q9]

def v844 : List W := [q61,q3,q7,q6,q5,q0,q1,q4,q45,q8,q9]

def v845 : List W := [q62,q3,q8,q7,q6,q5,q0,q1,q4,q45,q9]

def v846 : List W := [q63,q3,q8,q7,q6,q5,q0,q1,q4,q45,q9]

def v847 : List W := [q64,q3,q9,q8,q7,q6,q5,q0,q1,q4,q45]

def v848 : List W := [q65,q3,q9,q8,q7,q6,q5,q0,q1,q4,q45]

def v849 : List W := [q10,q1,q0,q3,q4,q45,q5,q6,q7,q8,q9]

def v850 : List W := [q11,q1,q3,q4,q45,q5,q6,q7,q8,q9]

def v851 : List W := [q11,q1,q0,q3,q4,q45,q5,q6,q7,q8,q9]

def v852 : List W := [q33,q1,q5,q0,q3,q4,q45,q6,q7,q8,q9]

def v853 : List W := [q34,q1,q5,q0,q3,q4,q45,q6,q7,q8,q9]

def v854 : List W := [q35,q1,q6,q5,q0,q3,q4,q45,q7,q8,q9]

def v855 : List W := [q36,q1,q6,q5,q0,q3,q4,q45,q7,q8,q9]

def v856 : List W := [q37,q1,q7,q6,q5,q0,q3,q4,q45,q8,q9]

def v857 : List W := [q38,q1,q7,q6,q5,q0,q3,q4,q45,q8,q9]

def v858 : List W := [q39,q1,q8,q7,q6,q5,q0,q3,q4,q45,q9]

def v859 : List W := [q40,q1,q8,q7,q6,q5,q0,q3,q4,q45,q9]

def v860 : List W := [q41,q1,q9,q8,q7,q6,q5,q0,q3,q4,q45]

def v861 : List W := [q13,q1,q9,q8,q7,q6,q5,q0,q3,q4,q45]

def v862 : List W := [q115,q0,q5,q1,q3,q4,q45,q6,q7,q8,q9]

def v863 : List W := [q116,q0,q5,q1,q3,q4,q45,q6,q7,q8,q9]

def v864 : List W := [q117,q0,q6,q5,q1,q3,q4,q45,q7,q8,q9]

def v865 : List W := [q118,q0,q6,q5,q1,q3,q4,q45,q7,q8,q9]

def v866 : List W := [q119,q0,q7,q6,q5,q1,q3,q4,q45,q8,q9]

def v867 : List W := [q120,q7,q6,q5,q1,q3,q4,q45,q8,q9]

def v868 : List W := [q120,q0,q7,q6,q5,q1,q3,q4,q45,q8,q9]

def v869 : List W := [q121,q0,q8,q7,q6,q5,q1,q3,q4,q45,q9]

def v870 : List W := [q122,q0,q8,q7,q6,q5,q1,q3,q4,q45,q9]

def v871 : List W := [q76,q5,q6,q0,q1,q3,q4,q45,q7,q8,q9]

def v872 : List W := [q77,q5,q6,q0,q1,q3,q4,q45,q7,q8,q9]

def v873 : List W := [q78,q5,q7,q6,q0,q1,q3,q4,q45,q8,q9]

def v874 : List W := [q79,q5,q7,q6,q0,q1,q3,q4,q45,q8,q9]

def v875 : List W := [q80,q5,q8,q7,q6,q0,q1,q3,q4,q45,q9]

def v876 : List W := [q81,q5,q8,q7,q6,q0,q1,q3,q4,q45,q9]

def v877 : List W := [q82,q5,q9,q8,q7,q6,q0,q1,q3,q4,q45]

def v878 : List W := [q83,q5,q9,q8,q7,q6,q0,q1,q3,q4,q45]

def v879 : List W := [q84,q6,q7,q5,q0,q1,q3,q4,q45,q8,q9]

def v880 : List W := [q85,q6,q7,q5,q0,q1,q3,q4,q45,q8,q9]

def v881 : List W := [q86,q6,q8,q7,q5,q0,q1,q3,q4,q45,q9]

def v882 : List W := [q87,q6,q8,q7,q5,q0,q1,q3,q4,q45,q9]

def v883 : List W := [q88,q6,q9,q8,q7,q5,q0,q1,q3,q4,q45]

def v884 : List W := [q89,q6,q9,q8,q7,q5,q0,q1,q3,q4,q45]

def v885 : List W := [q90,q7,q8,q6,q5,q0,q1,q3,q4,q45,q9]

def v886 : List W := [q91,q7,q8,q6,q5,q0,q1,q3,q4,q45,q9]

def v887 : List W := [q92,q7,q9,q8,q6,q5,q0,q1,q3,q4,q45]

def v888 : List W := [q93,q7,q9,q8,q6,q5,q0,q1,q3,q4,q45]

def v889 : List W := [q94,q8,q9,q7,q6,q5,q0,q1,q3,q4,q45]

def v890 : List W := [q95,q8,q9,q7,q6,q5,q0,q1,q3,q4,q45]

def v891 : List W := [q45,q2,q4,q3,q1,q0,q5,q6,q7,q8,q9]

def v892 : List W := [q46,q2,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v893 : List W := [q47,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v894 : List W := [q222,q47,q4,q5,q3,q1,q0,q6,q7,q8,q9]

def v895 : List W := [q215,q4,q5,q3,q1,q0,q6,q7,q8,q9]

def v896 : List W := [q215,q47,q4,q5,q3,q1,q0,q6,q7,q8,q9]

def v897 : List W := [q223,q47,q3,q4,q5,q1,q0,q6,q7,q8,q9]

def v898 : List W := [q224,q47,q3,q4,q5,q1,q0,q6,q7,q8,q9]

def v899 : List W := [q225,q47,q1,q3,q4,q5,q0,q6,q7,q8,q9]

def v900 : List W := [q178,q1,q3,q4,q5,q0,q6,q7,q8,q9]

def v901 : List W := [q178,q47,q1,q3,q4,q5,q0,q6,q7,q8,q9]

def v902 : List W := [q226,q47,q1,q3,q4,q5,q6,q7,q8,q9]

def v903 : List W := [q226,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v904 : List W := [q226,q47,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v905 : List W := [q83,q47,q0,q1,q3,q4,q5,q6,q7,q8,q9]

def v906 : List W := [q227,q47,q6,q0,q1,q3,q4,q5,q7,q8,q9]

def v907 : List W := [q228,q47,q6,q0,q1,q3,q4,q5,q7,q8,q9]

def v908 : List W := [q229,q47,q6,q0,q1,q3,q4,q5,q8,q9]

def v909 : List W := [q229,q47,q7,q6,q0,q1,q3,q4,q5,q8,q9]

def v910 : List W := [q230,q47,q7,q6,q0,q1,q3,q4,q5,q8,q9]

def v911 : List W := [q231,q47,q8,q7,q6,q0,q1,q3,q4,q5,q9]

def v912 : List W := [q232,q47,q8,q7,q6,q0,q1,q3,q4,q5,q9]

def v913 : List W := [q152,q9,q8,q7,q6,q0,q1,q3,q4,q5]

def v914 : List W := [q152,q47,q9,q8,q7,q6,q0,q1,q3,q4,q5]

def v915 : List W := [q83,q47,q9,q8,q7,q6,q0,q1,q3,q4,q5]

def v916 : List W := [q66,q5,q4,q47,q3,q1,q0,q6,q7,q8,q9]

def v917 : List W := [q67,q5,q4,q47,q3,q1,q0,q6,q7,q8,q9]

def v918 : List W := [q56,q5,q3,q4,q47,q1,q0,q6,q7,q8,q9]

def v919 : List W := [q57,q3,q4,q47,q1,q0,q6,q7,q8,q9]

def v920 : List W := [q57,q5,q3,q4,q47,q1,q0,q6,q7,q8,q9]

def v921 : List W := [q33,q5,q1,q3,q4,q47,q0,q6,q7,q8,q9]

def v922 : List W := [q34,q1,q3,q4,q47,q0,q6,q7,q8,q9]

def v923 : List W := [q34,q5,q1,q3,q4,q47,q0,q6,q7,q8,q9]

def v924 : List W := [q115,q5,q0,q1,q3,q4,q47,q6,q7,q8,q9]

def v925 : List W := [q116,q5,q0,q1,q3,q4,q47,q6,q7,q8,q9]

def v926 : List W := [q76,q5,q6,q0,q1,q3,q4,q47,q7,q8,q9]

def v927 : List W := [q77,q5,q6,q0,q1,q3,q4,q47,q7,q8,q9]

def v928 : List W := [q78,q5,q7,q6,q0,q1,q3,q4,q47,q8,q9]

def v929 : List W := [q79,q7,q6,q0,q1,q3,q4,q47,q8,q9]

def v930 : List W := [q79,q5,q7,q6,q0,q1,q3,q4,q47,q8,q9]

def v931 : List W := [q80,q5,q8,q7,q6,q0,q1,q3,q4,q47,q9]

def v932 : List W := [q81,q5,q8,q7,q6,q0,q1,q3,q4,q47,q9]

def v933 : List W := [q82,q9,q8,q7,q6,q0,q1,q3,q4,q47]

def v934 : List W := [q82,q5,q9,q8,q7,q6,q0,q1,q3,q4,q47]

def v935 : List W := [q83,q5,q9,q8,q7,q6,q0,q1,q3,q4,q47]

def v936 : List W := [q54,q4,q3,q5,q47,q1,q0,q6,q7,q8,q9]

def v937 : List W := [q55,q4,q3,q5,q47,q1,q0,q6,q7,q8,q9]

def v938 : List W := [q31,q4,q1,q3,q5,q47,q0,q6,q7,q8,q9]

def v939 : List W := [q32,q4,q1,q3,q5,q47,q0,q6,q7,q8,q9]

def v940 : List W := [q113,q4,q0,q1,q3,q5,q47,q6,q7,q8,q9]

def v941 : List W := [q114,q4,q0,q1,q3,q5,q47,q6,q7,q8,q9]

def v942 : List W := [q68,q4,q6,q0,q1,q3,q5,q47,q7,q8,q9]

def v943 : List W := [q69,q4,q6,q0,q1,q3,q5,q47,q7,q8,q9]

def v944 : List W := [q70,q4,q7,q6,q0,q1,q3,q5,q47,q8,q9]

def v945 : List W := [q71,q4,q7,q6,q0,q1,q3,q5,q47,q8,q9]

def v946 : List W := [q72,q4,q8,q7,q6,q0,q1,q3,q5,q47,q9]

def v947 : List W := [q73,q4,q8,q7,q6,q0,q1,q3,q5,q47,q9]

def v948 : List W := [q74,q4,q9,q8,q7,q6,q0,q1,q3,q5,q47]

def v949 : List W := [q75,q4,q9,q8,q7,q6,q0,q1,q3,q5,q47]

def v950 : List W := [q29,q3,q1,q4,q5,q47,q0,q6,q7,q8,q9]

def v951 : List W := [q30,q3,q1,q4,q5,q47,q0,q6,q7,q8,q9]

def v952 : List W := [q111,q3,q0,q1,q4,q5,q47,q6,q7,q8,q9]

def v953 : List W := [q112,q3,q1,q4,q5,q47,q6,q7,q8,q9]

def v954 : List W := [q112,q3,q0,q1,q4,q5,q47,q6,q7,q8,q9]

def v955 : List W := [q58,q3,q6,q0,q1,q4,q5,q47,q7,q8,q9]

def v956 : List W := [q59,q3,q6,q0,q1,q4,q5,q47,q7,q8,q9]

def v957 : List W := [q60,q3,q7,q6,q0,q1,q4,q5,q47,q8,q9]

def v958 : List W := [q61,q3,q7,q6,q0,q1,q4,q5,q47,q8,q9]

def v959 : List W := [q62,q3,q8,q7,q6,q0,q1,q4,q5,q47,q9]

def v960 : List W := [q63,q3,q8,q7,q6,q0,q1,q4,q5,q47,q9]

def v961 : List W := [q64,q3,q9,q8,q7,q6,q0,q1,q4,q5,q47]

def v962 : List W := [q65,q3,q9,q8,q7,q6,q0,q1,q4,q5,q47]

def v963 : List W := [q10,q1,q0,q3,q4,q5,q47,q6,q7,q8,q9]

def v964 : List W := [q11,q1,q3,q4,q5,q47,q6,q7,q8,q9]

def v965 : List W := [q11,q1,q0,q3,q4,q5,q47,q6,q7,q8,q9]

def v966 : List W := [q35,q1,q6,q0,q3,q4,q5,q47,q7,q8,q9]

def v967 : List W := [q36,q1,q6,q0,q3,q4,q5,q47,q7,q8,q9]

def v968 : List W := [q37,q1,q7,q6,q0,q3,q4,q5,q47,q8,q9]

def v969 : List W := [q38,q1,q7,q6,q0,q3,q4,q5,q47,q8,q9]

def v970 : List W := [q39,q1,q8,q7,q6,q0,q3,q4,q5,q47,q9]

def v971 : List W := [q40,q1,q8,q7,q6,q0,q3,q4,q5,q47,q9]

def v972 : List W := [q41,q1,q9,q8,q7,q6,q0,q3,q4,q5,q47]

def v973 : List W := [q13,q1,q9,q8,q7,q6,q0,q3,q4,q5,q47]

def v974 : List W := [q117,q0,q6,q1,q3,q4,q5,q47,q7,q8,q9]

def v975 : List W := [q118,q0,q6,q1,q3,q4,q5,q47,q7,q8,q9]

def v976 : List W := [q119,q0,q7,q6,q1,q3,q4,q5,q47,q8,q9]

def v977 : List W := [q120,q7,q6,q1,q3,q4,q5,q47,q8,q9]

def v978 : List W := [q120,q0,q7,q6,q1,q3,q4,q5,q47,q8,q9]

def v979 : List W := [q121,q0,q8,q7,q6,q1,q3,q4,q5,q47,q9]

def v980 : List W := [q122,q0,q8,q7,q6,q1,q3,q4,q5,q47,q9]

def v981 : List W := [q84,q6,q7,q0,q1,q3,q4,q5,q47,q8,q9]

def v982 : List W := [q85,q6,q7,q0,q1,q3,q4,q5,q47,q8,q9]

def v983 : List W := [q86,q6,q8,q7,q0,q1,q3,q4,q5,q47,q9]

def v984 : List W := [q87,q6,q8,q7,q0,q1,q3,q4,q5,q47,q9]

def v985 : List W := [q88,q6,q9,q8,q7,q0,q1,q3,q4,q5,q47]

def v986 : List W := [q89,q6,q9,q8,q7,q0,q1,q3,q4,q5,q47]

def v987 : List W := [q90,q7,q8,q6,q0,q1,q3,q4,q5,q47,q9]

def v988 : List W := [q91,q7,q8,q6,q0,q1,q3,q4,q5,q47,q9]

def v989 : List W := [q92,q7,q9,q8,q6,q0,q1,q3,q4,q5,q47]

def v990 : List W := [q93,q7,q9,q8,q6,q0,q1,q3,q4,q5,q47]

def v991 : List W := [q94,q8,q9,q7,q6,q0,q1,q3,q4,q5,q47]

def v992 : List W := [q95,q8,q9,q7,q6,q0,q1,q3,q4,q5,q47]

def v993 : List W := [q47,q2,q5,q4,q3,q1,q0,q6,q7,q8,q9]

def v994 : List W := [q48,q2,q6,q5,q4,q3,q1,q0,q7,q8,q9]

def v995 : List W := [q49,q2,q6,q5,q4,q3,q1,q0,q7,q8,q9]

def v996 : List W := [q50,q2,q7,q6,q5,q4,q3,q1,q0,q8,q9]

def v997 : List W := [q233,q6,q7,q2,q5,q4,q3,q1,q0,q8,q9]

def v998 : List W := [q234,q7,q2,q5,q4,q3,q1,q0,q8,q9]

def v999 : List W := [q234,q50,q7,q2,q5,q4,q3,q1,q0,q8,q9]

def v1000 : List W := [q234,q6,q7,q2,q5,q4,q3,q1,q0,q8,q9]

def v1001 : List W := [q235,q5,q6,q7,q2,q4,q3,q1,q0,q8,q9]

def v1002 : List W := [q236,q6,q7,q2,q4,q3,q1,q0,q8,q9]

def v1003 : List W := [q236,q50,q6,q7,q2,q4,q3,q1,q0,q8,q9]

def v1004 : List W := [q236,q5,q6,q7,q2,q4,q3,q1,q0,q8,q9]

def v1005 : List W := [q237,q4,q5,q6,q7,q2,q3,q1,q0,q8,q9]

def v1006 : List W := [q238,q5,q6,q7,q2,q3,q1,q0,q8,q9]

def v1007 : List W := [q238,q50,q5,q6,q7,q2,q3,q1,q0,q8,q9]

def v1008 : List W := [q238,q4,q5,q6,q7,q2,q3,q1,q0,q8,q9]

def v1009 : List W := [q206,q3,q4,q5,q6,q7,q2,q1,q0,q8,q9]

def v1010 : List W := [q239,q4,q5,q6,q7,q2,q1,q0,q8,q9]

def v1011 : List W := [q239,q50,q4,q5,q6,q7,q2,q1,q0,q8,q9]

def v1012 : List W := [q239,q3,q4,q5,q6,q7,q2,q1,q0,q8,q9]

def v1013 : List W := [q240,q3,q4,q5,q6,q7,q2,q0,q8,q9]

def v1014 : List W := [q240,q50,q3,q4,q5,q6,q7,q2,q0,q8,q9]

def v1015 : List W := [q240,q1,q3,q4,q5,q6,q7,q2,q0,q8,q9]

def v1016 : List W := [q107,q0,q1,q3,q4,q5,q6,q7,q2,q8,q9]

def v1017 : List W := [q171,q1,q3,q4,q5,q6,q7,q2,q8,q9]

def v1018 : List W := [q171,q50,q1,q3,q4,q5,q6,q7,q2,q8,q9]

def v1019 : List W := [q171,q0,q1,q3,q4,q5,q6,q7,q2,q8,q9]

def v1020 : List W := [q241,q8,q0,q1,q3,q4,q5,q6,q7,q2,q9]

def v1021 : List W := [q242,q0,q1,q3,q4,q5,q6,q7,q2,q9]

def v1022 : List W := [q242,q50,q0,q1,q3,q4,q5,q6,q7,q2,q9]

def v1023 : List W := [q242,q8,q0,q1,q3,q4,q5,q6,q7,q2,q9]

def v1024 : List W := [q51,q50,q6,q5,q4,q3,q1,q0,q8,q9]

def v1025 : List W := [q51,q2,q50,q6,q5,q4,q3,q1,q0,q8,q9]

def v1026 : List W := [q51,q7,q50,q6,q5,q4,q3,q1,q0,q8,q9]

def v1027 : List W := [q47,q5,q6,q7,q50,q4,q3,q1,q0,q8,q9]

def v1028 : List W := [q45,q4,q5,q6,q7,q50,q3,q1,q0,q8,q9]

def v1029 : List W := [q42,q3,q4,q5,q6,q7,q50,q1,q0,q8,q9]

def v1030 : List W := [q28,q1,q3,q4,q5,q6,q7,q50,q0,q8,q9]

def v1031 : List W := [q96,q2,q1,q3,q4,q5,q6,q7,q50,q8,q9]

def v1032 : List W := [q96,q0,q1,q3,q4,q5,q6,q7,q50,q8,q9]

def v1033 : List W := [q53,q8,q0,q1,q3,q4,q5,q6,q7,q50,q9]

def v1034 : List W := [q78,q5,q6,q2,q50,q4,q3,q1,q0,q8,q9]

def v1035 : List W := [q120,q1,q3,q4,q5,q6,q2,q50,q8,q9]

def v1036 : List W := [q120,q7,q1,q3,q4,q5,q6,q2,q50,q8,q9]

def v1037 : List W := [q120,q0,q1,q3,q4,q5,q6,q2,q50,q8,q9]

def v1038 : List W := [q91,q8,q0,q1,q3,q4,q5,q6,q2,q50,q9]

def v1039 : List W := [q93,q9,q8,q0,q1,q3,q4,q5,q6,q2,q50]

def v1040 : List W := [q112,q3,q1,q4,q5,q6,q7,q2,q50,q8,q9]

def v1041 : List W := [q11,q1,q3,q4,q5,q6,q7,q2,q50,q8,q9]

def v1042 : List W := [q51,q2,q7,q6,q5,q4,q3,q1,q0,q8,q9]

def v1043 : List W := [q52,q2,q8,q7,q6,q5,q4,q3,q1,q0,q9]

def v1044 : List W := [q53,q2,q8,q7,q6,q5,q4,q3,q1,q0,q9]

def v1045 : List W := [q54,q3,q4,q2,q1,q0,q5,q6,q7,q8,q9]

def v1046 : List W := [q55,q3,q4,q2,q1,q0,q5,q6,q7,q8,q9]

def v1047 : List W := [q56,q3,q5,q4,q2,q1,q0,q6,q7,q8,q9]

def v1048 : List W := [q57,q3,q5,q4,q2,q1,q0,q6,q7,q8,q9]

def v1049 : List W := [q58,q3,q6,q5,q4,q2,q1,q0,q7,q8,q9]

def v1050 : List W := [q59,q3,q6,q5,q4,q2,q1,q0,q7,q8,q9]

def v1051 : List W := [q60,q3,q7,q6,q5,q4,q2,q1,q0,q8,q9]

def v1052 : List W := [q61,q3,q7,q6,q5,q4,q2,q1,q0,q8,q9]

def v1053 : List W := [q243,q6,q7,q3,q5,q4,q2,q1,q0,q8,q9]

def v1054 : List W := [q244,q6,q7,q3,q5,q4,q2,q1,q0,q8,q9]

def v1055 : List W := [q245,q5,q6,q7,q3,q4,q2,q1,q0,q8,q9]

def v1056 : List W := [q246,q5,q6,q7,q3,q4,q2,q1,q0,q8,q9]

def v1057 : List W := [q247,q4,q5,q6,q7,q3,q2,q1,q0,q8,q9]

def v1058 : List W := [q248,q4,q5,q6,q7,q3,q2,q1,q0,q8,q9]

def v1059 : List W := [q249,q4,q5,q6,q7,q3,q1,q0,q8,q9]

def v1060 : List W := [q249,q61,q4,q5,q6,q7,q3,q1,q0,q8,q9]

def v1061 : List W := [q249,q2,q4,q5,q6,q7,q3,q1,q0,q8,q9]

def v1062 : List W := [q250,q2,q4,q5,q6,q7,q3,q1,q0,q8,q9]

def v1063 : List W := [q251,q1,q2,q4,q5,q6,q7,q3,q0,q8,q9]

def v1064 : List W := [q252,q1,q2,q4,q5,q6,q7,q3,q0,q8,q9]

def v1065 : List W := [q253,q0,q1,q2,q4,q5,q6,q7,q3,q8,q9]

def v1066 : List W := [q132,q1,q2,q4,q5,q6,q7,q3,q8,q9]

def v1067 : List W := [q132,q61,q1,q2,q4,q5,q6,q7,q3,q8,q9]

def v1068 : List W := [q132,q0,q1,q2,q4,q5,q6,q7,q3,q8,q9]

def v1069 : List W := [q254,q8,q0,q1,q2,q4,q5,q6,q7,q3,q9]

def v1070 : List W := [q255,q8,q0,q1,q2,q4,q5,q6,q7,q3,q9]

def v1071 : List W := [q256,q9,q8,q0,q1,q2,q4,q5,q6,q7,q3]

def v1072 : List W := [q257,q9,q8,q0,q1,q2,q4,q5,q6,q7,q3]

def v1073 : List W := [q60,q3,q61,q6,q5,q4,q2,q1,q0,q8,q9]

def v1074 : List W := [q60,q7,q61,q6,q5,q4,q2,q1,q0,q8,q9]

def v1075 : List W := [q57,q5,q6,q7,q61,q4,q2,q1,q0,q8,q9]

def v1076 : List W := [q43,q2,q4,q5,q6,q7,q61,q1,q0,q8,q9]

def v1077 : List W := [q112,q3,q1,q2,q4,q5,q6,q7,q61,q8,q9]

def v1078 : List W := [q78,q5,q6,q3,q61,q4,q2,q1,q0,q8,q9]

def v1079 : List W := [q71,q4,q5,q6,q3,q61,q2,q1,q0,q8,q9]

def v1080 : List W := [q51,q2,q4,q5,q6,q3,q61,q1,q0,q8,q9]

def v1081 : List W := [q120,q1,q2,q4,q5,q6,q3,q61,q8,q9]

def v1082 : List W := [q120,q7,q1,q2,q4,q5,q6,q3,q61,q8,q9]

def v1083 : List W := [q120,q0,q1,q2,q4,q5,q6,q3,q61,q8,q9]

def v1084 : List W := [q91,q8,q0,q1,q2,q4,q5,q6,q3,q61,q9]

def v1085 : List W := [q93,q9,q8,q0,q1,q2,q4,q5,q6,q3,q61]

def v1086 : List W := [q47,q5,q4,q6,q7,q3,q61,q1,q0,q8,q9]

def v1087 : List W := [q45,q4,q5,q6,q7,q3,q61,q1,q0,q8,q9]

def v1088 : List W := [q28,q1,q4,q5,q6,q7,q3,q61,q0,q8,q9]

def v1089 : List W := [q96,q2,q1,q4,q5,q6,q7,q3,q61,q8,q9]

def v1090 : List W := [q96,q0,q1,q4,q5,q6,q7,q3,q61,q8,q9]

def v1091 : List W := [q11,q1,q2,q4,q5,q6,q7,q3,q61,q8,q9]

def v1092 : List W := [q62,q3,q8,q7,q6,q5,q4,q2,q1,q0,q9]

def v1093 : List W := [q63,q3,q8,q7,q6,q5,q4,q2,q1,q0,q9]

def v1094 : List W := [q64,q3,q9,q8,q7,q6,q5,q4,q2,q1,q0]

def v1095 : List W := [q65,q3,q9,q8,q7,q6,q5,q4,q2,q1,q0]

def v1096 : List W := [q66,q4,q5,q3,q2,q1,q0,q6,q7,q8,q9]

def v1097 : List W := [q67,q4,q5,q3,q2,q1,q0,q6,q7,q8,q9]

def v1098 : List W := [q258,q3,q5,q4,q2,q1,q0,q6,q7,q8,q9]

def v1099 : List W := [q259,q3,q5,q4,q2,q1,q0,q6,q7,q8,q9]

def v1100 : List W := [q260,q2,q3,q5,q4,q1,q0,q6,q7,q8,q9]

def v1101 : List W := [q215,q3,q5,q4,q1,q0,q6,q7,q8,q9]

def v1102 : List W := [q215,q67,q3,q5,q4,q1,q0,q6,q7,q8,q9]

def v1103 : List W := [q215,q2,q3,q5,q4,q1,q0,q6,q7,q8,q9]

def v1104 : List W := [q261,q1,q2,q3,q5,q4,q0,q6,q7,q8,q9]

def v1105 : List W := [q262,q1,q2,q3,q5,q4,q0,q6,q7,q8,q9]

def v1106 : List W := [q263,q1,q2,q3,q5,q4,q6,q7,q8,q9]

def v1107 : List W := [q263,q67,q1,q2,q3,q5,q4,q6,q7,q8,q9]

def v1108 : List W := [q263,q0,q1,q2,q3,q5,q4,q6,q7,q8,q9]

def v1109 : List W := [q264,q0,q1,q2,q3,q5,q4,q6,q7,q8,q9]

def v1110 : List W := [q265,q6,q0,q1,q2,q3,q5,q4,q7,q8,q9]

def v1111 : List W := [q266,q6,q0,q1,q2,q3,q5,q4,q7,q8,q9]

def v1112 : List W := [q267,q7,q6,q0,q1,q2,q3,q5,q4,q8,q9]

def v1113 : List W := [q268,q7,q6,q0,q1,q2,q3,q5,q4,q8,q9]

def v1114 : List W := [q269,q8,q7,q6,q0,q1,q2,q3,q5,q4,q9]

def v1115 : List W := [q270,q8,q7,q6,q0,q1,q2,q3,q5,q4,q9]

def v1116 : List W := [q271,q9,q8,q7,q6,q0,q1,q2,q3,q5,q4]

def v1117 : List W := [q272,q9,q8,q7,q6,q0,q1,q2,q3,q5,q4]

def v1118 : List W := [q66,q4,q67,q3,q2,q1,q0,q6,q7,q8,q9]

def v1119 : List W := [q66,q5,q67,q3,q2,q1,q0,q6,q7,q8,q9]

def v1120 : List W := [q54,q3,q5,q67,q2,q1,q0,q6,q7,q8,q9]

def v1121 : List W := [q45,q3,q5,q67,q1,q0,q6,q7,q8,q9]

def v1122 : List W := [q45,q4,q3,q5,q67,q1,q0,q6,q7,q8,q9]

def v1123 : List W := [q45,q2,q3,q5,q67,q1,q0,q6,q7,q8,q9]

def v1124 : List W := [q114,q0,q1,q2,q3,q5,q67,q6,q7,q8,q9]

def v1125 : List W := [q71,q7,q6,q0,q1,q2,q3,q5,q67,q8,q9]

def v1126 : List W := [q73,q8,q7,q6,q0,q1,q2,q3,q5,q67,q9]

def v1127 : List W := [q75,q9,q8,q7,q6,q0,q1,q2,q3,q5,q67]

def v1128 : List W := [q57,q3,q4,q67,q2,q1,q0,q6,q7,q8,q9]

def v1129 : List W := [q47,q5,q3,q4,q67,q1,q0,q6,q7,q8,q9]

def v1130 : List W := [q116,q0,q1,q2,q3,q4,q67,q6,q7,q8,q9]

def v1131 : List W := [q112,q3,q1,q2,q5,q4,q67,q6,q7,q8,q9]

def v1132 : List W := [q28,q1,q3,q5,q4,q67,q0,q6,q7,q8,q9]

def v1133 : List W := [q96,q2,q1,q3,q5,q4,q67,q6,q7,q8,q9]

def v1134 : List W := [q96,q0,q1,q3,q5,q4,q67,q6,q7,q8,q9]

def v1135 : List W := [q11,q1,q2,q3,q5,q4,q67,q6,q7,q8,q9]

def v1136 : List W := [q120,q7,q6,q1,q2,q3,q5,q4,q67,q8,q9]

def v1137 : List W := [q68,q4,q6,q5,q3,q2,q1,q0,q7,q8,q9]

def v1138 : List W := [q69,q4,q6,q5,q3,q2,q1,q0,q7,q8,q9]

def v1139 : List W := [q70,q4,q7,q6,q5,q3,q2,q1,q0,q8,q9]

def v1140 : List W := [q71,q4,q7,q6,q5,q3,q2,q1,q0,q8,q9]

def v1141 : List W := [q72,q4,q8,q7,q6,q5,q3,q2,q1,q0,q9]

def v1142 : List W := [q73,q4,q8,q7,q6,q5,q3,q2,q1,q0,q9]

def v1143 : List W := [q74,q4,q9,q8,q7,q6,q5,q3,q2,q1,q0]

def v1144 : List W := [q75,q4,q9,q8,q7,q6,q5,q3,q2,q1,q0]

def v1145 : List W := [q76,q5,q6,q4,q3,q2,q1,q0,q7,q8,q9]

def v1146 : List W := [q77,q5,q6,q4,q3,q2,q1,q0,q7,q8,q9]

def v1147 : List W := [q78,q5,q7,q6,q4,q3,q2,q1,q0,q8,q9]

def v1148 : List W := [q273,q6,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1149 : List W := [q274,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1150 : List W := [q274,q78,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1151 : List W := [q274,q6,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1152 : List W := [q275,q4,q6,q7,q5,q3,q2,q1,q0,q8,q9]

def v1153 : List W := [q276,q6,q7,q5,q3,q2,q1,q0,q8,q9]

def v1154 : List W := [q276,q78,q6,q7,q5,q3,q2,q1,q0,q8,q9]

def v1155 : List W := [q276,q4,q6,q7,q5,q3,q2,q1,q0,q8,q9]

def v1156 : List W := [q277,q3,q4,q6,q7,q5,q2,q1,q0,q8,q9]

def v1157 : List W := [q278,q4,q6,q7,q5,q2,q1,q0,q8,q9]

def v1158 : List W := [q278,q78,q4,q6,q7,q5,q2,q1,q0,q8,q9]

def v1159 : List W := [q278,q3,q4,q6,q7,q5,q2,q1,q0,q8,q9]

def v1160 : List W := [q235,q2,q3,q4,q6,q7,q5,q1,q0,q8,q9]

def v1161 : List W := [q279,q3,q4,q6,q7,q5,q1,q0,q8,q9]

def v1162 : List W := [q279,q78,q3,q4,q6,q7,q5,q1,q0,q8,q9]

def v1163 : List W := [q279,q2,q3,q4,q6,q7,q5,q1,q0,q8,q9]

def v1164 : List W := [q280,q1,q2,q3,q4,q6,q7,q5,q0,q8,q9]

def v1165 : List W := [q281,q2,q3,q4,q6,q7,q5,q0,q8,q9]

def v1166 : List W := [q281,q78,q2,q3,q4,q6,q7,q5,q0,q8,q9]

def v1167 : List W := [q281,q1,q2,q3,q4,q6,q7,q5,q0,q8,q9]

def v1168 : List W := [q156,q0,q1,q2,q3,q4,q6,q7,q5,q8,q9]

def v1169 : List W := [q282,q1,q2,q3,q4,q6,q7,q5,q8,q9]

def v1170 : List W := [q282,q78,q1,q2,q3,q4,q6,q7,q5,q8,q9]

def v1171 : List W := [q282,q0,q1,q2,q3,q4,q6,q7,q5,q8,q9]

def v1172 : List W := [q283,q8,q0,q1,q2,q3,q4,q6,q7,q5,q9]

def v1173 : List W := [q284,q0,q1,q2,q3,q4,q6,q7,q5,q9]

def v1174 : List W := [q284,q78,q0,q1,q2,q3,q4,q6,q7,q5,q9]

def v1175 : List W := [q284,q8,q0,q1,q2,q3,q4,q6,q7,q5,q9]

def v1176 : List W := [q285,q9,q8,q0,q1,q2,q3,q4,q6,q7,q5]

def v1177 : List W := [q286,q9,q8,q0,q1,q2,q3,q4,q6,q7,q5]

def v1178 : List W := [q79,q78,q6,q4,q3,q2,q1,q0,q8,q9]

def v1179 : List W := [q79,q5,q78,q6,q4,q3,q2,q1,q0,q8,q9]

def v1180 : List W := [q79,q7,q78,q6,q4,q3,q2,q1,q0,q8,q9]

def v1181 : List W := [q47,q5,q3,q4,q6,q7,q78,q1,q0,q8,q9]

def v1182 : List W := [q61,q3,q4,q6,q5,q78,q2,q1,q0,q8,q9]

def v1183 : List W := [q50,q2,q3,q4,q6,q5,q78,q1,q0,q8,q9]

def v1184 : List W := [q38,q1,q2,q3,q4,q6,q5,q78,q0,q8,q9]

def v1185 : List W := [q120,q7,q1,q2,q3,q4,q6,q5,q78,q8,q9]

def v1186 : List W := [q92,q9,q8,q0,q1,q2,q3,q4,q6,q5,q78]

def v1187 : List W := [q45,q4,q3,q6,q7,q5,q78,q1,q0,q8,q9]

def v1188 : List W := [q112,q3,q1,q2,q4,q6,q7,q5,q78,q8,q9]

def v1189 : List W := [q28,q1,q3,q4,q6,q7,q5,q78,q0,q8,q9]

def v1190 : List W := [q96,q2,q1,q3,q4,q6,q7,q5,q78,q8,q9]

def v1191 : List W := [q96,q0,q1,q3,q4,q6,q7,q5,q78,q8,q9]

def v1192 : List W := [q11,q1,q2,q3,q4,q6,q7,q5,q78,q8,q9]

def v1193 : List W := [q79,q5,q7,q6,q4,q3,q2,q1,q0,q8,q9]

def v1194 : List W := [q80,q5,q8,q7,q6,q4,q3,q2,q1,q0,q9]

def v1195 : List W := [q81,q5,q8,q7,q6,q4,q3,q2,q1,q0,q9]

def v1196 : List W := [q82,q5,q9,q8,q7,q6,q4,q3,q2,q1,q0]

def v1197 : List W := [q83,q5,q9,q8,q7,q6,q4,q3,q2,q1,q0]

def v1198 : List W := [q84,q6,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1199 : List W := [q85,q6,q7,q5,q4,q3,q2,q1,q0,q8,q9]

def v1200 : List W := [q86,q6,q8,q7,q5,q4,q3,q2,q1,q0,q9]

def v1201 : List W := [q287,q7,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1202 : List W := [q288,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1203 : List W := [q288,q86,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1204 : List W := [q288,q7,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1205 : List W := [q289,q5,q7,q8,q6,q4,q3,q2,q1,q0,q9]

def v1206 : List W := [q290,q7,q8,q6,q4,q3,q2,q1,q0,q9]

def v1207 : List W := [q290,q86,q7,q8,q6,q4,q3,q2,q1,q0,q9]

def v1208 : List W := [q290,q5,q7,q8,q6,q4,q3,q2,q1,q0,q9]

def v1209 : List W := [q291,q4,q5,q7,q8,q6,q3,q2,q1,q0,q9]

def v1210 : List W := [q292,q5,q7,q8,q6,q3,q2,q1,q0,q9]

def v1211 : List W := [q292,q86,q5,q7,q8,q6,q3,q2,q1,q0,q9]

def v1212 : List W := [q292,q4,q5,q7,q8,q6,q3,q2,q1,q0,q9]

def v1213 : List W := [q293,q3,q4,q5,q7,q8,q6,q2,q1,q0,q9]

def v1214 : List W := [q294,q4,q5,q7,q8,q6,q2,q1,q0,q9]

def v1215 : List W := [q294,q86,q4,q5,q7,q8,q6,q2,q1,q0,q9]

def v1216 : List W := [q294,q3,q4,q5,q7,q8,q6,q2,q1,q0,q9]

def v1217 : List W := [q295,q2,q3,q4,q5,q7,q8,q6,q1,q0,q9]

def v1218 : List W := [q296,q3,q4,q5,q7,q8,q6,q1,q0,q9]

def v1219 : List W := [q296,q86,q3,q4,q5,q7,q8,q6,q1,q0,q9]

def v1220 : List W := [q296,q2,q3,q4,q5,q7,q8,q6,q1,q0,q9]

def v1221 : List W := [q297,q1,q2,q3,q4,q5,q7,q8,q6,q0,q9]

def v1222 : List W := [q298,q2,q3,q4,q5,q7,q8,q6,q0,q9]

def v1223 : List W := [q298,q86,q2,q3,q4,q5,q7,q8,q6,q0,q9]

def v1224 : List W := [q298,q1,q2,q3,q4,q5,q7,q8,q6,q0,q9]

def v1225 : List W := [q299,q0,q1,q2,q3,q4,q5,q7,q8,q6,q9]

def v1226 : List W := [q300,q1,q2,q3,q4,q5,q7,q8,q6,q9]

def v1227 : List W := [q300,q86,q1,q2,q3,q4,q5,q7,q8,q6,q9]

def v1228 : List W := [q300,q0,q1,q2,q3,q4,q5,q7,q8,q6,q9]

def v1229 : List W := [q301,q9,q0,q1,q2,q3,q4,q5,q7,q8,q6]

def v1230 : List W := [q302,q9,q0,q1,q2,q3,q4,q5,q7,q8,q6]

def v1231 : List W := [q87,q86,q7,q5,q4,q3,q2,q1,q0,q9]

def v1232 : List W := [q87,q6,q86,q7,q5,q4,q3,q2,q1,q0,q9]

def v1233 : List W := [q87,q8,q86,q7,q5,q4,q3,q2,q1,q0,q9]

def v1234 : List W := [q49,q2,q3,q4,q5,q7,q8,q86,q1,q0,q9]

def v1235 : List W := [q35,q1,q2,q3,q4,q5,q7,q8,q86,q0,q9]

def v1236 : List W := [q118,q0,q1,q2,q3,q4,q5,q7,q8,q86,q9]

def v1237 : List W := [q89,q9,q0,q1,q2,q3,q4,q5,q7,q8,q86]

def v1238 : List W := [q120,q7,q1,q2,q3,q4,q5,q8,q6,q86,q9]

def v1239 : List W := [q47,q5,q3,q4,q7,q8,q6,q86,q1,q0,q9]

def v1240 : List W := [q45,q4,q3,q5,q7,q8,q6,q86,q1,q0,q9]

def v1241 : List W := [q112,q3,q1,q2,q4,q5,q7,q8,q6,q86,q9]

def v1242 : List W := [q28,q1,q3,q4,q5,q7,q8,q6,q86,q0,q9]

def v1243 : List W := [q96,q2,q1,q3,q4,q5,q7,q8,q6,q86,q9]

def v1244 : List W := [q96,q0,q1,q3,q4,q5,q7,q8,q6,q86,q9]

def v1245 : List W := [q11,q1,q2,q3,q4,q5,q7,q8,q6,q86,q9]

def v1246 : List W := [q87,q6,q8,q7,q5,q4,q3,q2,q1,q0,q9]

def v1247 : List W := [q88,q6,q9,q8,q7,q5,q4,q3,q2,q1,q0]

def v1248 : List W := [q89,q6,q9,q8,q7,q5,q4,q3,q2,q1,q0]

def v1249 : List W := [q90,q7,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1250 : List W := [q91,q7,q8,q6,q5,q4,q3,q2,q1,q0,q9]

def v1251 : List W := [q92,q7,q9,q8,q6,q5,q4,q3,q2,q1,q0]

def v1252 : List W := [q93,q7,q9,q8,q6,q5,q4,q3,q2,q1,q0]

def v1253 : List W := [q94,q8,q9,q7,q6,q5,q4,q3,q2,q1,q0]

def v1254 : List W := [q95,q8,q9,q7,q6,q5,q4,q3,q2,q1,q0]

def c438 : List (List W) := [v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477]

def c996 : List (List W) := [v997,v998,v999,v1000,v1001,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1016,v1017,v1018,v1019,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v1033,v1034,v1035,v1036,v1037,v1038,v1039,v1040,v1041]

def c1147 : List (List W) := [v1148,v1149,v1150,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1167,v1168,v1169,v1170,v1171,v1172,v1173,v1174,v1175,v1176,v1177,v1178,v1179,v1180,v1181,v1182,v1183,v1184,v1185,v1186,v1187,v1188,v1189,v1190,v1191,v1192]

def c1200 : List (List W) := [v1201,v1202,v1203,v1204,v1205,v1206,v1207,v1208,v1209,v1210,v1211,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219,v1220,v1221,v1222,v1223,v1224,v1225,v1226,v1227,v1228,v1229,v1230,v1231,v1232,v1233,v1234,v1235,v1236,v1237,v1238,v1239,v1240,v1241,v1242,v1243,v1244,v1245]

def c747 : List (List W) := [v748,v749,v750,v751,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774,v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787]

def c194 : List (List W) := [v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286]

def c101 : List (List W) := [v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193]

def c698 : List (List W) := [v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v720,v721,v722,v723,v724,v725,v726,v727,v728,v729,v730,v731,v732,v733,v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v744,v745]

def c893 : List (List W) := [v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911,v912,v913,v914,v915,v916,v917,v918,v919,v920,v921,v922,v923,v924,v925,v926,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946,v947,v948,v949,v950,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v963,v964,v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981,v982,v983,v984,v985,v986,v987,v988,v989,v990,v991,v992]

def c587 : List (List W) := [v588,v589,v590,v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684]

def c390 : List (List W) := [v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436]

def c482 : List (List W) := [v483,v484,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582]

def c2 : List (List W) := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99]

def c1052 : List (List W) := [v1053,v1054,v1055,v1056,v1057,v1058,v1059,v1060,v1061,v1062,v1063,v1064,v1065,v1066,v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081,v1082,v1083,v1084,v1085,v1086,v1087,v1088,v1089,v1090,v1091]

def c289 : List (List W) := [v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388]

def c1097 : List (List W) := [v1098,v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112,v1113,v1114,v1115,v1116,v1117,v1118,v1119,v1120,v1121,v1122,v1123,v1124,v1125,v1126,v1127,v1128,v1129,v1130,v1131,v1132,v1133,v1134,v1135,v1136]

def c790 : List (List W) := [v791,v792,v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835,v836,v837,v838,v839,v840,v841,v842,v843,v844,v845,v846,v847,v848,v849,v850,v851,v852,v853,v854,v855,v856,v857,v858,v859,v860,v861,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v872,v873,v874,v875,v876,v877,v878,v879,v880,v881,v882,v883,v884,v885,v886,v887,v888,v889,v890]

def c0 : List (List W) := [v1,v2,v100,v101,v194,v287,v288,v289,v389,v390,v437,v438,v478,v479,v480,v481,v482,v583,v584,v585,v586,v587,v685,v686,v687,v688,v689,v690,v691,v692,v693,v694,v695,v696,v697,v698,v746,v747,v788,v789,v790,v891,v892,v893,v993,v994,v995,v996,v1042,v1043,v1044,v1045,v1046,v1047,v1048,v1049,v1050,v1051,v1052,v1092,v1093,v1094,v1095,v1096,v1097,v1137,v1138,v1139,v1140,v1141,v1142,v1143,v1144,v1145,v1146,v1147,v1193,v1194,v1195,v1196,v1197,v1198,v1199,v1200,v1246,v1247,v1248,v1249,v1250,v1251,v1252,v1253,v1254]

lemma deny3 : go 5 v3 = false := by decide +kernel

lemma deny4 : go 5 v4 = false := by decide +kernel

lemma deny5 : go 5 v5 = false := by decide +kernel

lemma deny6 : go 5 v6 = false := by decide +kernel

lemma deny7 : go 5 v7 = false := by decide +kernel

lemma deny8 : go 5 v8 = false := by decide +kernel

lemma deny9 : go 5 v9 = false := by decide +kernel

lemma deny10 : go 5 v10 = false := by decide +kernel

lemma deny11 : go 5 v11 = false := by decide +kernel

lemma deny12 : go 5 v12 = false := by decide +kernel

lemma deny13 : go 5 v13 = false := by decide +kernel

lemma deny14 : go 5 v14 = false := by decide +kernel

lemma deny15 : go 5 v15 = false := by decide +kernel

lemma deny16 : go 5 v16 = false := by decide +kernel

lemma deny17 : go 5 v17 = false := by decide +kernel

lemma deny18 : go 5 v18 = false := by decide +kernel

lemma deny19 : go 5 v19 = false := by decide +kernel

lemma deny20 : go 5 v20 = false := by decide +kernel

lemma deny21 : go 5 v21 = false := by decide +kernel

lemma deny22 : go 5 v22 = false := by decide +kernel

lemma deny23 : go 5 v23 = false := by decide +kernel

lemma deny24 : go 5 v24 = false := by decide +kernel

lemma deny25 : go 5 v25 = false := by decide +kernel

lemma deny26 : go 5 v26 = false := by decide +kernel

lemma deny27 : go 5 v27 = false := by decide +kernel

lemma deny28 : go 5 v28 = false := by decide +kernel

lemma deny29 : go 5 v29 = false := by decide +kernel

lemma deny30 : go 5 v30 = false := by decide +kernel

lemma deny31 : go 5 v31 = false := by decide +kernel

lemma deny32 : go 5 v32 = false := by decide +kernel

lemma deny33 : go 5 v33 = false := by decide +kernel

lemma deny34 : go 5 v34 = false := by decide +kernel

lemma deny35 : go 5 v35 = false := by decide +kernel

lemma deny36 : go 5 v36 = false := by decide +kernel

lemma deny37 : go 5 v37 = false := by decide +kernel

lemma deny38 : go 5 v38 = false := by decide +kernel

lemma deny39 : go 5 v39 = false := by decide +kernel

lemma deny40 : go 5 v40 = false := by decide +kernel

lemma deny41 : go 5 v41 = false := by decide +kernel

lemma deny42 : go 5 v42 = false := by decide +kernel

lemma deny43 : go 5 v43 = false := by decide +kernel

lemma deny44 : go 5 v44 = false := by decide +kernel

lemma deny45 : go 5 v45 = false := by decide +kernel

lemma deny46 : go 5 v46 = false := by decide +kernel

lemma deny47 : go 5 v47 = false := by decide +kernel

lemma deny48 : go 5 v48 = false := by decide +kernel

lemma deny49 : go 5 v49 = false := by decide +kernel

lemma deny50 : go 5 v50 = false := by decide +kernel

lemma deny51 : go 5 v51 = false := by decide +kernel

lemma deny52 : go 5 v52 = false := by decide +kernel

lemma deny53 : go 5 v53 = false := by decide +kernel

lemma deny54 : go 5 v54 = false := by decide +kernel

lemma deny55 : go 5 v55 = false := by decide +kernel

lemma deny56 : go 5 v56 = false := by decide +kernel

lemma deny57 : go 5 v57 = false := by decide +kernel

lemma deny58 : go 5 v58 = false := by decide +kernel

lemma deny59 : go 5 v59 = false := by decide +kernel

lemma deny60 : go 5 v60 = false := by decide +kernel

lemma deny61 : go 5 v61 = false := by decide +kernel

lemma deny62 : go 5 v62 = false := by decide +kernel

lemma deny63 : go 5 v63 = false := by decide +kernel

lemma deny64 : go 5 v64 = false := by decide +kernel

lemma deny65 : go 5 v65 = false := by decide +kernel

lemma deny66 : go 5 v66 = false := by decide +kernel

lemma deny67 : go 5 v67 = false := by decide +kernel

lemma deny68 : go 5 v68 = false := by decide +kernel

lemma deny69 : go 5 v69 = false := by decide +kernel

lemma deny70 : go 5 v70 = false := by decide +kernel

lemma deny71 : go 5 v71 = false := by decide +kernel

lemma deny72 : go 5 v72 = false := by decide +kernel

lemma deny73 : go 5 v73 = false := by decide +kernel

lemma deny74 : go 5 v74 = false := by decide +kernel

lemma deny75 : go 5 v75 = false := by decide +kernel

lemma deny76 : go 5 v76 = false := by decide +kernel

lemma deny77 : go 5 v77 = false := by decide +kernel

lemma deny78 : go 5 v78 = false := by decide +kernel

lemma deny79 : go 5 v79 = false := by decide +kernel

lemma deny80 : go 5 v80 = false := by decide +kernel

lemma deny81 : go 5 v81 = false := by decide +kernel

lemma deny82 : go 5 v82 = false := by decide +kernel

lemma deny83 : go 5 v83 = false := by decide +kernel

lemma deny84 : go 5 v84 = false := by decide +kernel

lemma deny85 : go 5 v85 = false := by decide +kernel

lemma deny86 : go 5 v86 = false := by decide +kernel

lemma deny87 : go 5 v87 = false := by decide +kernel

lemma deny88 : go 5 v88 = false := by decide +kernel

lemma deny89 : go 5 v89 = false := by decide +kernel

lemma deny90 : go 5 v90 = false := by decide +kernel

lemma deny91 : go 5 v91 = false := by decide +kernel

lemma deny92 : go 5 v92 = false := by decide +kernel

lemma deny93 : go 5 v93 = false := by decide +kernel

lemma deny94 : go 5 v94 = false := by decide +kernel

lemma deny95 : go 5 v95 = false := by decide +kernel

lemma deny96 : go 5 v96 = false := by decide +kernel

lemma deny97 : go 5 v97 = false := by decide +kernel

lemma deny98 : go 5 v98 = false := by decide +kernel

lemma deny99 : go 5 v99 = false := by decide +kernel

lemma deny102 : go 5 v102 = false := by decide +kernel

lemma deny103 : go 5 v103 = false := by decide +kernel

lemma deny104 : go 5 v104 = false := by decide +kernel

lemma deny105 : go 5 v105 = false := by decide +kernel

lemma deny106 : go 5 v106 = false := by decide +kernel

lemma deny107 : go 5 v107 = false := by decide +kernel

lemma deny108 : go 5 v108 = false := by decide +kernel

lemma deny109 : go 5 v109 = false := by decide +kernel

lemma deny110 : go 5 v110 = false := by decide +kernel

lemma deny111 : go 5 v111 = false := by decide +kernel

lemma deny112 : go 5 v112 = false := by decide +kernel

lemma deny113 : go 5 v113 = false := by decide +kernel

lemma deny114 : go 5 v114 = false := by decide +kernel

lemma deny115 : go 5 v115 = false := by decide +kernel

lemma deny116 : go 5 v116 = false := by decide +kernel

lemma deny117 : go 5 v117 = false := by decide +kernel

lemma deny118 : go 5 v118 = false := by decide +kernel

lemma deny119 : go 5 v119 = false := by decide +kernel

lemma deny120 : go 5 v120 = false := by decide +kernel

lemma deny121 : go 5 v121 = false := by decide +kernel

lemma deny122 : go 5 v122 = false := by decide +kernel

lemma deny123 : go 5 v123 = false := by decide +kernel

lemma deny124 : go 5 v124 = false := by decide +kernel

lemma deny125 : go 5 v125 = false := by decide +kernel

lemma deny126 : go 5 v126 = false := by decide +kernel

lemma deny127 : go 5 v127 = false := by decide +kernel

lemma deny128 : go 5 v128 = false := by decide +kernel

lemma deny129 : go 5 v129 = false := by decide +kernel

lemma deny130 : go 5 v130 = false := by decide +kernel

lemma deny131 : go 5 v131 = false := by decide +kernel

lemma deny132 : go 5 v132 = false := by decide +kernel

lemma deny133 : go 5 v133 = false := by decide +kernel

lemma deny134 : go 5 v134 = false := by decide +kernel

lemma deny135 : go 5 v135 = false := by decide +kernel

lemma deny136 : go 5 v136 = false := by decide +kernel

lemma deny137 : go 5 v137 = false := by decide +kernel

lemma deny138 : go 5 v138 = false := by decide +kernel

lemma deny139 : go 5 v139 = false := by decide +kernel

lemma deny140 : go 5 v140 = false := by decide +kernel

lemma deny141 : go 5 v141 = false := by decide +kernel

lemma deny142 : go 5 v142 = false := by decide +kernel

lemma deny143 : go 5 v143 = false := by decide +kernel

lemma deny144 : go 5 v144 = false := by decide +kernel

lemma deny145 : go 5 v145 = false := by decide +kernel

lemma deny146 : go 5 v146 = false := by decide +kernel

lemma deny147 : go 5 v147 = false := by decide +kernel

lemma deny148 : go 5 v148 = false := by decide +kernel

lemma deny149 : go 5 v149 = false := by decide +kernel

lemma deny150 : go 5 v150 = false := by decide +kernel

lemma deny151 : go 5 v151 = false := by decide +kernel

lemma deny152 : go 5 v152 = false := by decide +kernel

lemma deny153 : go 5 v153 = false := by decide +kernel

lemma deny154 : go 5 v154 = false := by decide +kernel

lemma deny155 : go 5 v155 = false := by decide +kernel

lemma deny156 : go 5 v156 = false := by decide +kernel

lemma deny157 : go 5 v157 = false := by decide +kernel

lemma deny158 : go 5 v158 = false := by decide +kernel

lemma deny159 : go 5 v159 = false := by decide +kernel

lemma deny160 : go 5 v160 = false := by decide +kernel

lemma deny161 : go 5 v161 = false := by decide +kernel

lemma deny162 : go 5 v162 = false := by decide +kernel

lemma deny163 : go 5 v163 = false := by decide +kernel

lemma deny164 : go 5 v164 = false := by decide +kernel

lemma deny165 : go 5 v165 = false := by decide +kernel

lemma deny166 : go 5 v166 = false := by decide +kernel

lemma deny167 : go 5 v167 = false := by decide +kernel

lemma deny168 : go 5 v168 = false := by decide +kernel

lemma deny169 : go 5 v169 = false := by decide +kernel

lemma deny170 : go 5 v170 = false := by decide +kernel

lemma deny171 : go 5 v171 = false := by decide +kernel

lemma deny172 : go 5 v172 = false := by decide +kernel

lemma deny173 : go 5 v173 = false := by decide +kernel

lemma deny174 : go 5 v174 = false := by decide +kernel

lemma deny175 : go 5 v175 = false := by decide +kernel

lemma deny176 : go 5 v176 = false := by decide +kernel

lemma deny177 : go 5 v177 = false := by decide +kernel

lemma deny178 : go 5 v178 = false := by decide +kernel

lemma deny179 : go 5 v179 = false := by decide +kernel

lemma deny180 : go 5 v180 = false := by decide +kernel

lemma deny181 : go 5 v181 = false := by decide +kernel

lemma deny182 : go 5 v182 = false := by decide +kernel

lemma deny183 : go 5 v183 = false := by decide +kernel

lemma deny184 : go 5 v184 = false := by decide +kernel

lemma deny185 : go 5 v185 = false := by decide +kernel

lemma deny186 : go 5 v186 = false := by decide +kernel

lemma deny187 : go 5 v187 = false := by decide +kernel

lemma deny188 : go 5 v188 = false := by decide +kernel

lemma deny189 : go 5 v189 = false := by decide +kernel

lemma deny190 : go 5 v190 = false := by decide +kernel

lemma deny191 : go 5 v191 = false := by decide +kernel

lemma deny192 : go 5 v192 = false := by decide +kernel

lemma deny193 : go 5 v193 = false := by decide +kernel

lemma deny195 : go 5 v195 = false := by decide +kernel

lemma deny196 : go 5 v196 = false := by decide +kernel

lemma deny197 : go 5 v197 = false := by decide +kernel

lemma deny198 : go 5 v198 = false := by decide +kernel

lemma deny199 : go 5 v199 = false := by decide +kernel

lemma deny200 : go 5 v200 = false := by decide +kernel

lemma deny201 : go 5 v201 = false := by decide +kernel

lemma deny202 : go 5 v202 = false := by decide +kernel

lemma deny203 : go 5 v203 = false := by decide +kernel

lemma deny204 : go 5 v204 = false := by decide +kernel

lemma deny205 : go 5 v205 = false := by decide +kernel

lemma deny206 : go 5 v206 = false := by decide +kernel

lemma deny207 : go 5 v207 = false := by decide +kernel

lemma deny208 : go 5 v208 = false := by decide +kernel

lemma deny209 : go 5 v209 = false := by decide +kernel

lemma deny210 : go 5 v210 = false := by decide +kernel

lemma deny211 : go 5 v211 = false := by decide +kernel

lemma deny212 : go 5 v212 = false := by decide +kernel

lemma deny213 : go 5 v213 = false := by decide +kernel

lemma deny214 : go 5 v214 = false := by decide +kernel

lemma deny215 : go 5 v215 = false := by decide +kernel

lemma deny216 : go 5 v216 = false := by decide +kernel

lemma deny217 : go 5 v217 = false := by decide +kernel

lemma deny218 : go 5 v218 = false := by decide +kernel

lemma deny219 : go 5 v219 = false := by decide +kernel

lemma deny220 : go 5 v220 = false := by decide +kernel

lemma deny221 : go 5 v221 = false := by decide +kernel

lemma deny222 : go 5 v222 = false := by decide +kernel

lemma deny223 : go 5 v223 = false := by decide +kernel

lemma deny224 : go 5 v224 = false := by decide +kernel

lemma deny225 : go 5 v225 = false := by decide +kernel

lemma deny226 : go 5 v226 = false := by decide +kernel

lemma deny227 : go 5 v227 = false := by decide +kernel

lemma deny228 : go 5 v228 = false := by decide +kernel

lemma deny229 : go 5 v229 = false := by decide +kernel

lemma deny230 : go 5 v230 = false := by decide +kernel

lemma deny231 : go 5 v231 = false := by decide +kernel

lemma deny232 : go 5 v232 = false := by decide +kernel

lemma deny233 : go 5 v233 = false := by decide +kernel

lemma deny234 : go 5 v234 = false := by decide +kernel

lemma deny235 : go 5 v235 = false := by decide +kernel

lemma deny236 : go 5 v236 = false := by decide +kernel

lemma deny237 : go 5 v237 = false := by decide +kernel

lemma deny238 : go 5 v238 = false := by decide +kernel

lemma deny239 : go 5 v239 = false := by decide +kernel

lemma deny240 : go 5 v240 = false := by decide +kernel

lemma deny241 : go 5 v241 = false := by decide +kernel

lemma deny242 : go 5 v242 = false := by decide +kernel

lemma deny243 : go 5 v243 = false := by decide +kernel

lemma deny244 : go 5 v244 = false := by decide +kernel

lemma deny245 : go 5 v245 = false := by decide +kernel

lemma deny246 : go 5 v246 = false := by decide +kernel

lemma deny247 : go 5 v247 = false := by decide +kernel

lemma deny248 : go 5 v248 = false := by decide +kernel

lemma deny249 : go 5 v249 = false := by decide +kernel

lemma deny250 : go 5 v250 = false := by decide +kernel

lemma deny251 : go 5 v251 = false := by decide +kernel

lemma deny252 : go 5 v252 = false := by decide +kernel

lemma deny253 : go 5 v253 = false := by decide +kernel

lemma deny254 : go 5 v254 = false := by decide +kernel

lemma deny255 : go 5 v255 = false := by decide +kernel

lemma deny256 : go 5 v256 = false := by decide +kernel

lemma deny257 : go 5 v257 = false := by decide +kernel

lemma deny258 : go 5 v258 = false := by decide +kernel

lemma deny259 : go 5 v259 = false := by decide +kernel

lemma deny260 : go 5 v260 = false := by decide +kernel

lemma deny261 : go 5 v261 = false := by decide +kernel

lemma deny262 : go 5 v262 = false := by decide +kernel

lemma deny263 : go 5 v263 = false := by decide +kernel

lemma deny264 : go 5 v264 = false := by decide +kernel

lemma deny265 : go 5 v265 = false := by decide +kernel

lemma deny266 : go 5 v266 = false := by decide +kernel

lemma deny267 : go 5 v267 = false := by decide +kernel

lemma deny268 : go 5 v268 = false := by decide +kernel

lemma deny269 : go 5 v269 = false := by decide +kernel

lemma deny270 : go 5 v270 = false := by decide +kernel

lemma deny271 : go 5 v271 = false := by decide +kernel

lemma deny272 : go 5 v272 = false := by decide +kernel

lemma deny273 : go 5 v273 = false := by decide +kernel

lemma deny274 : go 5 v274 = false := by decide +kernel

lemma deny275 : go 5 v275 = false := by decide +kernel

lemma deny276 : go 5 v276 = false := by decide +kernel

lemma deny277 : go 5 v277 = false := by decide +kernel

lemma deny278 : go 5 v278 = false := by decide +kernel

lemma deny279 : go 5 v279 = false := by decide +kernel

lemma deny280 : go 5 v280 = false := by decide +kernel

lemma deny281 : go 5 v281 = false := by decide +kernel

lemma deny282 : go 5 v282 = false := by decide +kernel

lemma deny283 : go 5 v283 = false := by decide +kernel

lemma deny284 : go 5 v284 = false := by decide +kernel

lemma deny285 : go 5 v285 = false := by decide +kernel

lemma deny286 : go 5 v286 = false := by decide +kernel

lemma deny290 : go 5 v290 = false := by decide +kernel

lemma deny291 : go 5 v291 = false := by decide +kernel

lemma deny292 : go 5 v292 = false := by decide +kernel

lemma deny293 : go 5 v293 = false := by decide +kernel

lemma deny294 : go 5 v294 = false := by decide +kernel

lemma deny295 : go 5 v295 = false := by decide +kernel

lemma deny296 : go 5 v296 = false := by decide +kernel

lemma deny297 : go 5 v297 = false := by decide +kernel

lemma deny298 : go 5 v298 = false := by decide +kernel

lemma deny299 : go 5 v299 = false := by decide +kernel

lemma deny300 : go 5 v300 = false := by decide +kernel

lemma deny301 : go 5 v301 = false := by decide +kernel

lemma deny302 : go 5 v302 = false := by decide +kernel

lemma deny303 : go 5 v303 = false := by decide +kernel

lemma deny304 : go 5 v304 = false := by decide +kernel

lemma deny305 : go 5 v305 = false := by decide +kernel

lemma deny306 : go 5 v306 = false := by decide +kernel

lemma deny307 : go 5 v307 = false := by decide +kernel

lemma deny308 : go 5 v308 = false := by decide +kernel

lemma deny309 : go 5 v309 = false := by decide +kernel

lemma deny310 : go 5 v310 = false := by decide +kernel

lemma deny311 : go 5 v311 = false := by decide +kernel

lemma deny312 : go 5 v312 = false := by decide +kernel

lemma deny313 : go 5 v313 = false := by decide +kernel

lemma deny314 : go 5 v314 = false := by decide +kernel

lemma deny315 : go 5 v315 = false := by decide +kernel

lemma deny316 : go 5 v316 = false := by decide +kernel

lemma deny317 : go 5 v317 = false := by decide +kernel

lemma deny318 : go 5 v318 = false := by decide +kernel

lemma deny319 : go 5 v319 = false := by decide +kernel

lemma deny320 : go 5 v320 = false := by decide +kernel

lemma deny321 : go 5 v321 = false := by decide +kernel

lemma deny322 : go 5 v322 = false := by decide +kernel

lemma deny323 : go 5 v323 = false := by decide +kernel

lemma deny324 : go 5 v324 = false := by decide +kernel

lemma deny325 : go 5 v325 = false := by decide +kernel

lemma deny326 : go 5 v326 = false := by decide +kernel

lemma deny327 : go 5 v327 = false := by decide +kernel

lemma deny328 : go 5 v328 = false := by decide +kernel

lemma deny329 : go 5 v329 = false := by decide +kernel

lemma deny330 : go 5 v330 = false := by decide +kernel

lemma deny331 : go 5 v331 = false := by decide +kernel

lemma deny332 : go 5 v332 = false := by decide +kernel

lemma deny333 : go 5 v333 = false := by decide +kernel

lemma deny334 : go 5 v334 = false := by decide +kernel

lemma deny335 : go 5 v335 = false := by decide +kernel

lemma deny336 : go 5 v336 = false := by decide +kernel

lemma deny337 : go 5 v337 = false := by decide +kernel

lemma deny338 : go 5 v338 = false := by decide +kernel

lemma deny339 : go 5 v339 = false := by decide +kernel

lemma deny340 : go 5 v340 = false := by decide +kernel

lemma deny341 : go 5 v341 = false := by decide +kernel

lemma deny342 : go 5 v342 = false := by decide +kernel

lemma deny343 : go 5 v343 = false := by decide +kernel

lemma deny344 : go 5 v344 = false := by decide +kernel

lemma deny345 : go 5 v345 = false := by decide +kernel

lemma deny346 : go 5 v346 = false := by decide +kernel

lemma deny347 : go 5 v347 = false := by decide +kernel

lemma deny348 : go 5 v348 = false := by decide +kernel

lemma deny349 : go 5 v349 = false := by decide +kernel

lemma deny350 : go 5 v350 = false := by decide +kernel

lemma deny351 : go 5 v351 = false := by decide +kernel

lemma deny352 : go 5 v352 = false := by decide +kernel

lemma deny353 : go 5 v353 = false := by decide +kernel

lemma deny354 : go 5 v354 = false := by decide +kernel

lemma deny355 : go 5 v355 = false := by decide +kernel

lemma deny356 : go 5 v356 = false := by decide +kernel

lemma deny357 : go 5 v357 = false := by decide +kernel

lemma deny358 : go 5 v358 = false := by decide +kernel

lemma deny359 : go 5 v359 = false := by decide +kernel

lemma deny360 : go 5 v360 = false := by decide +kernel

lemma deny361 : go 5 v361 = false := by decide +kernel

lemma deny362 : go 5 v362 = false := by decide +kernel

lemma deny363 : go 5 v363 = false := by decide +kernel

lemma deny364 : go 5 v364 = false := by decide +kernel

lemma deny365 : go 5 v365 = false := by decide +kernel

lemma deny366 : go 5 v366 = false := by decide +kernel

lemma deny367 : go 5 v367 = false := by decide +kernel

lemma deny368 : go 5 v368 = false := by decide +kernel

lemma deny369 : go 5 v369 = false := by decide +kernel

lemma deny370 : go 5 v370 = false := by decide +kernel

lemma deny371 : go 5 v371 = false := by decide +kernel

lemma deny372 : go 5 v372 = false := by decide +kernel

lemma deny373 : go 5 v373 = false := by decide +kernel

lemma deny374 : go 5 v374 = false := by decide +kernel

lemma deny375 : go 5 v375 = false := by decide +kernel

lemma deny376 : go 5 v376 = false := by decide +kernel

lemma deny377 : go 5 v377 = false := by decide +kernel

lemma deny378 : go 5 v378 = false := by decide +kernel

lemma deny379 : go 5 v379 = false := by decide +kernel

lemma deny380 : go 5 v380 = false := by decide +kernel

lemma deny381 : go 5 v381 = false := by decide +kernel

lemma deny382 : go 5 v382 = false := by decide +kernel

lemma deny383 : go 5 v383 = false := by decide +kernel

lemma deny384 : go 5 v384 = false := by decide +kernel

lemma deny385 : go 5 v385 = false := by decide +kernel

lemma deny386 : go 5 v386 = false := by decide +kernel

lemma deny387 : go 5 v387 = false := by decide +kernel

lemma deny388 : go 5 v388 = false := by decide +kernel

lemma deny391 : go 5 v391 = false := by decide +kernel

lemma deny392 : go 5 v392 = false := by decide +kernel

lemma deny393 : go 5 v393 = false := by decide +kernel

lemma deny394 : go 5 v394 = false := by decide +kernel

lemma deny395 : go 5 v395 = false := by decide +kernel

lemma deny396 : go 5 v396 = false := by decide +kernel

lemma deny397 : go 5 v397 = false := by decide +kernel

lemma deny398 : go 5 v398 = false := by decide +kernel

lemma deny399 : go 5 v399 = false := by decide +kernel

lemma deny400 : go 5 v400 = false := by decide +kernel

lemma deny401 : go 5 v401 = false := by decide +kernel

lemma deny402 : go 5 v402 = false := by decide +kernel

lemma deny403 : go 5 v403 = false := by decide +kernel

lemma deny404 : go 5 v404 = false := by decide +kernel

lemma deny405 : go 5 v405 = false := by decide +kernel

lemma deny406 : go 5 v406 = false := by decide +kernel

lemma deny407 : go 5 v407 = false := by decide +kernel

lemma deny408 : go 5 v408 = false := by decide +kernel

lemma deny409 : go 5 v409 = false := by decide +kernel

lemma deny410 : go 5 v410 = false := by decide +kernel

lemma deny411 : go 5 v411 = false := by decide +kernel

lemma deny412 : go 5 v412 = false := by decide +kernel

lemma deny413 : go 5 v413 = false := by decide +kernel

lemma deny414 : go 5 v414 = false := by decide +kernel

lemma deny415 : go 5 v415 = false := by decide +kernel

lemma deny416 : go 5 v416 = false := by decide +kernel

lemma deny417 : go 5 v417 = false := by decide +kernel

lemma deny418 : go 5 v418 = false := by decide +kernel

lemma deny419 : go 5 v419 = false := by decide +kernel

lemma deny420 : go 5 v420 = false := by decide +kernel

lemma deny421 : go 5 v421 = false := by decide +kernel

lemma deny422 : go 5 v422 = false := by decide +kernel

lemma deny423 : go 5 v423 = false := by decide +kernel

lemma deny424 : go 5 v424 = false := by decide +kernel

lemma deny425 : go 5 v425 = false := by decide +kernel

lemma deny426 : go 5 v426 = false := by decide +kernel

lemma deny427 : go 5 v427 = false := by decide +kernel

lemma deny428 : go 5 v428 = false := by decide +kernel

lemma deny429 : go 5 v429 = false := by decide +kernel

lemma deny430 : go 5 v430 = false := by decide +kernel

lemma deny431 : go 5 v431 = false := by decide +kernel

lemma deny432 : go 5 v432 = false := by decide +kernel

lemma deny433 : go 5 v433 = false := by decide +kernel

lemma deny434 : go 5 v434 = false := by decide +kernel

lemma deny435 : go 5 v435 = false := by decide +kernel

lemma deny436 : go 5 v436 = false := by decide +kernel

lemma deny439 : go 5 v439 = false := by decide +kernel

lemma deny440 : go 5 v440 = false := by decide +kernel

lemma deny441 : go 5 v441 = false := by decide +kernel

lemma deny442 : go 5 v442 = false := by decide +kernel

lemma deny443 : go 5 v443 = false := by decide +kernel

lemma deny444 : go 5 v444 = false := by decide +kernel

lemma deny445 : go 5 v445 = false := by decide +kernel

lemma deny446 : go 5 v446 = false := by decide +kernel

lemma deny447 : go 5 v447 = false := by decide +kernel

lemma deny448 : go 5 v448 = false := by decide +kernel

lemma deny449 : go 5 v449 = false := by decide +kernel

lemma deny450 : go 5 v450 = false := by decide +kernel

lemma deny451 : go 5 v451 = false := by decide +kernel

lemma deny452 : go 5 v452 = false := by decide +kernel

lemma deny453 : go 5 v453 = false := by decide +kernel

lemma deny454 : go 5 v454 = false := by decide +kernel

lemma deny455 : go 5 v455 = false := by decide +kernel

lemma deny456 : go 5 v456 = false := by decide +kernel

lemma deny457 : go 5 v457 = false := by decide +kernel

lemma deny458 : go 5 v458 = false := by decide +kernel

lemma deny459 : go 5 v459 = false := by decide +kernel

lemma deny460 : go 5 v460 = false := by decide +kernel

lemma deny461 : go 5 v461 = false := by decide +kernel

lemma deny462 : go 5 v462 = false := by decide +kernel

lemma deny463 : go 5 v463 = false := by decide +kernel

lemma deny464 : go 5 v464 = false := by decide +kernel

lemma deny465 : go 5 v465 = false := by decide +kernel

lemma deny466 : go 5 v466 = false := by decide +kernel

lemma deny467 : go 5 v467 = false := by decide +kernel

lemma deny468 : go 5 v468 = false := by decide +kernel

lemma deny469 : go 5 v469 = false := by decide +kernel

lemma deny470 : go 5 v470 = false := by decide +kernel

lemma deny471 : go 5 v471 = false := by decide +kernel

lemma deny472 : go 5 v472 = false := by decide +kernel

lemma deny473 : go 5 v473 = false := by decide +kernel

lemma deny474 : go 5 v474 = false := by decide +kernel

lemma deny475 : go 5 v475 = false := by decide +kernel

lemma deny476 : go 5 v476 = false := by decide +kernel

lemma deny477 : go 5 v477 = false := by decide +kernel

lemma deny483 : go 5 v483 = false := by decide +kernel

lemma deny484 : go 5 v484 = false := by decide +kernel

lemma deny485 : go 5 v485 = false := by decide +kernel

lemma deny486 : go 5 v486 = false := by decide +kernel

lemma deny487 : go 5 v487 = false := by decide +kernel

lemma deny488 : go 5 v488 = false := by decide +kernel

lemma deny489 : go 5 v489 = false := by decide +kernel

lemma deny490 : go 5 v490 = false := by decide +kernel

lemma deny491 : go 5 v491 = false := by decide +kernel

lemma deny492 : go 5 v492 = false := by decide +kernel

lemma deny493 : go 5 v493 = false := by decide +kernel

lemma deny494 : go 5 v494 = false := by decide +kernel

lemma deny495 : go 5 v495 = false := by decide +kernel

lemma deny496 : go 5 v496 = false := by decide +kernel

lemma deny497 : go 5 v497 = false := by decide +kernel

lemma deny498 : go 5 v498 = false := by decide +kernel

lemma deny499 : go 5 v499 = false := by decide +kernel

lemma deny500 : go 5 v500 = false := by decide +kernel

lemma deny501 : go 5 v501 = false := by decide +kernel

lemma deny502 : go 5 v502 = false := by decide +kernel

lemma deny503 : go 5 v503 = false := by decide +kernel

lemma deny504 : go 5 v504 = false := by decide +kernel

lemma deny505 : go 5 v505 = false := by decide +kernel

lemma deny506 : go 5 v506 = false := by decide +kernel

lemma deny507 : go 5 v507 = false := by decide +kernel

lemma deny508 : go 5 v508 = false := by decide +kernel

lemma deny509 : go 5 v509 = false := by decide +kernel

lemma deny510 : go 5 v510 = false := by decide +kernel

lemma deny511 : go 5 v511 = false := by decide +kernel

lemma deny512 : go 5 v512 = false := by decide +kernel

lemma deny513 : go 5 v513 = false := by decide +kernel

lemma deny514 : go 5 v514 = false := by decide +kernel

lemma deny515 : go 5 v515 = false := by decide +kernel

lemma deny516 : go 5 v516 = false := by decide +kernel

lemma deny517 : go 5 v517 = false := by decide +kernel

lemma deny518 : go 5 v518 = false := by decide +kernel

lemma deny519 : go 5 v519 = false := by decide +kernel

lemma deny520 : go 5 v520 = false := by decide +kernel

lemma deny521 : go 5 v521 = false := by decide +kernel

lemma deny522 : go 5 v522 = false := by decide +kernel

lemma deny523 : go 5 v523 = false := by decide +kernel

lemma deny524 : go 5 v524 = false := by decide +kernel

lemma deny525 : go 5 v525 = false := by decide +kernel

lemma deny526 : go 5 v526 = false := by decide +kernel

lemma deny527 : go 5 v527 = false := by decide +kernel

lemma deny528 : go 5 v528 = false := by decide +kernel

lemma deny529 : go 5 v529 = false := by decide +kernel

lemma deny530 : go 5 v530 = false := by decide +kernel

lemma deny531 : go 5 v531 = false := by decide +kernel

lemma deny532 : go 5 v532 = false := by decide +kernel

lemma deny533 : go 5 v533 = false := by decide +kernel

lemma deny534 : go 5 v534 = false := by decide +kernel

lemma deny535 : go 5 v535 = false := by decide +kernel

lemma deny536 : go 5 v536 = false := by decide +kernel

lemma deny537 : go 5 v537 = false := by decide +kernel

lemma deny538 : go 5 v538 = false := by decide +kernel

lemma deny539 : go 5 v539 = false := by decide +kernel

lemma deny540 : go 5 v540 = false := by decide +kernel

lemma deny541 : go 5 v541 = false := by decide +kernel

lemma deny542 : go 5 v542 = false := by decide +kernel

lemma deny543 : go 5 v543 = false := by decide +kernel

lemma deny544 : go 5 v544 = false := by decide +kernel

lemma deny545 : go 5 v545 = false := by decide +kernel

lemma deny546 : go 5 v546 = false := by decide +kernel

lemma deny547 : go 5 v547 = false := by decide +kernel

lemma deny548 : go 5 v548 = false := by decide +kernel

lemma deny549 : go 5 v549 = false := by decide +kernel

lemma deny550 : go 5 v550 = false := by decide +kernel

lemma deny551 : go 5 v551 = false := by decide +kernel

lemma deny552 : go 5 v552 = false := by decide +kernel

lemma deny553 : go 5 v553 = false := by decide +kernel

lemma deny554 : go 5 v554 = false := by decide +kernel

lemma deny555 : go 5 v555 = false := by decide +kernel

lemma deny556 : go 5 v556 = false := by decide +kernel

lemma deny557 : go 5 v557 = false := by decide +kernel

lemma deny558 : go 5 v558 = false := by decide +kernel

lemma deny559 : go 5 v559 = false := by decide +kernel

lemma deny560 : go 5 v560 = false := by decide +kernel

lemma deny561 : go 5 v561 = false := by decide +kernel

lemma deny562 : go 5 v562 = false := by decide +kernel

lemma deny563 : go 5 v563 = false := by decide +kernel

lemma deny564 : go 5 v564 = false := by decide +kernel

lemma deny565 : go 5 v565 = false := by decide +kernel

lemma deny566 : go 5 v566 = false := by decide +kernel

lemma deny567 : go 5 v567 = false := by decide +kernel

lemma deny568 : go 5 v568 = false := by decide +kernel

lemma deny569 : go 5 v569 = false := by decide +kernel

lemma deny570 : go 5 v570 = false := by decide +kernel

lemma deny571 : go 5 v571 = false := by decide +kernel

lemma deny572 : go 5 v572 = false := by decide +kernel

lemma deny573 : go 5 v573 = false := by decide +kernel

lemma deny574 : go 5 v574 = false := by decide +kernel

lemma deny575 : go 5 v575 = false := by decide +kernel

lemma deny576 : go 5 v576 = false := by decide +kernel

lemma deny577 : go 5 v577 = false := by decide +kernel

lemma deny578 : go 5 v578 = false := by decide +kernel

lemma deny579 : go 5 v579 = false := by decide +kernel

lemma deny580 : go 5 v580 = false := by decide +kernel

lemma deny581 : go 5 v581 = false := by decide +kernel

lemma deny582 : go 5 v582 = false := by decide +kernel

lemma deny588 : go 5 v588 = false := by decide +kernel

lemma deny589 : go 5 v589 = false := by decide +kernel

lemma deny590 : go 5 v590 = false := by decide +kernel

lemma deny591 : go 5 v591 = false := by decide +kernel

lemma deny592 : go 5 v592 = false := by decide +kernel

lemma deny593 : go 5 v593 = false := by decide +kernel

lemma deny594 : go 5 v594 = false := by decide +kernel

lemma deny595 : go 5 v595 = false := by decide +kernel

lemma deny596 : go 5 v596 = false := by decide +kernel

lemma deny597 : go 5 v597 = false := by decide +kernel

lemma deny598 : go 5 v598 = false := by decide +kernel

lemma deny599 : go 5 v599 = false := by decide +kernel

lemma deny600 : go 5 v600 = false := by decide +kernel

lemma deny601 : go 5 v601 = false := by decide +kernel

lemma deny602 : go 5 v602 = false := by decide +kernel

lemma deny603 : go 5 v603 = false := by decide +kernel

lemma deny604 : go 5 v604 = false := by decide +kernel

lemma deny605 : go 5 v605 = false := by decide +kernel

lemma deny606 : go 5 v606 = false := by decide +kernel

lemma deny607 : go 5 v607 = false := by decide +kernel

lemma deny608 : go 5 v608 = false := by decide +kernel

lemma deny609 : go 5 v609 = false := by decide +kernel

lemma deny610 : go 5 v610 = false := by decide +kernel

lemma deny611 : go 5 v611 = false := by decide +kernel

lemma deny612 : go 5 v612 = false := by decide +kernel

lemma deny613 : go 5 v613 = false := by decide +kernel

lemma deny614 : go 5 v614 = false := by decide +kernel

lemma deny615 : go 5 v615 = false := by decide +kernel

lemma deny616 : go 5 v616 = false := by decide +kernel

lemma deny617 : go 5 v617 = false := by decide +kernel

lemma deny618 : go 5 v618 = false := by decide +kernel

lemma deny619 : go 5 v619 = false := by decide +kernel

lemma deny620 : go 5 v620 = false := by decide +kernel

lemma deny621 : go 5 v621 = false := by decide +kernel

lemma deny622 : go 5 v622 = false := by decide +kernel

lemma deny623 : go 5 v623 = false := by decide +kernel

lemma deny624 : go 5 v624 = false := by decide +kernel

lemma deny625 : go 5 v625 = false := by decide +kernel

lemma deny626 : go 5 v626 = false := by decide +kernel

lemma deny627 : go 5 v627 = false := by decide +kernel

lemma deny628 : go 5 v628 = false := by decide +kernel

lemma deny629 : go 5 v629 = false := by decide +kernel

lemma deny630 : go 5 v630 = false := by decide +kernel

lemma deny631 : go 5 v631 = false := by decide +kernel

lemma deny632 : go 5 v632 = false := by decide +kernel

lemma deny633 : go 5 v633 = false := by decide +kernel

lemma deny634 : go 5 v634 = false := by decide +kernel

lemma deny635 : go 5 v635 = false := by decide +kernel

lemma deny636 : go 5 v636 = false := by decide +kernel

lemma deny637 : go 5 v637 = false := by decide +kernel

lemma deny638 : go 5 v638 = false := by decide +kernel

lemma deny639 : go 5 v639 = false := by decide +kernel

lemma deny640 : go 5 v640 = false := by decide +kernel

lemma deny641 : go 5 v641 = false := by decide +kernel

lemma deny642 : go 5 v642 = false := by decide +kernel

lemma deny643 : go 5 v643 = false := by decide +kernel

lemma deny644 : go 5 v644 = false := by decide +kernel

lemma deny645 : go 5 v645 = false := by decide +kernel

lemma deny646 : go 5 v646 = false := by decide +kernel

lemma deny647 : go 5 v647 = false := by decide +kernel

lemma deny648 : go 5 v648 = false := by decide +kernel

lemma deny649 : go 5 v649 = false := by decide +kernel

lemma deny650 : go 5 v650 = false := by decide +kernel

lemma deny651 : go 5 v651 = false := by decide +kernel

lemma deny652 : go 5 v652 = false := by decide +kernel

lemma deny653 : go 5 v653 = false := by decide +kernel

lemma deny654 : go 5 v654 = false := by decide +kernel

lemma deny655 : go 5 v655 = false := by decide +kernel

lemma deny656 : go 5 v656 = false := by decide +kernel

lemma deny657 : go 5 v657 = false := by decide +kernel

lemma deny658 : go 5 v658 = false := by decide +kernel

lemma deny659 : go 5 v659 = false := by decide +kernel

lemma deny660 : go 5 v660 = false := by decide +kernel

lemma deny661 : go 5 v661 = false := by decide +kernel

lemma deny662 : go 5 v662 = false := by decide +kernel

lemma deny663 : go 5 v663 = false := by decide +kernel

lemma deny664 : go 5 v664 = false := by decide +kernel

lemma deny665 : go 5 v665 = false := by decide +kernel

lemma deny666 : go 5 v666 = false := by decide +kernel

lemma deny667 : go 5 v667 = false := by decide +kernel

lemma deny668 : go 5 v668 = false := by decide +kernel

lemma deny669 : go 5 v669 = false := by decide +kernel

lemma deny670 : go 5 v670 = false := by decide +kernel

lemma deny671 : go 5 v671 = false := by decide +kernel

lemma deny672 : go 5 v672 = false := by decide +kernel

lemma deny673 : go 5 v673 = false := by decide +kernel

lemma deny674 : go 5 v674 = false := by decide +kernel

lemma deny675 : go 5 v675 = false := by decide +kernel

lemma deny676 : go 5 v676 = false := by decide +kernel

lemma deny677 : go 5 v677 = false := by decide +kernel

lemma deny678 : go 5 v678 = false := by decide +kernel

lemma deny679 : go 5 v679 = false := by decide +kernel

lemma deny680 : go 5 v680 = false := by decide +kernel

lemma deny681 : go 5 v681 = false := by decide +kernel

lemma deny682 : go 5 v682 = false := by decide +kernel

lemma deny683 : go 5 v683 = false := by decide +kernel

lemma deny684 : go 5 v684 = false := by decide +kernel

lemma deny699 : go 5 v699 = false := by decide +kernel

lemma deny700 : go 5 v700 = false := by decide +kernel

lemma deny701 : go 5 v701 = false := by decide +kernel

lemma deny702 : go 5 v702 = false := by decide +kernel

lemma deny703 : go 5 v703 = false := by decide +kernel

lemma deny704 : go 5 v704 = false := by decide +kernel

lemma deny705 : go 5 v705 = false := by decide +kernel

lemma deny706 : go 5 v706 = false := by decide +kernel

lemma deny707 : go 5 v707 = false := by decide +kernel

lemma deny708 : go 5 v708 = false := by decide +kernel

lemma deny709 : go 5 v709 = false := by decide +kernel

lemma deny710 : go 5 v710 = false := by decide +kernel

lemma deny711 : go 5 v711 = false := by decide +kernel

lemma deny712 : go 5 v712 = false := by decide +kernel

lemma deny713 : go 5 v713 = false := by decide +kernel

lemma deny714 : go 5 v714 = false := by decide +kernel

lemma deny715 : go 5 v715 = false := by decide +kernel

lemma deny716 : go 5 v716 = false := by decide +kernel

lemma deny717 : go 5 v717 = false := by decide +kernel

lemma deny718 : go 5 v718 = false := by decide +kernel

lemma deny719 : go 5 v719 = false := by decide +kernel

lemma deny720 : go 5 v720 = false := by decide +kernel

lemma deny721 : go 5 v721 = false := by decide +kernel

lemma deny722 : go 5 v722 = false := by decide +kernel

lemma deny723 : go 5 v723 = false := by decide +kernel

lemma deny724 : go 5 v724 = false := by decide +kernel

lemma deny725 : go 5 v725 = false := by decide +kernel

lemma deny726 : go 5 v726 = false := by decide +kernel

lemma deny727 : go 5 v727 = false := by decide +kernel

lemma deny728 : go 5 v728 = false := by decide +kernel

lemma deny729 : go 5 v729 = false := by decide +kernel

lemma deny730 : go 5 v730 = false := by decide +kernel

lemma deny731 : go 5 v731 = false := by decide +kernel

lemma deny732 : go 5 v732 = false := by decide +kernel

lemma deny733 : go 5 v733 = false := by decide +kernel

lemma deny734 : go 5 v734 = false := by decide +kernel

lemma deny735 : go 5 v735 = false := by decide +kernel

lemma deny736 : go 5 v736 = false := by decide +kernel

lemma deny737 : go 5 v737 = false := by decide +kernel

lemma deny738 : go 5 v738 = false := by decide +kernel

lemma deny739 : go 5 v739 = false := by decide +kernel

lemma deny740 : go 5 v740 = false := by decide +kernel

lemma deny741 : go 5 v741 = false := by decide +kernel

lemma deny742 : go 5 v742 = false := by decide +kernel

lemma deny743 : go 5 v743 = false := by decide +kernel

lemma deny744 : go 5 v744 = false := by decide +kernel

lemma deny745 : go 5 v745 = false := by decide +kernel

lemma deny748 : go 5 v748 = false := by decide +kernel

lemma deny749 : go 5 v749 = false := by decide +kernel

lemma deny750 : go 5 v750 = false := by decide +kernel

lemma deny751 : go 5 v751 = false := by decide +kernel

lemma deny752 : go 5 v752 = false := by decide +kernel

lemma deny753 : go 5 v753 = false := by decide +kernel

lemma deny754 : go 5 v754 = false := by decide +kernel

lemma deny755 : go 5 v755 = false := by decide +kernel

lemma deny756 : go 5 v756 = false := by decide +kernel

lemma deny757 : go 5 v757 = false := by decide +kernel

lemma deny758 : go 5 v758 = false := by decide +kernel

lemma deny759 : go 5 v759 = false := by decide +kernel

lemma deny760 : go 5 v760 = false := by decide +kernel

lemma deny761 : go 5 v761 = false := by decide +kernel

lemma deny762 : go 5 v762 = false := by decide +kernel

lemma deny763 : go 5 v763 = false := by decide +kernel

lemma deny764 : go 5 v764 = false := by decide +kernel

lemma deny765 : go 5 v765 = false := by decide +kernel

lemma deny766 : go 5 v766 = false := by decide +kernel

lemma deny767 : go 5 v767 = false := by decide +kernel

lemma deny768 : go 5 v768 = false := by decide +kernel

lemma deny769 : go 5 v769 = false := by decide +kernel

lemma deny770 : go 5 v770 = false := by decide +kernel

lemma deny771 : go 5 v771 = false := by decide +kernel

lemma deny772 : go 5 v772 = false := by decide +kernel

lemma deny773 : go 5 v773 = false := by decide +kernel

lemma deny774 : go 5 v774 = false := by decide +kernel

lemma deny775 : go 5 v775 = false := by decide +kernel

lemma deny776 : go 5 v776 = false := by decide +kernel

lemma deny777 : go 5 v777 = false := by decide +kernel

lemma deny778 : go 5 v778 = false := by decide +kernel

lemma deny779 : go 5 v779 = false := by decide +kernel

lemma deny780 : go 5 v780 = false := by decide +kernel

lemma deny781 : go 5 v781 = false := by decide +kernel

lemma deny782 : go 5 v782 = false := by decide +kernel

lemma deny783 : go 5 v783 = false := by decide +kernel

lemma deny784 : go 5 v784 = false := by decide +kernel

lemma deny785 : go 5 v785 = false := by decide +kernel

lemma deny786 : go 5 v786 = false := by decide +kernel

lemma deny787 : go 5 v787 = false := by decide +kernel

lemma deny791 : go 5 v791 = false := by decide +kernel

lemma deny792 : go 5 v792 = false := by decide +kernel

lemma deny793 : go 5 v793 = false := by decide +kernel

lemma deny794 : go 5 v794 = false := by decide +kernel

lemma deny795 : go 5 v795 = false := by decide +kernel

lemma deny796 : go 5 v796 = false := by decide +kernel

lemma deny797 : go 5 v797 = false := by decide +kernel

lemma deny798 : go 5 v798 = false := by decide +kernel

lemma deny799 : go 5 v799 = false := by decide +kernel

lemma deny800 : go 5 v800 = false := by decide +kernel

lemma deny801 : go 5 v801 = false := by decide +kernel

lemma deny802 : go 5 v802 = false := by decide +kernel

lemma deny803 : go 5 v803 = false := by decide +kernel

lemma deny804 : go 5 v804 = false := by decide +kernel

lemma deny805 : go 5 v805 = false := by decide +kernel

lemma deny806 : go 5 v806 = false := by decide +kernel

lemma deny807 : go 5 v807 = false := by decide +kernel

lemma deny808 : go 5 v808 = false := by decide +kernel

lemma deny809 : go 5 v809 = false := by decide +kernel

lemma deny810 : go 5 v810 = false := by decide +kernel

lemma deny811 : go 5 v811 = false := by decide +kernel

lemma deny812 : go 5 v812 = false := by decide +kernel

lemma deny813 : go 5 v813 = false := by decide +kernel

lemma deny814 : go 5 v814 = false := by decide +kernel

lemma deny815 : go 5 v815 = false := by decide +kernel

lemma deny816 : go 5 v816 = false := by decide +kernel

lemma deny817 : go 5 v817 = false := by decide +kernel

lemma deny818 : go 5 v818 = false := by decide +kernel

lemma deny819 : go 5 v819 = false := by decide +kernel

lemma deny820 : go 5 v820 = false := by decide +kernel

lemma deny821 : go 5 v821 = false := by decide +kernel

lemma deny822 : go 5 v822 = false := by decide +kernel

lemma deny823 : go 5 v823 = false := by decide +kernel

lemma deny824 : go 5 v824 = false := by decide +kernel

lemma deny825 : go 5 v825 = false := by decide +kernel

lemma deny826 : go 5 v826 = false := by decide +kernel

lemma deny827 : go 5 v827 = false := by decide +kernel

lemma deny828 : go 5 v828 = false := by decide +kernel

lemma deny829 : go 5 v829 = false := by decide +kernel

lemma deny830 : go 5 v830 = false := by decide +kernel

lemma deny831 : go 5 v831 = false := by decide +kernel

lemma deny832 : go 5 v832 = false := by decide +kernel

lemma deny833 : go 5 v833 = false := by decide +kernel

lemma deny834 : go 5 v834 = false := by decide +kernel

lemma deny835 : go 5 v835 = false := by decide +kernel

lemma deny836 : go 5 v836 = false := by decide +kernel

lemma deny837 : go 5 v837 = false := by decide +kernel

lemma deny838 : go 5 v838 = false := by decide +kernel

lemma deny839 : go 5 v839 = false := by decide +kernel

lemma deny840 : go 5 v840 = false := by decide +kernel

lemma deny841 : go 5 v841 = false := by decide +kernel

lemma deny842 : go 5 v842 = false := by decide +kernel

lemma deny843 : go 5 v843 = false := by decide +kernel

lemma deny844 : go 5 v844 = false := by decide +kernel

lemma deny845 : go 5 v845 = false := by decide +kernel

lemma deny846 : go 5 v846 = false := by decide +kernel

lemma deny847 : go 5 v847 = false := by decide +kernel

lemma deny848 : go 5 v848 = false := by decide +kernel

lemma deny849 : go 5 v849 = false := by decide +kernel

lemma deny850 : go 5 v850 = false := by decide +kernel

lemma deny851 : go 5 v851 = false := by decide +kernel

lemma deny852 : go 5 v852 = false := by decide +kernel

lemma deny853 : go 5 v853 = false := by decide +kernel

lemma deny854 : go 5 v854 = false := by decide +kernel

lemma deny855 : go 5 v855 = false := by decide +kernel

lemma deny856 : go 5 v856 = false := by decide +kernel

lemma deny857 : go 5 v857 = false := by decide +kernel

lemma deny858 : go 5 v858 = false := by decide +kernel

lemma deny859 : go 5 v859 = false := by decide +kernel

lemma deny860 : go 5 v860 = false := by decide +kernel

lemma deny861 : go 5 v861 = false := by decide +kernel

lemma deny862 : go 5 v862 = false := by decide +kernel

lemma deny863 : go 5 v863 = false := by decide +kernel

lemma deny864 : go 5 v864 = false := by decide +kernel

lemma deny865 : go 5 v865 = false := by decide +kernel

lemma deny866 : go 5 v866 = false := by decide +kernel

lemma deny867 : go 5 v867 = false := by decide +kernel

lemma deny868 : go 5 v868 = false := by decide +kernel

lemma deny869 : go 5 v869 = false := by decide +kernel

lemma deny870 : go 5 v870 = false := by decide +kernel

lemma deny871 : go 5 v871 = false := by decide +kernel

lemma deny872 : go 5 v872 = false := by decide +kernel

lemma deny873 : go 5 v873 = false := by decide +kernel

lemma deny874 : go 5 v874 = false := by decide +kernel

lemma deny875 : go 5 v875 = false := by decide +kernel

lemma deny876 : go 5 v876 = false := by decide +kernel

lemma deny877 : go 5 v877 = false := by decide +kernel

lemma deny878 : go 5 v878 = false := by decide +kernel

lemma deny879 : go 5 v879 = false := by decide +kernel

lemma deny880 : go 5 v880 = false := by decide +kernel

lemma deny881 : go 5 v881 = false := by decide +kernel

lemma deny882 : go 5 v882 = false := by decide +kernel

lemma deny883 : go 5 v883 = false := by decide +kernel

lemma deny884 : go 5 v884 = false := by decide +kernel

lemma deny885 : go 5 v885 = false := by decide +kernel

lemma deny886 : go 5 v886 = false := by decide +kernel

lemma deny887 : go 5 v887 = false := by decide +kernel

lemma deny888 : go 5 v888 = false := by decide +kernel

lemma deny889 : go 5 v889 = false := by decide +kernel

lemma deny890 : go 5 v890 = false := by decide +kernel

lemma deny894 : go 5 v894 = false := by decide +kernel

lemma deny895 : go 5 v895 = false := by decide +kernel

lemma deny896 : go 5 v896 = false := by decide +kernel

lemma deny897 : go 5 v897 = false := by decide +kernel

lemma deny898 : go 5 v898 = false := by decide +kernel

lemma deny899 : go 5 v899 = false := by decide +kernel

lemma deny900 : go 5 v900 = false := by decide +kernel

lemma deny901 : go 5 v901 = false := by decide +kernel

lemma deny902 : go 5 v902 = false := by decide +kernel

lemma deny903 : go 5 v903 = false := by decide +kernel

lemma deny904 : go 5 v904 = false := by decide +kernel

lemma deny905 : go 5 v905 = false := by decide +kernel

lemma deny906 : go 5 v906 = false := by decide +kernel

lemma deny907 : go 5 v907 = false := by decide +kernel

lemma deny908 : go 5 v908 = false := by decide +kernel

lemma deny909 : go 5 v909 = false := by decide +kernel

lemma deny910 : go 5 v910 = false := by decide +kernel

lemma deny911 : go 5 v911 = false := by decide +kernel

lemma deny912 : go 5 v912 = false := by decide +kernel

lemma deny913 : go 5 v913 = false := by decide +kernel

lemma deny914 : go 5 v914 = false := by decide +kernel

lemma deny915 : go 5 v915 = false := by decide +kernel

lemma deny916 : go 5 v916 = false := by decide +kernel

lemma deny917 : go 5 v917 = false := by decide +kernel

lemma deny918 : go 5 v918 = false := by decide +kernel

lemma deny919 : go 5 v919 = false := by decide +kernel

lemma deny920 : go 5 v920 = false := by decide +kernel

lemma deny921 : go 5 v921 = false := by decide +kernel

lemma deny922 : go 5 v922 = false := by decide +kernel

lemma deny923 : go 5 v923 = false := by decide +kernel

lemma deny924 : go 5 v924 = false := by decide +kernel

lemma deny925 : go 5 v925 = false := by decide +kernel

lemma deny926 : go 5 v926 = false := by decide +kernel

lemma deny927 : go 5 v927 = false := by decide +kernel

lemma deny928 : go 5 v928 = false := by decide +kernel

lemma deny929 : go 5 v929 = false := by decide +kernel

lemma deny930 : go 5 v930 = false := by decide +kernel

lemma deny931 : go 5 v931 = false := by decide +kernel

lemma deny932 : go 5 v932 = false := by decide +kernel

lemma deny933 : go 5 v933 = false := by decide +kernel

lemma deny934 : go 5 v934 = false := by decide +kernel

lemma deny935 : go 5 v935 = false := by decide +kernel

lemma deny936 : go 5 v936 = false := by decide +kernel

lemma deny937 : go 5 v937 = false := by decide +kernel

lemma deny938 : go 5 v938 = false := by decide +kernel

lemma deny939 : go 5 v939 = false := by decide +kernel

lemma deny940 : go 5 v940 = false := by decide +kernel

lemma deny941 : go 5 v941 = false := by decide +kernel

lemma deny942 : go 5 v942 = false := by decide +kernel

lemma deny943 : go 5 v943 = false := by decide +kernel

lemma deny944 : go 5 v944 = false := by decide +kernel

lemma deny945 : go 5 v945 = false := by decide +kernel

lemma deny946 : go 5 v946 = false := by decide +kernel

lemma deny947 : go 5 v947 = false := by decide +kernel

lemma deny948 : go 5 v948 = false := by decide +kernel

lemma deny949 : go 5 v949 = false := by decide +kernel

lemma deny950 : go 5 v950 = false := by decide +kernel

lemma deny951 : go 5 v951 = false := by decide +kernel

lemma deny952 : go 5 v952 = false := by decide +kernel

lemma deny953 : go 5 v953 = false := by decide +kernel

lemma deny954 : go 5 v954 = false := by decide +kernel

lemma deny955 : go 5 v955 = false := by decide +kernel

lemma deny956 : go 5 v956 = false := by decide +kernel

lemma deny957 : go 5 v957 = false := by decide +kernel

lemma deny958 : go 5 v958 = false := by decide +kernel

lemma deny959 : go 5 v959 = false := by decide +kernel

lemma deny960 : go 5 v960 = false := by decide +kernel

lemma deny961 : go 5 v961 = false := by decide +kernel

lemma deny962 : go 5 v962 = false := by decide +kernel

lemma deny963 : go 5 v963 = false := by decide +kernel

lemma deny964 : go 5 v964 = false := by decide +kernel

lemma deny965 : go 5 v965 = false := by decide +kernel

lemma deny966 : go 5 v966 = false := by decide +kernel

lemma deny967 : go 5 v967 = false := by decide +kernel

lemma deny968 : go 5 v968 = false := by decide +kernel

lemma deny969 : go 5 v969 = false := by decide +kernel

lemma deny970 : go 5 v970 = false := by decide +kernel

lemma deny971 : go 5 v971 = false := by decide +kernel

lemma deny972 : go 5 v972 = false := by decide +kernel

lemma deny973 : go 5 v973 = false := by decide +kernel

lemma deny974 : go 5 v974 = false := by decide +kernel

lemma deny975 : go 5 v975 = false := by decide +kernel

lemma deny976 : go 5 v976 = false := by decide +kernel

lemma deny977 : go 5 v977 = false := by decide +kernel

lemma deny978 : go 5 v978 = false := by decide +kernel

lemma deny979 : go 5 v979 = false := by decide +kernel

lemma deny980 : go 5 v980 = false := by decide +kernel

lemma deny981 : go 5 v981 = false := by decide +kernel

lemma deny982 : go 5 v982 = false := by decide +kernel

lemma deny983 : go 5 v983 = false := by decide +kernel

lemma deny984 : go 5 v984 = false := by decide +kernel

lemma deny985 : go 5 v985 = false := by decide +kernel

lemma deny986 : go 5 v986 = false := by decide +kernel

lemma deny987 : go 5 v987 = false := by decide +kernel

lemma deny988 : go 5 v988 = false := by decide +kernel

lemma deny989 : go 5 v989 = false := by decide +kernel

lemma deny990 : go 5 v990 = false := by decide +kernel

lemma deny991 : go 5 v991 = false := by decide +kernel

lemma deny992 : go 5 v992 = false := by decide +kernel

lemma deny997 : go 5 v997 = false := by decide +kernel

lemma deny998 : go 5 v998 = false := by decide +kernel

lemma deny999 : go 5 v999 = false := by decide +kernel

lemma deny1000 : go 5 v1000 = false := by decide +kernel

lemma deny1001 : go 5 v1001 = false := by decide +kernel

lemma deny1002 : go 5 v1002 = false := by decide +kernel

lemma deny1003 : go 5 v1003 = false := by decide +kernel

lemma deny1004 : go 5 v1004 = false := by decide +kernel

lemma deny1005 : go 5 v1005 = false := by decide +kernel

lemma deny1006 : go 5 v1006 = false := by decide +kernel

lemma deny1007 : go 5 v1007 = false := by decide +kernel

lemma deny1008 : go 5 v1008 = false := by decide +kernel

lemma deny1009 : go 5 v1009 = false := by decide +kernel

lemma deny1010 : go 5 v1010 = false := by decide +kernel

lemma deny1011 : go 5 v1011 = false := by decide +kernel

lemma deny1012 : go 5 v1012 = false := by decide +kernel

lemma deny1013 : go 5 v1013 = false := by decide +kernel

lemma deny1014 : go 5 v1014 = false := by decide +kernel

lemma deny1015 : go 5 v1015 = false := by decide +kernel

lemma deny1016 : go 5 v1016 = false := by decide +kernel

lemma deny1017 : go 5 v1017 = false := by decide +kernel

lemma deny1018 : go 5 v1018 = false := by decide +kernel

lemma deny1019 : go 5 v1019 = false := by decide +kernel

lemma deny1020 : go 5 v1020 = false := by decide +kernel

lemma deny1021 : go 5 v1021 = false := by decide +kernel

lemma deny1022 : go 5 v1022 = false := by decide +kernel

lemma deny1023 : go 5 v1023 = false := by decide +kernel

lemma deny1024 : go 5 v1024 = false := by decide +kernel

lemma deny1025 : go 5 v1025 = false := by decide +kernel

lemma deny1026 : go 5 v1026 = false := by decide +kernel

lemma deny1027 : go 5 v1027 = false := by decide +kernel

lemma deny1028 : go 5 v1028 = false := by decide +kernel

lemma deny1029 : go 5 v1029 = false := by decide +kernel

lemma deny1030 : go 5 v1030 = false := by decide +kernel

lemma deny1031 : go 5 v1031 = false := by decide +kernel

lemma deny1032 : go 5 v1032 = false := by decide +kernel

lemma deny1033 : go 5 v1033 = false := by decide +kernel

lemma deny1034 : go 5 v1034 = false := by decide +kernel

lemma deny1035 : go 5 v1035 = false := by decide +kernel

lemma deny1036 : go 5 v1036 = false := by decide +kernel

lemma deny1037 : go 5 v1037 = false := by decide +kernel

lemma deny1038 : go 5 v1038 = false := by decide +kernel

lemma deny1039 : go 5 v1039 = false := by decide +kernel

lemma deny1040 : go 5 v1040 = false := by decide +kernel

lemma deny1041 : go 5 v1041 = false := by decide +kernel

lemma deny1053 : go 5 v1053 = false := by decide +kernel

lemma deny1054 : go 5 v1054 = false := by decide +kernel

lemma deny1055 : go 5 v1055 = false := by decide +kernel

lemma deny1056 : go 5 v1056 = false := by decide +kernel

lemma deny1057 : go 5 v1057 = false := by decide +kernel

lemma deny1058 : go 5 v1058 = false := by decide +kernel

lemma deny1059 : go 5 v1059 = false := by decide +kernel

lemma deny1060 : go 5 v1060 = false := by decide +kernel

lemma deny1061 : go 5 v1061 = false := by decide +kernel

lemma deny1062 : go 5 v1062 = false := by decide +kernel

lemma deny1063 : go 5 v1063 = false := by decide +kernel

lemma deny1064 : go 5 v1064 = false := by decide +kernel

lemma deny1065 : go 5 v1065 = false := by decide +kernel

lemma deny1066 : go 5 v1066 = false := by decide +kernel

lemma deny1067 : go 5 v1067 = false := by decide +kernel

lemma deny1068 : go 5 v1068 = false := by decide +kernel

lemma deny1069 : go 5 v1069 = false := by decide +kernel

lemma deny1070 : go 5 v1070 = false := by decide +kernel

lemma deny1071 : go 5 v1071 = false := by decide +kernel

lemma deny1072 : go 5 v1072 = false := by decide +kernel

lemma deny1073 : go 5 v1073 = false := by decide +kernel

lemma deny1074 : go 5 v1074 = false := by decide +kernel

lemma deny1075 : go 5 v1075 = false := by decide +kernel

lemma deny1076 : go 5 v1076 = false := by decide +kernel

lemma deny1077 : go 5 v1077 = false := by decide +kernel

lemma deny1078 : go 5 v1078 = false := by decide +kernel

lemma deny1079 : go 5 v1079 = false := by decide +kernel

lemma deny1080 : go 5 v1080 = false := by decide +kernel

lemma deny1081 : go 5 v1081 = false := by decide +kernel

lemma deny1082 : go 5 v1082 = false := by decide +kernel

lemma deny1083 : go 5 v1083 = false := by decide +kernel

lemma deny1084 : go 5 v1084 = false := by decide +kernel

lemma deny1085 : go 5 v1085 = false := by decide +kernel

lemma deny1086 : go 5 v1086 = false := by decide +kernel

lemma deny1087 : go 5 v1087 = false := by decide +kernel

lemma deny1088 : go 5 v1088 = false := by decide +kernel

lemma deny1089 : go 5 v1089 = false := by decide +kernel

lemma deny1090 : go 5 v1090 = false := by decide +kernel

lemma deny1091 : go 5 v1091 = false := by decide +kernel

lemma deny1098 : go 5 v1098 = false := by decide +kernel

lemma deny1099 : go 5 v1099 = false := by decide +kernel

lemma deny1100 : go 5 v1100 = false := by decide +kernel

lemma deny1101 : go 5 v1101 = false := by decide +kernel

lemma deny1102 : go 5 v1102 = false := by decide +kernel

lemma deny1103 : go 5 v1103 = false := by decide +kernel

lemma deny1104 : go 5 v1104 = false := by decide +kernel

lemma deny1105 : go 5 v1105 = false := by decide +kernel

lemma deny1106 : go 5 v1106 = false := by decide +kernel

lemma deny1107 : go 5 v1107 = false := by decide +kernel

lemma deny1108 : go 5 v1108 = false := by decide +kernel

lemma deny1109 : go 5 v1109 = false := by decide +kernel

lemma deny1110 : go 5 v1110 = false := by decide +kernel

lemma deny1111 : go 5 v1111 = false := by decide +kernel

lemma deny1112 : go 5 v1112 = false := by decide +kernel

lemma deny1113 : go 5 v1113 = false := by decide +kernel

lemma deny1114 : go 5 v1114 = false := by decide +kernel

lemma deny1115 : go 5 v1115 = false := by decide +kernel

lemma deny1116 : go 5 v1116 = false := by decide +kernel

lemma deny1117 : go 5 v1117 = false := by decide +kernel

lemma deny1118 : go 5 v1118 = false := by decide +kernel

lemma deny1119 : go 5 v1119 = false := by decide +kernel

lemma deny1120 : go 5 v1120 = false := by decide +kernel

lemma deny1121 : go 5 v1121 = false := by decide +kernel

lemma deny1122 : go 5 v1122 = false := by decide +kernel

lemma deny1123 : go 5 v1123 = false := by decide +kernel

lemma deny1124 : go 5 v1124 = false := by decide +kernel

lemma deny1125 : go 5 v1125 = false := by decide +kernel

lemma deny1126 : go 5 v1126 = false := by decide +kernel

lemma deny1127 : go 5 v1127 = false := by decide +kernel

lemma deny1128 : go 5 v1128 = false := by decide +kernel

lemma deny1129 : go 5 v1129 = false := by decide +kernel

lemma deny1130 : go 5 v1130 = false := by decide +kernel

lemma deny1131 : go 5 v1131 = false := by decide +kernel

lemma deny1132 : go 5 v1132 = false := by decide +kernel

lemma deny1133 : go 5 v1133 = false := by decide +kernel

lemma deny1134 : go 5 v1134 = false := by decide +kernel

lemma deny1135 : go 5 v1135 = false := by decide +kernel

lemma deny1136 : go 5 v1136 = false := by decide +kernel

lemma deny1148 : go 5 v1148 = false := by decide +kernel

lemma deny1149 : go 5 v1149 = false := by decide +kernel

lemma deny1150 : go 5 v1150 = false := by decide +kernel

lemma deny1151 : go 5 v1151 = false := by decide +kernel

lemma deny1152 : go 5 v1152 = false := by decide +kernel

lemma deny1153 : go 5 v1153 = false := by decide +kernel

lemma deny1154 : go 5 v1154 = false := by decide +kernel

lemma deny1155 : go 5 v1155 = false := by decide +kernel

lemma deny1156 : go 5 v1156 = false := by decide +kernel

lemma deny1157 : go 5 v1157 = false := by decide +kernel

lemma deny1158 : go 5 v1158 = false := by decide +kernel

lemma deny1159 : go 5 v1159 = false := by decide +kernel

lemma deny1160 : go 5 v1160 = false := by decide +kernel

lemma deny1161 : go 5 v1161 = false := by decide +kernel

lemma deny1162 : go 5 v1162 = false := by decide +kernel

lemma deny1163 : go 5 v1163 = false := by decide +kernel

lemma deny1164 : go 5 v1164 = false := by decide +kernel

lemma deny1165 : go 5 v1165 = false := by decide +kernel

lemma deny1166 : go 5 v1166 = false := by decide +kernel

lemma deny1167 : go 5 v1167 = false := by decide +kernel

lemma deny1168 : go 5 v1168 = false := by decide +kernel

lemma deny1169 : go 5 v1169 = false := by decide +kernel

lemma deny1170 : go 5 v1170 = false := by decide +kernel

lemma deny1171 : go 5 v1171 = false := by decide +kernel

lemma deny1172 : go 5 v1172 = false := by decide +kernel

lemma deny1173 : go 5 v1173 = false := by decide +kernel

lemma deny1174 : go 5 v1174 = false := by decide +kernel

lemma deny1175 : go 5 v1175 = false := by decide +kernel

lemma deny1176 : go 5 v1176 = false := by decide +kernel

lemma deny1177 : go 5 v1177 = false := by decide +kernel

lemma deny1178 : go 5 v1178 = false := by decide +kernel

lemma deny1179 : go 5 v1179 = false := by decide +kernel

lemma deny1180 : go 5 v1180 = false := by decide +kernel

lemma deny1181 : go 5 v1181 = false := by decide +kernel

lemma deny1182 : go 5 v1182 = false := by decide +kernel

lemma deny1183 : go 5 v1183 = false := by decide +kernel

lemma deny1184 : go 5 v1184 = false := by decide +kernel

lemma deny1185 : go 5 v1185 = false := by decide +kernel

lemma deny1186 : go 5 v1186 = false := by decide +kernel

lemma deny1187 : go 5 v1187 = false := by decide +kernel

lemma deny1188 : go 5 v1188 = false := by decide +kernel

lemma deny1189 : go 5 v1189 = false := by decide +kernel

lemma deny1190 : go 5 v1190 = false := by decide +kernel

lemma deny1191 : go 5 v1191 = false := by decide +kernel

lemma deny1192 : go 5 v1192 = false := by decide +kernel

lemma deny1201 : go 5 v1201 = false := by decide +kernel

lemma deny1202 : go 5 v1202 = false := by decide +kernel

lemma deny1203 : go 5 v1203 = false := by decide +kernel

lemma deny1204 : go 5 v1204 = false := by decide +kernel

lemma deny1205 : go 5 v1205 = false := by decide +kernel

lemma deny1206 : go 5 v1206 = false := by decide +kernel

lemma deny1207 : go 5 v1207 = false := by decide +kernel

lemma deny1208 : go 5 v1208 = false := by decide +kernel

lemma deny1209 : go 5 v1209 = false := by decide +kernel

lemma deny1210 : go 5 v1210 = false := by decide +kernel

lemma deny1211 : go 5 v1211 = false := by decide +kernel

lemma deny1212 : go 5 v1212 = false := by decide +kernel

lemma deny1213 : go 5 v1213 = false := by decide +kernel

lemma deny1214 : go 5 v1214 = false := by decide +kernel

lemma deny1215 : go 5 v1215 = false := by decide +kernel

lemma deny1216 : go 5 v1216 = false := by decide +kernel

lemma deny1217 : go 5 v1217 = false := by decide +kernel

lemma deny1218 : go 5 v1218 = false := by decide +kernel

lemma deny1219 : go 5 v1219 = false := by decide +kernel

lemma deny1220 : go 5 v1220 = false := by decide +kernel

lemma deny1221 : go 5 v1221 = false := by decide +kernel

lemma deny1222 : go 5 v1222 = false := by decide +kernel

lemma deny1223 : go 5 v1223 = false := by decide +kernel

lemma deny1224 : go 5 v1224 = false := by decide +kernel

lemma deny1225 : go 5 v1225 = false := by decide +kernel

lemma deny1226 : go 5 v1226 = false := by decide +kernel

lemma deny1227 : go 5 v1227 = false := by decide +kernel

lemma deny1228 : go 5 v1228 = false := by decide +kernel

lemma deny1229 : go 5 v1229 = false := by decide +kernel

lemma deny1230 : go 5 v1230 = false := by decide +kernel

lemma deny1231 : go 5 v1231 = false := by decide +kernel

lemma deny1232 : go 5 v1232 = false := by decide +kernel

lemma deny1233 : go 5 v1233 = false := by decide +kernel

lemma deny1234 : go 5 v1234 = false := by decide +kernel

lemma deny1235 : go 5 v1235 = false := by decide +kernel

lemma deny1236 : go 5 v1236 = false := by decide +kernel

lemma deny1237 : go 5 v1237 = false := by decide +kernel

lemma deny1238 : go 5 v1238 = false := by decide +kernel

lemma deny1239 : go 5 v1239 = false := by decide +kernel

lemma deny1240 : go 5 v1240 = false := by decide +kernel

lemma deny1241 : go 5 v1241 = false := by decide +kernel

lemma deny1242 : go 5 v1242 = false := by decide +kernel

lemma deny1243 : go 5 v1243 = false := by decide +kernel

lemma deny1244 : go 5 v1244 = false := by decide +kernel

lemma deny1245 : go 5 v1245 = false := by decide +kernel

lemma deny1 : go 6 v1 = false := by decide +kernel

lemma deny2 : go 6 v2 = false := by
  apply cutGo 5 v2 c2
  · decide +kernel
  · simp [c2,deny3,deny4,deny5,deny6,deny7,deny8,deny9,deny10,deny11,deny12,deny13,deny14,deny15,deny16,deny17,deny18,deny19,deny20,deny21,deny22,deny23,deny24,deny25,deny26,deny27,deny28,deny29,deny30,deny31,deny32,deny33,deny34,deny35,deny36,deny37,deny38,deny39,deny40,deny41,deny42,deny43,deny44,deny45,deny46,deny47,deny48,deny49,deny50,deny51,deny52,deny53,deny54,deny55,deny56,deny57,deny58,deny59,deny60,deny61,deny62,deny63,deny64,deny65,deny66,deny67,deny68,deny69,deny70,deny71,deny72,deny73,deny74,deny75,deny76,deny77,deny78,deny79,deny80,deny81,deny82,deny83,deny84,deny85,deny86,deny87,deny88,deny89,deny90,deny91,deny92,deny93,deny94,deny95,deny96,deny97,deny98,deny99]

lemma deny100 : go 6 v100 = false := by decide +kernel

lemma deny101 : go 6 v101 = false := by
  apply cutGo 5 v101 c101
  · decide +kernel
  · simp [c101,deny102,deny103,deny104,deny105,deny106,deny107,deny108,deny109,deny110,deny111,deny112,deny113,deny114,deny115,deny116,deny117,deny118,deny119,deny120,deny121,deny122,deny123,deny124,deny125,deny126,deny127,deny128,deny129,deny130,deny131,deny132,deny133,deny134,deny135,deny136,deny137,deny138,deny139,deny140,deny141,deny142,deny143,deny144,deny145,deny146,deny147,deny148,deny149,deny150,deny151,deny152,deny153,deny154,deny155,deny156,deny157,deny158,deny159,deny160,deny161,deny162,deny163,deny164,deny165,deny166,deny167,deny168,deny169,deny170,deny171,deny172,deny173,deny174,deny175,deny176,deny177,deny178,deny179,deny180,deny181,deny182,deny183,deny184,deny185,deny186,deny187,deny188,deny189,deny190,deny191,deny192,deny193]

lemma deny194 : go 6 v194 = false := by
  apply cutGo 5 v194 c194
  · decide +kernel
  · simp [c194,deny195,deny196,deny197,deny198,deny199,deny200,deny201,deny202,deny203,deny204,deny205,deny206,deny207,deny208,deny209,deny210,deny211,deny212,deny213,deny214,deny215,deny216,deny217,deny218,deny219,deny220,deny221,deny222,deny223,deny224,deny225,deny226,deny227,deny228,deny229,deny230,deny231,deny232,deny233,deny234,deny235,deny236,deny237,deny238,deny239,deny240,deny241,deny242,deny243,deny244,deny245,deny246,deny247,deny248,deny249,deny250,deny251,deny252,deny253,deny254,deny255,deny256,deny257,deny258,deny259,deny260,deny261,deny262,deny263,deny264,deny265,deny266,deny267,deny268,deny269,deny270,deny271,deny272,deny273,deny274,deny275,deny276,deny277,deny278,deny279,deny280,deny281,deny282,deny283,deny284,deny285,deny286]

lemma deny287 : go 6 v287 = false := by decide +kernel

lemma deny288 : go 6 v288 = false := by decide +kernel

lemma deny289 : go 6 v289 = false := by
  apply cutGo 5 v289 c289
  · decide +kernel
  · simp [c289,deny290,deny291,deny292,deny293,deny294,deny295,deny296,deny297,deny298,deny299,deny300,deny301,deny302,deny303,deny304,deny305,deny306,deny307,deny308,deny309,deny310,deny311,deny312,deny313,deny314,deny315,deny316,deny317,deny318,deny319,deny320,deny321,deny322,deny323,deny324,deny325,deny326,deny327,deny328,deny329,deny330,deny331,deny332,deny333,deny334,deny335,deny336,deny337,deny338,deny339,deny340,deny341,deny342,deny343,deny344,deny345,deny346,deny347,deny348,deny349,deny350,deny351,deny352,deny353,deny354,deny355,deny356,deny357,deny358,deny359,deny360,deny361,deny362,deny363,deny364,deny365,deny366,deny367,deny368,deny369,deny370,deny371,deny372,deny373,deny374,deny375,deny376,deny377,deny378,deny379,deny380,deny381,deny382,deny383,deny384,deny385,deny386,deny387,deny388]

lemma deny389 : go 6 v389 = false := by decide +kernel

lemma deny390 : go 6 v390 = false := by
  apply cutGo 5 v390 c390
  · decide +kernel
  · simp [c390,deny391,deny392,deny393,deny394,deny395,deny396,deny397,deny398,deny399,deny400,deny401,deny402,deny403,deny404,deny405,deny406,deny407,deny408,deny409,deny410,deny411,deny412,deny413,deny414,deny415,deny416,deny417,deny418,deny419,deny420,deny421,deny422,deny423,deny424,deny425,deny426,deny427,deny428,deny429,deny430,deny431,deny432,deny433,deny434,deny435,deny436]

lemma deny437 : go 6 v437 = false := by decide +kernel

lemma deny438 : go 6 v438 = false := by
  apply cutGo 5 v438 c438
  · decide +kernel
  · simp [c438,deny439,deny440,deny441,deny442,deny443,deny444,deny445,deny446,deny447,deny448,deny449,deny450,deny451,deny452,deny453,deny454,deny455,deny456,deny457,deny458,deny459,deny460,deny461,deny462,deny463,deny464,deny465,deny466,deny467,deny468,deny469,deny470,deny471,deny472,deny473,deny474,deny475,deny476,deny477]

lemma deny478 : go 6 v478 = false := by decide +kernel

lemma deny479 : go 6 v479 = false := by decide +kernel

lemma deny480 : go 6 v480 = false := by decide +kernel

lemma deny481 : go 6 v481 = false := by decide +kernel

lemma deny482 : go 6 v482 = false := by
  apply cutGo 5 v482 c482
  · decide +kernel
  · simp [c482,deny483,deny484,deny485,deny486,deny487,deny488,deny489,deny490,deny491,deny492,deny493,deny494,deny495,deny496,deny497,deny498,deny499,deny500,deny501,deny502,deny503,deny504,deny505,deny506,deny507,deny508,deny509,deny510,deny511,deny512,deny513,deny514,deny515,deny516,deny517,deny518,deny519,deny520,deny521,deny522,deny523,deny524,deny525,deny526,deny527,deny528,deny529,deny530,deny531,deny532,deny533,deny534,deny535,deny536,deny537,deny538,deny539,deny540,deny541,deny542,deny543,deny544,deny545,deny546,deny547,deny548,deny549,deny550,deny551,deny552,deny553,deny554,deny555,deny556,deny557,deny558,deny559,deny560,deny561,deny562,deny563,deny564,deny565,deny566,deny567,deny568,deny569,deny570,deny571,deny572,deny573,deny574,deny575,deny576,deny577,deny578,deny579,deny580,deny581,deny582]

lemma deny583 : go 6 v583 = false := by decide +kernel

lemma deny584 : go 6 v584 = false := by decide +kernel

lemma deny585 : go 6 v585 = false := by decide +kernel

lemma deny586 : go 6 v586 = false := by decide +kernel

lemma deny587 : go 6 v587 = false := by
  apply cutGo 5 v587 c587
  · decide +kernel
  · simp [c587,deny588,deny589,deny590,deny591,deny592,deny593,deny594,deny595,deny596,deny597,deny598,deny599,deny600,deny601,deny602,deny603,deny604,deny605,deny606,deny607,deny608,deny609,deny610,deny611,deny612,deny613,deny614,deny615,deny616,deny617,deny618,deny619,deny620,deny621,deny622,deny623,deny624,deny625,deny626,deny627,deny628,deny629,deny630,deny631,deny632,deny633,deny634,deny635,deny636,deny637,deny638,deny639,deny640,deny641,deny642,deny643,deny644,deny645,deny646,deny647,deny648,deny649,deny650,deny651,deny652,deny653,deny654,deny655,deny656,deny657,deny658,deny659,deny660,deny661,deny662,deny663,deny664,deny665,deny666,deny667,deny668,deny669,deny670,deny671,deny672,deny673,deny674,deny675,deny676,deny677,deny678,deny679,deny680,deny681,deny682,deny683,deny684]

lemma deny685 : go 6 v685 = false := by decide +kernel

lemma deny686 : go 6 v686 = false := by decide +kernel

lemma deny687 : go 6 v687 = false := by decide +kernel

lemma deny688 : go 6 v688 = false := by decide +kernel

lemma deny689 : go 6 v689 = false := by decide +kernel

lemma deny690 : go 6 v690 = false := by decide +kernel

lemma deny691 : go 6 v691 = false := by decide +kernel

lemma deny692 : go 6 v692 = false := by decide +kernel

lemma deny693 : go 6 v693 = false := by decide +kernel

lemma deny694 : go 6 v694 = false := by decide +kernel

lemma deny695 : go 6 v695 = false := by decide +kernel

lemma deny696 : go 6 v696 = false := by decide +kernel

lemma deny697 : go 6 v697 = false := by decide +kernel

lemma deny698 : go 6 v698 = false := by
  apply cutGo 5 v698 c698
  · decide +kernel
  · simp [c698,deny699,deny700,deny701,deny702,deny703,deny704,deny705,deny706,deny707,deny708,deny709,deny710,deny711,deny712,deny713,deny714,deny715,deny716,deny717,deny718,deny719,deny720,deny721,deny722,deny723,deny724,deny725,deny726,deny727,deny728,deny729,deny730,deny731,deny732,deny733,deny734,deny735,deny736,deny737,deny738,deny739,deny740,deny741,deny742,deny743,deny744,deny745]

lemma deny746 : go 6 v746 = false := by decide +kernel

lemma deny747 : go 6 v747 = false := by
  apply cutGo 5 v747 c747
  · decide +kernel
  · simp [c747,deny748,deny749,deny750,deny751,deny752,deny753,deny754,deny755,deny756,deny757,deny758,deny759,deny760,deny761,deny762,deny763,deny764,deny765,deny766,deny767,deny768,deny769,deny770,deny771,deny772,deny773,deny774,deny775,deny776,deny777,deny778,deny779,deny780,deny781,deny782,deny783,deny784,deny785,deny786,deny787]

lemma deny788 : go 6 v788 = false := by decide +kernel

lemma deny789 : go 6 v789 = false := by decide +kernel

lemma deny790 : go 6 v790 = false := by
  apply cutGo 5 v790 c790
  · decide +kernel
  · simp [c790,deny791,deny792,deny793,deny794,deny795,deny796,deny797,deny798,deny799,deny800,deny801,deny802,deny803,deny804,deny805,deny806,deny807,deny808,deny809,deny810,deny811,deny812,deny813,deny814,deny815,deny816,deny817,deny818,deny819,deny820,deny821,deny822,deny823,deny824,deny825,deny826,deny827,deny828,deny829,deny830,deny831,deny832,deny833,deny834,deny835,deny836,deny837,deny838,deny839,deny840,deny841,deny842,deny843,deny844,deny845,deny846,deny847,deny848,deny849,deny850,deny851,deny852,deny853,deny854,deny855,deny856,deny857,deny858,deny859,deny860,deny861,deny862,deny863,deny864,deny865,deny866,deny867,deny868,deny869,deny870,deny871,deny872,deny873,deny874,deny875,deny876,deny877,deny878,deny879,deny880,deny881,deny882,deny883,deny884,deny885,deny886,deny887,deny888,deny889,deny890]

lemma deny891 : go 6 v891 = false := by decide +kernel

lemma deny892 : go 6 v892 = false := by decide +kernel

lemma deny893 : go 6 v893 = false := by
  apply cutGo 5 v893 c893
  · decide +kernel
  · simp [c893,deny894,deny895,deny896,deny897,deny898,deny899,deny900,deny901,deny902,deny903,deny904,deny905,deny906,deny907,deny908,deny909,deny910,deny911,deny912,deny913,deny914,deny915,deny916,deny917,deny918,deny919,deny920,deny921,deny922,deny923,deny924,deny925,deny926,deny927,deny928,deny929,deny930,deny931,deny932,deny933,deny934,deny935,deny936,deny937,deny938,deny939,deny940,deny941,deny942,deny943,deny944,deny945,deny946,deny947,deny948,deny949,deny950,deny951,deny952,deny953,deny954,deny955,deny956,deny957,deny958,deny959,deny960,deny961,deny962,deny963,deny964,deny965,deny966,deny967,deny968,deny969,deny970,deny971,deny972,deny973,deny974,deny975,deny976,deny977,deny978,deny979,deny980,deny981,deny982,deny983,deny984,deny985,deny986,deny987,deny988,deny989,deny990,deny991,deny992]

lemma deny993 : go 6 v993 = false := by decide +kernel

lemma deny994 : go 6 v994 = false := by decide +kernel

lemma deny995 : go 6 v995 = false := by decide +kernel

lemma deny996 : go 6 v996 = false := by
  apply cutGo 5 v996 c996
  · decide +kernel
  · simp [c996,deny997,deny998,deny999,deny1000,deny1001,deny1002,deny1003,deny1004,deny1005,deny1006,deny1007,deny1008,deny1009,deny1010,deny1011,deny1012,deny1013,deny1014,deny1015,deny1016,deny1017,deny1018,deny1019,deny1020,deny1021,deny1022,deny1023,deny1024,deny1025,deny1026,deny1027,deny1028,deny1029,deny1030,deny1031,deny1032,deny1033,deny1034,deny1035,deny1036,deny1037,deny1038,deny1039,deny1040,deny1041]

lemma deny1042 : go 6 v1042 = false := by decide +kernel

lemma deny1043 : go 6 v1043 = false := by decide +kernel

lemma deny1044 : go 6 v1044 = false := by decide +kernel

lemma deny1045 : go 6 v1045 = false := by decide +kernel

lemma deny1046 : go 6 v1046 = false := by decide +kernel

lemma deny1047 : go 6 v1047 = false := by decide +kernel

lemma deny1048 : go 6 v1048 = false := by decide +kernel

lemma deny1049 : go 6 v1049 = false := by decide +kernel

lemma deny1050 : go 6 v1050 = false := by decide +kernel

lemma deny1051 : go 6 v1051 = false := by decide +kernel

lemma deny1052 : go 6 v1052 = false := by
  apply cutGo 5 v1052 c1052
  · decide +kernel
  · simp [c1052,deny1053,deny1054,deny1055,deny1056,deny1057,deny1058,deny1059,deny1060,deny1061,deny1062,deny1063,deny1064,deny1065,deny1066,deny1067,deny1068,deny1069,deny1070,deny1071,deny1072,deny1073,deny1074,deny1075,deny1076,deny1077,deny1078,deny1079,deny1080,deny1081,deny1082,deny1083,deny1084,deny1085,deny1086,deny1087,deny1088,deny1089,deny1090,deny1091]

lemma deny1092 : go 6 v1092 = false := by decide +kernel

lemma deny1093 : go 6 v1093 = false := by decide +kernel

lemma deny1094 : go 6 v1094 = false := by decide +kernel

lemma deny1095 : go 6 v1095 = false := by decide +kernel

lemma deny1096 : go 6 v1096 = false := by decide +kernel

lemma deny1097 : go 6 v1097 = false := by
  apply cutGo 5 v1097 c1097
  · decide +kernel
  · simp [c1097,deny1098,deny1099,deny1100,deny1101,deny1102,deny1103,deny1104,deny1105,deny1106,deny1107,deny1108,deny1109,deny1110,deny1111,deny1112,deny1113,deny1114,deny1115,deny1116,deny1117,deny1118,deny1119,deny1120,deny1121,deny1122,deny1123,deny1124,deny1125,deny1126,deny1127,deny1128,deny1129,deny1130,deny1131,deny1132,deny1133,deny1134,deny1135,deny1136]

lemma deny1137 : go 6 v1137 = false := by decide +kernel

lemma deny1138 : go 6 v1138 = false := by decide +kernel

lemma deny1139 : go 6 v1139 = false := by decide +kernel

lemma deny1140 : go 6 v1140 = false := by decide +kernel

lemma deny1141 : go 6 v1141 = false := by decide +kernel

lemma deny1142 : go 6 v1142 = false := by decide +kernel

lemma deny1143 : go 6 v1143 = false := by decide +kernel

lemma deny1144 : go 6 v1144 = false := by decide +kernel

lemma deny1145 : go 6 v1145 = false := by decide +kernel

lemma deny1146 : go 6 v1146 = false := by decide +kernel

lemma deny1147 : go 6 v1147 = false := by
  apply cutGo 5 v1147 c1147
  · decide +kernel
  · simp [c1147,deny1148,deny1149,deny1150,deny1151,deny1152,deny1153,deny1154,deny1155,deny1156,deny1157,deny1158,deny1159,deny1160,deny1161,deny1162,deny1163,deny1164,deny1165,deny1166,deny1167,deny1168,deny1169,deny1170,deny1171,deny1172,deny1173,deny1174,deny1175,deny1176,deny1177,deny1178,deny1179,deny1180,deny1181,deny1182,deny1183,deny1184,deny1185,deny1186,deny1187,deny1188,deny1189,deny1190,deny1191,deny1192]

lemma deny1193 : go 6 v1193 = false := by decide +kernel

lemma deny1194 : go 6 v1194 = false := by decide +kernel

lemma deny1195 : go 6 v1195 = false := by decide +kernel

lemma deny1196 : go 6 v1196 = false := by decide +kernel

lemma deny1197 : go 6 v1197 = false := by decide +kernel

lemma deny1198 : go 6 v1198 = false := by decide +kernel

lemma deny1199 : go 6 v1199 = false := by decide +kernel

lemma deny1200 : go 6 v1200 = false := by
  apply cutGo 5 v1200 c1200
  · decide +kernel
  · simp [c1200,deny1201,deny1202,deny1203,deny1204,deny1205,deny1206,deny1207,deny1208,deny1209,deny1210,deny1211,deny1212,deny1213,deny1214,deny1215,deny1216,deny1217,deny1218,deny1219,deny1220,deny1221,deny1222,deny1223,deny1224,deny1225,deny1226,deny1227,deny1228,deny1229,deny1230,deny1231,deny1232,deny1233,deny1234,deny1235,deny1236,deny1237,deny1238,deny1239,deny1240,deny1241,deny1242,deny1243,deny1244,deny1245]

lemma deny1246 : go 6 v1246 = false := by decide +kernel

lemma deny1247 : go 6 v1247 = false := by decide +kernel

lemma deny1248 : go 6 v1248 = false := by decide +kernel

lemma deny1249 : go 6 v1249 = false := by decide +kernel

lemma deny1250 : go 6 v1250 = false := by decide +kernel

lemma deny1251 : go 6 v1251 = false := by decide +kernel

lemma deny1252 : go 6 v1252 = false := by decide +kernel

lemma deny1253 : go 6 v1253 = false := by decide +kernel

lemma deny1254 : go 6 v1254 = false := by decide +kernel

lemma deny0 : go 7 v0 = false := by
  apply cutGo 6 v0 c0
  · decide +kernel
  · simp [c0,deny1,deny2,deny100,deny101,deny194,deny287,deny288,deny289,deny389,deny390,deny437,deny438,deny478,deny479,deny480,deny481,deny482,deny583,deny584,deny585,deny586,deny587,deny685,deny686,deny687,deny688,deny689,deny690,deny691,deny692,deny693,deny694,deny695,deny696,deny697,deny698,deny746,deny747,deny788,deny789,deny790,deny891,deny892,deny893,deny993,deny994,deny995,deny996,deny1042,deny1043,deny1044,deny1045,deny1046,deny1047,deny1048,deny1049,deny1050,deny1051,deny1052,deny1092,deny1093,deny1094,deny1095,deny1096,deny1097,deny1137,deny1138,deny1139,deny1140,deny1141,deny1142,deny1143,deny1144,deny1145,deny1146,deny1147,deny1193,deny1194,deny1195,deny1196,deny1197,deny1198,deny1199,deny1200,deny1246,deny1247,deny1248,deny1249,deny1250,deny1251,deny1252,deny1253,deny1254]

end PEqualNP.Outside.L_meta_5056_aux

open PEqualNP.Outside.L_meta_5056_aux

theorem PEqualNP.Outside.L_meta_5056 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (8 : ℕ) →       (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →           have x6 : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => Relation.ReflTransGen (fun (x8 x9 : ℕ) => (10 : ℕ) ≤ x9 ∧ x9 < (17 : ℕ) ∧ x8 < x9 ∧ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x9 - (9 : ℕ))).inputs) x6 x7;           have x7 : (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)));           ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card = (6 : ℕ) → (9 : ℕ) ∈ x8 → ¬((0 : ℕ) ∈ x8 ∧ (2 : ℕ) ∈ x8) → (∀ x13 < (9 : ℕ), ∃ x15 ∈ x8, x6 x13 x15) → (∃ (x14 : Finset ℕ), (4 : ℕ) ≤ x14.card ∧ ∀ x15 ∈ x14, (10 : ℕ) ≤ x15 ∧ x15 < (17 : ℕ) ∧ ∃ x17 ∈ x8, x6 x15 x17) → ∃ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ) → Bool), x7 x15 ≠ x7 x16 ∧ ∀ x17 ∈ x8, (x1.wires (List.ofFn x15)).getD x17 Bool.false = (x1.wires (List.ofFn x16)).getD x17 Bool.false := by
  intro C legal sz nn first
  dsimp only
  intro S _ card included _ _ _
  by_contra ob
  have hit := frontier C legal sz nn first S card included ob
  have dead : go 7 (start.map code) = false := deny0
  simp [dead] at hit
