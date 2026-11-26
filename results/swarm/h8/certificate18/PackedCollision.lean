import SameSet

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.PackedCollision
open PEqualNP.Outside.L_meta_6581

abbrev Signals (n : Nat) := BitVec n × BitVec n

def ofRows {n : Nat} (rows : Fin n → Extended.Row) (w : Word) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i => Extended.bit (rows i) w)).cast List.length_ofFn

lemma ofRows_bit {n : Nat} (rows : Fin n → Extended.Row) (w : Word) (i : Fin n) :
    (ofRows rows w).getLsbD i.val = Extended.bit (rows i) w := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

lemma ofRows_bin {n : Nat} (rows : Fin n → Extended.Row) (d : Nat) (a b : Word) :
    ofRows rows (Extended.bin d a b) = bv d (ofRows rows a) (ofRows rows b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit rows (Extended.bin d a b) ⟨j,hj⟩
  rw [Automorphism.bit_bin,←ofRows_bit rows a ⟨j,hj⟩,←ofRows_bit rows b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]

def signature {n : Nat} (r s : Fin n → Extended.Row) (w : Word) : Signals n :=
  (ofRows r w,ofRows s w)

def gate {n : Nat} (d : Nat) (a b : Signals n) : Signals n :=
  (bv d a.1 b.1,bv d a.2 b.2)

lemma signature_bin {n : Nat} (r s : Fin n → Extended.Row) (d : Nat) (a b : Word) :
    signature r s (Extended.bin d a b) = gate d (signature r s a) (signature r s b) := by
  simp only [signature,gate,ofRows_bin]

lemma signature_zero {n : Nat} (r s : Fin n → Extended.Row) :
    signature r s Extended.zero = (0,0) := by
  have hz (rows : Fin n → Extended.Row) : ofRows rows Extended.zero = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [ofRows_bit rows Extended.zero ⟨i,hi⟩]
    simp [Extended.bit,Extended.zero]
  exact Prod.ext (hz r) (hz s)

def lookup {α : Type} : List (Word × α) → Word → Option α
  | [], _ => none
  | p::ps, a => if p.1 == a then some p.2 else lookup ps a

lemma lookup_map {α : Type} (f : Word → α) (ws : List Word) (a : Word) :
    (lookup (ws.map fun w => (w,f w)) a).getD (f a) = f a := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons,lookup]
    cases h : w == a with
    | false => simpa only [h,Bool.false_eq_true,ite_false] using ih
    | true =>
      have e : w = a := beq_iff_eq.mp h
      subst w
      simp only [ite_true,Option.getD_some]

def read {n : Nat} (r s : Fin n → Extended.Row) (parent : List Word) (a : Word) : Signals n :=
  (lookup (parent.map fun w => (w,signature r s w)) a).getD (signature r s a)

lemma read_eq {n : Nat} (r s : Fin n → Extended.Row) (parent : List Word) (a : Word) :
    read r s parent a = signature r s a := lookup_map _ _ _

lemma read_fun_eq {n : Nat} (r s : Fin n → Extended.Row) (parent : List Word) :
    read r s parent = signature r s := funext (read_eq r s parent)

def coverage {n : Nat} : List (Signals n) → BitVec n
  | [] => 0
  | p::ps => (p.1 ^^^ p.2) ||| coverage ps

lemma coverage_agree {n : Nat} {ps : List (Signals n)} {i : Fin n}
    (h : (coverage ps).getLsbD i.val = false) :
    ∀ p ∈ ps, p.1.getLsbD i.val = p.2.getLsbD i.val := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    have ha : a.1.getLsbD i.val = a.2.getLsbD i.val := by
      cases h1 : a.1.getLsbD i.val <;> cases h2 : a.2.getLsbD i.val <;>
        simp_all [coverage,BitVec.getLsbD_or,BitVec.getLsbD_xor]
    have ht : (coverage ps).getLsbD i.val = false := by
      simpa only [coverage,BitVec.getLsbD_or,BitVec.getLsbD_xor,ha,Bool.xor_self,Bool.false_or] using h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hm
    · exact ha
    · exact ih ht p hm

lemma missingBit {n : Nat} (a : BitVec n) (h : a ≠ BitVec.allOnes n) :
    ∃ i : Fin n, a.getLsbD i.val = false := by
  classical
  by_contra none
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  cases hb : a.getLsbD j
  · exact False.elim (none ⟨⟨j,hj⟩,hb⟩)
  · simp [hb,BitVec.getLsbD_allOnes,hj]

lemma coverage_sound {n : Nat} {target : Word} {r s : Fin n → Extended.Row}
    (good : ∀ i, Extended.bit (r i) target ≠ Extended.bit (s i) target)
    {ws : List Word} (h : coverage (ws.map (signature r s)) ≠ BitVec.allOnes n)
    (cap : Nat) : Impossible target cap ws := by
  obtain ⟨i,hi⟩ := missingBit _ h
  have agree := coverage_agree hi
  intro k hk run
  obtain ⟨w,hw,different⟩ := Extended.live_row_difference run (good i)
  have eq := agree (signature r s w) (List.mem_map_of_mem (List.mem_toFinset.mp hw))
  exact different (by simpa only [signature,ofRows_bit] using eq)

def check {n : Nat} (r s : Fin n → Extended.Row) (parent : List Word)
    (ws : List Word) (op : Choice) : Bool :=
  match ws with
  | [] => false
  | z::rest => z == Projection.choiceVal op &&
      (coverage (gate op.1 (read r s parent op.2.1) (read r s parent op.2.2) ::
        rest.map (read r s parent)) != BitVec.allOnes n)

lemma check_sound {n : Nat} {target : Word} {r s : Fin n → Extended.Row}
    (good : ∀ i, Extended.bit (r i) target ≠ Extended.bit (s i) target)
    {parent ws : List Word} {op : Choice} (checked : check r s parent ws op = true)
    (cap : Nat) : Impossible target cap ws := by
  cases ws with
  | nil => simp [check] at checked
  | cons z rest =>
    simp only [check,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at checked
    obtain ⟨rfl,h⟩ := checked
    apply coverage_sound good _ cap
    simpa only [List.map_cons,Projection.choiceVal,signature_bin,read_fun_eq] using h

lemma lookup_valid {α : Type} (f : Word → α) (cache : List (Word × α))
    (valid : ∀ p ∈ cache, p.2 = f p.1) (a : Word) :
    (lookup cache a).getD (f a) = f a := by
  induction cache with
  | nil => rfl
  | cons p ps ih =>
    simp only [lookup]
    cases h : p.1 == a with
    | false =>
      simpa only [h,Bool.false_eq_true,ite_false] using
        ih (fun q hq => valid q (List.mem_cons_of_mem p hq))
    | true =>
      have eq := beq_iff_eq.mp h
      simpa only [ite_true,Option.getD_some,←eq] using valid p List.mem_cons_self

def readCached {n : Nat} (r s : Fin n → Extended.Row)
    (cache : List (Word × Signals n)) (a : Word) : Signals n :=
  (lookup cache a).getD (signature r s a)

lemma readCached_eq {n : Nat} (r s : Fin n → Extended.Row)
    (cache : List (Word × Signals n))
    (valid : ∀ p ∈ cache, p.2 = signature r s p.1) :
    readCached r s cache = signature r s := funext (lookup_valid _ _ valid)

def checkCached {n : Nat} (r s : Fin n → Extended.Row)
    (cache : List (Word × Signals n)) (ws : List Word) (op : Choice) : Bool :=
  match ws with
  | [] => false
  | z::rest => z == Projection.choiceVal op &&
      (coverage (gate op.1 (readCached r s cache op.2.1) (readCached r s cache op.2.2) ::
        rest.map (readCached r s cache)) != BitVec.allOnes n)

lemma checkCached_sound {n : Nat} {target : Word} {r s : Fin n → Extended.Row}
    (good : ∀ i, Extended.bit (r i) target ≠ Extended.bit (s i) target)
    {cache : List (Word × Signals n)}
    (valid : ∀ p ∈ cache, p.2 = signature r s p.1)
    {ws : List Word} {op : Choice} (checked : checkCached r s cache ws op = true)
    (cap : Nat) : Impossible target cap ws := by
  cases ws with
  | nil => simp [checkCached] at checked
  | cons z rest =>
    simp only [checkCached,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at checked
    obtain ⟨rfl,h⟩ := checked
    apply coverage_sound good _ cap
    simpa only [List.map_cons,Projection.choiceVal,signature_bin,readCached_eq r s cache valid] using h

end PEqualNP.Outside.L_meta_2373_aux.Cert18.PackedCollision
