import PEqualNP.Defs

-- Adapted from the public proof by benoitrazet in PR 12184, under Apache-2.0.
-- Source: https://github.com/brilliant-hq/pequalnp-proofs/pull/12184
-- Source revision: 23cfcb8f020d4c1dfbf6b54a16284e8f1a932234.
-- Helper names are shortened reversibly; all certificate values and proof steps are preserved.

-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670.Projection
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def ZaU (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def Zcg (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem ZbE {u d} (h : ZaU u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem ZeD {u d} (h : ZaU u d) (a b : Sig) : bin d a b = bin (Zcg d) b a := by
  rcases ZbE h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,Zcg,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : ZaU u d) : ZaU u (Zcg d) ∧ Zcg (Zcg d)=d := by
  rcases ZbE h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [Zcg,ZaU]

def Zar (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), ZaU u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Zar u target k (insert (bin d a b) U)
theorem Zar.stop {u} {target : Sig} (hp : proper target) : Zar u target 0 {target} := ⟨rfl,hp⟩
theorem Zar.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : ZaU u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zar u target k (insert (bin d a b) U)) :
    Zar u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Zar.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Zar u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Zar.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : ZaU u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zar u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Zar.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Zar u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma Zff {u target k S} (h : Zar u target k S) : ∀ a ∈ S, proper a := by
  induction h using Zar.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma Zez {u target k S} (h : Zar u target k S) : S.card ≤ k+1 := by
  induction h using Zar.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma Zcw (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma Zcc (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem Zbc {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem Zk3 (a : Sig) : nrm false a = a := rfl
theorem ZnX (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,Zcw]
theorem ZeR {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem ZgN (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,Zcw,neg_neg']
theorem ZjI {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem ZjJ {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact ZjI h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem ZcN (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem Zk4 (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply Zbc
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,ZcN,ha,hb,Zcc,Zcw,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,Zcw,ZcN]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def ZbM (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def ZbF (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := ZbF w (nrm u v)

private lemma Zgs (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply Zbc <;> intro i <;>
    simp [Zcc,bit_zero,bit_one]

private lemma ZmK : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma Ze4 {w : List Sig} {a : Sig} (h : ZbF w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def ZcW (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, ZaU u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma ZgJ {u w a b} (d : Nat) (hd : ZaU u d) (ha : ZbF w a) (hb : ZbF w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    ZbF w (bin d a b) ∨ ZcW u w (bin d a b) := by
  have rz : ZbF w zero := Or.inr (fun h => h.1 rfl)
  have ro : ZbF w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := Zgs a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := Zgs b
  by_cases he : a=b
  · subst b
    left
    rcases ZbE hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases Ze4 ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases ZbE hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases ZbE hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases Ze4 hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases ZbE hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases ZbE hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem Zfk (a : Sig) : nrm true a ≠ one := by
  intro h
  have := ZnX a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem Zgn {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ ZcW u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := ZgJ (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [Zk3] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := Zk4 d a b
    unfold Repr
    rw [eq]
    exact ZgJ e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨Zfk a,Zfk b⟩)
theorem Zc6 {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := ZjJ hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma Zdf {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Zc6 (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem ZmO {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [ZgN]

def Zbk (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma Zl5 (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → Zbk g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (Zbk g=false ∧ ZcW u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      ZcW u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply Zbc
      intro i
      cases d <;> simp [ZcN,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (Zc6 (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (Zdf w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact Zgn d (Zdf w i) (Zdf w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [Zbk])
    left
    cases l with
    | nil => exact Zc6 (Or.inr (by simp [gv,ZmK]))
    | cons i l => exact ZmO (Zdf w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma Zgo {u target} {w : List Sig} {z : Sig} {k S c} (h : Zar u target k S)
    (hz : ZbF w z ∨ (c=1 ∧ ZcW u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Zar u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := Zff h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Zar u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Zar.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, Zbk g=false)
    (hp : proper target) (hout : target ∈ (ZbM gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !Zbk g) ∧ Zar u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Zar.stop hp,by simpa [ZbM] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := Zl5 u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : ZbF (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if Zbk g then 0 else 1)=1 ∧ ZcW u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := Zgo ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : Zbk g <;> simp [hn] at hl ⊢ <;> omega

private lemma ZgX (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma Zn6 (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [ZgX]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [ZcN]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [ZcN]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [Zcw,bit_zero]
    | cons a l => exact Zcw _ _

private lemma ZhJ (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (ZbM gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (ZbM gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,Zn6 i g w (hg g (by simp))]

abbrev Zaj (R : Type) := R → Bool

def inv {R} (a : Zaj R) : Zaj R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Zaj R) : Zaj R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Zbw {R} (d : Nat) (a b : Zaj R) : Zaj R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def ZaJ {R} (a : Zaj R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def ZaN {R} (a : Zaj R) : Nat := by
  classical exact if ZaJ a then 1 else 0

noncomputable def ZaZ {R} (xs : List (Zaj R)) : Nat := (xs.map ZaN).sum

def Zau {R} (u : Bool) (pool : List (Zaj R)) (v : Zaj R) : Prop :=
  v ∈ pool ∨ ZaJ v ∨ (u=true ∧ inv v ∈ pool)

def Zcz {R} (u : Bool) (pool xs : List (Zaj R)) := ∀ a ∈ xs, Zau u pool a

def Zav {R} (u : Bool) (roots : List (Zaj R)) : Nat → List (Zaj R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Zaj R)) (a b : Zaj R), Zav u roots p bank ∧ Zau u bank a ∧
      Zau u bank b ∧ c=combine op a b :: bank
theorem Zav.start {R u} {roots : List (Zaj R)} : Zav u roots 0 roots := rfl
theorem Zav.two {R u} {roots : List (Zaj R)} {p bank a b} (op : Bool) (h : Zav u roots p bank)
    (ha : Zau u bank a) (hb : Zau u bank b) : Zav u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Zav.ind {R u} {roots : List (Zaj R)} {motive : ∀ p bank, Zav u roots p bank → Prop}
    (start : motive 0 roots Zav.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Zav u roots p bank) (ha : Zau u bank a)
      (hb : Zau u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Zav.two op h ha hb))
    {p bank} (h : Zav u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Zaj R) : Nat → List (Zaj R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Zaj R) (rest : List (Zaj R)), ZaU u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (Zbw op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Zaj R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Zaj R} {s : Nat} {xs zs : List (Zaj R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Zaj R} {s : Nat} {a b : Zaj R} {rest : List (Zaj R)} (op : Nat) (hd : ZaU u op) (ka kb : Bool)
    (h : Run u goal s (Zbw op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Zaj R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : ZaU u op) (ka kb : Bool) (h : Run u goal s (Zbw op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem ZcP {R} (a : Zaj R) (xs) : ZaZ (a::xs)=ZaN a + ZaZ xs := by
  simp [ZaZ]

theorem Zgl {R} (a : Zaj R) (xs) (k : Bool) : ZaZ xs ≤ ZaZ (kept k a xs) := by
  cases k <;> simp [kept,ZcP]

theorem Zee {R} {a : Zaj R} (h : ZaJ a) : ZaJ (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Zaj R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem Zgu {R} (a : Zaj R) : ZaN (inv a)=ZaN a := by
  have : ZaJ (inv a) ↔ ZaJ a := ⟨fun h => inv_inv' a ▸ Zee h,Zee⟩
  by_cases h : ZaJ a
  · simp only [ZaN,if_pos h,if_pos (this.mpr h)]
  · simp only [ZaN,if_neg h,if_neg (fun x => h (this.mp x))]
theorem Zet {R u} {bank : List (Zaj R)} {a} (hu : u=true) (h : Zau u bank a) : Zau u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (Zee h))
  · exact Or.inl h
theorem Zhq {R} {a b : Zaj R} (op) (h : ZaJ a) (g : ZaJ b) :
    ZaJ (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem Zhu {R u} (op) {a b : Zaj R} {bank}
    (h : ZaJ a ∨ ZaJ b) (ha : Zau u bank a) (hb : Zau u bank b) :
    Zau u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem ZeZ {R u} {bank v} (w : Zaj R) (h : Zau u bank v) :
    Zau u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem Zjr {R u} (roots : List (Zaj R)) {p bank a b} (op) (hp : Zav u roots p bank)
    (ha : Zau u bank a) (hb : Zau u bank b) :
    ∃ q next, Zav u roots q next ∧ Zau u next (combine op a b) ∧
        (∀ v, Zau u bank v → Zau u next v) ∧
        q+ZaN a+ZaN b ≤ p+1+ZaN (combine op a b) := by
  classical
  by_cases c : ZaJ a ∨ ZaJ b
  · refine ⟨p,bank,hp,Zhu op c ha hb,fun _ h => h,?_⟩
    by_cases ca : ZaJ a <;> by_cases cb : ZaJ b
    · simp [ZaN,ca,cb,Zhq op ca cb]
    · simp [ZaN,ca,cb]
    · simp [ZaN,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬ZaJ a := fun h => c (Or.inl h)
    have cb : ¬ZaJ b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Zav.two op hp ha hb,Or.inl (by simp),fun _ h => ZeZ _ h,
      by simp [ZaN,ca,cb]⟩
theorem Zfm {R u} {bank : List (Zaj R)} {d a b} (hd : ZaU u d) (ha : Zau u bank a) (hb : Zau u bank b) :
    ∃ op x y, Zbw d a b=combine op x y ∧ Zau u bank x ∧ Zau u bank y ∧ ZaN x=ZaN a ∧ ZaN y=ZaN b := by
  rcases ZbE hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,Zet hu hb,rfl,Zgu b⟩
  · exact ⟨false,inv a,b,rfl,Zet hu ha,hb,Zgu a,rfl⟩
theorem ZiG {R u} (roots : List (Zaj R)) {p bank a b} (d) (hd : ZaU u d) (hp : Zav u roots p bank)
    (ha : Zau u bank a) (hb : Zau u bank b) :
    ∃ q next, Zav u roots q next ∧ Zau u next (Zbw d a b) ∧
        (∀ v, Zau u bank v → Zau u next v) ∧
        q+ZaN a+ZaN b ≤ p+1+ZaN (Zbw d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := Zfm hd ha hb
  rw [e,←cx,←cy]
  exact Zjr roots op hp hx hy

theorem Zgz {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Zaj R} (nc : ¬ZaJ goal) {s ws}
    (h : Run u goal s ws) (roots : List (Zaj R)) {p bank}
    (hp : Zav u roots p bank) (hs : Zcz u bank ws) :
    ∃ q next, Zav u roots q next ∧ Zau u next goal ∧ q+ZaZ ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [ZaZ,ZaN,nc]⟩
  | perm eq _ ih =>
    have hsub : Zcz u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [ZaZ,←(eq.map ZaN).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := ZiG roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : Zcz u T (Zbw op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases Zgz hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Zgz hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := Zgl a (kept kb b rest) ka
    have hlen' := Zgl b rest kb
    rw [ZcP] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [ZcP,ZcP]
    omega

def ZaA {R S : Type} (rows : S → R) (a : Zaj R) : Zaj S :=
  fun r => a (rows r)

theorem Zhw {R S : Type} (rows : S → R) (k : Bool) (a : Zaj R) (ws) :
    (kept k a ws).map (ZaA rows) =
    kept k (ZaA rows a) (ws.map (ZaA rows)) := by
  cases k <;> simp [kept]

theorem Ze5 {R S : Type} (rows : S → R) (d) (a b : Zaj R) :
    ZaA rows (Zbw d a b) = Zbw d (ZaA rows a) (ZaA rows b) := by
  unfold Zbw
  split_ifs <;> rfl
theorem ZhP {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (ZaA rows goal) s (ws.map (ZaA rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,Zhw,Ze5] at ih ⊢
    exact Run.two op hd ka kb ih

theorem Zd7 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬ZaJ (ZaA rows goal)) {roots : List (Zaj S)} {p bank L}
    (hp : Zav u roots p bank) (hs : Zcz u bank (ws.map (ZaA rows)))
    (hl : ∀ q bs, Zav u roots q bs → Zau u bs (ZaA rows goal) → L ≤ q) :
    L + ZaZ (ws.map (ZaA rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (ZhP rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Zaj Row := fun r => bit r a
def table (f : Zaj Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem Zb8 (f : Zaj Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem Zec (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact Zb8 (observe v) ⟨j,hj⟩

theorem Zhv (f : Zaj Row) : observe (table f) = f := by
  funext r
  exact Zb8 f r

theorem ZgP (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact Zcw _ _

theorem ZgO (d : Nat) (a b : Sig) :
    observe (bin d a b) = Zbw d (observe a) (observe b) := by
  funext r
  simp only [observe,Zcc,Zbw]
  split_ifs <;> rfl

theorem Zgy {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem ZdW {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem ZdH (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem ZeJ {u} {T : Sig} {k S} (h : Zar u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Zar.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := ZdW kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := ZdW ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [ZdH,ZdH,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,Zgy,Zgy,ZgO] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem Zli (f : Zaj Row) : table (inv f) = neg (table f) := by
  rw [←Zec (neg (table f)),ZgP,Zhv]

theorem Zi6 (d : Bool) (f g : Zaj Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply Zbc
  intro r
  rw [Zb8,ZcN,Zb8,Zb8]
  cases d <;> rfl

theorem Zd9 {u} {bank : List (Zaj Row)} {a} (h : Zau u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply Zc6
    cases b
    · exact Or.inl (Zbc fun i => (Zb8 _ i).trans (bit_zero i).symm)
    · exact Or.inr (Zbc fun i => (Zb8 _ i).trans (bit_one i).symm)
  · have := Zli a
    refine Or.inl ?_
    rw [←ZgN,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem Zhm {u} {roots : List (Zaj Row)} {p bank}
    (h : Zav u roots p bank) {T k S} (run : Zar u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Zar u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Zav.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,Zi6] at sub
    have rep := Zgn d (Zd9 ha) (Zd9 hb)
    obtain ⟨k',S',hk,run',sub'⟩ := Zgo (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def Za0 (a : Sig) : Bool := !(bit 0 a)
theorem ZgM {u} {w : List Sig} (h : w.all Za0=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact ZeR (by simpa [Za0] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem Zdv {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : Za0 T=true) (nR : roots.all Za0=true)
    (h : Zav u (roots.map observe) p bank) (hit : Zau u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Zar u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := Zd9 hit
  rw [Zec] at hm
  unfold Repr at hm
  rw [ZeR (by simpa [Za0] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := Zhm h (Zar.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,Zec]
  rw [e,ZgM nR] at hs
  exact hs

theorem ZeT {u T k S} (h : Zar u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Zar.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [Zcc,Zcc,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem Zc3 {u T k S} (h : Zar u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := ZeT h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def Zg2 : Sig := inputs.getD 0 zero ||| inputs.getD 6 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem Zjq : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem Zqz : ∀ r : Row, bit r Zg2 = (sample r 0 || sample r 6) := by decide +kernel
theorem Ze8 : proper graph := by unfold proper; decide +kernel
theorem Zqy : Zg2 ≠ zero := by decide +kernel
theorem Zen : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem Zn7 (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←Zen]
  rw [List.map_ofFn]
  rfl

theorem Zj5 (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((ZbM C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←ZgX,ZhJ _ _ _ (fun g hg => (h g hg).1),Zn7]
  rfl

theorem Zqw (gs : List Gate) (ws : List Sig) : ∃ l, ZbM gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [ZbM]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [ZbM,List.append_assoc] using hl⟩

theorem Zk8 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ u k S, k ≤ (if u then 14 else 15) ∧ Zar u graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  have goalEq : (ZbM C.gates inputs).getD C.output zero = graph := by
    apply Zbc
    intro r
    exact (Zj5 C legal C.output r).trans ((congrFun computes (sample r)).trans (Zjq r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, Zbk g=false) ∧ C.gates.countP (fun g => !Zbk g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, Zbk g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !Zbk g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !Zbk g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !Zbk g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := Zdf (u:=u) (ZbM C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph=false := by decide +kernel
  rw [ZeR pg] at out
  have targetIn := out.resolve_right (fun hn => hn Ze8)
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates inputs legal mono Ze8 targetIn
  have ns : inputs.all Za0=true := by decide +kernel
  rw [ZgM ns] at hs
  exact ⟨u,k,S,by omega,run,hs⟩
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem Zb4 (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := Zb8 _ _
theorem Zc1 (f : Row → Row) (a : Sig) :
    observe (rename f a) = ZaA f (observe a) := by funext r; exact Zb4 f a r
theorem ZfN (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply Zbc
  intro r
  simp only [Zb4,Zcc]

theorem ZjK (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [Zb4,Zb4,hr] at he
  exact he
theorem ZeV (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (Zb4 f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (Zb4 f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem ZiQ {u T k S} (h : Zar u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Zar u (rename f T) k (S.image (rename f)) := by
  have inj := ZjK f onto
  obtain ⟨fz,fo⟩ := ZeV f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Zar.ind with
  | stop hp => simpa using Zar.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,ZfN] at fresh ih ⊢
    exact Zar.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem Zg4 {u T k S} (h : Zar u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Zar.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [Zcc] at hp hn
      subst none
      rcases ZbE hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Zad (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Zav u (roots.map observe) p bank → Zau u bank (observe T) → L ≤ p
theorem ZmN {R u} {roots : List (Zaj R)} {p bank} (h : Zav false roots p bank) : Zav u roots p bank := by
  have up {bank : List (Zaj R)} {a} (h : Zau false bank a) : Zau u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Zav.ind with
  | start => exact Zav.start
  | two op h ha hb ih => exact Zav.two op ih (up ha) (up hb)
theorem ZjF {u roots T L} (h : Zad true roots T L) : Zad u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (ZmN hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Zax (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Zar u T k S

def Zdy (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem Zd6 {u roots T L} (hp : proper T) (nT : Za0 T=true) (nR : roots.all Za0=true)
    (essential : ∀ a ∈ roots, Zdy T roots a)
    (noRun : Zax u T L roots.toFinset) : Zad u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := Zdv hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact Zc3 run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem Zd8 {v : Sig} (hv : proper v) : ¬ZaJ (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply Zc6
    cases b
    · exact Or.inl (Zbc fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (Zbc fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : ZbF [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem ZiR {R} (a b : List (Zaj R)) : ZaZ (a++b) = ZaZ a + ZaZ b := by
  simp [ZaZ]
theorem Zhk {R} (xs : List (Zaj R)) (hc : ∀ x ∈ xs, ZaJ x) :
    ZaZ xs = xs.length := by
  induction xs with
  | nil => simp [ZaZ]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [ZcP,List.length_cons,ZaN,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem Zfh {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : Za0 T=true) (nR : roots.all Za0=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Zau u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Zdy T roots a)
    (constant : ∀ a ∈ singles, ZaJ (observe (rename r a)))
    (L : Nat) (prior : Zad u other G L) : Zad u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := Zdv pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact Zc3 run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := ZeJ run front nd fe
  have gc : ZaA r (observe T) = observe G := (Zc1 _ _).symm.trans (congrArg observe eq)
  have supp : Zcz u (other.map observe) ((front.map observe).map (ZaA r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←Zc1]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := Zd7 r run' (gc ▸ Zd8 pG) Zav.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ ZaZ ((front.map observe).map (ZaA r)) := by
    simp only [front,List.map_append,ZiR]
    let xs := (singles.toList.map observe).map (ZaA r)
    have only : ∀ v ∈ xs, ZaJ v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←Zc1]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := Zhk xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ ZaZ xs + _
    rw [sz]
    omega
  omega



def Zbz (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem ZfW {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem ZkN {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, ZaU u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (Zbz ws a b d ka kb).length ≤ cap →
      Zax u T (cap-1) (Zbz ws a b d ka kb).toFinset) :
    Zax u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Zar.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := Zff tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,ZfW (hn.erase _) b,
        ZfW hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [ZdH,ZdH,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := ZdW kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (Zbz ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,ZdW ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (Zbz ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := Zez tail
    have len : (Zbz ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem ZiE {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem ZiD {u T k S} (h : Zar u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (ZiE (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := ZeT h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := Zg4 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem Zhh {u T ws k} (h : Zar u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply ZiD h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Zau u (roots.map observe) (ZaA f (observe a))) ∧
    ¬ZaJ (ZaA f (observe T)) ∧
    ∀ p bank, Zav u (roots.map observe) p bank → Zau u bank (ZaA f (observe T)) → L ≤ p

def ZaE (d a : Sig) := a &&& d
def ZaH (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := ZaE d a
  m == zero || m == d || (pool.map (ZaE d)).any (fun v => v==m) ||
    (u && (let c := ZaE d (neg a); (pool.map (ZaE d)).any (fun v => v==c)))

theorem Zgk {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaE d a = ZaE d b) :
    ZaA f (observe a) = ZaA f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,ZaE,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem Zfj {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaE d a = zero) : ZaA f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,ZaE,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem ZfK {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaE d a = d) : ZaA f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,ZaE,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def Zcm (u : Bool) (f : Row → Row) (bank : List (Zaj Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Zau u bank (ZaA f (observe a))

theorem ZcF {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : Zcm u f bank pool)
    (check : ZaH u d pool a = true) : Zau u bank (ZaA f (observe a)) := by
  simp only [ZaH,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,Zfj dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,ZfK dom ho⟩)
  · exact Zgk dom he ▸ supplyB v hv
  · have h := Zet hu (Zgk dom he ▸ supplyB v hv)
    rw [ZgP] at h
    have e : inv (ZaA f (inv (observe a))) = ZaA f (observe a) := by
      funext r
      simp [inv,ZaA]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def ZaS (c : Choice) := bin c.1 c.2.1 c.2.2
def ZcR (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem Zis {u d} (h : ZcR u d=true) : ZaU u d := by
  simpa [ZcR,ZaU] using h
def Zcq (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  ZcR u c.1 && (ZaH u d pool c.2.1 && ZaH u d pool c.2.2)

theorem ZfM {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Zav u roots q bank) (hs : Zcm u f bank pool)
    (c : Choice) (valid : Zcq u d pool c = true) :
    ∃ next, Zav u roots (q+1) next ∧ Zcm u f next (ZaS c :: pool) := by
  simp only [Zcq,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := Zfm (Zis valid.1) (ZcF dom hs valid.2.1)
    (ZcF dom hs valid.2.2)
  refine ⟨_,Zav.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [ZaS,ZgO,Ze5,e]
    exact Or.inl (by simp)
  · exact ZeZ _ (hs _ hm)

def Zct (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if Zcq u d pool c then Zct u d (ZaS c::pool) cs else none

theorem Ze0 {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Zav u roots q bank) (hs : Zcm u f bank pool)
    (cs : List Choice) {result} (ok : Zct u d pool cs = some result) :
    ∃ next, Zav u roots (q+cs.length) next ∧ Zcm u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [Zct] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := ZfM dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def ZaK (d a : Sig) := ZaE d a == zero || ZaE d a == d
theorem ZeX {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (ZaK d) ≤ ZaZ ((ws.map observe).map (ZaA f)) := by
  classical
  induction ws with
  | nil => simp [ZaZ]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,ZcP]
    cases h : ZaK d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : ZaJ (ZaA f (observe a)) := by
        have hh : ZaE d a = zero ∨ ZaE d a = d := by simpa only [ZaK,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,Zfj dom hz⟩
        · exact ⟨true,ZfK dom ho⟩
      simpa [ZaN,hc,Nat.add_comm] using Nat.succ_le_succ ih

def Zdh (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (ZaK d)) && ws.all (ZaH u d pool)

theorem Zeb {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : Zct u d raw cs = some pool)
    (nd : ws.Nodup) (cut : Zdh u d L cap cs.length pool ws = true) :
    Zax u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := Ze0 dom (Zav.start (roots:=roots.map observe)) base cs built
  simp only [Zdh,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : Zcz u bank ((ws.map observe).map (ZaA f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact ZcF dom hs (List.all_eq_true.mp all a ha)
  have b := Zd7 f (ZeJ h ws nd rfl) nc hr coveredS lo
  have massLo := ZeX dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Zbg := Sig × Sig × Row
def Zd2 (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def ZfQ (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def ZeO (m : Zbg) (r : Row) : Row :=
  if bit r m.1 then Zd2 m.2.2 r else if bit r m.2.1 then Zd2 (ZfQ m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def Zde (m : Zbg) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (ZfQ m.2.2).val) a)

theorem ZkK (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (Zd2 d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [Zd2,h,r.isLt]

theorem ZlX (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem Zni (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact ZlX _ _ _

theorem ZlW (r : Row) (m : Zbg) (a : Sig) : bit r (Zde m a) = bit (ZeO m r) a := by
  simp only [Zde,Zni,ZkK,ZeO]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def Zbb (ms : List Zbg) (r : Row) := ms.foldl (fun j m => ZeO m j) r
def ZaI (ms : List Zbg) (a : Sig) := ms.foldr Zde a
theorem Zc9 (ms : List Zbg) (a : Sig) (r : Row) :
    bit r (ZaI ms a) = bit (Zbb ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (ZlW r m _).trans (ih _)
theorem Zck (ms : List Zbg) (a : Sig) : ZaI ms a = rename (Zbb ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (Zc9 ms a ⟨j,hj⟩).trans (Zb4 _ _ ⟨j,hj⟩).symm

def ZeF (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem ZiH {u roots w} (ok : ZeF roots w = true) :
    Zau u (roots.map observe) (observe w) := by
  simp only [ZeF,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def Zca (ms : List Zbg) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  ZaI ms T == G && raw.all (fun a => ZeF base (ZaI ms a))

theorem Zeh {u ms raw T base G} (ok : Zca ms raw T base G = true) :
    rename (Zbb ms) T = G ∧
    ∀ a ∈ raw, Zau u (base.map observe) (observe (rename (Zbb ms) a)) := by
  simp only [Zca,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,Zck] at ok
  exact ⟨ok.1,fun a ha => ZiH (ok.2 a ha)⟩

theorem Zk0 {u ms raw T base G L} (ok : Zca ms raw T base G = true)
    (pT : proper T) (nT : Za0 T=true) (nR : raw.all Za0=true) (pG : proper G)
    (hL : Zad u base G L) : Zad u raw T L := by
  obtain ⟨eq,supp⟩ := Zeh ok
  simpa using Zfh pT nT nR pG (Zbb ms) eq supp ∅ (by simp) (by simp) L hL

theorem ZhB {u ms raw T base G L d} (ok : Zca ms raw T base G = true)
    (all : ZaI ms d = one) (properG : proper G) (hL : Zad u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := Zeh ok
  have obs : ZaA (Zbb ms) (observe T) = observe G :=
    (Zc1 _ _).symm.trans (congrArg observe eq)
  refine ⟨Zbb ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←Zc9,all,bit_one]
  · intro a ha
    rw [←Zc1]
    exact supp a ha
  · rw [obs]
    exact Zd8 properG
  · rw [obs]
    exact hL

def ZdS (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem Ze2 {T roots a rs} (ok : ZdS T roots a rs = true) : Zdy T roots a := by
  simp only [ZdS,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def Zbm (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  Za0 T && raw.all Za0 && xs.all (fun a => ZdS T raw a.1 a.2)
theorem ZcG {T raw xs} (ok : Zbm T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Zdy T raw a := by
  simp only [Zbm,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact Ze2 (List.all_eq_true.mp ok.2 _ hm)

theorem Zbl {T raw xs} (ok : Zbm T raw xs = true) :
    Za0 T=true ∧ raw.all Za0=true := by
  simp only [Zbm,Bool.and_eq_true] at ok
  exact ok.1
theorem Zfg {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : Zbm T raw xs = true) :
    Zad u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := Zdv properT (Zbl ok).1 (Zbl ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := ZcG ok a ha
    exact Zc3 run raw a sub r s hd iso
  have bound := Zez run
  omega

def Zev (ms : List Zbg) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  Zca ms raw T base G && Zbm T raw xs &&
    xs.all (fun a => ZaI ms a.1 == zero || ZaI ms a.1 == one)

theorem ZnB {u ms T raw base G xs L} (ok : Zev ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Zad u base G L) :
    Zad u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [Zev,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := Zeh ok.1.1
  apply Zfh properT (Zbl ok.1.2).1 (Zbl ok.1.2).2 properG _ eq supp _ (ZcG ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,Zck] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def ZbA (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (ZbA m).map Prod.snd
def ZdR (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def Zae (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [ZdR (m/512-1)]
def Zdm (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def Zaa (m : Nat) : Sig :=
  let x := Zdm m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def ZpU : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def ZpV : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def ZpW : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def Zce (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((ZpU (fixed &&& 7)*ZpV ((fixed >>> 3) &&& 7)*ZpW ((fixed >>> 6) &&& 7)) <<< o)
def ZeN (z o : Nat) : List Zbg :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Zbg :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def Ze9 (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (ZbA mask).map fun (i,a) =>
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def ZcJ (m hints : Nat) : List (Sig × Row × Row) :=
  (ZbA m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def Za1 (T : Sig) := T != zero && T != one
theorem Zbr (T : Sig) (h : Za1 T = true) : proper T := by
  simpa only [Za1,proper,Bool.and_eq_true,bne_iff_ne] using h
def Zfl (m hints L : Nat) :=
  let xs := ZcJ m hints
  Za1 (Zaa m) && Zbm (Zaa m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem ZqC {u m hints L} (h : Zfl m hints L = true) :
    Zad u (vars m) (Zaa m) L := by
  simp only [Zfl,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (Zfg (Zbr _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ZaO := Nat × Nat × Nat × Nat × Nat
def ZeM (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def Zb9 (m : Nat) : Sig := Zaa m
def Zcd (m : Nat) (c : ZaO) : Nat := m % 512+512*(c.1/512)
def ZcS (m : Nat) (c : ZaO) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := ZeN z o
  let raw := Zcd m c
  let free := ZeM raw (z % 512) o
  let G := ZaI ms (Zb9 m)
  let xs := Ze9 (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  Za1 G && Zca ms (Zae raw) (Zb9 m) (Zae free) G &&
    (ZaI ms (Zce z o)==one) &&
    (if q=0 then Zbm G (Zae free) xs && decide (L ≤ count-1)
     else Za1 (Zaa q) &&
       Zev (ZeN (ZeM free q 0) 0) G (Zae free) (Zae q) (Zaa q) xs &&
       decide (L ≤ prior q+count))

theorem Zdz {u} {m : Nat} (c : ZaO) (prior : Nat → Nat)
    (valid : ∀ q, Zad u (Zae q) (Zaa q) (prior q))
    (ok : ZcS m c prior = true) : Slice u (Zae (Zcd m c)) (Zb9 m) (Zce c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := ZeN z o
  let raw := Zcd m (z,o,q,s,L)
  let free := ZeM raw (z % 512) o
  let G := ZaI ms (Zb9 m)
  let xs := Ze9 (z/512+80) s
  change (((Za1 G && Zca ms (Zae raw) (Zb9 m) (Zae free) G) &&
    (ZaI ms (Zce z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply ZhB ok.1.1.2 ok.1.2 (Zbr _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [ZcS,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (Zfg (Zbr _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [ZcS,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ZnB hh.1.2 (Zbr _ ok.1.1.1) (Zbr _ hh.1.1) (valid q) p bank hr ha)

def ZeL (old rep : Nat) (swaps : List Nat) :=
  (Za1 (Zaa old) && Za0 (Zaa old) && (Zae old).all Za0) && Za1 (Zaa rep) &&
    Zca (swaps.map swapRows) (Zae old) (Zaa old) (Zae rep) (Zaa rep)
theorem ZlZ {u old rep L swaps} (ok : ZeL old rep swaps = true)
    (h : Zad u (Zae rep) (Zaa rep) L) : Zad u (Zae old) (Zaa old) L := by
  simp only [ZeL,Bool.and_eq_true] at ok
  exact Zk0 ok.2 (Zbr _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (Zbr _ ok.1.2) h

def Zam (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem Zaf {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Zad u (Zae e.1) (Zaa e.1) e.2) (q : Nat) :
    Zad u (Zae q) (Zaa q) (Zam entries q) := by
  unfold Zam
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev ZaP := Sig × Nat × Nat × List Sig
def ZaP.domain (c : ZaP) : Sig := c.1
def ZaP.bound (c : ZaP) : Nat := c.2.1
def ZaP.ZaG (c : ZaP) : Nat := c.2.2.1
def ZaP.wires (c : ZaP) : List Sig := c.2.2.2

def Zb7 (u : Bool) (raw : List Sig) (T : Sig) (c : ZaP) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Zaj Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬ZaJ (ZaA f (observe T)) ∧
    (∀ q ws, Zav u (roots.map observe) q ws → Zau u ws (ZaA f (observe T)) → c.bound ≤ q) ∧
    Zav u (roots.map observe) c.ZaG bank ∧ Zcm u f bank c.wires ∧ True

theorem Zit {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : Zct u d raw cs = some ws) : Zb7 u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := Ze0 dom (Zav.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [ZaP.ZaG] using hr,hs,trivial⟩

theorem ZhD {u raw T c} (valid : Zb7 u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (ZaG : Bool)
    (known : ∀ a ∈ rest, ZaH u c.domain c.wires a = true)
    (buy : if ZaG then Zcq u c.domain c.wires choice = true
       else ZaH u c.domain c.wires (ZaS choice) = true)
    (bound : k+c.ZaG+ZaG.toNat <
      c.bound+(ZaS choice :: rest).countP (ZaK c.domain))
    (nd : (ZaS choice :: rest).Nodup) :
    Zax u T k (ZaS choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := ZaS choice::rest
  have done (n : Nat) (out : List (Zaj Row)) (reach : Zav u (roots.map observe) n out)
      (zs : Zcm u f out (ZaS choice::rest)) (le : n = c.ZaG+ZaG.toNat) : False := by
    have covered : Zcz u out ((ws.map observe).map (ZaA f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := Zd7 f (ZeJ run ws nd rfl) nc reach covered lo
    have cm := ZeX dom ws
    change k+c.ZaG+ZaG.toNat < c.bound+ws.countP (ZaK c.domain) at bound
    omega
  cases ZaG with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact ZcF dom hs buy
    · exact ZcF dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := ZfM dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Zau u out (ZaA f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact ZcF dom point (known _ hm)

def Zb2 (u : Bool) (c : ZaP) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := ZaS op
  let extra := !(ZaH u c.domain c.wires z)
  ((k+c.ZaG+extra.toNat < c.bound+(z::rest).countP (ZaK c.domain)) &&
    rest.all (ZaH u c.domain c.wires)) && (!extra || Zcq u c.domain c.wires op)

theorem Zg5 {u raw T c} (valid : Zb7 u raw T c) {k rest op}
    (nd : (ZaS op::rest).Nodup) (cut : Zb2 u c k rest op = true) :
    Zax u T k (ZaS op::rest).toFinset := by
  let extra := !(ZaH u c.domain c.wires (ZaS op))
  apply ZhD valid k rest op extra _ _ _ nd
  · simp only [Zb2,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [Zb2,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : ZaH u c.domain c.wires (ZaS op) <;> simp_all [extra]
  · simp only [Zb2,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def Zei (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option ZaP :=
  (Zct u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem Zg7 {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : Zei u raw cs d L = some c) : Zb7 u raw T c := by
  unfold Zei at h
  cases he : Zct u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact Zit slice cs he


abbrev Bits := BitVec 768
abbrev ZdU := Bits × Bits
abbrev Zac := Sig × ZdU

def ZbC {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ZbU {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ZbC r v).getLsbD i.val = bit (r i) v := by
  simp only [ZbC,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def ZbN (r s : Fin 768 → Row) (a : Sig) : ZdU := (ZbC r a,ZbC s a)
def Zc4 (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem ZmL {T r s} (h : Zc4 T r s) : Sep T 768 r s (ZbN r s) := by
  exact ⟨h,fun a i => ⟨ZbU _ _ _,ZbU _ _ _⟩⟩
def Zbf (r s : Fin 768 → Row) (x : Zac) := x.2 = ZbN r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def ZaY (d : Nat) (x y : Zac) : Zac := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ZjH {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ZbC r (bin d a b) = bv d (ZbC r a) (ZbC r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ZbU r (bin d a b) ⟨j,hj⟩
  rw [Zcc,←ZbU r a ⟨j,hj⟩,←ZbU r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem Ze6 {r s x y} (d) (hx : Zbf r s x) (hy : Zbf r s y) :
    Zbf r s (ZaY d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [Zbf,ZaY,ZbN,ZjH,hx,hy]

def Za6 : Zac := (zero,0,0)
theorem Zg9 (r s) : Zbf r s Za6 := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ZbC r zero).getLsbD j
    rw [show (ZbC r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ZbU _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ZbC s zero).getLsbD j
    rw [show (ZbC s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ZbU _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem Ze7 {r s ws} (all : ∀ v ∈ ws, Zbf r s v) (i : Nat) :
    Zbf r s (List.getD ws i Za6) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact Zg9 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def Zc5 (n : Nat) (bits : Nat) (ws : List Zac) : List Zac :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) Za6
    let b := ws.getD ((bits >>> 4) &&& 15) Za6
    Zc5 k (bits >>> 10) (ws++[ZaY ((bits >>> 8) &&& 3) a b])
theorem Zhb (n bits) (ws) (r s) (base : ∀ v ∈ ws, Zbf r s v) :
    ∀ v ∈ Zc5 n bits ws, Zbf r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact Ze6 _ (Ze7 base _) (Ze7 base _)

def Zbj (Zbd : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (Zbd j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem Ziu : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem Ziv : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem Ziw : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem Zix : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem Ziy : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem Ziz : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem ZiA : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem ZiB : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem ZiC : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem Zed : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact Ziu r
  · exact Ziv r
  · exact Ziw r
  · exact Zix r
  · exact Ziy r
  · exact Ziz r
  · exact ZiA r
  · exact ZiB r
  · exact ZiC r
theorem Zes (Zbd : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (Zbj Zbd i) (inputs.getD j.val zero) = (Zbd j.val).getLsbD i.val := by
  rw [Zed]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (Zbd h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def ZdO (m : Nat) (p q : Nat → Bits) : List Zac :=
  (ZbA m).map (fun (j,a) => (a,p j,q j))
theorem Ze1 {m j a} (h : (j,a) ∈ ZbA m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem ZhO (m) (p q : Nat → Bits) :
    ∀ a ∈ ZdO m p q, Zbf (Zbj p) (Zbj q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := Ze1 hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (Zes p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ZbU _ _ ⟨i,hi⟩).symm
  · exact (Zes q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ZbU _ _ ⟨i,hi⟩).symm

def ZeI (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem Zjn (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (Zbj v i) (Zdm m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [Zdm,hh] using Zes v i j
  · simp [Zdm,hh,bit_zero]
theorem ZhI (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (Zbj v i) (Zaa m) = (ZeI m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (Zdm m j).getLsbD (Zbj v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := Zjn m v i ⟨j,hj⟩
  simp only [bit,Zaa,ZeI,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def Zbi (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def ZaT (d : Bool) (v : List Zac) : Cov :=
  v.foldr (fun a c => Zbi (column d a.2) c) (0,0,0)

def ZbX (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def ZcV (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem Znj (c : Cov) (a : Bits) : ZbX (Zbi a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ZbX,Zbi,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem Znk (c : Cov) (a b : Bits) : ZcV (Zbi a (Zbi b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ZcV,Zbi,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem ZlV (c : Cov) (a b : Bits) : Zbi a (Zbi b c)=Zbi b (Zbi a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Zbi,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [Zbi,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem Zgv (d : Bool) {l r : List Zac} (h : l.Perm r) : ZaT d l=ZaT d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (Zbi (column d a.2)) ih
  | swap a b t => exact ZlV _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem Zl0 (d : Bool) (v : List Zac) {r s} (good : ∀ a ∈ v, Zbf r s a) :
    (ZaT d v).1 = covered d (ZbN r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (ZaT d v).1) = column d (ZbN r s a.1) ||| _
    rw [show a.2=ZbN r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def Zbu (ws : List Zac) (a : Zac) (keep : Bool) :=
  if keep then ws else ws.erase a
def ZaR (ws : List Zac) (a b : Zac) (ka kb : Bool) :=
  Zbu (Zbu ws a ka) b kb

theorem Zef {ws : List Zac} (a : Zac) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem ZfU {ws : List Zac} (d : Bool) (a : Zac) (ha : a ∈ ws) (keep : Bool) :
    (ZaT d (Zbu ws a keep)).1 =
      (if keep then (ZaT d ws).1 else ZbX (ZaT d ws) (column d a.2)) := by
  cases keep
  · change (ZaT d (ws.erase a)).1 = ZbX (ZaT d ws) _
    rw [Zgv d (Zef a ha)]
    exact (Znj _ _).symm
  · rfl
theorem ZiF {ws : List Zac} (a b : Zac) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (Zef a ha).trans (List.Perm.cons _ (Zef b hm))

theorem ZkM {ws : List Zac} (d : Bool) (a b : Zac) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (ZaT d (ZaR ws a b ka kb)).1 =
      (if ka then (if kb then (ZaT d ws).1 else ZbX (ZaT d ws) (column d b.2))
       else if kb then ZbX (ZaT d ws) (column d a.2)
       else ZcV (ZaT d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (ZaT d ((ws.erase a).erase b)).1 = ZcV (ZaT d ws) _ _
    rw [Zgv d (ZiF a b ha hb ne)]
    exact (Znk _ _ _).symm
  · exact ZfU d a ha false
  · exact ZfU d b hb false
  · rfl

def ZcQ (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem ZeY {xs ys} (h : ZcQ xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [ZcQ,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def ZbB (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def Zdk (xs : List Sig) := xs.foldl (fun v x => v+ZbB x) 0

def ZcI (u : Bool) (pools : List ZaP) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := ZaS op::rest
  (links (Zdk ws)).any (ZcQ ws) || pools.any (fun p => Zb2 u p k rest op)

theorem Zg8 {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, Zb7 u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Zax u T k (List.toFinset xs))
    (nd : (ZaS op :: rest).Nodup)
    (h : ZcI u pools links k rest op = true) :
    Zax u T k (ZaS op :: rest).toFinset := by
  simp only [ZcI,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [ZeY ok]
    exact lValid _ _ hx
  · exact Zg5 (pValid _ hp) nd ok

abbrev ZgI := Cov × Bool
def Zdl (u : Bool) (ws : List Zac) : ZgI := (ZaT (!u) ws,u)
def Zcy (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else ZbX v b) else if kb then ZbX v a else ZcV v a b

theorem Zek (ws : List Zac) (a : Zac) (k : Bool) : (Zbu ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem Zmf (ws : List Zac) (a b : Zac) (ka kb : Bool) :
    (ZaR ws a b ka kb).Sublist ws := (Zek _ _ _).trans (Zek _ _ _)
theorem Zmg (ws : List Zac) (a b : Zac) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (ZaR ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [ZaR,Zbu,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def Zbn (op : Nat) (a b : Zac) : Choice := (op,a.1,b.1)

abbrev ZaW := Nat × Nat × List Zac × ZgI × List ZaP × (Nat → List (List Sig))
def Zcb (c : ZaW) (op : Nat) (a b z : Zac) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := Zcy cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !Za1 z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (ZaR ws a b ka kb).map Prod.fst
      ZcI cov.2 pools links (cap-1) rest (Zbn op a b)

def ZeA (ws : List Zac) (op : Nat) (a b : Zac) (ka kb : Bool) :=
  (ZaY op a b).1 :: (ZaR ws a b ka kb).map Prod.fst
theorem Zhi {u raw T r s ws pools links cap a b op ka kb}
    (pairs : Zc4 T r s) (faith : ∀ w ∈ ws, Zbf r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, Zb7 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Zax u T (cap-1) (List.toFinset xs))
    (pro : proper (ZaY op a b).1) (fresh : (ZaY op a b).1 ∉ ws.map Prod.fst)
    (test : Zcb (cap,ws.length,ws,Zdl u ws,pools,links) op a b (ZaY op a b) ka kb = true) :
    Zax u T (cap-1) (ZeA ws op a b ka kb).toFinset := by
  let z := ZaY op a b
  let rest := ZaR ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := Zmf _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : Za1 z.1 = true := by simpa [Za1,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,Zmg _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := Zez h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold Zcb at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := Zhh h (ZmL pairs)
  let d := !u
  have g : (ZaT d rest).1 = covered d (ZbN r s) (rest.map Prod.fst) :=
    Zl0 _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (ZaT d rest).1 = Zcy (ZaT d ws) (column d a.2) (column d b.2) ka kb :=
    ZkM d a b ha hb ne ka kb
  have hf := Ze6 op (faith _ ha) (faith _ hb)
  change column d (ZbN r s z.1) ||| covered d (ZbN r s) (rest.map Prod.fst) = _ at sep
  change z.2 = ZbN r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((Zcy (ZaT (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (Zcy (ZaT (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !Za1 z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact Zg8 (op:=Zbn op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def Zcv (ctx : ZaW) (a b : Zac) (op : Nat) :=
  let z := ZaY op a b
  let attempt := Zcb ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def ZcB (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem Zgm {u d} (h : ZaU u d) : d ∈ ZcB u := by
  rcases ZbE h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [ZcB]
  · cases u <;> simp [ZcB]
  · simp [ZcB]
  · simp [ZcB]
def ZeP (ctx : ZaW) (a : Zac) (bs : List Zac) :=
    bs.all (fun b => (ZcB ctx.2.2.2.1.2).all (Zcv ctx a b))
def ZbY (ctx : ZaW) : List Zac → Bool
  | [] => true
  | a::bs => ZeP ctx a bs && ZbY ctx bs

theorem Zjm {ctx ws} (h : ZbY ctx ws=true) {a b : Zac} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, ZaU ctx.2.2.2.1.2 d → Zcv ctx a b d=true) ∨
      (∀ d, ZaU ctx.2.2.2.1.2 d → Zcv ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [ZbY,Bool.and_eq_true,ZeP,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (Zgm hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (Zgm hd)
      · exact ih h.2 haTail hbTail

theorem Zi7 {ctx a b d} (h : Zcv ctx a b d = true) (ka kb : Bool) :
    Zcb ctx d a b (ZaY d a b) ka kb = true := by
  simp only [Zcv,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem Zgx {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem ZfL {v : List Zac} (nd : v.Nodup) (a w : Zac) (k : Bool) :
    w ∈ Zbu v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [Zbu,nd.mem_erase_iff,and_comm]

theorem Zfa {ws : List Zac} (nd : (ws.map Prod.fst).Nodup) {a b : Zac}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem Zfo {ws : List Zac} (nd : (ws.map Prod.fst).Nodup) {a b : Zac}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (ZaR ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (Zek ws a ka)
  simp only [ZaR,List.mem_map,ZfL wn,ZfL dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (Zfa nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (Zfa nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem ZhH {ws : List Zac} (nd : (ws.map Prod.fst).Nodup) {a b : Zac}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (ZeA ws d a b ka kb).toFinset =
      (Zbz (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [ZeA,Zbz,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    Zfo nd ha hb,Zgx,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,ZaY]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem Zhr {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : ZaU u d) (ka kb : Bool) :
    (Zbz v a b d ka kb).toFinset = (Zbz v b a (Zcg d) kb ka).toFinset := by
  ext x
  simp only [Zbz,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    Zgx,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,ZeD hd a b]
  tauto

theorem ZjG {u raw T r s ws pools links cap}
    (pairs : Zc4 T r s) (faith : ∀ w ∈ ws, Zbf r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, Zb7 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Zax u T (cap-1) (List.toFinset xs))
    (checks : ZbY (cap,ws.length,ws,Zdl u ws,pools,links) ws = true) :
    Zax u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply ZkN nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Zac) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : Zcv (cap,ws.length,ws,Zdl u ws,pools,links) a b d = true) :
      Zax u T (cap-1) (Zbz (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←ZhH nd aa bb ne']
    exact Zhi pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (Zi7 test ka kb)
  rcases Zjm checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [Zhr _ nd _ _ d hd]
    exact one b a (Zcg d) hbW haW (Ne.symm ne) kb ka (ZeD hd a.1 b.1 ▸ pro)
      (ZeD hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem ZhE (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← Zen]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (Zed i r).symm.trans ((h _ hm).trans (Zed i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def Zej (p q : List Zbg) := inputs.all (fun a => ZaI p (ZaI q a) == a)
theorem Zfd {p q} (h : Zej p q = true) (r : Row) :
    Zbb q (Zbb p r) = r := by
  apply ZhE
  intro a ha
  rw [←Zc9,←Zc9]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def Zdj (T : Sig) (p : List Zbg) :=
  (ZaI p T == T) && Zej p p.reverse && Zej p.reverse p
theorem Zhg {u T n} {ws : List Sig} (hi : Zax u T n ws.toFinset)
    (p : List Zbg) (ok : Zdj T p = true) : Zax u T n (ws.map (ZaI p.reverse)).toFinset := by
  simp only [Zdj,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (Zbb p) := fun r => ⟨Zbb p.reverse r,Zfd ok.2 r⟩
  intro k hk h
  have run := ZiQ h (Zbb p) onto
  have goal : rename (Zbb p) T = T := (Zck p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (Zbb p) (ZaI p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [Zb4,Zc9,Zfd ok.1.2]
  have back : (ws.map (ZaI p.reverse)).toFinset.image (rename (Zbb p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Zag := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def Za3 : Zag := (0,0,0,0,0,0,0,fun _ => 0)
def Zbh (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def ZaB (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := Zbh data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := Zbh data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Zai := Nat × Nat × (Nat → Bits × Bits) × List ZaO × List (List Nat) ×
  (Nat → Zag) × (Nat → Nat → Option (Nat × Nat))
def Zai.mask (g : Zai) : Nat := g.1
def Zai.mode (g : Zai) : Bool := !(g.1.testBit 10)
def Zai.cap (g : Zai) : Nat := g.2.1
def Zai.Zbt (g : Zai) : Nat → Bits × Bits := g.2.2.1
def Zai.Zbd (g : Zai) : List ZaO := g.2.2.2.1
def Zai.ZcA (g : Zai) : List (List Nat) := g.2.2.2.2.1
def Zai.levels (g : Zai) : Nat → Zag := g.2.2.2.2.2.1
def Zai.index (g : Zai) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def Zcf (g : Zai) :=
  let ws := ZdO g.mask (fun j => (g.Zbt j).1) (fun j => (g.Zbt j).2)
  ws
theorem Zhp (g : Zai) : ∀ a ∈ Zcf g,
    Zbf (Zbj fun j => (g.Zbt j).1) (Zbj fun j => (g.Zbt j).2) a := by
  exact ZhO g.mask (fun j => (g.Zbt j).1) (fun j => (g.Zbt j).2)

def ZaQ (g : Zai) := Zb9 g.mask
def Zc2 (m : Nat) (v : Nat → Bits) :=
  ZeI m v
theorem ZkL (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (Zbj v i) (Zb9 m) = (Zc2 m v).getLsbD i.val := by
  exact ZhI m v i
theorem Zfb {m : Nat} {p q : Nat → Bits}
    (hp : Zc2 m p = BitVec.allOnes 768) (hq : Zc2 m q = 0) :
    Zc4 (Zb9 m) (Zbj p) (Zbj q) := by
  intro i
  simp only [ZkL,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def ZbH {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::ZbH (bits >>> 1) ws else ZbH (bits >>> 1) ws
theorem Zho {α : Type} (bits : Nat) (ws : List α) : (ZbH bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold ZbH
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def Zdt (_g : Zai) (depth : Nat) := depth
def ZdP (g : Zai) (k i : Nat) : Nat × List Zac × List Zac :=
  let raw := Zcf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*Zdt g depth
  let width := len+raw.length+depth
  let recp := Zbh data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := Zc5 depth ops raw
  (ops,bank,ZbH (recp >>> len) bank)

def ZfY (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def Zfc (bank : List Zac) (ops ZaG : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := Zfc bank (ops >>> 10) (ZaG >>> 1) n
    if ZaG &&& 1 == 0 then more else
      (ZfY ops 8 2,(bank.getD (ops &&& 15) Za6).1,
        (bank.getD (ZfY ops 4 4) Za6).1) :: more

def buildRule (g : Zai) (ops d : Nat) (bank : List Zac) (idx ZaG : Nat) : Option ZaP :=
  (g.Zbd[idx]?).bind fun ci =>
    Zei g.mode (Zae (Zcd g.mask ci)) (Zfc bank ops ZaG d) (Zce ci.1 ci.2.1) ci.2.2.2.2

theorem Zha (g : Zai)
    (Zbd : ∀ ci ∈ g.Zbd, Slice g.mode (Zae (Zcd g.mask ci)) (ZaQ g) (Zce ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank ZaG c} (h : buildRule g ops depth bank i ZaG = some c) :
    Zb7 g.mode (vars g.mask) (ZaQ g) c := by
  unfold buildRule at h
  cases e : g.Zbd[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply Zg7 _ h
    exact Zbd ci (List.mem_of_getElem? e)

def ZeG (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := Zbh data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: ZeG data w v n (pos+w+v)

def Zbs (g : Zai) (k i : Nat) := (ZdP g k i).2.2.map Prod.fst
def Zco (g : Zai) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.ZcA[pair.2]?).map fun perm => (Zbs g k pair.1).map (ZaI (perm.map swapRows).reverse)

theorem Zhc (g : Zai) (k : Nat)
    (names : ∀ x ∈ g.ZcA, Zdj (ZaQ g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Zax g.mode (ZaQ g) k (Zbs g k i).toFinset)
    {pair out} (h : Zco g k pair = some out) :
    Zax g.mode (ZaQ g) k out.toFinset := by
  unfold Zco at h
  split at h
  · contradiction
  next valid =>
    cases e : g.ZcA[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact Zhg (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def ZcH (g : Zai) (k i : Nat) :=
  let raw := Zcf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := ZdP g k i
  let values := ws.map Prod.fst
  let start := num*(10*Zdt g depth+raw.length+depth)
  let pos := start+num*offw+Zbh data (start+i*offw) offw
  let nr := Zbh data pos 5
  let nl := Zbh data (pos+5) lw
  let st := pos+5+lw
  let rules := (ZeG data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zco g (k-1))).toList
  decide values.Nodup && !(values.contains (ZaQ g)) &&
    (if k=0 then true else ZbY (k,ws.length,ws,Zdl g.mode ws,rules,ls) ws)

theorem ZeU (g : Zai) (k i : Nat)
    (Zbt : Zc4 (ZaQ g) (Zbj fun j => (g.Zbt j).1) (Zbj fun j => (g.Zbt j).2))
    (Zbd : ∀ ci ∈ g.Zbd, Slice g.mode (Zae (Zcd g.mask ci)) (ZaQ g) (Zce ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.ZcA, Zdj (ZaQ g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Zax g.mode (ZaQ g) (k-1) (Zbs g (k-1) j).toFinset)
    (checked : ZcH g k i = true) : Zax g.mode (ZaQ g) k (Zbs g k i).toFinset := by
  simp only [ZcH,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : ZaQ g ∉ Zbs g k i := by simpa [Zbs] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (Zbs g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply ZjG (raw:=vars g.mask) Zbt _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply Zhb _ _ _ _ _ (Zhp g) v
    exact (Zho _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact Zha g Zbd h
  · intro tag xs hx
    have e : ((g.index k tag).bind (Zco g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact Zhc g _ names (prior (by omega)) h


def block (g : Zai) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => ZcH g k (start+n) && block g k start n
theorem Zgt {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    ZcH g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem ZaC {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def ZaV (g : Zai) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def Zay (g : Zai) (prior : Nat → Nat) :=
  (Zc2 g.mask (fun j => (g.Zbt j).1) == BitVec.allOnes 768) &&
  (Zc2 g.mask (fun j => (g.Zbt j).2) == 0) &&
  g.Zbd.all (fun c => ZcS g.mask c prior) &&
  g.ZcA.all (fun p => Zdj (ZaQ g) (p.map swapRows))

theorem Zjs (g : Zai) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Zad g.mode (Zae q) (Zaa q) (prior q))
    (geometry : Zay g prior = true) (rows : ZaV g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Zax g.mode (ZaQ g) k (Zbs g k i).toFinset := by
  simp only [Zay,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply ZeU g 0 i (Zfb geometry.1.1.1 geometry.1.1.2)
      (fun x hx => Zdz _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact Zgt (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply ZeU g _ i (Zfb geometry.1.1.1 geometry.1.1.2)
      (fun x hx => Zdz _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact Zgt (rows _ hk) i (by omega) (by omega)

def Zds (g : Zai) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && ZcQ (Zbs g k i) ws
theorem ZfO {g top prior k i ws} (low : ∀ q, Zad g.mode (Zae q) (Zaa q) (prior q))
    (geom : Zay g prior = true) (blocks : ZaV g top) (le : k ≤ top)
    (idx : Zds g k i ws = true) : Zax g.mode (ZaQ g) k ws.toFinset := by
  simp only [Zds,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←ZeY idx.2]
  exact Zjs g top prior low geom blocks _ le i idx.1

theorem Zqx {g prior i hints} (low : ∀ q, Zad g.mode (Zae q) (Zaa q) (prior q))
    (geom : Zay g prior = true) (blocks : ZaV g g.cap)
    (idx : Zds g g.cap i (vars g.mask) = true) (hp : Za1 (ZaQ g) = true)
    (ess : Zbm (ZaQ g) (vars g.mask) (ZcJ g.mask hints) = true)
    (all : (ZcJ g.mask hints).map Prod.fst = vars g.mask) :
    Zad g.mode (vars g.mask) (ZaQ g) (g.cap+1) := by
  apply Zd6 (Zbr _ hp) (Zbl ess).1 (Zbl ess).2 _ (ZfO low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply ZcG ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem Zqv {g prior ci hints} (low : ∀ q, Zad g.mode (Zae q) (Zaa q) (prior q))
    (ok : ZcS g.mask ci prior = true)
    (hp : Za1 (ZaQ g) = true)
    (ess : Zbm (ZaQ g) (vars g.mask) (ZcJ g.mask hints) = true)
    (all : (ZcJ g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : Zdh g.mode (Zce ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (Zae (Zcd g.mask ci)) (vars g.mask)=true) :
    Zad g.mode (vars g.mask) (ZaQ g) (g.cap+1) := by
  apply Zd6 (Zbr _ hp) (Zbl ess).1 (Zbl ess).2 _ (Zeb (Zdz ci prior low ok) [] rfl nd cut)
  intro a ha
  apply ZcG ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Zah (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Zad u (Zae e.1) (Zaa e.1) e.2
def Zak (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem Zal {u old L m carries} (previous : Zah u old)
    (main : Zad u (Zae m) (Zaa m) L)
    (ok : carries.all (fun v => ZeL v.1 m v.2) = true) :
    Zah u (Zak old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact ZlZ (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem ZfR : Zah true [] := by simp [Zah]
theorem ZjD {u es} (h : Zah true es) : Zah u es := fun e he => ZjF (h e he)
def Za5 (v : Nat) (upper : Nat) := 2^769*upper+v
def ZaF {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => Za5 (f x).toNat (ZaF f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => Za5 1 (units n)
theorem Zey (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem Zk6 (a b : Bits) (u v : Nat) :
    Za5 a.toNat u &&& Za5 b.toNat v = Za5 (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Za5,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (Zey _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem ZmM (a b : Bits) (u v : Nat) :
    Za5 a.toNat u ||| Za5 b.toNat v = Za5 (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Za5,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (Zey _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem Zk7 (a b : Bits) (u v : Nat) :
    Za5 a.toNat u ^^^ Za5 b.toNat v = Za5 (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Za5,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (Zey _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem Zda {α} (f g : α → Bits) (xs) :
    ZaF f xs &&& ZaF g xs = ZaF (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [ZaF]
  | cons a xs ih => simp only [ZaF,Zk6,ih]
theorem ZeH {α} (f g : α → Bits) (xs) :
    ZaF f xs ||| ZaF g xs = ZaF (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [ZaF]
  | cons a xs ih => simp only [ZaF,ZmM,ih]
theorem ZdC {α} (f g : α → Bits) (xs) :
    ZaF f xs ^^^ ZaF g xs = ZaF (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [ZaF]
  | cons a xs ih => simp only [ZaF,Zk7,ih]
theorem ZqB {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = ZaF (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,ZaF]
  | cons v xs ih => simp only [List.length_cons,units,ZaF,Za5,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def ZdB (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem Znc (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,Za5,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem Zmd (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem ZnW {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (ZdB (units xs.length) (ZaF f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [ZdB,Nat.testBit_and,Nat.testBit_shiftRight,Znc _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [ZaF,List.length_cons,units,Za5]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using Zmd (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev Zc8 := Nat × Nat
abbrev Zer := Nat × Nat × Nat

def Zby {α} (s : α → ZdU) (xs : List α) : Zc8 :=
  (ZaF (fun x => (s x).1) xs,ZaF (fun x => (s x).2) xs)
def ZdF {α} (c : α → Cov) (xs : List α) : Zer :=
  (ZaF (fun x => (c x).1) xs,ZaF (fun x => (c x).2.1) xs,
   ZaF (fun x => (c x).2.2) xs)
def Zb3 (d : Bool) (a : Zc8) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem ZdT (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem Zea {α} (s : α → ZdU) (xs : List α) (d : Bool) :
    Zb3 d (Zby s xs) = ZaF (fun x => column d (s x)) xs := by
  cases d <;> simp only [Zb3,Zby,column,Bool.false_eq_true,ite_false,ite_true,Zda,ZdC,ZdT]

def Zcu (op : Nat) (a b : Zc8) : Zc8 :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem Zk5 {α} (a b : α → Zac) (xs : List α) (op : Nat) :
    Zcu op (Zby (fun x => (a x).2) xs) (Zby (fun x => (b x).2) xs) =
    Zby (fun x => (ZaY op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [Zcu,h0,ite_true,Zby,Zda,ZaY,bv]
  by_cases h1 : op=1
  · simp [Zcu,h1,Zby,ZeH,ZaY,bv]
  by_cases h2 : op=2
  · simp [Zcu,h2,Zby,Zda,ZdC,ZdT,ZaY,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [Zcu,h0,h1,h2,ite_false,Zby,Zda,ZdC,ZdT,ZaY,bv,e]

def Zdw (c : Zer) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem ZhC {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    Zdw (ZdF c xs) (ZaF a xs) (ZaF b xs) ka kb =
    ZaF (fun x => Zcy (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [Zdw,ZdF,Zda,ZeH,ZdC,ZdT,Zcy,ZbX,ZcV,
      Bool.false_eq_true,ite_false,ite_true]

def Zas (c : ZaW) (i : Nat) := c.2.2.1.getD i Za6
def Zcx (c : ZaW) (i j op : Nat) (ka kb : Bool) :=
  let a := Zas c i
  let b := Zas c j
  Zcb c op a b (ZaY op a b) ka kb
def Zew (c : ZaW) (d ka kb : Bool) (op i j : Nat) :=
  let a := Zas c i
  let b := Zas c j
  Zcy c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (ZaY op a b).2

def Zdg {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && Zdg f (mask >>> 769) xs
theorem Zk2 {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : Zdg f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [Zdg,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List Zc8 × Zer
def ZbJ (k n : Nat) (xs : List ZaW) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => Zby (fun c => (Zas c i).2) xs),
    ZdF (fun c => c.2.2.2.1.1) xs)
def ZcU (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem Zfe (k n) (xs) {i : Nat} (h : i<n) :
    ZcU (ZbJ k n xs) i = Zby (fun c => (Zas c i).2) xs := by
  simp [ZcU,ZbJ,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def ZeW (u : Bool) (p : ZaP) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (ZaE p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (ZaE p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem Zfi (d x : Sig) : ZaE d (neg x) = d ^^^ ZaE d x := by
  apply Zbc
  intro r
  simp only [ZaE,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem Zqu (u) (p : ZaP) (x : Sig) :
    ZaH u p.domain p.wires x = ZeW u p (ZaE p.domain x) := by
  simp only [ZaH,ZeW,Zfi]

def Za9 (p : Zac → Bool) (a : Zac) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem Zgj (p : Zac → Bool) (ws : List Zac) (a : Zac) (keep : Bool) :
    ws.countP p ≤ (Zbu ws a keep).countP p + Za9 p a keep := by
  cases keep
  · simp only [Zbu,Bool.false_eq_true,ite_false,Za9,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [Zbu,Za9]

theorem ZkZ (p : Zac → Bool) (ws : List Zac) (a b : Zac) (ka kb : Bool) :
    ws.countP p - Za9 p a ka - Za9 p b kb ≤
    (ZaR ws a b ka kb).countP p := by
  have h1 := Zgj p ws a ka
  have h2 := Zgj p (Zbu ws a ka) b kb
  simp only [ZaR]
  omega

abbrev ZqA := ZaP × Nat × Bool
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem ZbW {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def Zcs {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem Zeg {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : Zcs f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => Zcs f l fun xs => k (x::xs)) = _
    rw [ZbW,ih]
    rfl
def Zat (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def ZbP (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def Zch (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def Zbv (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (Zch d m) (ZbP m pm)) (and u (ZbP (Nat.xor d m) pm))
theorem Zdd (d a : Sig) : Zat d.toNat a = (ZaE d a).toNat := (BitVec.toNat_and _ _).symm
theorem Zeu (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem ZdE (d a : Sig) : Zch d.toNat (Zat d.toNat a) = ZaK d a := by
  rw [Zdd]
  have e : Nat.beq (ZaE d a).toNat 0 = (ZaE d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←Zeu,z0]
  rw [Zch,e,Zeu]
  rfl
theorem Zgr (x d : Sig) (pool : List Sig) : ZbP x.toNat (pool.map (Zat d.toNat)) = (pool.map (ZaE d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (Zat d.toNat a)) (ZbP x.toNat (l.map (Zat d.toNat))) = _
    rw [ih,Zdd,Zeu,List.map_cons,List.any_cons,Bool.beq_comm]
theorem ZdD (u : Bool) (d a : Sig) (pool : List Sig) :
    Zbv u d.toNat (pool.map (Zat d.toNat)) (Zat d.toNat a) = ZaH u d pool a := by
  have x : Nat.xor d.toNat (ZaE d a).toNat = (ZaE d (neg a)).toNat := by
    rw [Zfi]
    exact (BitVec.toNat_xor _ _).symm
  rw [Zbv,ZdE,Zdd,x,Zgr,Zgr]
  simp only [ZaH,ZaK]
def Zcj (u : Bool) (p : ZaP) (w : Zac) : Nat := cond (ZaH u p.domain p.wires w.1) 0 1
def ZdQ (u : Bool) (p : ZaP) (ws : List Zac) (k : Nat) (a b : Zac) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Zac => ZaK p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - Za9 const a ka - Za9 const b kb + (ZaK p.domain z).toNat
  (((ws.map (Zcj u p)).sum == cond ka 0 (Zcj u p a) + cond kb 0 (Zcj u p b)) &&
    decide (k+p.ZaG+(!ZaH u p.domain p.wires z).toNat < p.bound+cm)) &&
    (ZaH u p.domain p.wires z || (ZaH u p.domain p.wires a.1 && ZaH u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem Zg0 (op : Nat) (d a b : Sig) : zN op (Zat d.toNat a) (Zat d.toNat b) = Zat d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [Zdd]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply Zbc
    intro r
    simp only [ZaE,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply Zbc
    intro r
    simp only [ZaE,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply Zbc
    intro r
    simp only [ZaE,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply Zbc
  intro r
  simp only [ZaE,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def ZbQ (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (Zch d x) 1 0)
theorem ZgA (d : Sig) (a : Zac) (keep : Bool) :
    ZbQ d.toNat (Zat d.toNat a.1) keep = Za9 (fun w : Zac => ZaK d w.1) a keep := by
  rw [ZbQ,ZdE,Za9]
  cases keep
  · cases ZaK d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def Zdb (u : Bool) (k : Nat) (ws : List Zac) (p : ZaP) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Zac => Zat d w.1)
  (d,ms.countP (Zch d),p.bound,Nat.add k p.ZaG,(ms.map fun m => cond (Zbv u d (p.wires.map (Zat d)) m) 0 1).sum,ms,p.wires.map (Zat d),u)
noncomputable def ZfX {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def ZdA {β : Type} (u : Bool) (k : Nat) (ws : List Zac) (p : ZaP) (f : QS → β) : β :=
  force p.domain.toNat fun d => Zcs (Zat d) p.wires fun pm => Zcs (fun w : Zac => Zat d w.1) ws fun ms =>
  force (ms.countP (Zch d)) fun c => force p.bound fun l => force (Nat.add k p.ZaG) fun t =>
  force (ms.map fun m => cond (Zbv u d pm m) 0 1).sum fun v => ZfX u fun u => f (d,c,l,t,v,ms,pm,u)
theorem ZhL {β : Type} (u k ws p) (f : QS → β) : ZdA u k ws p f = f (Zdb u k ws p) := by
  have e (b : Bool) (f : Bool → β) : ZfX b f = f b := by cases b <;> rfl
  simp only [ZdA,ZbW,Zeg,e]
  rfl
noncomputable def Zdu {β : Type} (u : Bool) (k : Nat) (ws : List Zac) (ps : List ZaP) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => ZdA u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem Zht {β : Type} (u k ws ps) (f : List QS → β) : Zdu u k ws ps f = f (ps.map (Zdb u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change ZdA u k ws p (fun q => Zdu u k ws ps fun qs => f (q::qs)) = _
    rw [ZhL,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Zb0 := ZaW × Nat × Nat × List QS × List Nat × Nat
noncomputable def ZbO (c : ZaW) : Zb0 :=
  let ws := c.2.2.1.map (fun w : Zac => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (Zdb c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def Zem {β : Type} (cs : List ZaW) : (List Zb0 → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    Zcs (fun w : Zac => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    Zdu c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem Ze3 {β : Type} (cs) (f : List Zb0 → β) : Zem cs f = f (cs.map ZbO) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      Zcs (fun w : Zac => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      Zdu c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => Zem cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [ZbW,ZbW,Zeg,ZbW,Zht,ih]
    rfl
noncomputable def ZeE (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := Zbv s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (ZbQ s.1 x ka)) (ZbQ s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (Zch s.1 (zN op x y)) false))
theorem Znb {d : Nat} (ws : List Zac) (i : Nat) (hd : Zat d zero=0) :
    (ws.map (fun w : Zac => Zat d w.1)).getD i 0 = Zat d (ws.getD i Za6).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem ZkO {u k p ws i j op ka kb} (h : ZeE (Zdb u k ws p) i j op ka kb=true) :
    ZdQ u p ws k (ws.getD i Za6) (ws.getD j Za6) op ka kb=true := by
  have z0 : Zat p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [Zat,this]
  have su : (((ws.map (fun w : Zac => Zat p.domain.toNat w.1)).map fun m => cond (Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat)) m) 0 1).sum) =
      (ws.map (Zcj u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat)) (Zat p.domain.toNat w.1)) 0 1 = _
    rw [ZdD]
    rfl
  simp only [ZeE,Zdb,ZbW,Znb _ _ z0,su,List.countP_map,Function.comp_def,ZdE] at h
  generalize ws.getD i Za6=a at h ⊢
  generalize ws.getD j Za6=b at h ⊢
  replace h : and (Nat.beq (ws.map (Zcj u p)).sum (Nat.add (cond ka 0 (cond ((Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat))) (Zat p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat))) (Zat p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.ZaG)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zac => ZaK p.domain w.1)) (ZbQ p.domain.toNat (Zat p.domain.toNat a.1) ka)) (ZbQ p.domain.toNat (Zat p.domain.toNat b.1) kb))))
    (or ((Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat))) (zN op (Zat p.domain.toNat a.1) (Zat p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.ZaG) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zac => ZaK p.domain w.1)) (ZbQ p.domain.toNat (Zat p.domain.toNat a.1) ka)) (ZbQ p.domain.toNat (Zat p.domain.toNat b.1) kb)))) (and ((Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat))) (Zat p.domain.toNat a.1)) ((Zbv u p.domain.toNat (p.wires.map (Zat p.domain.toNat))) (Zat p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.ZaG) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zac => ZaK p.domain w.1)) (ZbQ p.domain.toNat (Zat p.domain.toNat a.1) ka)) (ZbQ p.domain.toNat (Zat p.domain.toNat b.1) kb)))) (Zch p.domain.toNat (zN op (Zat p.domain.toNat a.1) (Zat p.domain.toNat b.1))) false)) = true := h
  rw [Zg0,ZdE,ZdD,ZdD,ZdD,ZgA,ZgA] at h
  have ca : ZaK p.domain (bin op a.1 b.1)=true → ZaH u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [ZaH,ZaK,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [ZdQ,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => ZaK p.domain w.1) - Za9 (fun w : Zac => ZaK p.domain w.1) a ka -
      Za9 (fun w : Zac => ZaK p.domain w.1) b kb = c at h ⊢
    generalize ZaK p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize ZaH u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.ZaG+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.ZaG) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem ZkJ (m : Nat) (l : List Nat) : ZbP m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [ZbP]
  | cons a l ih =>
    change or (Nat.beq m a) (ZbP m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def ZeQ (fl : Nat → Option (List Nat)) (l : Zb0) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => Zcs (fun v => v) ys fun ys =>
    and (ZbP z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (ZbP v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (ZbP v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem ZjC (xs : List Sig) : Zdk xs = (xs.map ZbB).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+ZbB x) a = a+(xs.map ZbB).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem Zfn (f : Zac → Nat) {ws : List Zac} {a b : Zac} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((ZaR ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Zac} {x : Zac} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [ZaR,Zbu,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem Zhs {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : ZcR u op=true)
    (h : ZdQ u p ws k a b op ka kb=true) :
    Zb2 u p k ((ZaR ws a b ka kb).map Prod.fst) (Zbn op a b)=true := by
  let const := fun w : Zac => ZaK p.domain w.1
  let z := bin op a.1 b.1
  let rest := ZaR ws a b ka kb
  have ck := ZkZ const ws a b ka kb
  change ws.countP const - Za9 const a ka - Za9 const b kb ≤ rest.countP const at ck
  simp only [ZdQ,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := Zfn (Zcj u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((ZaR ws a b ka kb).map (Zcj u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (ZaH u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : ZaH u p.domain p.wires w.1
    · simp [Zcj,e] at v
    · rfl
  have opOK : (!(!ZaH u p.domain p.wires z) || Zcq u p.domain p.wires (Zbn op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [Zcq,Zbn,x,y,al]
  change k+p.ZaG+(!ZaH u p.domain p.wires z).toNat < p.bound+(ws.countP const - Za9 const a ka -
        Za9 const b kb+(ZaK p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : ZaS (Zbn op a b)=z := rfl
  simp only [Zb2,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.ZaG+(!ZaH u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if ZaK p.domain z then 1 else 0)
  cases hc' : ZaK p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem ZgW (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : Zat one.toNat v = v.toNat := by
    rw [Zdd]
    congr 1
    exact BitVec.and_allOnes
  have := Zg0 op one a b
  rwa [e,e,e] at this
theorem Zqt (ws : List Zac) (i : Nat) :
    (ws.map (fun w : Zac => w.1.toNat)).getD i 0 = (ws.getD i Za6).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem ZgV {c : ZaW} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (Zas c i).1 ≠ (Zas c j).1 := by
  have gi : Zas c i = c.2.2.1[i] := by simp [Zas,List.getD_eq_getElem?_getD,hi]
  have gj : Zas c j = c.2.2.1[j] := by simp [Zas,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem ZjE {c : ZaW} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : ZeQ fl (ZbO c) i j op ka kb=true) :
    (c.2.2.2.2.2 (Zdk (ZaS (Zbn op (Zas c i) (Zas c j)) ::
      (ZaR c.2.2.1 (Zas c i) (Zas c j) ka kb).map Prod.fst))).any (ZcQ
      (ZaS (Zbn op (Zas c i) (Zas c j)) ::
      (ZaR c.2.2.1 (Zas c i) (Zas c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : Zas c t ∈ c.2.2.1 := by
    simp [Zas,List.getD_eq_getElem?_getD,ht]
  have hne := ZgV nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : Zas c i ≠ Zas c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := Zfo nd ha hb ka kb v
  have sum := Zfn (fun w : Zac => ZbB w.1) ha hb hab ka kb
  have wi : Zas c i = c.2.2.1.getD i Za6 := rfl
  have wj : Zas c j = c.2.2.1.getD j Za6 := rfl
  simp only [ZeQ,ZbO,ZbW,Zqt,←wi,←wj,ZgW] at h
  generalize Zas c i=a at *
  generalize Zas c j=b at *
  change Option.rec false _ (fl (ZbB (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Zac => w.1.toNat)).map kwN).sum -
    (cond ka 0 (ZbB a.1)) - (cond kb 0 (ZbB b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Zac => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Zac => ZbB w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : Zdk (ZaS (Zbn op a b) :: (ZaR c.2.2.1 a b ka kb).map Prod.fst) =
      ZbB (bin op a.1 b.1)+((ZaR c.2.2.1 a b ka kb).map (fun w : Zac => ZbB w.1)).sum := by
    rw [ZjC,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize Zdk (ZaS (Zbn op a b) :: (ZaR c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [Zeg,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,ZkJ,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [ZcQ,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def Zel (fl : Nat → Option (List Nat)) (l : Zb0) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => ZeE s i j op ka kb) (ZeQ fl l i j op ka kb))) (Zcx l.1 i j op ka kb)
theorem Zhj {c : ZaW} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : Zel fl (ZbO c) i j op ka kb=true) :
    Zcx c i j op ka kb=true := by
  simp only [Zel,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : ZcR c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [ZcR] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : Zas c t ∈ c.2.2.1 := by
      simp [Zas,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := ZgV nd hi hj (fun e => by simp [e] at hn)
    have closed := Zhs (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (ZkO ok)
    have cut : c.2.2.2.2.1.any (fun p => Zb2 c.2.2.2.1.2 p (c.1-1)
        ((ZaR c.2.2.1 (Zas c i) (Zas c j) ka kb).map Prod.fst)
        (Zbn op (Zas c i) (Zas c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [Zcx,Zcb,ZcI,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := ZjE nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [Zcx,Zcb,ZcI,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def Zdi (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def Zcp (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem Zj4 : ∀ v : Fin 144, Zcp v.val=true → ∀ t : Fin 9, Zdi v.val t.val<9 ∧
    Zde (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (Zdi v.val t.val) zero := by decide +kernel
theorem Zj3 {v t : Nat} (hv : Zcp v=true) (ht : t<9) : Zdi v t<9 ∧
    Zde (swapRows v) (inputs.getD t zero) = inputs.getD (Zdi v t) zero := by
  have lt : v<144 := by
    simp only [Zcp,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact Zj4 ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => Zdi v t) t
theorem Zme {perm : List Nat} (ok : perm.all Zcp=true) {t : Nat} (ht : t<9) :
    ZaI (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [ZaI,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := Zj3 ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def ZdV : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => ZdV n (bits >>> 10) (ws++[z])
theorem Zjp (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Zac) :
    (Zc5 n bits ds).map (fun w => F w.1) = ZdV n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Zac) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i Za6).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [ZdV,ZbW,Zc5,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem Zhn {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (ZbH bits ws).map f = ZbH bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,ZbH,ZbH]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def Zex (g : Zai) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (ZbA g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (Zbh data (i*(len+(ZbA g.mask).length+depth)) (len+(ZbA g.mask).length+depth)) fun rec =>
  ZbH (rec >>> len) (ZdV depth (rec &&& ((1 <<< len)-1)) raw)
theorem ZhK (g : Zai) (k i : Nat) {perm : List Nat} (ok : perm.all Zcp=true) :
    Zex g k i perm = ((Zbs g k i).map (ZaI (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (ZaI ms a).toNat
  have F0 : F zero=0 := by
    change (ZaI ms zero).toNat=0
    rw [Zck,(ZeV _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (ZaI ms (bin op a b)).toNat = zN op (ZaI ms a).toNat (ZaI ms b).toNat
    rw [ZgW,Zck,ZfN,Zck,Zck]
  have raw : (Zcf g).map (fun w => F w.1) = (ZbA g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [Zcf,ZdO,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := Ze1 hm
    exact congrArg BitVec.toNat (Zme ok hj)
  have len : (Zcf g).length = (ZbA g.mask).length := by simp [Zcf,ZdO]
  unfold Zex Zbs ZdP
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [ZbW,Zdt,len]
  rw [List.map_map,List.map_map,Zhn,←raw,←Zjp F F0 Fb]
  rfl
noncomputable def ZfJ (g : Zai) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.ZcA[pair.2]?).bind fun perm => cond (perm.all Zcp) (some (Zex g k pair.1 perm)) none
noncomputable def ZcC (g : Zai) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (ZfJ g (k-1))
noncomputable def ZfS (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Zb0) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := ZcU b i
    let b' := ZcU b j
    let z := Zcu op a b'
    let mask := ZdB r (Zdw cov (Zb3 (!u) a) (Zb3 (!u) b') ka kb ||| Zb3 (!u) z)
    Zdg (fun c => Zel fl c i j op ka kb) mask xs

theorem ZhF {fl u} (k n) (xs : List ZaW) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : ZfS fl u (ZbJ k n xs) (xs.map ZbO) i j op ka kb=true) :
    Zcx xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : Zcx xs[q] i j op ka kb =
      if len>k then true else if Zew xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !Za1 (ZaY op (Zas xs[q] i) (Zas xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(ZaY op (Zas xs[q] i) (Zas xs[q] j)).1)
      then true else ZcI u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((ZaR xs[q].2.2.1 (Zas xs[q] i) (Zas xs[q] j) ka kb).map Prod.fst)
        (Zbn op (Zas xs[q] i) (Zas xs[q] j)) := by
    simp only [Zcx,Zcb,budget,arity,mode,len,Zew] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := ZcU (ZbJ k n xs) i
    let b := ZcU (ZbJ k n xs) j
    let cov := ZdF (fun c : ZaW => c.2.2.2.1.1) xs
    change (if len>k then true else Zdg _ (ZdB r
       (Zdw cov (Zb3 (!u) a) (Zb3 (!u) b) ka kb |||
        Zb3 (!u) (Zcu op a b))) (xs.map ZbO)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := Zfe k n xs hi
    have cb : b = _ := Zfe k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,Zk5,Zea,Zea,Zea,ZhC,ZeH] at pass
    by_cases hit : Zew xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply Zhj nd hfl
      have m := Zk2 _ _ _ q (by simpa using hq) (by
        rw [ZnW _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def ZfT (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Zb0) (i j op : Nat) :=
  let f := ZfS fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def ZdG (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Zb0) (i : Nat) (js : List Nat) :=
    js.all (fun j => (ZcB u).all (ZfT fl u b xs i j))
noncomputable def ZcM (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Zb0) : List Nat → Bool
  | [] => true
  | i::js => ZdG fl u b xs i js && ZcM fl u b xs js

theorem ZhG {fl u} (k n) (xs : List ZaW) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : ZcM fl u (ZbJ k n xs) (xs.map ZbO) js=true) :
    ZbY xs[q] (js.map (Zas xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [ZcM,Bool.and_eq_true,ZdG,List.all_eq_true] at allRows
    simp only [List.map_cons,ZbY,ZeP,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @ZhF fl u k n xs i j op
    simp only [ZfT,Bool.and_eq_true] at pass
    simp only [Zcv,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def ZeK (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List ZaW) :=
    ZcM fl u (ZbJ k n xs) (xs.map ZbO) (List.range n)
theorem Zi5 {fl u k n} {xs : List ZaW} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : ZeK fl u k n xs=true) : ZbY xs[q] xs[q].2.2.1=true := by
  have all := ZhG k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (Zas xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [Zas,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def ZcO (g : Zai) (k i : Nat) : ZaW :=
  let raw := Zcf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := ZdP g k i
  let start := num*(10*Zdt g depth+raw.length+depth)
  let pos := start+num*offw+Zbh data (start+i*offw) offw
  let nr := Zbh data pos 5
  let nl := Zbh data (pos+5) lw
  let st := pos+5+lw
  let rules := (ZeG data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zco g (k-1))).toList
  (k,ws.length,ws,Zdl g.mode ws,rules,ls)


theorem Znm (g : Zai) (k i tag : Nat) (ys) (h : ZcC g k tag=some ys) :
    ∃ xs ∈ (ZcO g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (Zco g (k-1))).toList, _
  unfold ZcC at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,ZfJ] at h
    simp only [Option.bind_some,Zco]
    split at h
    · contradiction
    next v =>
      cases ha : g.ZcA[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all Zcp with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(Zbs g (k-1) pair.1).map (ZaI (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (ZhK g _ _ hv)

def ZeS (T : Sig) (c : ZaW) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem ZhM (g : Zai) (k i : Nat) :
    ZcH g k i = (ZeS (ZaQ g) (ZcO g k i) &&
      (if k=0 then true else ZbY (ZcO g k i) (ZcO g k i).2.2.1)) := rfl

theorem Zk1 {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → ZcH g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def Zcr (g : Zai) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (ZcO g k)
def header (g : Zai) (k start n ar : Nat) :=
  (Zcr g k start n).all (fun c => c.2.1==ar && ZeS (ZaQ g) c)
noncomputable def ZbD (g : Zai) (k start n ar lo len : Nat) :=
  let xs := Zcr g k start n
  let b := ZbJ k ar xs
  Zem xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    ZdG (ZcC g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem ZeC {g k start n ar lo len} (h : ZbD g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    ZdG (ZcC g k) g.mode (ZbJ k ar (Zcr g k start n)) ((Zcr g k start n).map ZbO)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [ZbD,Ze3] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem Zir {g k start n ar lo a b}
    (h : ZbD g k start n ar lo a=true) (t : ZbD g k start n ar (lo+a) b=true) :
    ZbD g k start n ar lo (a+b)=true := by
  simp only [ZbD,Ze3]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact ZeC h (lo+j) (by omega) (by omega)
  · exact ZeC t (lo+j) (by omega) (by omega)

theorem Znl {g k start n ar} (h : ZbD g k start n ar 0 ar=true) :
    ZeK (ZcC g k) g.mode k ar (Zcr g k start n)=true := by
  let xs := Zcr g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      ZcM (ZcC g k) g.mode (ZbJ k ar xs) (xs.map ZbO) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,ZcM,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := ZeC h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold ZeK
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem ZfV {g k start n ar} (hd : header g k start n ar=true)
    (h : ZbD g k start n ar 0 ar=true) : block g k start n=true := by
  apply Zk1
  intro i lo hi
  let xs := Zcr g k start n
  have hm : ZcO g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [ZeS,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, ZcC g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => Znm g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [ZhM,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ Zi5 hq hb ha hm nd hfl hn (Znl h)

def Zdn (g : Zai) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => ZbD g k start n ar lo num=true
  | d+1 => Zdn g k start n ar lo (num/2) d ∧ Zdn g k start n ar (lo+num/2) (num-num/2) d
theorem ZlY {g k start n ar lo num d} (h : Zdn g k start n ar lo num d) :
    ZbD g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := Zir (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def Zdo (g : Zai) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ Zdn g k start n ar 0 ar rows
  | d+1 => Zdo g k start (n/2) ar rows d ∧ Zdo g k (start+n/2) (n-n/2) ar rows d
theorem Zjo {g k start n ar rows d} (h : Zdo g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact ZfV h.1 (ZlY h.2)
  | succ d ih =>
    have v := ZaC (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def ZaX {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => ZaX f (xs.take (xs.length/2)) d ∧ ZaX f (xs.drop (xs.length/2)) d
theorem ZaD {α f xs d} (h : @ZaX α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem Zj2 {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Zad u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,Zd8 pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem ZbZ {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Zad u (Zae q) (Zaa q) (prior q))
    (e : (Zaa q == Zaa m && (Zae q == vars m) && (prior q == cap+1) && Za1 (Zaa m) &&
      decide (vars m).Nodup && Zdh u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Zax u (Zaa m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact Zeb (Zj2 (Zbr _ e4) h) [] rfl e5 e6

theorem ZaL {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Zad u (Zae q) (Zaa q) (prior q)) (ci : ZaO)
    (ok : ZcS m ci prior = true)
    (cut : (decide ws.Nodup && Zdh u (Zce ci.1 ci.2.1) ci.2.2.2.2 cap 0 (Zae (Zcd m ci)) ws)=true) :
    Zax u (Zaa m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact Zeb (Zdz ci prior low ok) [] rfl cut.1 cut.2

theorem Zaz {u} {g : Zai} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Zad u (Zae q) (Zaa q) (prior q))
    (geom : Zay g prior = true) (blocks : ZaV g cap)
    (idx : Zds g cap i ws = true) : Zax u (Zaa m) cap ws.toFinset := by
  subst hm
  subst hu
  exact ZfO low geom blocks (Nat.le_refl _) idx

def ZgY (m hints : Nat) : Bool :=
  let xs := ZcJ m hints
  Za1 (Zaa m) && Zbm (Zaa m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem Zbq {u} {m hints cap : Nat} (ok : ZgY m hints = true)
    (a : Zax u (Zaa m) cap (vars m).toFinset) : Zad u (vars m) (Zaa m) (cap+1) := by
  simp only [ZgY,Bool.and_eq_true,beq_iff_eq] at ok
  apply Zd6 (Zbr _ ok.1.1) (Zbl ok.1.2).1 (Zbl ok.1.2).2 _ a
  intro v hv
  apply ZcG ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def Znd (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((ZbA m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def Zd3 (m : Nat) (rs : List Nat) : Bool :=
  let xs := Znd m rs
  Zbm (Zaa m) (Zae m) xs && (xs.map Prod.fst == vars m) &&
    Za1 (Zaa m) && decide (Zae m = vars m ++ [ZdR (m/512-1)])
theorem Zjt {u} {m : Nat} {rs : List Nat} (ok : Zd3 m rs = true) {k : Nat} {S : Finset Sig}
    (h : Zar u (Zaa m) k S) (sub : ∀ v ∈ S, v ∈ Zae m) :
    S=(vars m).toFinset ∨ S=(Zae m).toFinset := by
  simp only [Zd3,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := ZcG ess v (List.mem_toFinset.mpr hv)
    exact Zc3 h (Zae m) v sub r s hd hi
  have mem : ∀ v, v ∈ Zae m ↔ v ∈ vars m ∨ v=ZdR (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : ZdR (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem Zaq {u} {m q cap : Nat} {rs : List Nat} (ok : Zd3 m rs = true)
    (e : Zaa m = Zaa q) (ev : vars m = vars q)
    (a : Zax u (Zaa q) cap (vars q).toFinset)
    (b : Zax u (Zaa q) cap (Zae m).toFinset) :
    Zad u (Zae m) (Zaa m) (cap+1) := by
  have ok' := ok
  simp only [Zd3,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := Zdv (Zbr _ ok'.1.2) (Zbl ok'.1.1.1).1 (Zbl ok'.1.1.1).2 hr ha
  by_contra! small
  rcases Zjt ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def ZpX (i : Nat) : Nat := 0xf
def ZpY : Zag := (1,0,1,0,0,0,0,ZpX)
def Zjw : Array (Bits × Bits) := #[((-0x1b8b8d),0x173652),((-0x168581),0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def Zjv : List ZaO := []
def Zl1 : List (List Nat) := [[],[48,33]]
def ZkR : Nat → Zag
  | 3 => ZpY
  | _ => Za3
def Zl2 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Zai := ⟨15,3,fun j => Zjw[j]?.getD (0,0),Zjv,Zl1,ZkR,Zl2⟩
set_option maxHeartbeats 0 in
theorem Znz : Zay g15 (Zam []) = true := by
  simp only [Zay,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaD (d:=0) ?_⟩,ZaD (d:=0) ?_⟩
  all_goals simp only [ZaX]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zep (g : Zai) (k : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | i, (n,a,d)::xs => Zdo g k i n a 0 d ∧ Zep g k (i+n) xs

theorem Zan (g : Zai) (k i : Nat) (xs : List (Nat × Nat × Nat))
    (ok : Zep g k i xs := by
      simp only [Zep,Zdo,Zdn,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals first | exact True.intro | decide +kernel) :
    block g k i (xs.map Prod.fst).sum = true := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n,a,d⟩ := x
    exact ZaC (Zjo ok.1) (ih (i+n) ok.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlj : ZaV g15 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact Zan g15 3 0 [(1,4,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp7 : Zad true (vars 15) (Zaa 15) 4 := Zbq (hints:=8449) (by decide +kernel) (Zaz (g:=g15) (i:=0) rfl rfl (Zaf [] ZfR) Znz Zlj (by decide +kernel))

end PEqualNP.Outside.L_meta_670.Projection
