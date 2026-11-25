import PEqualNP.Defs
-- Proof and certificates by 0xshuzo, PR12203, revision 0d2bbcdeb511ffff33552e155db3526648d8575b.
-- https://github.com/open-goat/pequalnp-proofs/pull/12203
-- Original proofs and batching retained; packed tables expanded with identical decoded nodes and ordered hints.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def Zbi (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def ZcQ (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem Zca {u d} (h : Zbi u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem Zfv {u d} (h : Zbi u d) (a b : Sig) : bin d a b = bin (ZcQ d) b a := by
  rcases Zca h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,ZcQ,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : Zbi u d) : Zbi u (ZcQ d) ∧ ZcQ (ZcQ d)=d := by
  rcases Zca h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [ZcQ,Zbi]

def Zav (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), Zbi u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Zav u target k (insert (bin d a b) U)
theorem Zav.stop {u} {target : Sig} (hp : proper target) : Zav u target 0 {target} := ⟨rfl,hp⟩
theorem Zav.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : Zbi u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zav u target k (insert (bin d a b) U)) :
    Zav u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Zav.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Zav u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Zav.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : Zbi u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zav u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Zav.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Zav u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma Zgg {u target k S} (h : Zav u target k S) : ∀ a ∈ S, proper a := by
  induction h using Zav.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma Zfs {u target k S} (h : Zav u target k S) : S.card ≤ k+1 := by
  induction h using Zav.ind with
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
private lemma Zc8 (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma ZcN (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem ZbI {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem Znb (a : Sig) : nrm false a = a := rfl
theorem ZrM (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,Zc8]
theorem ZfM {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem ZhY (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,Zc8,neg_neg']
theorem Zlf {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem Zlg {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact Zlf h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem Zdr (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem Znc (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply ZbI
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,Zdr,ha,hb,ZcN,Zc8,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,Zc8,Zdr]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def Zda (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def Zcb (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := Zcb w (nrm u v)

private lemma Zhy (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply ZbI <;> intro i <;>
    simp [ZcN,bit_zero,bit_one]

private lemma Zqj : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma Zf2 {w : List Sig} {a : Sig} (h : Zcb w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def Zdz (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, Zbi u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma ZhU {u w a b} (d : Nat) (hd : Zbi u d) (ha : Zcb w a) (hb : Zcb w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    Zcb w (bin d a b) ∨ Zdz u w (bin d a b) := by
  have rz : Zcb w zero := Or.inr (fun h => h.1 rfl)
  have ro : Zcb w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := Zhy a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := Zhy b
  by_cases he : a=b
  · subst b
    left
    rcases Zca hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases Zf2 ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases Zca hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases Zca hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases Zf2 hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases Zca hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases Zca hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem Zgk (a : Sig) : nrm true a ≠ one := by
  intro h
  have := ZrM a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem Zht {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ Zdz u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := ZhU (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [Znb] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := Znc d a b
    unfold Repr
    rw [eq]
    exact ZhU e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨Zgk a,Zgk b⟩)
theorem ZdK {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := Zlg hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma ZdW {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact ZdK (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem Zqo {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [ZhY]

def ZbQ (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma ZoB (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ZbQ g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (ZbQ g=false ∧ Zdz u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      Zdz u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply ZbI
      intro i
      cases d <;> simp [Zdr,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (ZdK (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (ZdW w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact Zht d (ZdW w i) (ZdW w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [ZbQ])
    left
    cases l with
    | nil => exact ZdK (Or.inr (by simp [gv,Zqj]))
    | cons i l => exact Zqo (ZdW w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma Zhu {u target} {w : List Sig} {z : Sig} {k S c} (h : Zav u target k S)
    (hz : Zcb w z ∨ (c=1 ∧ Zdz u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Zav u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := Zgg h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Zav u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Zav.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, ZbQ g=false)
    (hp : proper target) (hout : target ∈ (Zda gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !ZbQ g) ∧ Zav u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Zav.stop hp,by simpa [Zda] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := ZoB u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : Zcb (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if ZbQ g then 0 else 1)=1 ∧ Zdz u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := Zhu ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : ZbQ g <;> simp [hn] at hl ⊢ <;> omega

private lemma Zig (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma ZrO (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [Zig]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [Zdr]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [Zdr]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [Zc8,bit_zero]
    | cons a l => exact Zc8 _ _

private lemma Zi5 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (Zda gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Zda gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,ZrO i g w (hg g (by simp))]

abbrev Zam (R : Type) := R → Bool

def inv {R} (a : Zam R) : Zam R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Zam R) : Zam R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Zb0 {R} (d : Nat) (a b : Zam R) : Zam R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def ZaT {R} (a : Zam R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def Za9 {R} (a : Zam R) : Nat := by
  classical exact if ZaT a then 1 else 0

noncomputable def Zbr {R} (xs : List (Zam R)) : Nat := (xs.map Za9).sum

def ZaB {R} (u : Bool) (pool : List (Zam R)) (v : Zam R) : Prop :=
  v ∈ pool ∨ ZaT v ∨ (u=true ∧ inv v ∈ pool)

def Zdf {R} (u : Bool) (pool xs : List (Zam R)) := ∀ a ∈ xs, ZaB u pool a

def ZaC {R} (u : Bool) (roots : List (Zam R)) : Nat → List (Zam R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Zam R)) (a b : Zam R), ZaC u roots p bank ∧ ZaB u bank a ∧
      ZaB u bank b ∧ c=combine op a b :: bank
theorem ZaC.start {R u} {roots : List (Zam R)} : ZaC u roots 0 roots := rfl
theorem ZaC.two {R u} {roots : List (Zam R)} {p bank a b} (op : Bool) (h : ZaC u roots p bank)
    (ha : ZaB u bank a) (hb : ZaB u bank b) : ZaC u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem ZaC.ind {R u} {roots : List (Zam R)} {motive : ∀ p bank, ZaC u roots p bank → Prop}
    (start : motive 0 roots ZaC.start)
    (two : ∀ {p bank a b} (op : Bool) (h : ZaC u roots p bank) (ha : ZaB u bank a)
      (hb : ZaB u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (ZaC.two op h ha hb))
    {p bank} (h : ZaC u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Zam R) : Nat → List (Zam R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Zam R) (rest : List (Zam R)), Zbi u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (Zb0 op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Zam R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Zam R} {s : Nat} {xs zs : List (Zam R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Zam R} {s : Nat} {a b : Zam R} {rest : List (Zam R)} (op : Nat) (hd : Zbi u op) (ka kb : Bool)
    (h : Run u goal s (Zb0 op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Zam R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : Zbi u op) (ka kb : Bool) (h : Run u goal s (Zb0 op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem Zdt {R} (a : Zam R) (xs) : Zbr (a::xs)=Za9 a + Zbr xs := by
  simp [Zbr]

theorem Zhq {R} (a : Zam R) (xs) (k : Bool) : Zbr xs ≤ Zbr (kept k a xs) := by
  cases k <;> simp [kept,Zdt]

theorem Ze5 {R} {a : Zam R} (h : ZaT a) : ZaT (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Zam R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem ZhA {R} (a : Zam R) : Za9 (inv a)=Za9 a := by
  have : ZaT (inv a) ↔ ZaT a := ⟨fun h => inv_inv' a ▸ Ze5 h,Ze5⟩
  by_cases h : ZaT a
  · simp only [Za9,if_pos h,if_pos (this.mpr h)]
  · simp only [Za9,if_neg h,if_neg (fun x => h (this.mp x))]
theorem Zfl {R u} {bank : List (Zam R)} {a} (hu : u=true) (h : ZaB u bank a) : ZaB u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (Ze5 h))
  · exact Or.inl h
theorem ZiQ {R} {a b : Zam R} (op) (h : ZaT a) (g : ZaT b) :
    ZaT (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem ZiU {R u} (op) {a b : Zam R} {bank}
    (h : ZaT a ∨ ZaT b) (ha : ZaB u bank a) (hb : ZaB u bank b) :
    ZaB u bank (combine op a b) := by
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

theorem ZfU {R u} {bank v} (w : Zam R) (h : ZaB u bank v) :
    ZaB u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem ZkO {R u} (roots : List (Zam R)) {p bank a b} (op) (hp : ZaC u roots p bank)
    (ha : ZaB u bank a) (hb : ZaB u bank b) :
    ∃ q next, ZaC u roots q next ∧ ZaB u next (combine op a b) ∧
        (∀ v, ZaB u bank v → ZaB u next v) ∧
        q+Za9 a+Za9 b ≤ p+1+Za9 (combine op a b) := by
  classical
  by_cases c : ZaT a ∨ ZaT b
  · refine ⟨p,bank,hp,ZiU op c ha hb,fun _ h => h,?_⟩
    by_cases ca : ZaT a <;> by_cases cb : ZaT b
    · simp [Za9,ca,cb,ZiQ op ca cb]
    · simp [Za9,ca,cb]
    · simp [Za9,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬ZaT a := fun h => c (Or.inl h)
    have cb : ¬ZaT b := fun h => c (Or.inr h)
    exact ⟨p+1,_,ZaC.two op hp ha hb,Or.inl (by simp),fun _ h => ZfU _ h,
      by simp [Za9,ca,cb]⟩
theorem Zgn {R u} {bank : List (Zam R)} {d a b} (hd : Zbi u d) (ha : ZaB u bank a) (hb : ZaB u bank b) :
    ∃ op x y, Zb0 d a b=combine op x y ∧ ZaB u bank x ∧ ZaB u bank y ∧ Za9 x=Za9 a ∧ Za9 y=Za9 b := by
  rcases Zca hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,Zfl hu hb,rfl,ZhA b⟩
  · exact ⟨false,inv a,b,rfl,Zfl hu ha,hb,ZhA a,rfl⟩
theorem ZjF {R u} (roots : List (Zam R)) {p bank a b} (d) (hd : Zbi u d) (hp : ZaC u roots p bank)
    (ha : ZaB u bank a) (hb : ZaB u bank b) :
    ∃ q next, ZaC u roots q next ∧ ZaB u next (Zb0 d a b) ∧
        (∀ v, ZaB u bank v → ZaB u next v) ∧
        q+Za9 a+Za9 b ≤ p+1+Za9 (Zb0 d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := Zgn hd ha hb
  rw [e,←cx,←cy]
  exact ZkO roots op hp hx hy

theorem ZhK {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Zam R} (nc : ¬ZaT goal) {s ws}
    (h : Run u goal s ws) (roots : List (Zam R)) {p bank}
    (hp : ZaC u roots p bank) (hs : Zdf u bank ws) :
    ∃ q next, ZaC u roots q next ∧ ZaB u next goal ∧ q+Zbr ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [Zbr,Za9,nc]⟩
  | perm eq _ ih =>
    have hsub : Zdf u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [Zbr,←(eq.map Za9).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := ZjF roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : Zdf u T (Zb0 op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases ZhK hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (ZhK hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := Zhq a (kept kb b rest) ka
    have hlen' := Zhq b rest kb
    rw [Zdt] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [Zdt,Zdt]
    omega

def ZaG {R S : Type} (rows : S → R) (a : Zam R) : Zam S :=
  fun r => a (rows r)

theorem ZiW {R S : Type} (rows : S → R) (k : Bool) (a : Zam R) (ws) :
    (kept k a ws).map (ZaG rows) =
    kept k (ZaG rows a) (ws.map (ZaG rows)) := by
  cases k <;> simp [kept]

theorem Zf4 {R S : Type} (rows : S → R) (d) (a b : Zam R) :
    ZaG rows (Zb0 d a b) = Zb0 d (ZaG rows a) (ZaG rows b) := by
  unfold Zb0
  split_ifs <;> rfl
theorem Zjf {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (ZaG rows goal) s (ws.map (ZaG rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,ZiW,Zf4] at ih ⊢
    exact Run.two op hd ka kb ih

theorem ZeU {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬ZaT (ZaG rows goal)) {roots : List (Zam S)} {p bank L}
    (hp : ZaC u roots p bank) (hs : Zdf u bank (ws.map (ZaG rows)))
    (hl : ∀ q bs, ZaC u roots q bs → ZaB u bs (ZaG rows goal) → L ≤ q) :
    L + Zbr (ws.map (ZaG rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (Zjf rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Zam Row := fun r => bit r a
def table (f : Zam Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem ZcJ (f : Zam Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem Ze2 (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact ZcJ (observe v) ⟨j,hj⟩

theorem ZiV (f : Zam Row) : observe (table f) = f := by
  funext r
  exact ZcJ f r

theorem Zh0 (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact Zc8 _ _

theorem ZhZ (d : Nat) (a b : Sig) :
    observe (bin d a b) = Zb0 d (observe a) (observe b) := by
  funext r
  simp only [observe,ZcN,Zb0]
  split_ifs <;> rfl

theorem ZhJ {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem ZeH {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem Zeq (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem ZfB {u} {T : Sig} {k S} (h : Zav u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Zav.ind generalizing v with
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
    have bm := ZeH kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := ZeH ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [Zeq,Zeq,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,ZhJ,ZhJ,ZhZ] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem Znw (f : Zam Row) : table (inv f) = neg (table f) := by
  rw [←Ze2 (neg (table f)),Zh0,ZiV]

theorem Zj8 (d : Bool) (f g : Zam Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply ZbI
  intro r
  rw [ZcJ,Zdr,ZcJ,ZcJ]
  cases d <;> rfl

theorem ZeY {u} {bank : List (Zam Row)} {a} (h : ZaB u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply ZdK
    cases b
    · exact Or.inl (ZbI fun i => (ZcJ _ i).trans (bit_zero i).symm)
    · exact Or.inr (ZbI fun i => (ZcJ _ i).trans (bit_one i).symm)
  · have := Znw a
    refine Or.inl ?_
    rw [←ZhY,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem ZiK {u} {roots : List (Zam Row)} {p bank}
    (h : ZaC u roots p bank) {T k S} (run : Zav u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Zav u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using ZaC.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,Zj8] at sub
    have rep := Zht d (ZeY ha) (ZeY hb)
    obtain ⟨k',S',hk,run',sub'⟩ := Zhu (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def Zbt (a : Sig) : Bool := !(bit 0 a)
theorem ZhX {u} {w : List Sig} (h : w.all Zbt=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact ZfM (by simpa [Zbt] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem Zee {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : Zbt T=true) (nR : roots.all Zbt=true)
    (h : ZaC u (roots.map observe) p bank) (hit : ZaB u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Zav u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := ZeY hit
  rw [Ze2] at hm
  unfold Repr at hm
  rw [ZfM (by simpa [Zbt] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := ZiK h (Zav.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,Ze2]
  rw [e,ZhX nR] at hs
  exact hs

theorem ZfP {u T k S} (h : Zav u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Zav.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [ZcN,ZcN,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem ZdG {u T k S} (h : Zav u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := ZfP h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem ZkN : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem Zf8 : proper graph := by unfold proper; decide +kernel
theorem Zfg : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem ZrP (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←Zfg]
  rw [List.map_ofFn]
  rfl

theorem ZlJ (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((Zda C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←Zig,Zi5 _ _ _ (fun g hg => (h g hg).1),ZrP]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem ZcF (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := ZcJ _ _
theorem ZdC (f : Row → Row) (a : Sig) :
    observe (rename f a) = ZaG f (observe a) := by funext r; exact ZcF f a r
theorem ZgR (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply ZbI
  intro r
  simp only [ZcF,ZcN]

theorem Zlh (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [ZcF,ZcF,hr] at he
  exact he
theorem ZfR (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (ZcF f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (ZcF f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem ZjP {u T k S} (h : Zav u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Zav u (rename f T) k (S.image (rename f)) := by
  have inj := Zlh f onto
  obtain ⟨fz,fo⟩ := ZfR f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Zav.ind with
  | stop hp => simpa using Zav.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,ZgR] at fresh ih ⊢
    exact Zav.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem Zir {u T k S} (h : Zav u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Zav.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [ZcN] at hp hn
      subst none
      rcases Zca hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Zaf (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, ZaC u (roots.map observe) p bank → ZaB u bank (observe T) → L ≤ p
theorem Zqn {R u} {roots : List (Zam R)} {p bank} (h : ZaC false roots p bank) : ZaC u roots p bank := by
  have up {bank : List (Zam R)} {a} (h : ZaB false bank a) : ZaB u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using ZaC.ind with
  | start => exact ZaC.start
  | two op h ha hb ih => exact ZaC.two op ih (up ha) (up hb)
theorem Zlb {u roots T L} (h : Zaf true roots T L) : Zaf u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (Zqn hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Zax (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Zav u T k S

def Zeh (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem ZfQ {u roots T L} (hp : proper T) (nT : Zbt T=true) (nR : roots.all Zbt=true)
    (essential : ∀ a ∈ roots, Zeh T roots a)
    (noRun : Zax u T L roots.toFinset) : Zaf u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := Zee hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact ZdG run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem ZeX {v : Sig} (hv : proper v) : ¬ZaT (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply ZdK
    cases b
    · exact Or.inl (ZbI fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (ZbI fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : Zcb [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem ZjS {R} (a b : List (Zam R)) : Zbr (a++b) = Zbr a + Zbr b := by
  simp [Zbr]
theorem ZiJ {R} (xs : List (Zam R)) (hc : ∀ x ∈ xs, ZaT x) :
    Zbr xs = xs.length := by
  induction xs with
  | nil => simp [Zbr]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [Zdt,List.length_cons,Za9,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem Zgh {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : Zbt T=true) (nR : roots.all Zbt=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, ZaB u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Zeh T roots a)
    (constant : ∀ a ∈ singles, ZaT (observe (rename r a)))
    (L : Nat) (prior : Zaf u other G L) : Zaf u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := Zee pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact ZdG run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := ZfB run front nd fe
  have gc : ZaG r (observe T) = observe G := (ZdC _ _).symm.trans (congrArg observe eq)
  have supp : Zdf u (other.map observe) ((front.map observe).map (ZaG r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←ZdC]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := ZeU r run' (gc ▸ ZeX pG) ZaC.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ Zbr ((front.map observe).map (ZaG r)) := by
    simp only [front,List.map_append,ZjS]
    let xs := (singles.toList.map observe).map (ZaG r)
    have only : ∀ v ∈ xs, ZaT v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←ZdC]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := ZiJ xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ Zbr xs + _
    rw [sz]
    omega
  omega



def Zb5 (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem ZgZ {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem ZmW {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, Zbi u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (Zb5 ws a b d ka kb).length ≤ cap →
      Zax u T (cap-1) (Zb5 ws a b d ka kb).toFinset) :
    Zax u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Zav.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := Zgg tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,ZgZ (hn.erase _) b,
        ZgZ hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [Zeq,Zeq,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := ZeH kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (Zb5 ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,ZeH ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (Zb5 ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := Zfs tail
    have len : (Zb5 ws a b d ka kb).length ≤ cap := by
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

theorem ZjC {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem ZjB {u T k S} (h : Zav u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (ZjC (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := ZfP h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := Zir h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem ZiG {u T ws k} (h : Zav u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply ZjB h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, ZaB u (roots.map observe) (ZaG f (observe a))) ∧
    ¬ZaT (ZaG f (observe T)) ∧
    ∀ p bank, ZaC u (roots.map observe) p bank → ZaB u bank (ZaG f (observe T)) → L ≤ p

def ZaP (d a : Sig) := a &&& d
def ZaW (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := ZaP d a
  m == zero || m == d || (pool.map (ZaP d)).any (fun v => v==m) ||
    (u && (let c := ZaP d (neg a); (pool.map (ZaP d)).any (fun v => v==c)))

theorem Zhp {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaP d a = ZaP d b) :
    ZaG f (observe a) = ZaG f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,ZaP,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem Zgi {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaP d a = zero) : ZaG f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,ZaP,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem ZgM {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : ZaP d a = d) : ZaG f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,ZaP,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def ZcY (u : Bool) (f : Row → Row) (bank : List (Zam Row)) (pool : List Sig) :=
  ∀ a ∈ pool, ZaB u bank (ZaG f (observe a))

theorem Zdk {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : ZcY u f bank pool)
    (check : ZaW u d pool a = true) : ZaB u bank (ZaG f (observe a)) := by
  simp only [ZaW,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,Zgi dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,ZgM dom ho⟩)
  · exact Zhp dom he ▸ supplyB v hv
  · have h := Zfl hu (Zhp dom he ▸ supplyB v hv)
    rw [Zh0] at h
    have e : inv (ZaG f (inv (observe a))) = ZaG f (observe a) := by
      funext r
      simp [inv,ZaG]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def Zbg (c : Choice) := bin c.1 c.2.1 c.2.2
def Zdv (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem Zjq {u d} (h : Zdv u d=true) : Zbi u d := by
  simpa [Zdv,Zbi] using h
def Zc2 (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  Zdv u c.1 && (ZaW u d pool c.2.1 && ZaW u d pool c.2.2)

theorem ZgQ {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : ZaC u roots q bank) (hs : ZcY u f bank pool)
    (c : Choice) (valid : Zc2 u d pool c = true) :
    ∃ next, ZaC u roots (q+1) next ∧ ZcY u f next (Zbg c :: pool) := by
  simp only [Zc2,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := Zgn (Zjq valid.1) (Zdk dom hs valid.2.1)
    (Zdk dom hs valid.2.2)
  refine ⟨_,ZaC.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [Zbg,ZhZ,Zf4,e]
    exact Or.inl (by simp)
  · exact ZfU _ (hs _ hm)

def Zc5 (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if Zc2 u d pool c then Zc5 u d (Zbg c::pool) cs else none

theorem ZfV {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : ZaC u roots q bank) (hs : ZcY u f bank pool)
    (cs : List Choice) {result} (ok : Zc5 u d pool cs = some result) :
    ∃ next, ZaC u roots (q+cs.length) next ∧ ZcY u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [Zc5] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := ZgQ dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def ZaU (d a : Sig) := ZaP d a == zero || ZaP d a == d
theorem ZfS {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (ZaU d) ≤ Zbr ((ws.map observe).map (ZaG f)) := by
  classical
  induction ws with
  | nil => simp [Zbr]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,Zdt]
    cases h : ZaU d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : ZaT (ZaG f (observe a)) := by
        have hh : ZaP d a = zero ∨ ZaP d a = d := by simpa only [ZaU,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,Zgi dom hz⟩
        · exact ⟨true,ZgM dom ho⟩
      simpa [Za9,hc,Nat.add_comm] using Nat.succ_le_succ ih

def ZeN (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (ZaU d)) && ws.all (ZaW u d pool)

theorem Zf3 {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : Zc5 u d raw cs = some pool)
    (nd : ws.Nodup) (cut : ZeN u d L cap cs.length pool ws = true) :
    Zax u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := ZfV dom (ZaC.start (roots:=roots.map observe)) base cs built
  simp only [ZeN,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : Zdf u bank ((ws.map observe).map (ZaG f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact Zdk dom hs (List.all_eq_true.mp all a ha)
  have b := ZeU f (ZfB h ws nd rfl) nc hr coveredS lo
  have massLo := ZfS dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev ZbJ := Sig × Sig × Row
def ZeO (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def ZgU (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def ZfI (m : ZbJ) (r : Row) : Row :=
  if bit r m.1 then ZeO m.2.2 r else if bit r m.2.1 then ZeO (ZgU m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def ZdV (m : ZbJ) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (ZgU m.2.2).val) a)

theorem ZmS (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (ZeO d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [ZeO,h,r.isLt]

theorem Zou (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem ZqW (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact Zou _ _ _

theorem Zot (r : Row) (m : ZbJ) (a : Sig) : bit r (ZdV m a) = bit (ZfI m r) a := by
  simp only [ZdV,ZqW,ZmS,ZfI]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def ZbF (ms : List ZbJ) (r : Row) := ms.foldl (fun j m => ZfI m j) r
def ZaS (ms : List ZbJ) (a : Sig) := ms.foldr ZdV a
theorem ZdN (ms : List ZbJ) (a : Sig) (r : Row) :
    bit r (ZaS ms a) = bit (ZbF ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (Zot r m _).trans (ih _)
theorem ZcU (ms : List ZbJ) (a : Sig) : ZaS ms a = rename (ZbF ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (ZdN ms a ⟨j,hj⟩).trans (ZcF _ _ ⟨j,hj⟩).symm

def Zfy (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem ZjG {u roots w} (ok : Zfy roots w = true) :
    ZaB u (roots.map observe) (observe w) := by
  simp only [Zfy,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def ZcL (ms : List ZbJ) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  ZaS ms T == G && raw.all (fun a => Zfy base (ZaS ms a))

theorem Ze8 {u ms raw T base G} (ok : ZcL ms raw T base G = true) :
    rename (ZbF ms) T = G ∧
    ∀ a ∈ raw, ZaB u (base.map observe) (observe (rename (ZbF ms) a)) := by
  simp only [ZcL,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,ZcU] at ok
  exact ⟨ok.1,fun a ha => ZjG (ok.2 a ha)⟩

theorem Zm8 {u ms raw T base G L} (ok : ZcL ms raw T base G = true)
    (pT : proper T) (nT : Zbt T=true) (nR : raw.all Zbt=true) (pG : proper G)
    (hL : Zaf u base G L) : Zaf u raw T L := by
  obtain ⟨eq,supp⟩ := Ze8 ok
  simpa using Zgh pT nT nR pG (ZbF ms) eq supp ∅ (by simp) (by simp) L hL

theorem ZiX {u ms raw T base G L d} (ok : ZcL ms raw T base G = true)
    (all : ZaS ms d = one) (properG : proper G) (hL : Zaf u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := Ze8 ok
  have obs : ZaG (ZbF ms) (observe T) = observe G :=
    (ZdC _ _).symm.trans (congrArg observe eq)
  refine ⟨ZbF ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←ZdN,all,bit_one]
  · intro a ha
    rw [←ZdC]
    exact supp a ha
  · rw [obs]
    exact ZeX properG
  · rw [obs]
    exact hL

def ZfD (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem ZiP {T roots a rs} (ok : ZfD T roots a rs = true) : Zeh T roots a := by
  simp only [ZfD,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def Zb9 (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  Zbt T && raw.all Zbt && xs.all (fun a => ZfD T raw a.1 a.2)
theorem ZdF {T raw xs} (ok : Zb9 T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Zeh T raw a := by
  simp only [Zb9,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ZiP (List.all_eq_true.mp ok.2 _ hm)

theorem Zb8 {T raw xs} (ok : Zb9 T raw xs = true) :
    Zbt T=true ∧ raw.all Zbt=true := by
  simp only [Zb9,Bool.and_eq_true] at ok
  exact ok.1
theorem ZjQ {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : Zb9 T raw xs = true) :
    Zaf u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := Zee properT (Zb8 ok).1 (Zb8 ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := ZdF ok a ha
    exact ZdG run raw a sub r s hd iso
  have bound := Zfs run
  omega

def Zfn (ms : List ZbJ) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  ZcL ms raw T base G && Zb9 T raw xs &&
    xs.all (fun a => ZaS ms a.1 == zero || ZaS ms a.1 == one)

theorem Zrp {u ms T raw base G xs L} (ok : Zfn ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Zaf u base G L) :
    Zaf u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [Zfn,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := Ze8 ok.1.1
  apply Zgh properT (Zb8 ok.1.2).1 (Zb8 ok.1.2).2 properG _ eq supp _ (ZdF ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,ZcU] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def Zci (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (Zci m).map Prod.snd
def ZeB (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def Zag (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [ZeB (m/512-1)]
def Zd3 (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def Zac (m : Nat) : Sig :=
  let x := Zd3 m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def Zug : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def Zuh : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def Zui : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def Zde (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((Zug (fixed &&& 7)*Zuh ((fixed >>> 3) &&& 7)*Zui ((fixed >>> 6) &&& 7)) <<< o)
def ZfF (z o : Nat) : List ZbJ :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : ZbJ :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def Zga (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (Zci mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def Zff (m hints : Nat) : List (Sig × Row × Row) :=
  (Zci m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def ZbC (T : Sig) := T != zero && T != one
theorem Zcg (T : Sig) (h : ZbC T = true) : proper T := by
  simpa only [ZbC,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev Za7 := Nat × Nat × Nat × Nat × Nat
def ZfE (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def ZcK (m : Nat) : Sig := Zac m
def Zdc (m : Nat) (c : Za7) : Nat := m % 512+512*(c.1/512)
def ZdS (m : Nat) (c : Za7) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := ZfF z o
  let raw := Zdc m c
  let free := ZfE raw (z % 512) o
  let G := ZaS ms (ZcK m)
  let xs := Zga (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  ZbC G && ZcL ms (Zag raw) (ZcK m) (Zag free) G &&
    (ZaS ms (Zde z o)==one) &&
    (if q=0 then Zb9 G (Zag free) xs && decide (L ≤ count-1)
     else ZbC (Zac q) &&
       Zfn (ZfF (ZfE free q 0) 0) G (Zag free) (Zag q) (Zac q) xs &&
       decide (L ≤ prior q+count))

theorem ZdO {u} {m : Nat} (c : Za7) (prior : Nat → Nat)
    (valid : ∀ q, Zaf u (Zag q) (Zac q) (prior q))
    (ok : ZdS m c prior = true) : Slice u (Zag (Zdc m c)) (ZcK m) (Zde c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := ZfF z o
  let raw := Zdc m (z,o,q,s,L)
  let free := ZfE raw (z % 512) o
  let G := ZaS ms (ZcK m)
  let xs := Zga (z/512+80) s
  change (((ZbC G && ZcL ms (Zag raw) (ZcK m) (Zag free) G) &&
    (ZaS ms (Zde z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply ZiX ok.1.1.2 ok.1.2 (Zcg _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [ZdS,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ZjQ (Zcg _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [ZdS,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (Zrp hh.1.2 (Zcg _ ok.1.1.1) (Zcg _ hh.1.1) (valid q) p bank hr ha)

def ZeF (old rep : Nat) (swaps : List Nat) :=
  (ZbC (Zac old) && Zbt (Zac old) && (Zag old).all Zbt) && ZbC (Zac rep) &&
    ZcL (swaps.map swapRows) (Zag old) (Zac old) (Zag rep) (Zac rep)
theorem Zhz {u old rep L swaps} (ok : ZeF old rep swaps = true)
    (h : Zaf u (Zag rep) (Zac rep) L) : Zaf u (Zag old) (Zac old) L := by
  simp only [ZeF,Bool.and_eq_true] at ok
  exact Zm8 ok.2 (Zcg _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (Zcg _ ok.1.2) h

def Zat (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem Zai {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Zaf u (Zag e.1) (Zac e.1) e.2) (q : Nat) :
    Zaf u (Zag q) (Zac q) (Zat entries q) := by
  unfold Zat
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev Zbl := Sig × Nat × Nat × List Sig
def Zbl.domain (c : Zbl) : Sig := c.1
def Zbl.bound (c : Zbl) : Nat := c.2.1
def Zbl.ZaO (c : Zbl) : Nat := c.2.2.1
def Zbl.wires (c : Zbl) : List Sig := c.2.2.2

def ZcI (u : Bool) (raw : List Sig) (T : Sig) (c : Zbl) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Zam Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬ZaT (ZaG f (observe T)) ∧
    (∀ q ws, ZaC u (roots.map observe) q ws → ZaB u ws (ZaG f (observe T)) → c.bound ≤ q) ∧
    ZaC u (roots.map observe) c.ZaO bank ∧ ZcY u f bank c.wires ∧ True

theorem Zjr {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : Zc5 u d raw cs = some ws) : ZcI u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := ZfV dom (ZaC.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [Zbl.ZaO] using hr,hs,trivial⟩

theorem ZiZ {u raw T c} (valid : ZcI u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (ZaO : Bool)
    (known : ∀ a ∈ rest, ZaW u c.domain c.wires a = true)
    (buy : if ZaO then Zc2 u c.domain c.wires choice = true
       else ZaW u c.domain c.wires (Zbg choice) = true)
    (bound : k+c.ZaO+ZaO.toNat <
      c.bound+(Zbg choice :: rest).countP (ZaU c.domain))
    (nd : (Zbg choice :: rest).Nodup) :
    Zax u T k (Zbg choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := Zbg choice::rest
  have done (n : Nat) (out : List (Zam Row)) (reach : ZaC u (roots.map observe) n out)
      (zs : ZcY u f out (Zbg choice::rest)) (le : n = c.ZaO+ZaO.toNat) : False := by
    have covered : Zdf u out ((ws.map observe).map (ZaG f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := ZeU f (ZfB run ws nd rfl) nc reach covered lo
    have cm := ZfS dom ws
    change k+c.ZaO+ZaO.toNat < c.bound+ws.countP (ZaU c.domain) at bound
    omega
  cases ZaO with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact Zdk dom hs buy
    · exact Zdk dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := ZgQ dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, ZaB u out (ZaG f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact Zdk dom point (known _ hm)

def ZcB (u : Bool) (c : Zbl) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := Zbg op
  let extra := !(ZaW u c.domain c.wires z)
  ((k+c.ZaO+extra.toNat < c.bound+(z::rest).countP (ZaU c.domain)) &&
    rest.all (ZaW u c.domain c.wires)) && (!extra || Zc2 u c.domain c.wires op)

theorem Zis {u raw T c} (valid : ZcI u raw T c) {k rest op}
    (nd : (Zbg op::rest).Nodup) (cut : ZcB u c k rest op = true) :
    Zax u T k (Zbg op::rest).toFinset := by
  let extra := !(ZaW u c.domain c.wires (Zbg op))
  apply ZiZ valid k rest op extra _ _ _ nd
  · simp only [ZcB,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [ZcB,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : ZaW u c.domain c.wires (Zbg op) <;> simp_all [extra]
  · simp only [ZcB,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def Ze9 (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option Zbl :=
  (Zc5 u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem Ziv {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : Ze9 u raw cs d L = some c) : ZcI u raw T c := by
  unfold Ze9 at h
  cases he : Zc5 u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact Zjr slice cs he


abbrev Bits := BitVec 152
abbrev ZeE := Bits × Bits
abbrev Zae := Sig × ZeE

def Zb7 {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem Zcs {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (Zb7 r v).getLsbD i.val = bit (r i) v := by
  simp only [Zb7,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def Zcj (r s : Fin 152 → Row) (a : Sig) : ZeE := (Zb7 r a,Zb7 s a)
def ZdI (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem Zql {T r s} (h : ZdI T r s) : Sep T 152 r s (Zcj r s) := by
  exact ⟨h,fun a i => ⟨Zcs _ _ _,Zcs _ _ _⟩⟩
def ZbH (r s : Fin 152 → Row) (x : Zae) := x.2 = Zcj r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def Zbp (d : Nat) (x y : Zae) : Zae := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem Zld {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    Zb7 r (bin d a b) = bv d (Zb7 r a) (Zb7 r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := Zcs r (bin d a b) ⟨j,hj⟩
  rw [ZcN,←Zcs r a ⟨j,hj⟩,←Zcs r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem Zf5 {r s x y} (d) (hx : ZbH r s x) (hy : ZbH r s y) :
    ZbH r s (Zbp d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [ZbH,Zbp,Zcj,Zld,hx,hy]

def Zbx : Zae := (zero,0,0)
theorem Zix (r s) : ZbH r s Zbx := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (Zb7 r zero).getLsbD j
    rw [show (Zb7 r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from Zcs _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (Zb7 s zero).getLsbD j
    rw [show (Zb7 s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from Zcs _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem Zf6 {r s ws} (all : ∀ v ∈ ws, ZbH r s v) (i : Nat) :
    ZbH r s (List.getD ws i Zbx) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact Zix _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def ZdJ (n : Nat) (bits : Nat) (ws : List Zae) : List Zae :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) Zbx
    let b := ws.getD ((bits >>> 4) &&& 15) Zbx
    ZdJ k (bits >>> 10) (ws++[Zbp ((bits >>> 8) &&& 3) a b])
theorem ZiC (n bits) (ws) (r s) (base : ∀ v ∈ ws, ZbH r s v) :
    ∀ v ∈ ZdJ n bits ws, ZbH r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact Zf5 _ (Zf6 base _) (Zf6 base _)

def ZbP (ZbG : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (ZbG j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem Zjs : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem Zjt : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem Zju : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem Zjv : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem Zjw : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem Zjx : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem Zjy : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem Zjz : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem ZjA : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem Ze4 : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact Zjs r
  · exact Zjt r
  · exact Zju r
  · exact Zjv r
  · exact Zjw r
  · exact Zjx r
  · exact Zjy r
  · exact Zjz r
  · exact ZjA r
theorem Zfk (ZbG : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (ZbP ZbG i) (inputs.getD j.val zero) = (ZbG j.val).getLsbD i.val := by
  rw [Ze4]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (ZbG h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def Zey (m : Nat) (p q : Nat → Bits) : List Zae :=
  (Zci m).map (fun (j,a) => (a,p j,q j))
theorem ZfX {m j a} (h : (j,a) ∈ Zci m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem Zje (m) (p q : Nat → Bits) :
    ∀ a ∈ Zey m p q, ZbH (ZbP p) (ZbP q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := ZfX hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (Zfk p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (Zcs _ _ ⟨i,hi⟩).symm
  · exact (Zfk q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (Zcs _ _ ⟨i,hi⟩).symm

def ZfA (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem ZkL (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (ZbP v i) (Zd3 m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [Zd3,hh] using Zfk v i j
  · simp [Zd3,hh,bit_zero]
theorem Zi4 (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (ZbP v i) (Zac m) = (ZfA m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (Zd3 m j).getLsbD (ZbP v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := ZkL m v i ⟨j,hj⟩
  simp only [bit,Zac,ZfA,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def ZbO (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def Zbh (d : Bool) (v : List Zae) : Cov :=
  v.foldr (fun a c => ZbO (column d a.2) c) (0,0,0)

def Zcx (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def Zdy (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem ZqX (c : Cov) (a : Bits) : Zcx (ZbO a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Zcx,ZbO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem ZqY (c : Cov) (a b : Bits) : Zdy (ZbO a (ZbO b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Zdy,ZbO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem Zon (c : Cov) (a b : Bits) : ZbO a (ZbO b c)=ZbO b (ZbO a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ZbO,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [ZbO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem ZhB (d : Bool) {l r : List Zae} (h : l.Perm r) : Zbh d l=Zbh d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (ZbO (column d a.2)) ih
  | swap a b t => exact Zon _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem Zow (d : Bool) (v : List Zae) {r s} (good : ∀ a ∈ v, ZbH r s a) :
    (Zbh d v).1 = covered d (Zcj r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (Zbh d v).1) = column d (Zcj r s a.1) ||| _
    rw [show a.2=Zcj r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def ZbY (ws : List Zae) (a : Zae) (keep : Bool) :=
  if keep then ws else ws.erase a
def Zbc (ws : List Zae) (a b : Zae) (ka kb : Bool) :=
  ZbY (ZbY ws a ka) b kb

theorem Ze6 {ws : List Zae} (a : Zae) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem ZgY {ws : List Zae} (d : Bool) (a : Zae) (ha : a ∈ ws) (keep : Bool) :
    (Zbh d (ZbY ws a keep)).1 =
      (if keep then (Zbh d ws).1 else Zcx (Zbh d ws) (column d a.2)) := by
  cases keep
  · change (Zbh d (ws.erase a)).1 = Zcx (Zbh d ws) _
    rw [ZhB d (Ze6 a ha)]
    exact (ZqX _ _).symm
  · rfl
theorem ZjD {ws : List Zae} (a b : Zae) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (Ze6 a ha).trans (List.Perm.cons _ (Ze6 b hm))

theorem ZmU {ws : List Zae} (d : Bool) (a b : Zae) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (Zbh d (Zbc ws a b ka kb)).1 =
      (if ka then (if kb then (Zbh d ws).1 else Zcx (Zbh d ws) (column d b.2))
       else if kb then Zcx (Zbh d ws) (column d a.2)
       else Zdy (Zbh d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (Zbh d ((ws.erase a).erase b)).1 = Zdy (Zbh d ws) _ _
    rw [ZhB d (ZjD a b ha hb ne)]
    exact (ZqY _ _ _).symm
  · exact ZgY d a ha false
  · exact ZgY d b hb false
  · rfl

def Zdu (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem ZeW {xs ys} (h : Zdu xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [Zdu,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def Zb6 (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def Zd0 (xs : List Sig) := xs.foldl (fun v x => v+Zb6 x) 0

def Zdm (u : Bool) (pools : List Zbl) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := Zbg op::rest
  (links (Zd0 ws)).any (Zdu ws) || pools.any (fun p => ZcB u p k rest op)

theorem Ziw {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ZcI u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Zax u T k (List.toFinset xs))
    (nd : (Zbg op :: rest).Nodup)
    (h : Zdm u pools links k rest op = true) :
    Zax u T k (Zbg op :: rest).toFinset := by
  simp only [Zdm,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [ZeW ok]
    exact lValid _ _ hx
  · exact Zis (pValid _ hp) nd ok

abbrev ZhT := Cov × Bool
def Zd2 (u : Bool) (ws : List Zae) : ZhT := (Zbh (!u) ws,u)
def Zdd (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else Zcx v b) else if kb then Zcx v a else Zdy v a b

theorem Zfc (ws : List Zae) (a : Zae) (k : Bool) : (ZbY ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem ZpD (ws : List Zae) (a b : Zae) (ka kb : Bool) :
    (Zbc ws a b ka kb).Sublist ws := (Zfc _ _ _).trans (Zfc _ _ _)
theorem ZpM (ws : List Zae) (a b : Zae) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (Zbc ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [Zbc,ZbY,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def ZbU (op : Nat) (a b : Zae) : Choice := (op,a.1,b.1)

abbrev Zbj := Nat × Nat × List Zae × ZhT × List Zbl × (Nat → List (List Sig))
def ZcM (c : Zbj) (op : Nat) (a b z : Zae) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := Zdd cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !ZbC z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (Zbc ws a b ka kb).map Prod.fst
      Zdm cov.2 pools links (cap-1) rest (ZbU op a b)

def Zft (ws : List Zae) (op : Nat) (a b : Zae) (ka kb : Bool) :=
  (Zbp op a b).1 :: (Zbc ws a b ka kb).map Prod.fst
theorem ZiH {u raw T r s ws pools links cap a b op ka kb}
    (pairs : ZdI T r s) (faith : ∀ w ∈ ws, ZbH r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ZcI u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Zax u T (cap-1) (List.toFinset xs))
    (pro : proper (Zbp op a b).1) (fresh : (Zbp op a b).1 ∉ ws.map Prod.fst)
    (test : ZcM (cap,ws.length,ws,Zd2 u ws,pools,links) op a b (Zbp op a b) ka kb = true) :
    Zax u T (cap-1) (Zft ws op a b ka kb).toFinset := by
  let z := Zbp op a b
  let rest := Zbc ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := ZpD _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : ZbC z.1 = true := by simpa [ZbC,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,ZpM _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := Zfs h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold ZcM at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := ZiG h (Zql pairs)
  let d := !u
  have g : (Zbh d rest).1 = covered d (Zcj r s) (rest.map Prod.fst) :=
    Zow _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (Zbh d rest).1 = Zdd (Zbh d ws) (column d a.2) (column d b.2) ka kb :=
    ZmU d a b ha hb ne ka kb
  have hf := Zf5 op (faith _ ha) (faith _ hb)
  change column d (Zcj r s z.1) ||| covered d (Zcj r s) (rest.map Prod.fst) = _ at sep
  change z.2 = Zcj r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((Zdd (Zbh (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (Zdd (Zbh (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !ZbC z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact Ziw (op:=ZbU op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def Zc7 (ctx : Zbj) (a b : Zae) (op : Nat) :=
  let z := Zbp op a b
  let attempt := ZcM ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def Zdh (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem Zhs {u d} (h : Zbi u d) : d ∈ Zdh u := by
  rcases Zca h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [Zdh]
  · cases u <;> simp [Zdh]
  · simp [Zdh]
  · simp [Zdh]
def ZfJ (ctx : Zbj) (a : Zae) (bs : List Zae) :=
    bs.all (fun b => (Zdh ctx.2.2.2.1.2).all (Zc7 ctx a b))
def Zcy (ctx : Zbj) : List Zae → Bool
  | [] => true
  | a::bs => ZfJ ctx a bs && Zcy ctx bs

theorem ZkG {ctx ws} (h : Zcy ctx ws=true) {a b : Zae} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, Zbi ctx.2.2.2.1.2 d → Zc7 ctx a b d=true) ∨
      (∀ d, Zbi ctx.2.2.2.1.2 d → Zc7 ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [Zcy,Bool.and_eq_true,ZfJ,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (Zhs hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (Zhs hd)
      · exact ih h.2 haTail hbTail

theorem Zj9 {ctx a b d} (h : Zc7 ctx a b d = true) (ka kb : Bool) :
    ZcM ctx d a b (Zbp d a b) ka kb = true := by
  simp only [Zc7,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem ZhH {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem ZgN {v : List Zae} (nd : v.Nodup) (a w : Zae) (k : Bool) :
    w ∈ ZbY v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [ZbY,nd.mem_erase_iff,and_comm]

theorem Zgb {ws : List Zae} (nd : (ws.map Prod.fst).Nodup) {a b : Zae}
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

theorem Zgq {ws : List Zae} (nd : (ws.map Prod.fst).Nodup) {a b : Zae}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (Zbc ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (Zfc ws a ka)
  simp only [Zbc,List.mem_map,ZgN wn,ZgN dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (Zgb nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (Zgb nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem Zi3 {ws : List Zae} (nd : (ws.map Prod.fst).Nodup) {a b : Zae}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (Zft ws d a b ka kb).toFinset =
      (Zb5 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [Zft,Zb5,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    Zgq nd ha hb,ZhH,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,Zbp]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem ZiR {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : Zbi u d) (ka kb : Bool) :
    (Zb5 v a b d ka kb).toFinset = (Zb5 v b a (ZcQ d) kb ka).toFinset := by
  ext x
  simp only [Zb5,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    ZhH,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,Zfv hd a b]
  tauto

theorem Zlc {u raw T r s ws pools links cap}
    (pairs : ZdI T r s) (faith : ∀ w ∈ ws, ZbH r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ZcI u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Zax u T (cap-1) (List.toFinset xs))
    (checks : Zcy (cap,ws.length,ws,Zd2 u ws,pools,links) ws = true) :
    Zax u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply ZmW nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Zae) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : Zc7 (cap,ws.length,ws,Zd2 u ws,pools,links) a b d = true) :
      Zax u T (cap-1) (Zb5 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←Zi3 nd aa bb ne']
    exact ZiH pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (Zj9 test ka kb)
  rcases ZkG checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [ZiR _ nd _ _ d hd]
    exact one b a (ZcQ d) hbW haW (Ne.symm ne) kb ka (Zfv hd a.1 b.1 ▸ pro)
      (Zfv hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem Zi0 (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← Zfg]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (Ze4 i r).symm.trans ((h _ hm).trans (Ze4 i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def Zfb (p q : List ZbJ) := inputs.all (fun a => ZaS p (ZaS q a) == a)
theorem Zgd {p q} (h : Zfb p q = true) (r : Row) :
    ZbF q (ZbF p r) = r := by
  apply Zi0
  intro a ha
  rw [←ZdN,←ZdN]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def ZdZ (T : Sig) (p : List ZbJ) :=
  (ZaS p T == T) && Zfb p p.reverse && Zfb p.reverse p
theorem ZiF {u T n} {ws : List Sig} (hi : Zax u T n ws.toFinset)
    (p : List ZbJ) (ok : ZdZ T p = true) : Zax u T n (ws.map (ZaS p.reverse)).toFinset := by
  simp only [ZdZ,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (ZbF p) := fun r => ⟨ZbF p.reverse r,Zgd ok.2 r⟩
  intro k hk h
  have run := ZjP h (ZbF p) onto
  have goal : rename (ZbF p) T = T := (ZcU p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (ZbF p) (ZaS p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [ZcF,ZdN,Zgd ok.1.2]
  have back : (ws.map (ZaS p.reverse)).toFinset.image (rename (ZbF p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Zah := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def Zbs : Zah := (0,0,0,0,0,0,0,fun _ => 0)
def Za3 (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def ZaH (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := Za3 data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := Za3 data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


def ZbT (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := Za3 data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := Za3 data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Zaj := Nat × Nat × (Nat → Bits × Bits) × List Za7 × List (List Nat) ×
  (Nat → Zah) × (Nat → Nat → Option (Nat × Nat))
def Zaj.mask (g : Zaj) : Nat := g.1
def Zaj.mode (g : Zaj) : Bool := !(g.1.testBit 10)
def Zaj.cap (g : Zaj) : Nat := g.2.1
def Zaj.ZbX (g : Zaj) : Nat → Bits × Bits := g.2.2.1
def Zaj.ZbG (g : Zaj) : List Za7 := g.2.2.2.1
def Zaj.Zdg (g : Zaj) : List (List Nat) := g.2.2.2.2.1
def Zaj.levels (g : Zaj) : Nat → Zah := g.2.2.2.2.2.1
def Zaj.index (g : Zaj) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def ZcP (g : Zaj) :=
  let ws := Zey g.mask (fun j => (g.ZbX j).1) (fun j => (g.ZbX j).2)
  ws
theorem ZiO (g : Zaj) : ∀ a ∈ ZcP g,
    ZbH (ZbP fun j => (g.ZbX j).1) (ZbP fun j => (g.ZbX j).2) a := by
  exact Zje g.mask (fun j => (g.ZbX j).1) (fun j => (g.ZbX j).2)

def ZaN (g : Zaj) := ZcK g.mask
def ZdE (m : Nat) (v : Nat → Bits) :=
  ZfA m v
theorem ZmT (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (ZbP v i) (ZcK m) = (ZdE m v).getLsbD i.val := by
  exact Zi4 m v i
theorem Zeb {m : Nat} {p q : Nat → Bits}
    (hp : ZdE m p = BitVec.allOnes 152) (hq : ZdE m q = 0) :
    ZdI (ZcK m) (ZbP p) (ZbP q) := by
  intro i
  simp only [ZmT,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def Zcd {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::Zcd (bits >>> 1) ws else Zcd (bits >>> 1) ws
theorem ZiM {α : Type} (bits : Nat) (ws : List α) : (Zcd bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold Zcd
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def ZdH (d : Nat) := 10*(d-1)
def Zf0 (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def ZfZ (d raw dict : Nat) :=
  (dict % 65536)*ZdH d + (dict/65536)*(raw+d)

def Zf7 (tab : Zah) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then Za3 word (i*width) width else
    let off := ZfZ d raw dict+i*Zf0 d flags
    let pre := Za3 word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := Za3 word (off+flags % 16) lastBits
    let mask := Za3 word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*ZdH d
    Za3 word (pre*ZdH d) (ZdH d) |||
      (last <<< ZdH d) ||| (Za3 word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def Zgl (_g : Zaj) (depth : Nat) := depth
def Zez (g : Zaj) (k i : Nat) : Nat × List Zae × List Zae :=
  let raw := ZcP g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*Zgl g depth
  let width := len+raw.length+depth
  let recp := Zf7 (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := ZdJ depth ops raw
  (ops,bank,Zcd (recp >>> len) bank)

def Zg3 (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def Zgc (bank : List Zae) (ops ZaO : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := Zgc bank (ops >>> 10) (ZaO >>> 1) n
    if ZaO &&& 1 == 0 then more else
      (Zg3 ops 8 2,(bank.getD (ops &&& 15) Zbx).1,
        (bank.getD (Zg3 ops 4 4) Zbx).1) :: more

def buildRule (g : Zaj) (ops d : Nat) (bank : List Zae) (idx ZaO : Nat) : Option Zbl :=
  (g.ZbG[idx]?).bind fun ci =>
    Ze9 g.mode (Zag (Zdc g.mask ci)) (Zgc bank ops ZaO d) (Zde ci.1 ci.2.1) ci.2.2.2.2

theorem ZiB (g : Zaj)
    (ZbG : ∀ ci ∈ g.ZbG, Slice g.mode (Zag (Zdc g.mask ci)) (ZaN g) (Zde ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank ZaO c} (h : buildRule g ops depth bank i ZaO = some c) :
    ZcI g.mode (vars g.mask) (ZaN g) c := by
  unfold buildRule at h
  cases e : g.ZbG[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply Ziv _ h
    exact ZbG ci (List.mem_of_getElem? e)

def ZhG (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := Za3 data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: ZhG data w v n (pos+w+v)

def Zdn {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def ZeV (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    Zdn st fun pos => Zdn first fun base =>
    Zdn (Za3 data pos 32) fun head =>
    Zdn (Nat.log2 (head ^^^ (head+1))) fun ones =>
    Zdn (base+(ones <<< gapBits)+Za3 data (pos+ones+1) gapBits) fun key =>
    Zdn (Za3 data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        ZeV data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def Zjd {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def Zge (tab : Zah) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+Za3 data (start+i*ow) ow
    ZhG data cw d (Za3 data pos 5) (pos+5+marker)
  else
    let off := ZfZ d raw dict + num*Zf0 d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+Za3 data (off+i*ow) ow
    let n := Za3 data pos 5
    let gap := Za3 data (pos+5) 3
    if !priority || decide (n≤1) then ZeV data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := Za3 data (pos+8) width
      let b := if n=2 then 1-a else Za3 data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := ZeV data pairs cw d gap n (pos+8+extra) 0
      Zjd a b xs

def Zbm (g : Zaj) (k i : Nat) := (Zez g k i).2.2.map Prod.fst
def Zc0 (g : Zaj) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.Zdg[pair.2]?).map fun perm => (Zbm g k pair.1).map (ZaS (perm.map swapRows).reverse)

theorem ZiD (g : Zaj) (k : Nat)
    (names : ∀ x ∈ g.Zdg, ZdZ (ZaN g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Zax g.mode (ZaN g) k (Zbm g k i).toFinset)
    {pair out} (h : Zc0 g k pair = some out) :
    Zax g.mode (ZaN g) k out.toFinset := by
  unfold Zc0 at h
  split at h
  · contradiction
  next valid =>
    cases e : g.Zdg[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact ZiF (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def ZcC (g : Zaj) (k i : Nat) :=
  let raw := ZcP g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := Zez g k i
  let values := ws.map Prod.fst
  let rules := (Zge (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zc0 g (k-1))).toList
  decide values.Nodup && !(values.contains (ZaN g)) &&
    (if k=0 then true else Zcy (k,ws.length,ws,Zd2 g.mode ws,rules,ls) ws)

theorem Zd8 (g : Zaj) (k i : Nat)
    (ZbX : ZdI (ZaN g) (ZbP fun j => (g.ZbX j).1) (ZbP fun j => (g.ZbX j).2))
    (ZbG : ∀ ci ∈ g.ZbG, Slice g.mode (Zag (Zdc g.mask ci)) (ZaN g) (Zde ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.Zdg, ZdZ (ZaN g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Zax g.mode (ZaN g) (k-1) (Zbm g (k-1) j).toFinset)
    (checked : ZcC g k i = true) : Zax g.mode (ZaN g) k (Zbm g k i).toFinset := by
  simp only [ZcC,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : ZaN g ∉ Zbm g k i := by simpa [Zbm] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (Zbm g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply Zlc (raw:=vars g.mask) ZbX _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply ZiC _ _ _ _ _ (ZiO g) v
    exact (ZiM _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact ZiB g ZbG h
  · intro tag xs hx
    have e : ((g.index k tag).bind (Zc0 g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact ZiD g _ names (prior (by omega)) h


def block (g : Zaj) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => ZcC g k (start+n) && block g k start n
theorem Zfw {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    ZcC g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem ZaR {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def ZbS (g : Zaj) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def Zaz (g : Zaj) (prior : Nat → Nat) :=
  (ZdE g.mask (fun j => (g.ZbX j).1) == BitVec.allOnes 152) &&
  (ZdE g.mask (fun j => (g.ZbX j).2) == 0) &&
  g.ZbG.all (fun c => ZdS g.mask c prior) &&
  g.Zdg.all (fun p => ZdZ (ZaN g) (p.map swapRows))

theorem ZkP (g : Zaj) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Zaf g.mode (Zag q) (Zac q) (prior q))
    (geometry : Zaz g prior = true) (rows : ZbS g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Zax g.mode (ZaN g) k (Zbm g k i).toFinset := by
  simp only [Zaz,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply Zd8 g 0 i (Zeb geometry.1.1.1 geometry.1.1.2)
      (fun x hx => ZdO _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact Zfw (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply Zd8 g _ i (Zeb geometry.1.1.1 geometry.1.1.2)
      (fun x hx => ZdO _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact Zfw (rows _ hk) i (by omega) (by omega)

def ZcV (g : Zaj) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && Zdu (Zbm g k i) ws
theorem Zfh {g top prior k i ws} (low : ∀ q, Zaf g.mode (Zag q) (Zac q) (prior q))
    (geom : Zaz g prior = true) (blocks : ZbS g top) (le : k ≤ top)
    (idx : ZcV g k i ws = true) : Zax g.mode (ZaN g) k ws.toFinset := by
  simp only [ZcV,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←ZeW idx.2]
  exact ZkP g top prior low geom blocks _ le i idx.1

theorem Zvy {g prior i hints} (low : ∀ q, Zaf g.mode (Zag q) (Zac q) (prior q))
    (geom : Zaz g prior = true) (blocks : ZbS g g.cap)
    (idx : ZcV g g.cap i (vars g.mask) = true) (hp : ZbC (ZaN g) = true)
    (ess : Zb9 (ZaN g) (vars g.mask) (Zff g.mask hints) = true)
    (all : (Zff g.mask hints).map Prod.fst = vars g.mask) :
    Zaf g.mode (vars g.mask) (ZaN g) (g.cap+1) := by
  apply ZfQ (Zcg _ hp) (Zb8 ess).1 (Zb8 ess).2 _ (Zfh low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply ZdF ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Zak (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Zaf u (Zag e.1) (Zac e.1) e.2
def Zan (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem Zao {u old L m carries} (previous : Zak u old)
    (main : Zaf u (Zag m) (Zac m) L)
    (ok : carries.all (fun v => ZeF v.1 m v.2) = true) :
    Zak u (Zan old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact Zhz (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem ZgV : Zak true [] := by simp [Zak]
theorem Zk0 {u es} (h : Zak true es) : Zak u es := fun e he => Zlb (h e he)
def ZbA (v : Nat) (upper : Nat) := 2^153*upper+v
def ZaQ {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => ZbA (f x).toNat (ZaQ f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => ZbA 1 (units n)
theorem Zfr (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem Zne (a b : Bits) (u v : Nat) :
    ZbA a.toNat u &&& ZbA b.toNat v = ZbA (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZbA,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (Zfr _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem Zqm (a b : Bits) (u v : Nat) :
    ZbA a.toNat u ||| ZbA b.toNat v = ZbA (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZbA,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (Zfr _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem Znf (a b : Bits) (u v : Nat) :
    ZbA a.toNat u ^^^ ZbA b.toNat v = ZbA (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZbA,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (Zfr _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem ZdP {α} (f g : α → Bits) (xs) :
    ZaQ f xs &&& ZaQ g xs = ZaQ (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [ZaQ]
  | cons a xs ih => simp only [ZaQ,Zne,ih]
theorem Zfz {α} (f g : α → Bits) (xs) :
    ZaQ f xs ||| ZaQ g xs = ZaQ (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [ZaQ]
  | cons a xs ih => simp only [ZaQ,Zqm,ih]
theorem Zek {α} (f g : α → Bits) (xs) :
    ZaQ f xs ^^^ ZaQ g xs = ZaQ (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [ZaQ]
  | cons a xs ih => simp only [ZaQ,Znf,ih]
def Zej (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem ZqE (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,ZbA,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem ZoJ (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem ZrK {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (Zej (units xs.length) (ZaQ f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [Zej,Nat.testBit_and,Nat.testBit_shiftRight,ZqE _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [ZaQ,List.length_cons,units,ZbA]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using ZoJ (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev ZdM := Nat × Nat
abbrev Zfj := Nat × Nat × Nat

def Zb4 {α} (s : α → ZeE) (xs : List α) : ZdM :=
  (ZaQ (fun x => (s x).1) xs,ZaQ (fun x => (s x).2) xs)
def Zen {α} (c : α → Cov) (xs : List α) : Zfj :=
  (ZaQ (fun x => (c x).1) xs,ZaQ (fun x => (c x).2.1) xs,
   ZaQ (fun x => (c x).2.2) xs)
def ZcD (d : Bool) (a : ZdM) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem ZeD (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem ZeZ {α} (s : α → ZeE) (xs : List α) (d : Bool) :
    ZcD d (Zb4 s xs) = ZaQ (fun x => column d (s x)) xs := by
  cases d <;> simp only [ZcD,Zb4,column,Bool.false_eq_true,ite_false,ite_true,ZdP,Zek,ZeD]

def Zc6 (op : Nat) (a b : ZdM) : ZdM :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem Znd {α} (a b : α → Zae) (xs : List α) (op : Nat) :
    Zc6 op (Zb4 (fun x => (a x).2) xs) (Zb4 (fun x => (b x).2) xs) =
    Zb4 (fun x => (Zbp op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [Zc6,h0,ite_true,Zb4,ZdP,Zbp,bv]
  by_cases h1 : op=1
  · simp [Zc6,h1,Zb4,Zfz,Zbp,bv]
  by_cases h2 : op=2
  · simp [Zc6,h2,Zb4,ZdP,Zek,ZeD,Zbp,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [Zc6,h0,h1,h2,ite_false,Zb4,ZdP,Zek,ZeD,Zbp,bv,e]

def Zef (c : Zfj) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem ZiY {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    Zef (Zen c xs) (ZaQ a xs) (ZaQ b xs) ka kb =
    ZaQ (fun x => Zdd (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [Zef,Zen,ZdP,Zfz,Zek,ZeD,Zdd,Zcx,Zdy,
      Bool.false_eq_true,ite_false,ite_true]

def Zay (c : Zbj) (i : Nat) := c.2.2.1.getD i Zbx
def Zc9 (c : Zbj) (i j op : Nat) (ka kb : Bool) :=
  let a := Zay c i
  let b := Zay c j
  ZcM c op a b (Zbp op a b) ka kb
def Zfo (c : Zbj) (d ka kb : Bool) (op i j : Nat) :=
  let a := Zay c i
  let b := Zay c j
  Zdd c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (Zbp op a b).2

def ZdX {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && ZdX f (mask >>> 153) xs
theorem Zna {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : ZdX f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [ZdX,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List ZdM × Zfj
def Zcf (k n : Nat) (xs : List Zbj) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => Zb4 (fun c => (Zay c i).2) xs),
    Zen (fun c => c.2.2.2.1.1) xs)
def Zdx (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem Zgf (k n) (xs) {i : Nat} (h : i<n) :
    Zdx (Zcf k n xs) i = Zb4 (fun c => (Zay c i).2) xs := by
  simp [Zdx,Zcf,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem ZjR (d x : Sig) : ZaP d (neg x) = d ^^^ ZaP d x := by
  apply ZbI
  intro r
  simp only [ZaP,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def ZbD (p : Zae → Bool) (a : Zae) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem Zho (p : Zae → Bool) (ws : List Zae) (a : Zae) (keep : Bool) :
    ws.countP p ≤ (ZbY ws a keep).countP p + ZbD p a keep := by
  cases keep
  · simp only [ZbY,Bool.false_eq_true,ite_false,ZbD,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [ZbY,ZbD]

theorem Zm5 (p : Zae → Bool) (ws : List Zae) (a b : Zae) (ka kb : Bool) :
    ws.countP p - ZbD p a ka - ZbD p b kb ≤
    (Zbc ws a b ka kb).countP p := by
  have h1 := Zho p ws a ka
  have h2 := Zho p (ZbY ws a ka) b kb
  simp only [Zbc]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem Zcv {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def Zc4 {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem Ze7 {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : Zc4 f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => Zc4 f l fun xs => k (x::xs)) = _
    rw [Zcv,ih]
    rfl
def ZaA (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def Zcm (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def ZcR (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def ZbZ (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (ZcR d m) (Zcm m pm)) (and u (Zcm (Nat.xor d m) pm))
theorem ZdU (d a : Sig) : ZaA d.toNat a = (ZaP d a).toNat := (BitVec.toNat_and _ _).symm
theorem Zfm (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem Zem (d a : Sig) : ZcR d.toNat (ZaA d.toNat a) = ZaU d a := by
  rw [ZdU]
  have e : Nat.beq (ZaP d a).toNat 0 = (ZaP d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←Zfm,z0]
  rw [ZcR,e,Zfm]
  rfl
theorem Zhx (x d : Sig) (pool : List Sig) : Zcm x.toNat (pool.map (ZaA d.toNat)) = (pool.map (ZaP d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (ZaA d.toNat a)) (Zcm x.toNat (l.map (ZaA d.toNat))) = _
    rw [ih,ZdU,Zfm,List.map_cons,List.any_cons,Bool.beq_comm]
theorem Zel (u : Bool) (d a : Sig) (pool : List Sig) :
    ZbZ u d.toNat (pool.map (ZaA d.toNat)) (ZaA d.toNat a) = ZaW u d pool a := by
  have x : Nat.xor d.toNat (ZaP d a).toNat = (ZaP d (neg a)).toNat := by
    rw [ZjR]
    exact (BitVec.toNat_xor _ _).symm
  rw [ZbZ,Zem,ZdU,x,Zhx,Zhx]
  simp only [ZaW,ZaU]
def ZcT (u : Bool) (p : Zbl) (w : Zae) : Nat := cond (ZaW u p.domain p.wires w.1) 0 1
def ZeA (u : Bool) (p : Zbl) (ws : List Zae) (k : Nat) (a b : Zae) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Zae => ZaU p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - ZbD const a ka - ZbD const b kb + (ZaU p.domain z).toNat
  (((ws.map (ZcT u p)).sum == cond ka 0 (ZcT u p a) + cond kb 0 (ZcT u p b)) &&
    decide (k+p.ZaO+(!ZaW u p.domain p.wires z).toNat < p.bound+cm)) &&
    (ZaW u p.domain p.wires z || (ZaW u p.domain p.wires a.1 && ZaW u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem Zio (op : Nat) (d a b : Sig) : zN op (ZaA d.toNat a) (ZaA d.toNat b) = ZaA d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [ZdU]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply ZbI
    intro r
    simp only [ZaP,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply ZbI
    intro r
    simp only [ZaP,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply ZbI
    intro r
    simp only [ZaP,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply ZbI
  intro r
  simp only [ZaP,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def Zco (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (ZcR d x) 1 0)
theorem ZhL (d : Sig) (a : Zae) (keep : Bool) :
    Zco d.toNat (ZaA d.toNat a.1) keep = ZbD (fun w : Zae => ZaU d w.1) a keep := by
  rw [Zco,Zem,ZbD]
  cases keep
  · cases ZaU d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def ZdQ (u : Bool) (k : Nat) (ws : List Zae) (p : Zbl) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Zae => ZaA d w.1)
  (d,ms.countP (ZcR d),p.bound,Nat.add k p.ZaO,(ms.map fun m => cond (ZbZ u d (p.wires.map (ZaA d)) m) 0 1).sum,ms,p.wires.map (ZaA d),u)
noncomputable def Zg0 {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def Zei {β : Type} (u : Bool) (k : Nat) (ws : List Zae) (p : Zbl) (f : QS → β) : β :=
  force p.domain.toNat fun d => Zc4 (ZaA d) p.wires fun pm => Zc4 (fun w : Zae => ZaA d w.1) ws fun ms =>
  force (ms.countP (ZcR d)) fun c => force p.bound fun l => force (Nat.add k p.ZaO) fun t =>
  force (ms.map fun m => cond (ZbZ u d pm m) 0 1).sum fun v => Zg0 u fun u => f (d,c,l,t,v,ms,pm,u)
theorem Zja {β : Type} (u k ws p) (f : QS → β) : Zei u k ws p f = f (ZdQ u k ws p) := by
  have e (b : Bool) (f : Bool → β) : Zg0 b f = f b := by cases b <;> rfl
  simp only [Zei,Zcv,Ze7,e]
  rfl
noncomputable def Zec {β : Type} (u : Bool) (k : Nat) (ws : List Zae) (ps : List Zbl) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => Zei u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem ZiT {β : Type} (u k ws ps) (f : List QS → β) : Zec u k ws ps f = f (ps.map (ZdQ u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change Zei u k ws p (fun q => Zec u k ws ps fun qs => f (q::qs)) = _
    rw [Zja,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev ZcA := Zbj × Nat × Nat × List QS × List Nat × Nat
noncomputable def Zck (c : Zbj) : ZcA :=
  let ws := c.2.2.1.map (fun w : Zae => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (ZdQ c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def Zfe {β : Type} (cs : List Zbj) : (List ZcA → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    Zc4 (fun w : Zae => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    Zec c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem Zf1 {β : Type} (cs) (f : List ZcA → β) : Zfe cs f = f (cs.map Zck) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      Zc4 (fun w : Zae => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      Zec c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => Zfe cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [Zcv,Zcv,Ze7,Zcv,ZiT,ih]
    rfl
noncomputable def Zfx (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := ZbZ s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (Zco s.1 x ka)) (Zco s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (ZcR s.1 (zN op x y)) false))
theorem ZqA {d : Nat} (ws : List Zae) (i : Nat) (hd : ZaA d zero=0) :
    (ws.map (fun w : Zae => ZaA d w.1)).getD i 0 = ZaA d (ws.getD i Zbx).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem ZmX {u k p ws i j op ka kb} (h : Zfx (ZdQ u k ws p) i j op ka kb=true) :
    ZeA u p ws k (ws.getD i Zbx) (ws.getD j Zbx) op ka kb=true := by
  have z0 : ZaA p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [ZaA,this]
  have su : (((ws.map (fun w : Zae => ZaA p.domain.toNat w.1)).map fun m => cond (ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat)) m) 0 1).sum) =
      (ws.map (ZcT u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat)) (ZaA p.domain.toNat w.1)) 0 1 = _
    rw [Zel]
    rfl
  simp only [Zfx,ZdQ,Zcv,ZqA _ _ z0,su,List.countP_map,Function.comp_def,Zem] at h
  generalize ws.getD i Zbx=a at h ⊢
  generalize ws.getD j Zbx=b at h ⊢
  replace h : and (Nat.beq (ws.map (ZcT u p)).sum (Nat.add (cond ka 0 (cond ((ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat))) (ZaA p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat))) (ZaA p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.ZaO)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zae => ZaU p.domain w.1)) (Zco p.domain.toNat (ZaA p.domain.toNat a.1) ka)) (Zco p.domain.toNat (ZaA p.domain.toNat b.1) kb))))
    (or ((ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat))) (zN op (ZaA p.domain.toNat a.1) (ZaA p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.ZaO) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zae => ZaU p.domain w.1)) (Zco p.domain.toNat (ZaA p.domain.toNat a.1) ka)) (Zco p.domain.toNat (ZaA p.domain.toNat b.1) kb)))) (and ((ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat))) (ZaA p.domain.toNat a.1)) ((ZbZ u p.domain.toNat (p.wires.map (ZaA p.domain.toNat))) (ZaA p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.ZaO) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Zae => ZaU p.domain w.1)) (Zco p.domain.toNat (ZaA p.domain.toNat a.1) ka)) (Zco p.domain.toNat (ZaA p.domain.toNat b.1) kb)))) (ZcR p.domain.toNat (zN op (ZaA p.domain.toNat a.1) (ZaA p.domain.toNat b.1))) false)) = true := h
  rw [Zio,Zem,Zel,Zel,Zel,ZhL,ZhL] at h
  have ca : ZaU p.domain (bin op a.1 b.1)=true → ZaW u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [ZaW,ZaU,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [ZeA,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => ZaU p.domain w.1) - ZbD (fun w : Zae => ZaU p.domain w.1) a ka -
      ZbD (fun w : Zae => ZaU p.domain w.1) b kb = c at h ⊢
    generalize ZaU p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize ZaW u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.ZaO+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.ZaO) (p.bound+c)
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

theorem ZmR (m : Nat) (l : List Nat) : Zcm m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [Zcm]
  | cons a l ih =>
    change or (Nat.beq m a) (Zcm m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def ZfL (fl : Nat → Option (List Nat)) (l : ZcA) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => Zc4 (fun v => v) ys fun ys =>
    and (Zcm z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (Zcm v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (Zcm v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem ZkZ (xs : List Sig) : Zd0 xs = (xs.map Zb6).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+Zb6 x) a = a+(xs.map Zb6).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem Zgo (f : Zae → Nat) {ws : List Zae} {a b : Zae} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((Zbc ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Zae} {x : Zae} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [Zbc,ZbY,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem ZiS {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : Zdv u op=true)
    (h : ZeA u p ws k a b op ka kb=true) :
    ZcB u p k ((Zbc ws a b ka kb).map Prod.fst) (ZbU op a b)=true := by
  let const := fun w : Zae => ZaU p.domain w.1
  let z := bin op a.1 b.1
  let rest := Zbc ws a b ka kb
  have ck := Zm5 const ws a b ka kb
  change ws.countP const - ZbD const a ka - ZbD const b kb ≤ rest.countP const at ck
  simp only [ZeA,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := Zgo (ZcT u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((Zbc ws a b ka kb).map (ZcT u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (ZaW u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : ZaW u p.domain p.wires w.1
    · simp [ZcT,e] at v
    · rfl
  have opOK : (!(!ZaW u p.domain p.wires z) || Zc2 u p.domain p.wires (ZbU op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [Zc2,ZbU,x,y,al]
  change k+p.ZaO+(!ZaW u p.domain p.wires z).toNat < p.bound+(ws.countP const - ZbD const a ka -
        ZbD const b kb+(ZaU p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : Zbg (ZbU op a b)=z := rfl
  simp only [ZcB,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.ZaO+(!ZaW u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if ZaU p.domain z then 1 else 0)
  cases hc' : ZaU p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem Zif (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : ZaA one.toNat v = v.toNat := by
    rw [ZdU]
    congr 1
    exact BitVec.and_allOnes
  have := Zio op one a b
  rwa [e,e,e] at this
theorem Zvk (ws : List Zae) (i : Nat) :
    (ws.map (fun w : Zae => w.1.toNat)).getD i 0 = (ws.getD i Zbx).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem Zid {c : Zbj} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (Zay c i).1 ≠ (Zay c j).1 := by
  have gi : Zay c i = c.2.2.1[i] := by simp [Zay,List.getD_eq_getElem?_getD,hi]
  have gj : Zay c j = c.2.2.1[j] := by simp [Zay,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem Zla {c : Zbj} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : ZfL fl (Zck c) i j op ka kb=true) :
    (c.2.2.2.2.2 (Zd0 (Zbg (ZbU op (Zay c i) (Zay c j)) ::
      (Zbc c.2.2.1 (Zay c i) (Zay c j) ka kb).map Prod.fst))).any (Zdu
      (Zbg (ZbU op (Zay c i) (Zay c j)) ::
      (Zbc c.2.2.1 (Zay c i) (Zay c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : Zay c t ∈ c.2.2.1 := by
    simp [Zay,List.getD_eq_getElem?_getD,ht]
  have hne := Zid nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : Zay c i ≠ Zay c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := Zgq nd ha hb ka kb v
  have sum := Zgo (fun w : Zae => Zb6 w.1) ha hb hab ka kb
  have wi : Zay c i = c.2.2.1.getD i Zbx := rfl
  have wj : Zay c j = c.2.2.1.getD j Zbx := rfl
  simp only [ZfL,Zck,Zcv,Zvk,←wi,←wj,Zif] at h
  generalize Zay c i=a at *
  generalize Zay c j=b at *
  change Option.rec false _ (fl (Zb6 (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Zae => w.1.toNat)).map kwN).sum -
    (cond ka 0 (Zb6 a.1)) - (cond kb 0 (Zb6 b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Zae => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Zae => Zb6 w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : Zd0 (Zbg (ZbU op a b) :: (Zbc c.2.2.1 a b ka kb).map Prod.fst) =
      Zb6 (bin op a.1 b.1)+((Zbc c.2.2.1 a b ka kb).map (fun w : Zae => Zb6 w.1)).sum := by
    rw [ZkZ,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize Zd0 (Zbg (ZbU op a b) :: (Zbc c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [Ze7,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,ZmR,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [Zdu,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
noncomputable def Zfd (fl : Nat → Option (List Nat)) (l : ZcA) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => Zfx s i j op ka kb) (ZfL fl l i j op ka kb))) (Zc9 l.1 i j op ka kb)
theorem ZiI {c : Zbj} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : Zfd fl (Zck c) i j op ka kb=true) :
    Zc9 c i j op ka kb=true := by
  simp only [Zfd,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : Zdv c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [Zdv] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : Zay c t ∈ c.2.2.1 := by
      simp [Zay,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := Zid nd hi hj (fun e => by simp [e] at hn)
    have closed := ZiS (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (ZmX ok)
    have cut : c.2.2.2.2.1.any (fun p => ZcB c.2.2.2.1.2 p (c.1-1)
        ((Zbc c.2.2.1 (Zay c i) (Zay c j) ka kb).map Prod.fst)
        (ZbU op (Zay c i) (Zay c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [Zc9,ZcM,Zdm,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := Zla nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [Zc9,ZcM,Zdm,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def ZdY (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def Zc1 (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem ZlI : ∀ v : Fin 144, Zc1 v.val=true → ∀ t : Fin 9, ZdY v.val t.val<9 ∧
    ZdV (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (ZdY v.val t.val) zero := by decide +kernel
theorem ZlH {v t : Nat} (hv : Zc1 v=true) (ht : t<9) : ZdY v t<9 ∧
    ZdV (swapRows v) (inputs.getD t zero) = inputs.getD (ZdY v t) zero := by
  have lt : v<144 := by
    simp only [Zc1,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact ZlI ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => ZdY v t) t
theorem ZpC {perm : List Nat} (ok : perm.all Zc1=true) {t : Nat} (ht : t<9) :
    ZaS (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [ZaS,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := ZlH ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def ZeG : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => ZeG n (bits >>> 10) (ws++[z])
theorem ZkM (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Zae) :
    (ZdJ n bits ds).map (fun w => F w.1) = ZeG n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Zae) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i Zbx).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [ZeG,Zcv,ZdJ,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem ZiL {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (Zcd bits ws).map f = Zcd bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,Zcd,Zcd]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def Zfp (g : Zaj) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (Zci g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (Zf7 (g.levels k) (Zci g.mask).length i) fun rec =>
  Zcd (rec >>> len) (ZeG depth (rec &&& ((1 <<< len)-1)) raw)
theorem Zi9 (g : Zaj) (k i : Nat) {perm : List Nat} (ok : perm.all Zc1=true) :
    Zfp g k i perm = ((Zbm g k i).map (ZaS (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (ZaS ms a).toNat
  have F0 : F zero=0 := by
    change (ZaS ms zero).toNat=0
    rw [ZcU,(ZfR _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (ZaS ms (bin op a b)).toNat = zN op (ZaS ms a).toNat (ZaS ms b).toNat
    rw [Zif,ZcU,ZgR,ZcU,ZcU]
  have raw : (ZcP g).map (fun w => F w.1) = (Zci g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [ZcP,Zey,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := ZfX hm
    exact congrArg BitVec.toNat (ZpC ok hj)
  have len : (ZcP g).length = (Zci g.mask).length := by simp [ZcP,Zey]
  unfold Zfp Zbm Zez
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [Zcv,Zgl,len]
  rw [List.map_map,List.map_map,ZiL,←raw,←ZkM F F0 Fb]
  rfl
noncomputable def ZgL (g : Zaj) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.Zdg[pair.2]?).bind fun perm => cond (perm.all Zc1) (some (Zfp g k pair.1 perm)) none
noncomputable def Zdi (g : Zaj) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (ZgL g (k-1))
noncomputable def ZgW (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List ZcA) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := Zdx b i
    let b' := Zdx b j
    let z := Zc6 op a b'
    let mask := Zej r (Zef cov (ZcD (!u) a) (ZcD (!u) b') ka kb ||| ZcD (!u) z)
    ZdX (fun c => Zfd fl c i j op ka kb) mask xs

theorem Zi1 {fl u} (k n) (xs : List Zbj) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : ZgW fl u (Zcf k n xs) (xs.map Zck) i j op ka kb=true) :
    Zc9 xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : Zc9 xs[q] i j op ka kb =
      if len>k then true else if Zfo xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !ZbC (Zbp op (Zay xs[q] i) (Zay xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(Zbp op (Zay xs[q] i) (Zay xs[q] j)).1)
      then true else Zdm u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((Zbc xs[q].2.2.1 (Zay xs[q] i) (Zay xs[q] j) ka kb).map Prod.fst)
        (ZbU op (Zay xs[q] i) (Zay xs[q] j)) := by
    simp only [Zc9,ZcM,budget,arity,mode,len,Zfo] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := Zdx (Zcf k n xs) i
    let b := Zdx (Zcf k n xs) j
    let cov := Zen (fun c : Zbj => c.2.2.2.1.1) xs
    change (if len>k then true else ZdX _ (Zej r
       (Zef cov (ZcD (!u) a) (ZcD (!u) b) ka kb |||
        ZcD (!u) (Zc6 op a b))) (xs.map Zck)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := Zgf k n xs hi
    have cb : b = _ := Zgf k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,Znd,ZeZ,ZeZ,ZeZ,ZiY,Zfz] at pass
    by_cases hit : Zfo xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply ZiI nd hfl
      have m := Zna _ _ _ q (by simpa using hq) (by
        rw [ZrK _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def ZgX (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List ZcA) (i j op : Nat) :=
  let f := ZgW fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def Zep (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List ZcA) (i : Nat) (js : List Nat) :=
    js.all (fun j => (Zdh u).all (ZgX fl u b xs i j))
noncomputable def Zdq (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List ZcA) : List Nat → Bool
  | [] => true
  | i::js => Zep fl u b xs i js && Zdq fl u b xs js

theorem Zi2 {fl u} (k n) (xs : List Zbj) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : Zdq fl u (Zcf k n xs) (xs.map Zck) js=true) :
    Zcy xs[q] (js.map (Zay xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [Zdq,Bool.and_eq_true,Zep,List.all_eq_true] at allRows
    simp only [List.map_cons,Zcy,ZfJ,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @Zi1 fl u k n xs i j op
    simp only [ZgX,Bool.and_eq_true] at pass
    simp only [Zc7,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def ZfC (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List Zbj) :=
    Zdq fl u (Zcf k n xs) (xs.map Zck) (List.range n)
theorem Zj1 {fl u k n} {xs : List Zbj} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : ZfC fl u k n xs=true) : Zcy xs[q] xs[q].2.2.1=true := by
  have all := Zi2 k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (Zay xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [Zay,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def Zds (g : Zaj) (k i : Nat) : Zbj :=
  let raw := ZcP g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := Zez g k i
  let rules := (Zge (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zc0 g (k-1))).toList
  (k,ws.length,ws,Zd2 g.mode ws,rules,ls)


theorem Zq0 (g : Zaj) (k i tag : Nat) (ys) (h : Zdi g k tag=some ys) :
    ∃ xs ∈ (Zds g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (Zc0 g (k-1))).toList, _
  unfold Zdi at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,ZgL] at h
    simp only [Option.bind_some,Zc0]
    split at h
    · contradiction
    next v =>
      cases ha : g.Zdg[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all Zc1 with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(Zbm g (k-1) pair.1).map (ZaS (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (Zi9 g _ _ hv)

def ZfN (T : Sig) (c : Zbj) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem Zjb (g : Zaj) (k i : Nat) :
    ZcC g k i = (ZfN (ZaN g) (Zds g k i) &&
      (if k=0 then true else Zcy (Zds g k i) (Zds g k i).2.2.1)) := rfl

theorem Zm9 {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → ZcC g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def Zc3 (g : Zaj) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (Zds g k)
def header (g : Zaj) (k start n ar : Nat) :=
  (Zc3 g k start n).all (fun c => c.2.1==ar && ZfN (ZaN g) c)
noncomputable def Zcl (g : Zaj) (k start n ar lo len : Nat) :=
  let xs := Zc3 g k start n
  let b := Zcf k ar xs
  Zfe xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    Zep (Zdi g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem Zfu {g k start n ar lo len} (h : Zcl g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    Zep (Zdi g k) g.mode (Zcf k ar (Zc3 g k start n)) ((Zc3 g k start n).map Zck)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [Zcl,Zf1] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem Zjg {g k start n ar lo a b}
    (h : Zcl g k start n ar lo a=true) (t : Zcl g k start n ar (lo+a) b=true) :
    Zcl g k start n ar lo (a+b)=true := by
  simp only [Zcl,Zf1]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact Zfu h (lo+j) (by omega) (by omega)
  · exact Zfu t (lo+j) (by omega) (by omega)

theorem ZqZ {g k start n ar} (h : Zcl g k start n ar 0 ar=true) :
    ZfC (Zdi g k) g.mode k ar (Zc3 g k start n)=true := by
  let xs := Zc3 g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      Zdq (Zdi g k) g.mode (Zcf k ar xs) (xs.map Zck) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,Zdq,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := Zfu h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold ZfC
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem ZmV {g k start n ar} (hd : header g k start n ar=true)
    (h : Zcl g k start n ar 0 ar=true) : block g k start n=true := by
  apply Zm9
  intro i lo hi
  let xs := Zc3 g k start n
  have hm : Zds g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [ZfN,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, Zdi g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => Zq0 g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [Zjb,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ Zj1 hq hb ha hm nd hfl hn (ZqZ h)

def Zas (g : Zaj) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => Zcl g k start n ar lo num=true
  | d+1 => Zas g k start n ar lo (num/2) d ∧ Zas g k start n ar (lo+num/2) (num-num/2) d
theorem Zov {g k start n ar lo num d} (h : Zas g k start n ar lo num d) :
    Zcl g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := Zjg (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def Zab (g : Zaj) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ Zas g k start n ar 0 ar rows
  | d+1 => Zab g k start (n/2) ar rows d ∧ Zab g k (start+n/2) (n-n/2) ar rows d
theorem Zau {g k start n ar rows d} (h : Zab g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact ZmV h.1 (Zov h.2)
  | succ d ih =>
    have v := ZaR (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def Zba {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => Zba f (xs.take (xs.length/2)) d ∧ Zba f (xs.drop (xs.length/2)) d
theorem ZaF {α f xs d} (h : @Zba α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem ZlG {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Zaf u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,ZeX pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem Zcz {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Zaf u (Zag q) (Zac q) (prior q))
    (e : (Zac q == Zac m && (Zag q == vars m) && (prior q == cap+1) && ZbC (Zac m) &&
      decide (vars m).Nodup && ZeN u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Zax u (Zac m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact Zf3 (ZlG (Zcg _ e4) h) [] rfl e5 e6

theorem Za0 {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Zaf u (Zag q) (Zac q) (prior q)) (ci : Za7)
    (ok : ZdS m ci prior = true)
    (cut : (decide ws.Nodup && ZeN u (Zde ci.1 ci.2.1) ci.2.2.2.2 cap 0 (Zag (Zdc m ci)) ws)=true) :
    Zax u (Zac m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact Zf3 (ZdO ci prior low ok) [] rfl cut.1 cut.2

theorem ZcW {u} {g : Zaj} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Zaf u (Zag q) (Zac q) (prior q))
    (geom : Zaz g prior = true) (blocks : ZbS g cap)
    (idx : ZcV g cap i ws = true) : Zax u (Zac m) cap ws.toFinset := by
  subst hm
  subst hu
  exact Zfh low geom blocks (Nat.le_refl _) idx

def Zii (m hints : Nat) : Bool :=
  let xs := Zff m hints
  ZbC (Zac m) && Zb9 (Zac m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem ZbN {u} {m hints cap : Nat} (ok : Zii m hints = true)
    (a : Zax u (Zac m) cap (vars m).toFinset) : Zaf u (vars m) (Zac m) (cap+1) := by
  simp only [Zii,Bool.and_eq_true,beq_iff_eq] at ok
  apply ZfQ (Zcg _ ok.1.1) (Zb8 ok.1.2).1 (Zb8 ok.1.2).2 _ a
  intro v hv
  apply ZdF ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def ZqG (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((Zci m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def ZeP (m : Nat) (rs : List Nat) : Bool :=
  let xs := ZqG m rs
  Zb9 (Zac m) (Zag m) xs && (xs.map Prod.fst == vars m) &&
    ZbC (Zac m) && decide (Zag m = vars m ++ [ZeB (m/512-1)])
theorem ZkQ {u} {m : Nat} {rs : List Nat} (ok : ZeP m rs = true) {k : Nat} {S : Finset Sig}
    (h : Zav u (Zac m) k S) (sub : ∀ v ∈ S, v ∈ Zag m) :
    S=(vars m).toFinset ∨ S=(Zag m).toFinset := by
  simp only [ZeP,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := ZdF ess v (List.mem_toFinset.mpr hv)
    exact ZdG h (Zag m) v sub r s hd hi
  have mem : ∀ v, v ∈ Zag m ↔ v ∈ vars m ∨ v=ZeB (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : ZeB (m/512-1) ∈ S
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
theorem Zaw {u} {m q cap : Nat} {rs : List Nat} (ok : ZeP m rs = true)
    (e : Zac m = Zac q) (ev : vars m = vars q)
    (a : Zax u (Zac q) cap (vars q).toFinset)
    (b : Zax u (Zac q) cap (Zag m).toFinset) :
    Zaf u (Zag m) (Zac m) (cap+1) := by
  have ok' := ok
  simp only [ZeP,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := Zee (Zcg _ ok'.1.2) (Zb8 ok'.1.1.1).1 (Zb8 ok'.1.1.1).2 hr ha
  by_contra! small
  rcases ZkQ ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
abbrev ZaY (S : Finset Sig) (T : Sig) :=
  { owns : Sig → Row → Row → Prop //
    (∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n) ∧
    (∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false) ∧
    (∀ {v w p n}, owns v p n → owns w p n → v=w) ∧
    (∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) }
abbrev ZaY.owns {S T} (D : ZaY S T) := D.val
abbrev ZaY.total {S T} (D : ZaY S T) := D.property.1
abbrev ZaY.valid {S T} (D : ZaY S T) :
    ∀ {v p n}, D.owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false := D.property.2.1
abbrev ZaY.unique {S T} (D : ZaY S T) :
    ∀ {v w p n}, D.owns v p n → D.owns w p n → v=w := D.property.2.2.1
abbrev ZaY.Zbw {S T} (D : ZaY S T) :
    ∀ {v p n p' n'}, D.owns v p n' → D.owns v p' n → D.owns v p n := D.property.2.2.2
def ZaY.mk {S T} (owns : Sig → Row → Row → Prop)
    (total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n)
    (valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false)
    (unique : ∀ {v w p n}, owns v p n → owns w p n → v=w)
    (Zbw : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) : ZaY S T :=
  ⟨owns,total,valid,unique,Zbw⟩

def ZfK (T : Sig) : ZaY {T} T :=
  ZaY.mk (fun v p n => v=T ∧ bit p T=true ∧ bit n T=false)
    (fun p n hp hn => ⟨T,rfl,hp,hn⟩)
    (by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩)
    (by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm)
    (by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩)

def Zih {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : ZaY (insert (bin d a b) U) T) : ZaY (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have Zbn (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine ZaY.mk (fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)) ?_ ?_ ?_ ?_
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.Zbw hv hw⟩
    · exact False.elim (Zbn p' n (we ▸ vU))
    · exact False.elim (Zbn p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.Zbw hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem ZfH {u T k S} (h : Zav u T k S) : S.card ≤ k+1 := by
  induction h using Zav.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem ZfG {T k S} (run : Zav false T k S) (tight : S.card=k+1) :
    Nonempty (ZaY S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨ZfK T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := ZfH tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨Zih d01 ha hb fresh H⟩

def Za2 (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem ZcS {S T v p n} (H : ZaY S T) (one : Za2 S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem Zro {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : Za2 S T a p na) (B : Za2 S T b p nb)
    (C : Za2 S T a pa n) (D : Za2 S T b pb n) : Zax false T k S := by
  intro j hj run
  have lb := ZfH run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := ZfG run tight
  exact different (H.unique (H.Zbw (ZcS H A) (ZcS H C)) (H.Zbw (ZcS H B) (ZcS H D)))
abbrev ZaX (S : Finset Sig) (T H : Sig) :=
  { owns : Sig → Row → Row → Prop //
    (∀ p n, bit p T=true → bit n T=false → (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n) ∧
    (∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false) ∧
    (∀ {v w p n}, owns v p n → owns w p n → v=w) ∧
    (∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) }
abbrev ZaX.owns {S T H} (D : ZaX S T H) := D.val
abbrev ZaX.total {S T H} (D : ZaX S T H) := D.property.1
abbrev ZaX.valid {S T H} (D : ZaX S T H) :
    ∀ {v p n}, D.owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false := D.property.2.1
abbrev ZaX.unique {S T H} (D : ZaX S T H) :
    ∀ {v w p n}, D.owns v p n → D.owns w p n → v=w := D.property.2.2.1
abbrev ZaX.Zbw {S T H} (D : ZaX S T H) :
    ∀ {v p n p' n'}, D.owns v p n' → D.owns v p' n → D.owns v p n := D.property.2.2.2
def ZaX.mk {S T H} (owns : Sig → Row → Row → Prop)
    (total : ∀ p n, bit p T=true → bit n T=false → (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n)
    (valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false)
    (unique : ∀ {v w p n}, owns v p n → owns w p n → v=w)
    (Zbw : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n) : ZaX S T H :=
  ⟨owns,total,valid,unique,Zbw⟩

abbrev ZaK (S : Finset Sig) (T : Sig) :=
  Σ inner : Finset Sig, Σ Zbv : Finset Sig, Σ Zbo : Sig,
    { rooms : ZaY inner Zbo × ZaX Zbv T Zbo //
      inner ∪ Zbv = S ∧ Disjoint inner Zbv }
abbrev ZaK.inner {S T} (F : ZaK S T) := F.1
abbrev ZaK.Zbv {S T} (F : ZaK S T) := F.2.1
abbrev ZaK.Zbo {S T} (F : ZaK S T) := F.2.2.1
abbrev ZaK.cover {S T} (F : ZaK S T) := F.2.2.2.property.1
abbrev ZaK.Zcn {S T} (F : ZaK S T) := F.2.2.2.property.2
abbrev ZaK.inside {S T} (F : ZaK S T) := F.2.2.2.val.1
abbrev ZaK.Zbn {S T} (F : ZaK S T) := F.2.2.2.val.2
def ZaK.mk {S T} (inner Zbv : Finset Sig) (Zbo : Sig)
    (cover : inner ∪ Zbv = S) (Zcn : Disjoint inner Zbv)
    (inside : ZaY inner Zbo) (Zbn : ZaX Zbv T Zbo) : ZaK S T :=
  ⟨inner,Zbv,Zbo,⟨inside,Zbn⟩,cover,Zcn⟩

def Zox {S T} (D : ZaY S T) (h : Sig) : ZaX S T h :=
  ZaX.mk D.owns (fun p n hp hn => Or.inr (D.total p n hp hn))
    D.valid D.unique D.Zbw

def ZhD {S T h} (D : ZaX S T h) : ZaX (S.erase h) T h :=
  ZaX.mk (fun v p n => v≠h ∧ D.owns v p n)
    (by
      intro p n hp hn
      rcases D.total p n hp hn with yes | ⟨v,hv⟩
      · exact Or.inl yes
      · by_cases eq : v=h
        · exact Or.inl (eq ▸ (D.valid hv).2)
        · exact Or.inr ⟨v,eq,hv⟩)
    (by
      rintro v p n ⟨ne,hv⟩
      exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩)
    (fun h1 h2 => D.unique h1.2 h2.2)
    (fun a b => ⟨a.1,D.Zbw a.2 b.2⟩)

def Zi8 {S T} (D : ZaY S T) : ZaK S T :=
  ZaK.mk S ∅ T (by simp) (by simp) D
    (ZaX.mk (fun _ _ _ => False)
      (fun p n hp hn => Or.inl ⟨hp,hn⟩)
      (fun h => h.elim) (fun h _ => h.elim) (fun h _ => h.elim))

def ZhC {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : ZaX (insert (bin d a b) U) T h) : ZaX (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have Zbn (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine ZaX.mk (fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)) ?_ ?_ ?_ ?_
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.Zbw hv hw⟩
    · exact False.elim (Zbn p' n (we ▸ vU))
    · exact False.elim (Zbn p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.Zbw hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem Zgm {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB

def Zi6 {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : ZaK (insert (bin d a b) U) T) :
    ZaK (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,Zcn,ha,hb⟩ := Zgm F.cover F.Zcn inn freshA freshB freshZ
    have old : ZaY (insert z (F.inner.erase z)) F.Zbo := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ZaK.mk _ F.Zbv F.Zbo eq Zcn (Zih hd ha hb (by simp [z]) old) F.Zbn
  · have out : z∈F.Zbv := by
      have m : z∈F.inner∪F.Zbv := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,Zcn,ha,hb⟩ := Zgm ((Finset.union_comm _ _).trans F.cover) F.Zcn.symm out freshA freshB freshZ
    have old : ZaX (insert z (F.Zbv.erase z)) T F.Zbo := by
      rw [Finset.insert_erase out]; exact F.Zbn
    exact ZaK.mk F.inner _ F.Zbo ((Finset.union_comm _ _).trans eq) Zcn.symm F.inside
      (ZhC hd ha hb (by simp [z]) old)

def Zgp {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : ZaY (insert (bin d a b) U) T) :
    ZaK (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : ZaX (insert z (U.erase a)) T a := set0 ▸ ZhD (Zox H a)
  have H1 := ZhC hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : ZaX (insert a (insert b U)) T a := eq ▸ H1
  refine ZaK.mk {a} ((insert a (insert b U)).erase a) a ?_ ?_ (ZfK a) (ZhD H1')
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp

theorem Zqk {T k S} (r : Zav false T k S) (budget : k≤S.card) :
    Nonempty (ZaK S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨Zi8 (ZfK T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := ZfH tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := ZfG tail (by change (insert z U).card=k+1; omega)
        exact ⟨Zgp hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := ZfG tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : ZaY (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := Zgp hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨Zi6 hd01 fa fb zU F⟩
theorem Zi7 {S : Finset Sig} {T : Sig} (F : ZaK S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.Zbv, bit p v=true → bit n v=false → False) :
    bit p F.Zbo=true ∧ bit n F.Zbo=false := by
  rcases F.Zbn.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.Zbn.valid hv).1 (F.Zbn.valid hv).2.1 (F.Zbn.valid hv).2.2)

theorem Zea {S : Finset Sig} {T : Sig} (F : ZaK S T) {a p n} (ao : a∈F.Zbv)
    (one : Za2 S T a p n) : F.Zbn.owns a p n := by
  rcases F.Zbn.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.Zcn wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.Zbn.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw

theorem Ziz {S : Finset Sig} {T : Sig} (F : ZaK S T) {a b p n pa pb na nb}
    (aout : a∈F.Zbv) (bout : b∈F.Zbv)
    (different : a≠b) (A : Za2 S T a p na) (B : Za2 S T b p nb)
    (C : Za2 S T a pa n) (D : Za2 S T b pb n) : False :=
  different (F.Zbn.unique (F.Zbn.Zbw (Zea F aout A) (Zea F aout C))
    (F.Zbn.Zbw (Zea F bout B) (Zea F bout D)))

theorem Ziy {S : Finset Sig} {T : Sig} (F : ZaK S T) {a b p n pa pb na nb}
    (different : a≠b) (A : Za2 F.inner F.Zbo a p na) (B : Za2 F.inner F.Zbo b p nb)
    (C : Za2 F.inner F.Zbo a pa n) (D : Za2 F.inner F.Zbo b pb n) : False :=
  different (F.inside.unique (F.inside.Zbw (ZcS F.inside A) (ZcS F.inside C))
    (F.inside.Zbw (ZcS F.inside B) (ZcS F.inside D)))
theorem Zdl {S : Finset Sig} {T : Sig} (F : ZaK S T) {v p n}
    (hv : v∈F.inner) (only : Za2 S T v p n) : Za2 F.inner F.Zbo v p n := by
  have h : bit p F.Zbo=true ∧ bit n F.Zbo=false := by
    apply Zi7 F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.Zcn hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn

theorem Za1 {S : Finset Sig} {T : Sig} (F : ZaK S T) {a b c p n pa na}
    (ar : Za2 S T a p na) (br : Za2 S T b pa n) (cr : Za2 S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := Zdl F ia ar
  have bh := Zdl F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi

theorem Zbz {S : Finset Sig} {T : Sig} (F : ZaK S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : Za2 S T a p na) (h2 : Za2 S T b p nb)
    (h3 : Za2 S T a pa n) (h4 : Za2 S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact Ziy F ne (Zdl F ia h1) (Zdl F ib h2)
      (Zdl F ia h3) (Zdl F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact Ziz F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def Zdb (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem ZdD {ws T v p n} (h : Zdb ws T v p n=true) :
    Za2 ws.toFinset T v p n := by
  simp only [Zdb,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def ZcO (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def Zd1 (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := ZcO pos (field 2)
  let n := ZcO neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    Zdb ws T a p (ZcO neg (field 4)) && Zdb ws T b p (ZcO neg (field 5)) &&
    Zdb ws T a (ZcO pos (field 6)) n && Zdb ws T b (ZcO pos (field 7)) n
theorem Zf9 {pos neg T ws k v} (h : Zd1 pos neg T ws k v=true) : Zax false T k ws.toFinset := by
  simp only [Zd1,Bool.and_eq_true,decide_eq_true_eq] at h
  exact Zro h.1.1.1.1.1 h.1.1.1.1.2 (ZdD h.1.1.1.2)
    (ZdD h.1.1.2) (ZdD h.1.2) (ZdD h.2)

def Zaa (g : Zaj) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → ZcC g k j=true ∨ Zax g.mode (ZaN g) k (Zbm g k j).toFinset
theorem Zap (g : Zaj) (k a : Nat) : Zaa g k a 0 := by
  intro j lo hi
  omega
theorem ZaD {g k a n} (h : block g k a n=true) : Zaa g k a n :=
  fun j lo hi => Or.inl (Zfw h j lo hi)
theorem Zad {g k a x y} (first : Zaa g k a x) (last : Zaa g k (a+x) y) :
    Zaa g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def Zs5 (pos neg : Nat) (g : Zaj) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => Zd1 pos neg (ZaN g) (Zbm g k (a+j)) k (Za3 data (32*j) 32))
theorem ZbB {pos neg g k a n data} (mode : g.mode=false) (h : Zs5 pos neg g k a n data=true) :
    Zaa g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change Zd1 pos neg _ (Zbm g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact Zf9 hh

def ZbM (g : Zaj) (top : Nat) := ∀ k ≤ top, Zaa g k 0 (g.levels k).1
theorem ZjT (g : Zaj) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Zaf g.mode (Zag q) (Zac q) (prior q))
    (geometry : Zaz g prior=true) (rows : ZbM g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Zax g.mode (ZaN g) k (Zbm g k i).toFinset := by
  simp only [Zaz,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact Zd8 g 0 i (Zeb geometry.1.1.1 geometry.1.1.2)
        (fun x hx => ZdO _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact Zd8 g _ i (Zeb geometry.1.1.1 geometry.1.1.2)
        (fun x hx => ZdO _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem Zhr {g top prior k i ws} (lower : ∀ q, Zaf g.mode (Zag q) (Zac q) (prior q))
    (geom : Zaz g prior=true) (blocks : ZbM g top) (le : k≤top)
    (idx : ZcV g k i ws=true) : Zax g.mode (ZaN g) k ws.toFinset := by
  simp only [ZcV,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←ZeW idx.2]
  exact ZjT g top prior lower geom blocks _ le i idx.1
abbrev Zcu := Nat × Nat × Nat
def Zcr (arity : Nat) (tags : List Zcu) : Prop :=
  ∀ {S T}, (F : ZaK S T) → (w : Nat → Sig) → (p n : Nat → Row) →
    (∀ i<arity, w i∈S) → (∀ i<arity, ∀ j<arity, i≠j → w i≠w j) →
    (∀ t∈tags, Za2 S T (w t.1) (p t.2.1) (n t.2.2)) → False
abbrev ZcE := Σ arity : Nat, { tags : List Zcu // Zcr arity tags }
abbrev ZcE.arity (pc : ZcE) := pc.1
abbrev ZcE.tags (pc : ZcE) := pc.2.val
abbrev ZcE.closed (pc : ZcE) : Zcr pc.arity pc.tags := pc.2.property

def Zh1 : List Zcu := [(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
theorem ZjU (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A2 → A1) → (A0 → A3 → A1) → (A2 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u1 : A1
  · by_cases u0 : A0
    · exact r0 (Or.inl ⟨u0,u1⟩)
    · by_cases u3 : A3
      · exact u0 (r2 u1 u3)
      · by_cases u2 : A2
        · exact u3 (r5 u2 u1)
        · exact r1 (Or.inr ⟨u2,u3⟩)
  · by_cases u0 : A0
    · by_cases u3 : A3
      · exact u1 (r4 u0 u3)
      · by_cases u2 : A2
        · exact u1 (r3 u0 u2)
        · exact r1 (Or.inr ⟨u2,u3⟩)
    · exact r0 (Or.inr ⟨u0,u1⟩)
theorem Zte : Zcr 4 Zh1 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,2) (by decide)
  have c1 := Zab (1,1,2) (by decide)
  have c2 := Zab (2,2,3) (by decide)
  have c3 := Zab (3,3,3) (by decide)
  have c4 := Zab (0,4,1) (by decide)
  have c5 := Zab (1,4,3) (by decide)
  have c6 := Zab (2,5,0) (by decide)
  have c7 := Zab (3,5,1) (by decide)
  have c8 := Zab (3,5,2) (by decide)
  have r0 := Zbz F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := Zbz F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := Za1 F c5 c7 c4
  have r3 := Za1 F c4 c2 c5
  have r4 := Za1 F c4 c3 c5
  have r5 := Za1 F c6 c1 c8
  exact ZjU (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def Zh2 : List Zcu := [(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
theorem ZjV (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A3 → A1) → (A2 → A0 → A3) → (A3 → A1 → A2) → (A0 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u3 : A3
  · by_cases u0 : A0
    · exact r1 (Or.inl ⟨u0,u3⟩)
    · by_cases u1 : A1
      · by_cases u2 : A2
        · exact r0 (Or.inl ⟨u1,u2⟩)
        · exact u2 (r4 u3 u1)
      · by_cases u2 : A2
        · exact u1 (r2 u2 u3)
        · exact r0 (Or.inr ⟨u1,u2⟩)
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact u3 (r5 u0 u1)
      · by_cases u2 : A2
        · exact u3 (r3 u2 u0)
        · exact r0 (Or.inr ⟨u1,u2⟩)
    · exact r1 (Or.inr ⟨u0,u3⟩)
theorem Ztf : Zcr 4 Zh2 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,1) (by decide)
  have c1 := Zab (1,1,3) (by decide)
  have c2 := Zab (2,2,0) (by decide)
  have c3 := Zab (1,2,2) (by decide)
  have c4 := Zab (3,3,1) (by decide)
  have c5 := Zab (2,3,3) (by decide)
  have c6 := Zab (3,4,2) (by decide)
  have c7 := Zab (0,4,3) (by decide)
  have r0 := Zbz F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := Zbz F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4
  have r2 := Za1 F c2 c6 c3
  have r3 := Za1 F c5 c0 c4
  have r4 := Za1 F c4 c1 c5
  have r5 := Za1 F c7 c3 c6
  exact ZjV (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def Zh3 : List Zcu := [(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
theorem ZjW (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A2) → (A2 → A0 → A1) → False := by
  intro r0 r1 r2 r3 r4
  by_cases u2 : A2
  · by_cases u1 : A1
    · exact r0 (Or.inl ⟨u1,u2⟩)
    · by_cases u3 : A3
      · exact r2 (Or.inl ⟨u2,u3⟩)
      · by_cases u0 : A0
        · exact u1 (r4 u2 u0)
        · exact r1 (Or.inr ⟨u0,u3⟩)
  · by_cases u1 : A1
    · by_cases u3 : A3
      · exact u2 (r3 u1 u3)
      · exact r2 (Or.inr ⟨u2,u3⟩)
    · exact r0 (Or.inr ⟨u1,u2⟩)
theorem Ztg : Zcr 4 Zh3 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,2) (by decide)
  have c1 := Zab (1,1,1) (by decide)
  have c2 := Zab (2,2,0) (by decide)
  have c3 := Zab (1,2,2) (by decide)
  have c4 := Zab (3,3,0) (by decide)
  have c5 := Zab (0,3,1) (by decide)
  have c6 := Zab (2,4,1) (by decide)
  have c7 := Zab (3,4,2) (by decide)
  have r0 := Zbz F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6
  have r1 := Zbz F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7
  have r2 := Zbz F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4
  have r3 := Za1 F c3 c4 c2
  have r4 := Za1 F c2 c0 c3
  exact ZjW (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def Zh4 : List Zcu := [(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
theorem ZjX (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (A3 → A1 → A2) → (A2 → A1 → A3) → (A0 → A2 → A1) → (A0 → A3 → A1) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u1 : A1
  · by_cases u0 : A0
    · exact r1 (Or.inl ⟨u0,u1⟩)
    · by_cases u2 : A2
      · by_cases u3 : A3
        · exact r0 (Or.inl ⟨u2,u3⟩)
        · exact u3 (r3 u2 u1)
      · by_cases u3 : A3
        · exact u2 (r2 u3 u1)
        · exact r0 (Or.inr ⟨u2,u3⟩)
  · by_cases u0 : A0
    · by_cases u2 : A2
      · exact u1 (r4 u0 u2)
      · by_cases u3 : A3
        · exact u1 (r5 u0 u3)
        · exact r0 (Or.inr ⟨u2,u3⟩)
    · exact r1 (Or.inr ⟨u0,u1⟩)
theorem Zth : Zcr 4 Zh4 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,0) (by decide)
  have c1 := Zab (1,1,0) (by decide)
  have c2 := Zab (2,2,3) (by decide)
  have c3 := Zab (3,3,3) (by decide)
  have c4 := Zab (2,4,1) (by decide)
  have c5 := Zab (3,4,2) (by decide)
  have c6 := Zab (1,5,1) (by decide)
  have c7 := Zab (1,5,2) (by decide)
  have c8 := Zab (0,5,3) (by decide)
  have r0 := Zbz F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3
  have r1 := Zbz F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1
  have r2 := Za1 F c5 c6 c4
  have r3 := Za1 F c4 c7 c5
  have r4 := Za1 F c8 c4 c6
  have r5 := Za1 F c8 c5 c7
  exact ZjX (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def Zh5 : List Zcu := [(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
theorem ZjY (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A3 → A1) → (A2 → A0 → A3) → (A2 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u3 : A3
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact r0 (Or.inl ⟨u0,u1⟩)
      · exact u1 (r3 u0 u3)
    · by_cases u1 : A1
      · exact u0 (r2 u1 u3)
      · exact r0 (Or.inr ⟨u0,u1⟩)
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact r0 (Or.inl ⟨u0,u1⟩)
      · by_cases u2 : A2
        · exact u3 (r4 u2 u0)
        · exact r1 (Or.inr ⟨u2,u3⟩)
    · by_cases u1 : A1
      · by_cases u2 : A2
        · exact u3 (r5 u2 u1)
        · exact r1 (Or.inr ⟨u2,u3⟩)
      · exact r0 (Or.inr ⟨u0,u1⟩)
theorem Zti : Zcr 4 Zh5 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,3) (by decide)
  have c1 := Zab (1,1,3) (by decide)
  have c2 := Zab (2,2,3) (by decide)
  have c3 := Zab (3,3,3) (by decide)
  have c4 := Zab (0,4,1) (by decide)
  have c5 := Zab (1,4,2) (by decide)
  have c6 := Zab (2,5,0) (by decide)
  have c7 := Zab (3,5,1) (by decide)
  have c8 := Zab (3,5,2) (by decide)
  have r0 := Zbz F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := Zbz F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := Za1 F c5 c7 c4
  have r3 := Za1 F c4 c8 c5
  have r4 := Za1 F c6 c4 c7
  have r5 := Za1 F c6 c5 c8
  exact ZjY (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def Zh6 : List Zcu := [(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
theorem ZjZ (A0 A1 A2 A3 A4 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A0 → A1) → (A3 → A1 → A2) → (A0 → A1 → A2) → (A2 → A4 → A1) → (A3 → A2 → A4) → False := by
  intro r0 r1 r2 r3 r4 r5 r6
  by_cases u2 : A2
  · by_cases u1 : A1
    · exact r0 (Or.inl ⟨u1,u2⟩)
    · by_cases u0 : A0
      · exact u1 (r2 u2 u0)
      · by_cases u3 : A3
        · by_cases u4 : A4
          · exact u1 (r5 u2 u4)
          · exact u4 (r6 u3 u2)
        · exact r1 (Or.inr ⟨u0,u3⟩)
  · by_cases u1 : A1
    · by_cases u0 : A0
      · exact u2 (r4 u0 u1)
      · by_cases u3 : A3
        · exact u2 (r3 u3 u1)
        · exact r1 (Or.inr ⟨u0,u3⟩)
    · exact r0 (Or.inr ⟨u1,u2⟩)
theorem Ztj : Zcr 5 Zh6 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,2) (by decide)
  have c1 := Zab (1,1,3) (by decide)
  have c2 := Zab (2,2,0) (by decide)
  have c3 := Zab (1,2,4) (by decide)
  have c4 := Zab (3,3,1) (by decide)
  have c5 := Zab (2,3,3) (by decide)
  have c6 := Zab (0,3,4) (by decide)
  have c7 := Zab (3,4,2) (by decide)
  have c8 := Zab (4,4,3) (by decide)
  have c9 := Zab (4,4,4) (by decide)
  have r0 := Zbz F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := Zbz F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7
  have r2 := Za1 F c2 c6 c3
  have r3 := Za1 F c4 c1 c5
  have r4 := Za1 F c6 c1 c5
  have r5 := Za1 F c2 c9 c3
  have r6 := Za1 F c7 c5 c8
  exact ZjZ (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def Zh7 : List Zcu := [(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
theorem Zj0 (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A1 ∧ A3) ∨ (¬A1 ∧ ¬A3)) → False) → (A2 → A1 → A3) → (A0 → A3 → A1) → False := by
  intro r0 r1 r2 r3 r4
  by_cases u1 : A1
  · by_cases u3 : A3
    · exact r2 (Or.inl ⟨u1,u3⟩)
    · by_cases u0 : A0
      · exact r1 (Or.inl ⟨u0,u1⟩)
      · by_cases u2 : A2
        · exact u3 (r3 u2 u1)
        · exact r0 (Or.inr ⟨u2,u3⟩)
  · by_cases u3 : A3
    · by_cases u0 : A0
      · exact u1 (r4 u0 u3)
      · exact r1 (Or.inr ⟨u0,u1⟩)
    · exact r2 (Or.inr ⟨u1,u3⟩)
theorem Ztk : Zcr 4 Zh7 := by
  intro S T F w p n mem diff Zab
  have c0 := Zab (0,0,0) (by decide)
  have c1 := Zab (1,1,0) (by decide)
  have c2 := Zab (2,2,3) (by decide)
  have c3 := Zab (2,3,1) (by decide)
  have c4 := Zab (3,3,2) (by decide)
  have c5 := Zab (1,4,2) (by decide)
  have c6 := Zab (0,4,3) (by decide)
  have c7 := Zab (1,5,1) (by decide)
  have c8 := Zab (3,5,3) (by decide)
  have r0 := Zbz F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8
  have r1 := Zbz F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1
  have r2 := Zbz F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4
  have r3 := Za1 F c3 c5 c4
  have r4 := Za1 F c6 c4 c5
  exact Zj0 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def ZrN : Nat → ZcE
  | 0 => ⟨4,Zh1,Zte⟩
  | 1 => ⟨4,Zh2,Ztf⟩
  | 2 => ⟨4,Zh3,Ztg⟩
  | 3 => ⟨4,Zh4,Zth⟩
  | 4 => ⟨4,Zh5,Zti⟩
  | 5 => ⟨5,Zh6,Ztj⟩
  | _ => ⟨4,Zh7,Ztk⟩
def Zle (arity : Nat) (ws : List Sig) (w : Nat→Sig) :=
  (List.range arity).all (fun i => decide (w i∈ws) &&
    (List.range arity).all (fun j => (i==j) || decide (w i≠w j)))
def ZgP (pc : ZcE) (ws : List Sig) (T : Sig) (w : Nat→Sig) (p n : Nat→Row) :=
  Zle pc.arity ws w &&
    pc.tags.all (fun t => Zdb ws T (w t.1) (p t.2.1) (n t.2.2))
theorem Zex {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
theorem Zit {pc ws T w p n} (F : ZaK (List.toFinset ws) T)
    (h : ZgP pc ws T w p n=true) : False := by
  have ij := (Zex h).1
  have hrow (i : Nat) (hi : i<pc.arity) := Zex
    (List.all_eq_true.mp ij i (List.mem_range.mpr hi))
  apply pc.closed F w p n
  · intro i hi
    exact List.mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
  · intro i hi j hj ne
    have one := List.all_eq_true.mp (hrow i hi).2 j (List.mem_range.mpr hj)
    have diff : (i==j)=false := beq_eq_false_iff_ne.mpr ne
    simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
  · intro t ht
    exact ZdD (List.all_eq_true.mp (Zex h).2 t ht)

def Zeo (pos neg : Nat) (ws : List Sig) (T : Sig) (k rec : Nat) :=
  let field := fun i => (rec >>> (4*i)) &&& 15
  decide (k≤ws.toFinset.card) && ZgP (ZrN (field 0)) ws T
    (fun i => ws.getD (field (1+i)) zero)
    (fun i => ZcO pos (field (6+i))) (fun i => ZcO neg (field (12+i)))
theorem ZfT {pos neg ws T k rec} (ok : Zeo pos neg ws T k rec=true) :
    Zax false T k ws.toFinset := by
  obtain ⟨bound,check⟩ := Zex ok
  intro j hj live
  obtain ⟨F⟩ := Zqk live (hj.trans (of_decide_eq_true bound))
  exact Zit F check
def ZaJ : Nat := 0x9050141084210842110c0300c03
def ZaI : Nat := 0xc9606290568325147434114642a
def ZiE (pos neg : Nat) (g : Zaj) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun i => Zeo pos neg (Zbm g k (start+i)) (ZaN g) k (Za3 data (68*i) 68))
theorem ZaV {pos neg g k start n data} (mode : g.mode=false)
    (ok : ZiE pos neg g k start n data=true) : Zaa g k start n := by
  intro j lo hi
  right
  rw [mode]
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  change Zeo pos neg (Zbm g k (start+(j-start))) (ZaN g) k _=true at h
  rw [e] at h
  exact ZfT h
def Ze0 (pos neg : Nat) (g : Zaj) (k i : Nat) (kw panels : Nat→Nat) (tag : Nat) :=
  if tag=0 then ZcC g k i else if tag<128 then
    Zd1 pos neg (ZaN g) (Zbm g k i) k (Za3 kw (32*(tag-1)) 32)
  else Zeo pos neg (Zbm g k i) (ZaN g) k (Za3 panels (68*(tag-128)) 68)
def Ziu (pos neg : Nat) (g : Zaj) (k start n : Nat) (kw panels : Nat→Nat) (data : Nat) :=
  (List.range n).all fun j => Ze0 pos neg g k (start+j) kw panels ((data >>> (8*j)) &&& 255)
theorem Zar {pos neg g k start n kw panels data} (mode : g.mode=false)
    (h : Ziu pos neg g k start n kw panels data=true) : Zaa g k start n := by
  intro j lo hi
  have one := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have eq : start+(j-start)=j := by omega
  change Ze0 pos neg g k (start+(j-start)) kw panels _=true at one
  rw [eq] at one
  unfold Ze0 at one
  split at one
  · exact Or.inl one
  · right
    rw [mode]
    split at one
    · exact Zf9 one
    · exact ZfT one
theorem ZaM {u} {g : Zaj} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Zaf u (Zag q) (Zac q) (prior q))
    (geom : Zaz g prior=true) (blocks : ZbM g cap)
    (idx : ZcV g cap i ws=true) : Zax u (Zac m) cap ws.toFinset := by
  subst hm
  subst hu
  exact Zhr low geom blocks (Nat.le_refl _) idx

end PEqualNP.Outside.L_meta_670
