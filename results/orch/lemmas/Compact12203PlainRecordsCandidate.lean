import PEqualNP.Defs
-- Proof and certificates by 0xshuzo, PR12203, revision 0d2bbcdeb511ffff33552e155db3526648d8575b.
-- https://github.com/open-goat/pequalnp-proofs/pull/12203
-- Original proof, batching, data, and credits are retained without modification.

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
def Zuj (i : Nat) : Nat := 0xf
def Zuk : Zah := (1,0,1,0,0,0,0,Zuj)
def ZkT : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def ZkS : List Za7 := []
def Zoy : List (List Nat) := [[],[48,33]]
def Zm0 : Nat → Zah
  | 3 => Zuk
  | _ => Zbs
def Zoz : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Zaj := ⟨15,3,fun j => ZkT[j]?.getD (0,0),ZkS,Zoy,Zm0,Zoz⟩
set_option maxHeartbeats 0 in
theorem Zrd : Zaz g15 (Zat []) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zqp : block g15 3 0 1=true := by decide +kernel
theorem Zoo : block g15 3 0 1=true := Zqp
theorem Znx : ZbS g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact Zoo
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zuv : Zaf true (vars 15) (Zac 15) 4 := ZbN (hints:=8449) (by decide +kernel) (ZcW (g:=g15) (i:=0) rfl rfl (Zai [] ZgV) Zrd Znx (by decide +kernel))
def ZeI := Zan [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zh8 : Zak true ZeI := Zao (m:=15) ZgV Zuv (by decide +kernel)
def Zun (i : Nat) : Nat := 0x11a20bf
def Zus : Zah := (1,0,3,0,0,0,0,Zun)
def Zup (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def Zum (i : Nat) : Nat := 0x40828fd20fd10
def Zur : Zah := (2,1,3,0,0,3,0,Zum)
def Zuo (i : Nat) : Nat := 0x300
def Zul (i : Nat) : Nat := 0x5dd4520
def Zuq : Zah := (1,2,3,0,0,0,0,Zul)
def ZkX : Array (Bits × Bits) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def ZkW : List Za7 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def ZhE : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def Zm3 : Nat → Zah
  | 6 => Zus
  | 5 => Zur
  | 4 => Zuq
  | _ => Zbs
def ZoA : Nat → Nat → Option (Nat × Nat)
  | 6 => ZaH 5 15 3 9 1 4 Zup
  | 5 => ZaH 1 3 1 9 1 4 Zuo
  | _ => fun _ => none
def g31 : Zaj := ⟨31,6,fun j => ZkX[j]?.getD (0,0),ZkW,ZhE,Zm3,ZoA⟩
set_option maxHeartbeats 0 in
theorem Zre : Zaz g31 (Zat ZeI) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=1) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zqs : block g31 6 0 1=true := by decide +kernel
theorem Zor : block g31 6 0 1=true := Zqs
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zqr : block g31 5 0 2=true := by decide +kernel
theorem Zoq : block g31 5 0 2=true := Zqr
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zqq : block g31 4 0 1=true := by decide +kernel
theorem Zop : block g31 4 0 1=true := Zqq
theorem Zny : ZbS g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact Zop
  · exact Zoq
  · exact Zor
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zuw : Zaf true (vars 31) (Zac 31) 7 := ZbN (hints:=8449) (by decide +kernel) (ZcW (g:=g31) (i:=0) rfl rfl (Zai ZeI Zh8) Zre Zny (by decide +kernel))
def ZeJ := Zan ZeI 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zh9 : Zak true ZeJ := Zao (m:=31) Zh8 Zuw (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zux : Zaf true (vars 47) (Zac 47) 5 := ZbN (hints:=8449) (by decide +kernel) (Za0 (prior:=Zat ZeJ) (Zai ZeJ Zh9) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def ZeK := Zan ZeJ 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zia : Zak true ZeK := Zao (m:=47) Zh9 Zux (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zuy : Zaf true (vars 55) (Zac 55) 5 := ZbN (hints:=257) (by decide +kernel) (Za0 (prior:=Zat ZeK) (Zai ZeK Zia) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def ZeL := Zan ZeK 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zib : Zak true ZeL := Zao (m:=55) Zia Zuy (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zuz : Zaf true (vars 63) (Zac 63) 8 := ZbN (hints:=8449) (by decide +kernel) (Za0 (prior:=Zat ZeL) (Zai ZeL Zib) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def ZeM := Zan ZeL 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zic : Zak true ZeM := Zao (m:=63) Zib Zuz (by decide +kernel)
def Zsq (i : Nat) : Nat := 0x7213f
def Zst : Zah := (1,0,2,0,0,0,0,Zsq)
def Zsr (i : Nat) : Nat := 0x8000
def Zsp (i : Nat) : Nat := 0x17e51
def Zss : Zah := (1,1,2,0,0,0,0,Zsp)
def ZjI : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def ZjH : List Za7 := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def ZmY : List (List Nat) := [[],[32,83]]
def ZkR : Nat → Zah
  | 6 => Zst
  | 5 => Zss
  | _ => Zbs
def ZmZ : Nat → Nat → Option (Nat × Nat)
  | 6 => ZaH 1 3 1 6 1 1 Zsr
  | _ => fun _ => none
def Zb1 : Zaj := ⟨111,6,fun j => ZjI[j]?.getD (0,0),ZjH,ZmY,ZkR,ZmZ⟩
set_option maxHeartbeats 0 in
theorem ZoC : Zaz Zb1 (Zat ZeM) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znh : block Zb1 6 0 1=true := by decide +kernel
theorem ZmG : block Zb1 6 0 1=true := Znh
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zng : block Zb1 5 0 1=true := by decide +kernel
theorem ZmF : block Zb1 5 0 1=true := Zng
theorem ZlK : ZbS Zb1 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block Zb1 0 0 0 = true)
  · exact (rfl : block Zb1 1 0 0 = true)
  · exact (rfl : block Zb1 2 0 0 = true)
  · exact (rfl : block Zb1 3 0 0 = true)
  · exact (rfl : block Zb1 4 0 0 = true)
  · exact ZmF
  · exact ZmG
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zs6 : Zaf true (vars 111) (Zac 111) 7 := ZbN (hints:=16785665) (by decide +kernel) (ZcW (g:=Zb1) (i:=0) rfl rfl (Zai ZeM Zic) ZoC ZlK (by decide +kernel))
def Zer := Zan ZeM 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhM : Zak true Zer := Zao (m:=111) Zic Zs6 (by decide +kernel)
def Zsw (i : Nat) : Nat := 0x163441bf
def ZsB : Zah := (1,0,3,0,0,0,0,Zsw)
def Zsy (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def Zsv (i : Nat) : Nat := 0x420a3fa41fd10
def ZsA : Zah := (2,1,3,0,0,3,0,Zsv)
def Zsx (i : Nat) : Nat := 0x18000
def Zsu (i : Nat) : Nat := 0xb7d8d20
def Zsz : Zah := (1,2,3,0,0,0,0,Zsu)
def ZjK : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def ZjJ : List Za7 := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def Zg1 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def ZkU : Nat → Zah
  | 7 => ZsB
  | 6 => ZsA
  | 5 => Zsz
  | _ => Zbs
def Zm1 : Nat → Nat → Option (Nat × Nat)
  | 7 => ZaH 9 13 2 9 1 4 Zsy
  | 6 => ZaH 1 3 1 9 1 4 Zsx
  | _ => fun _ => none
def ZbK : Zaj := ⟨189,7,fun j => ZjK[j]?.getD (0,0),ZjJ,Zg1,ZkU,Zm1⟩
set_option maxHeartbeats 0 in
theorem ZoD : Zaz ZbK (Zat Zer) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=1) ?_⟩,ZaF (d:=2) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znk : block ZbK 7 0 1=true := by decide +kernel
theorem ZmJ : block ZbK 7 0 1=true := Znk
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znj : block ZbK 6 0 2=true := by decide +kernel
theorem ZmI : block ZbK 6 0 2=true := Znj
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zni : block ZbK 5 0 1=true := by decide +kernel
theorem ZmH : block ZbK 5 0 1=true := Zni
theorem ZlL : ZbS ZbK 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block ZbK 0 0 0 = true)
  · exact (rfl : block ZbK 1 0 0 = true)
  · exact (rfl : block ZbK 2 0 0 = true)
  · exact (rfl : block ZbK 3 0 0 = true)
  · exact (rfl : block ZbK 4 0 0 = true)
  · exact ZmH
  · exact ZmI
  · exact ZmJ
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zs8 : Zaf true (vars 189) (Zac 189) 8 := ZbN (hints:=536879876) (by decide +kernel) (ZcW (g:=ZbK) (i:=0) rfl rfl (Zai Zer ZhM) ZoD ZlL (by decide +kernel))
def Zet := Zan Zer 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhO : Zak true Zet := Zao (m:=189) ZhM Zs8 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zs7 : Zaf true (vars 127) (Zac 127) 9 := ZbN (hints:=16785665) (by decide +kernel) (Za0 (prior:=Zat Zet) (Zai Zet ZhO) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def Zes := Zan Zet 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhN : Zak true Zes := Zao (m:=127) ZhO Zs7 (by decide +kernel)
def Zq1 (i : Nat) : Nat := 0x8201ff
def Zq3 : Zah := (1,0,5,0,0,0,0,Zq1)
def Zq2 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def ZsF (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def ZsM : Zah := (12,1,5,0,0,10,0,ZsF)
def ZsI (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def ZsE (j : Nat) : Nat := 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def ZsL : Zah := (113,2,5,589836,68,12,1057,ZsE)
def ZsH (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def ZsD (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def ZsK : Zah := (116,3,5,0,0,11,0,ZsD)
def ZsG (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def ZsC (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def ZsJ : Zah := (12,4,5,0,0,6,0,ZsC)
def ZjM : Array (Bits × Bits) := #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]
def ZjL : List Za7 := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def Zfq : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def ZkV : Nat → Zah
  | 10 => Zq3
  | 9 => ZsM
  | 8 => ZsL
  | 7 => ZsK
  | 6 => ZsJ
  | _ => Zbs
def Zm2 : Nat → Nat → Option (Nat × Nat)
  | 10 => ZaH 16 41 5 10 4 2 Zq2
  | 9 => ZaH 67 277 6 13 7 2 ZsI
  | 8 => ZaH 100 251 6 13 7 2 ZsH
  | 7 => ZaH 4 19 2 10 4 2 ZsG
  | _ => fun _ => none
def ZaL : Zaj := ⟨191,10,fun j => ZjM[j]?.getD (0,0),ZjL,Zfq,ZkV,Zm2⟩
set_option maxHeartbeats 0 in
theorem ZoE : Zaz ZaL (Zat Zes) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=3) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zli : block ZaL 10 0 1=true := by decide +kernel
theorem ZkH : block ZaL 10 0 1=true := Zli
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znp : block ZaL 9 0 12=true := by
  apply Zau (ar:=8) (rows:=0) (d:=2)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmN : block ZaL 9 0 12=true := Znp
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znn : block ZaL 8 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zno : block ZaL 8 3 36=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlm : block ZaL 8 39 31=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zln : block ZaL 8 70 36=true := by
  apply Zau (ar:=9) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zj2 : block ZaL 8 106 7=true := by
  apply Zau (ar:=9) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmM : block ZaL 8 0 113=true := (@ZaR ZaL 8 0 106 7 (@ZaR ZaL 8 0 70 36 (@ZaR ZaL 8 0 39 31 (@ZaR ZaL 8 0 3 36 Znn Zno) Zlm) Zln) Zj2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znm : block ZaL 7 0 13=true := by
  apply Zau (ar:=7) (rows:=0) (d:=2)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlj : block ZaL 7 13 36=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlk : block ZaL 7 49 36=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zll : block ZaL 7 85 31=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmL : block ZaL 7 0 116=true := (@ZaR ZaL 7 0 85 31 (@ZaR ZaL 7 0 49 36 (@ZaR ZaL 7 0 13 36 Znm Zlj) Zlk) Zll)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znl : block ZaL 6 0 12=true := by
  apply Zau (ar:=7) (rows:=0) (d:=2)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmK : block ZaL 6 0 12=true := Znl
theorem ZlM : ZbS ZaL 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block ZaL 0 0 0 = true)
  · exact (rfl : block ZaL 1 0 0 = true)
  · exact (rfl : block ZaL 2 0 0 = true)
  · exact (rfl : block ZaL 3 0 0 = true)
  · exact (rfl : block ZaL 4 0 0 = true)
  · exact (rfl : block ZaL 5 0 0 = true)
  · exact ZmK
  · exact ZmL
  · exact ZmM
  · exact ZmN
  · exact ZkH
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zs9 : Zaf true (vars 191) (Zac 191) 11 := ZbN (hints:=536879361) (by decide +kernel) (ZcW (g:=ZaL) (i:=0) rfl rfl (Zai Zes ZhN) ZoE ZlM (by decide +kernel))
def Zeu := Zan Zes 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhP : Zak true Zeu := Zao (m:=191) ZhN Zs9 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zta : Zaf true (vars 251) (Zac 251) 8 := ZbN (hints:=1358970881) (by decide +kernel) (Za0 (prior:=Zat Zeu) (Zai Zeu ZhP) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def Zev := Zan Zeu 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhQ : Zak true Zev := Zao (m:=251) ZhP Zta (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Ztb : Zaf true (vars 255) (Zac 255) 12 := ZbN (hints:=553656577) (by decide +kernel) (Za0 (prior:=Zat Zev) (Zai Zev ZhQ) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def Zew := Zan Zev 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhR : Zak true Zew := Zao (m:=255) ZhQ Ztb (by decide +kernel)
def Zq6 (i : Nat) : Nat := 0x1840804ff
def Zrc : Zah := (1,0,6,0,0,0,0,Zq6)
def Zq9 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def Zq5 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def Zrb : Zah := (6,1,6,0,0,9,0,Zq5)
def Zq8 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def Zq4 (j : Nat) : Nat := 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def Zra : Zah := (47,2,6,524294,51,11,1060,Zq4)
def Zq7 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def ZsP (j : Nat) : Nat := (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def ZsU : Zah := (136,3,6,1638440,86,12,1083,ZsP)
def ZsR (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def ZsO (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def ZsT : Zah := (53,4,6,0,0,9,0,ZsO)
def ZsQ (i : Nat) : Nat := 0x834601a000
def ZsN (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def ZsS : Zah := (2,5,6,0,0,3,0,ZsN)
def ZjO : Array (Bits × Bits) := #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]
def ZjN : List Za7 := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def Zg2 : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def ZkY : Nat → Zah
  | 12 => Zrc
  | 11 => Zrb
  | 10 => Zra
  | 9 => ZsU
  | 8 => ZsT
  | 7 => ZsS
  | _ => Zbs
def Zm4 : Nat → Nat → Option (Nat × Nat)
  | 12 => ZaH 8 37 4 10 3 3 Zq9
  | 11 => ZaH 48 123 4 13 6 3 Zq8
  | 10 => ZaH 79 299 8 15 8 3 Zq7
  | 9 => ZaH 39 99 5 13 6 3 ZsR
  | 8 => ZaH 1 5 1 8 1 3 ZsQ
  | _ => fun _ => none
def ZaE : Zaj := ⟨383,12,fun j => ZjO[j]?.getD (0,0),ZjN,Zg2,ZkY,Zm4⟩
set_option maxHeartbeats 0 in
theorem ZoF : Zaz ZaE (Zat Zew) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=3) ?_⟩,ZaF (d:=1) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlr : block ZaE 12 0 1=true := by decide +kernel
theorem ZkK : block ZaE 12 0 1=true := Zlr
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlq : block ZaE 11 0 6=true := by
  apply Zau (ar:=9) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZkJ : block ZaE 11 0 6=true := Zlq
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlo : block ZaE 10 0 6=true := by
  apply Zau (ar:=8) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlp : block ZaE 10 6 13=true := by
  apply Zau (ar:=9) (rows:=0) (d:=2)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zj3 : block ZaE 10 19 28=true := by
  apply Zau (ar:=10) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZkI : block ZaE 10 0 47=true := (@ZaR ZaE 10 0 19 28 (@ZaR ZaE 10 0 6 13 Zlo Zlp) Zj3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zns : block ZaE 9 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znt : block ZaE 9 3 36=true := by
  apply Zau (ar:=9) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlu : block ZaE 9 39 36=true := by
  apply Zau (ar:=9) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlv : block ZaE 9 75 36=true := by
  apply Zau (ar:=9) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zj4 : block ZaE 9 111 8=true := by
  apply Zau (ar:=9) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zj5 : block ZaE 9 119 17=true := by
  apply Zau (ar:=10) (rows:=0) (d:=2)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmQ : block ZaE 9 0 136=true := (@ZaR ZaE 9 0 119 17 (@ZaR ZaE 9 0 111 8 (@ZaR ZaE 9 0 75 36 (@ZaR ZaE 9 0 39 36 (@ZaR ZaE 9 0 3 36 Zns Znt) Zlu) Zlv) Zj4) Zj5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znr : block ZaE 8 0 36=true := by
  apply Zau (ar:=8) (rows:=0) (d:=3)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zls : block ZaE 8 36 8=true := by
  apply Zau (ar:=8) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Zlt : block ZaE 8 44 9=true := by
  apply Zau (ar:=9) (rows:=0) (d:=1)
  simp only [Zab,Zas,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZmP : block ZaE 8 0 53=true := (@ZaR ZaE 8 0 44 9 (@ZaR ZaE 8 0 36 8 Znr Zls) Zlt)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem Znq : block ZaE 7 0 2=true := by decide +kernel
theorem ZmO : block ZaE 7 0 2=true := Znq
theorem ZlN : ZbS ZaE 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block ZaE 0 0 0 = true)
  · exact (rfl : block ZaE 1 0 0 = true)
  · exact (rfl : block ZaE 2 0 0 = true)
  · exact (rfl : block ZaE 3 0 0 = true)
  · exact (rfl : block ZaE 4 0 0 = true)
  · exact (rfl : block ZaE 5 0 0 = true)
  · exact (rfl : block ZaE 6 0 0 = true)
  · exact ZmO
  · exact ZmP
  · exact ZmQ
  · exact ZkI
  · exact ZkJ
  · exact ZkK
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Ztc : Zaf true (vars 383) (Zac 383) 13 := ZbN (hints:=12901687553) (by decide +kernel) (ZcW (g:=ZaE) (i:=0) rfl rfl (Zai Zew ZhR) ZoF ZlN (by decide +kernel))
def Zcw := Zan Zew 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZhS : Zak true Zcw := Zao (m:=383) ZhR Ztc (by decide +kernel)
theorem ZeQ : Zak false Zcw := Zk0 ZhS
def Zu3 (i : Nat) : Nat := 0x1a230180fd10fc20
def Zu6 : Zah := (2,1,2,0,0,4,0,Zu3)
def Zu4 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def Zu2 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def Zu5 : Zah := (5,2,2,0,0,5,0,Zu2)
def Zmi : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffc47,0xa86),(0xfffffffffffffffffffffffffffffffffff09b,0xfffffffffffffffffffffffffffffffffff531),(0x29c,0x8cc),(0xfffffffffffffffffffffffffffffffffff327,0xfffffffffffffffffffffffffffffffffff303),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def Zmh : List Za7 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def ZqH : List (List Nat) := ZhE
def Zn5 : Nat → Zah
  | 6 => Zu6
  | 5 => Zu5
  | _ => Zbs
def ZqI : Nat → Nat → Option (Nat × Nat)
  | 6 => ZaH 8 11 1 11 3 4 Zu4
  | _ => fun _ => none
def x31 : Zaj := ⟨1055,6,fun j => Zmi[j]?.getD (0,0),Zmh,ZqH,Zn5,ZqI⟩
set_option maxHeartbeats 0 in
theorem ZhV : Zaz x31 (Zat Zcw) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=1) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zvx : Nat := 0x110c0300c03
def Zvw : Nat := 0x14090281205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zm7 : Zaa x31 6 0 2 := by
  exact ZaD (by decide +kernel)
theorem Zrn : Zaa x31 6 0 2 := Zm7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zm6 : Zaa x31 5 0 5 := by
  apply ZbB (pos:=Zvx) (neg:=Zvw) (data:=fun _ => 0x4224033220301121141340101413401031423232) rfl
  decide +kernel
theorem Zrm : Zaa x31 5 0 5 := Zm6
theorem Zhv : ZbM x31 6 := by
  intro k hk
  interval_cases k
  · exact Zap x31 0 0
  · exact Zap x31 1 0
  · exact Zap x31 2 0
  · exact Zap x31 3 0
  · exact Zap x31 4 0
  · exact Zrm
  · exact Zrn
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Ziq : Zax false (Zac 1055) 6 (vars 1055).toFinset := Zcz (q:=31) (prior:=Zat Zcw) (Zai Zcw ZeQ) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zru : Zaf false (Zag 1567) (Zac 1567) 7 :=
  Zaw (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ziq
    (ZaM (g:=x31) (i:=0) rfl rfl (Zai Zcw ZeQ) ZhV Zhv (by decide +kernel))
def Zg8 := Zan Zcw 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnD : Zak false Zg8 := Zao (m:=1567) ZeQ Zru (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpR : Zaf false (Zag 42527) (Zac 42527) 7 :=
  Zaw (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ziq
    (ZaM (g:=x31) (i:=1) rfl rfl (Zai Zcw ZeQ) ZhV Zhv (by decide +kernel))
def ZcX := Zan Zg8 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zeg : Zak false ZcX := Zao (m:=42527) ZnD ZpR (by decide +kernel)
def Ztm (i : Nat) : Nat := 0x1040a3fa21fd51
def Ztp : Zah := (2,1,1,0,0,3,0,Ztm)
def Ztn (i : Nat) : Nat := 0x40000
def Ztl (i : Nat) : Nat := 0x102de54110
def Zto : Zah := (1,2,1,0,0,0,0,Ztl)
def Zkc : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffff9b5,0xe94),(0xfffffffffffffffffffffffffffffffffff0db,0xfffffffffffffffffffffffffffffffffff10b),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def Zkb : List Za7 := [(96,0,15,0,4),(1,32,78,0,4)]
def ZnT : List (List Nat) := [[],[32,83]]
def Zmb : Nat → Zah
  | 6 => Ztp
  | 5 => Zto
  | _ => Zbs
def ZnU : Nat → Nat → Option (Nat × Nat)
  | 6 => ZaH 1 3 1 6 1 1 Ztn
  | _ => fun _ => none
def ZbR : Zaj := ⟨1135,6,fun j => Zkc[j]?.getD (0,0),Zkb,ZnT,Zmb,ZnU⟩
set_option maxHeartbeats 0 in
theorem ZhF : Zaz ZbR (Zat ZcX) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zil : Nat := 0x42108300c03
def Zik : Nat := 0x68321248a2a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk2 : Zaa ZbR 6 0 2 := by
  apply ZbB (pos:=Zil) (neg:=Zik) (data:=fun _ => 0x2401212143203010) rfl
  decide +kernel
theorem ZpF : Zaa ZbR 6 0 2 := Zk2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk1 : Zaa ZbR 5 0 1 := by
  apply ZbB (pos:=Zil) (neg:=Zik) (data:=fun _ => 0x24012110) rfl
  decide +kernel
theorem ZpE : Zaa ZbR 5 0 1 := Zk1
theorem ZgS : ZbM ZbR 6 := by
  intro k hk
  interval_cases k
  · exact Zap ZbR 0 0
  · exact Zap ZbR 1 0
  · exact Zap ZbR 2 0
  · exact Zap ZbR 3 0
  · exact Zap ZbR 4 0
  · exact ZpE
  · exact ZpF
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zij : Zax false (Zac 1135) 6 (vars 1135).toFinset := Zcz (q:=111) (prior:=Zat ZcX) (Zai ZcX Zeg) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp8 : Zaf false (Zag 49775) (Zac 49775) 7 :=
  Zaw (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zij
    (ZaM (g:=ZbR) (i:=0) rfl rfl (Zai ZcX Zeg) ZhF ZgS (by decide +kernel))
def ZgE := Zan ZcX 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl4 : Zak false ZgE := Zao (m:=49775) Zeg Zp8 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpT : Zaf false (Zag 42607) (Zac 42607) 7 :=
  Zaw (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zij
    (ZaM (g:=ZbR) (i:=1) rfl rfl (Zai ZcX Zeg) ZhF ZgS (by decide +kernel))
def Zbu := Zan ZgE 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zct : Zak false Zbu := Zao (m:=42607) Zl4 ZpT (by decide +kernel)
def Zva (i : Nat) : Nat := 0x344640ac3f865fc10
def Zvh : Zah := (2,1,2,0,0,4,0,Zva)
def Zvd (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def Zu9 (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def Zvg : Zah := (12,2,2,0,0,7,0,Zu9)
def Zvc (i : Nat) : Nat := 0x24f9400060ba8030352
def Zu8 (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def Zvf : Zah := (6,3,2,0,0,6,0,Zu8)
def Zvb (i : Nat) : Nat := 0x20034000
def Zu7 (i : Nat) : Nat := 0x3b04813058432
def Zve : Zah := (1,4,2,0,0,0,0,Zu7)
def Zml : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffff209f,0xd8096),(0xfffffffffffffffffffffffffffffffff19c61,0xfffffffffffffffffffffffffffffffff03861),(0x97be,0x2c69c),(0xfffffffffffffffffffffffffffffffff04b47,0xfffffffffffffffffffffffffffffffffd3903),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def Zmk : List Za7 := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def ZqJ : List (List Nat) := [[],[65,50]]
def Zn8 : Nat → Zah
  | 7 => Zvh
  | 6 => Zvg
  | 5 => Zvf
  | 4 => Zve
  | _ => Zbs
def ZqK : Nat → Nat → Option (Nat × Nat)
  | 7 => ZaH 7 21 2 9 4 1 Zvd
  | 6 => ZaH 2 9 1 8 3 1 Zvc
  | 5 => ZaH 1 5 1 6 1 1 Zvb
  | _ => fun _ => none
def x63 : Zaj := ⟨1087,7,fun j => Zml[j]?.getD (0,0),Zmk,ZqJ,Zn8,ZqK⟩
set_option maxHeartbeats 0 in
theorem ZhW : Zaz x63 (Zat Zbu) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def ZeR (j : Nat) : Nat := 0x3514243035142420351320403142355431423232203411211512401013243543
def ZeC (j : Nat) : Nat := 0x3120043210043201024300234510350210243002345103402102430023451023051024300234010340210210341352003510002103413520030210
def ZeT : Nat := 0x42110c0300c03
def ZeS : Nat := 0x34190a81205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZqS : Zaa x63 4 0 1 := by
  apply Zar (pos:=ZeT) (neg:=ZeS) (kw:=ZeR) (panels:=ZeC) (data:=0x1) rfl
  decide +kernel
theorem Zuc : Zaa x63 4 0 1 := ZqS
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZqT : Zaa x63 5 0 6 := by
  apply Zar (pos:=ZeT) (neg:=ZeS) (kw:=ZeR) (panels:=ZeC) (data:=0x50008000607) rfl
  decide +kernel
theorem Zud : Zaa x63 5 0 6 := ZqT
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZqU : Zaa x63 6 0 12 := by
  apply Zar (pos:=ZeT) (neg:=ZeS) (kw:=ZeR) (panels:=ZeC) (data:=0x803020482818600838580) rfl
  decide +kernel
theorem Zue : Zaa x63 6 0 12 := ZqU
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZqV : Zaa x63 7 0 2 := by
  apply Zar (pos:=ZeT) (neg:=ZeS) (kw:=ZeR) (panels:=ZeC) (data:=0x84) rfl
  decide +kernel
theorem Zuf : Zaa x63 7 0 2 := ZqV
theorem Zhw : ZbM x63 7 := by
  intro k hk
  interval_cases k
  · exact Zap x63 0 0
  · exact Zap x63 1 0
  · exact Zap x63 2 0
  · exact Zap x63 3 0
  · exact Zuc
  · exact Zud
  · exact Zue
  · exact Zuf
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zdj : Zax false (Zac 1087) 7 (vars 1087).toFinset := Zcz (q:=63) (prior:=Zat Zbu) (Zai Zbu Zct) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrH : Zaf false (Zag 6719) (Zac 6719) 8 :=
  Zaw (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (Za0 (prior:=Zat Zbu) (Zai Zbu Zct) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def Zhl := Zan Zbu 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnQ : Zak false Zhl := Zao (m:=6719) Zct ZrH (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrq : Zaf false (Zag 1087) (Zac 1087) 8 :=
  Zaw (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (ZaM (g:=x63) (i:=0) rfl rfl (Zai Zbu Zct) ZhW Zhw (by decide +kernel))
def Zg4 := Zan Zhl 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Znz : Zak false Zg4 := Zao (m:=1087) ZnQ Zrq (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpN : Zaf false (Zag 11327) (Zac 11327) 8 :=
  Zaw (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (ZaM (g:=x63) (i:=1) rfl rfl (Zai Zbu Zct) ZhW Zhw (by decide +kernel))
def Zgr := Zan Zg4 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlR : Zak false Zgr := Zao (m:=11327) Znz ZpN (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrv : Zaf false (Zag 1599) (Zac 1599) 8 :=
  Zaw (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (Za0 (prior:=Zat Zbu) (Zai Zbu Zct) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def Zg9 := Zan Zgr 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnE : Zak false Zg9 := Zao (m:=1599) ZlR Zrv (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp6 : Zaf false (Zag 47679) (Zac 47679) 8 :=
  Zaw (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (Za0 (prior:=Zat Zbu) (Zai Zbu Zct) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def ZgD := Zan Zg9 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl3 : Zak false ZgD := Zao (m:=47679) ZnE Zp6 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpS : Zaf false (Zag 42559) (Zac 42559) 8 :=
  Zaw (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (Za0 (prior:=Zat Zbu) (Zai Zbu Zct) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def Zgv := Zan ZgD 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlV : Zak false Zgv := Zao (m:=42559) Zl3 ZpS (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp9 : Zaf false (Zag 52799) (Zac 52799) 8 :=
  Zaw (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zdj
    (Za0 (prior:=Zat Zbu) (Zai Zbu Zct) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def Zcc := Zan Zgv 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZcZ : Zak false Zcc := Zao (m:=52799) ZlV Zp9 (by decide +kernel)
def Ztx (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def ZtC : Zah := (5,1,3,0,0,7,0,Ztx)
def Ztz (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def Ztw (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def ZtB : Zah := (10,2,3,0,0,7,0,Ztw)
def Zty (i : Nat) : Nat := 0x700009040000000000ddd0800002
def Ztv (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def ZtA : Zah := (3,3,3,0,0,5,0,Ztv)
def Zkg : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffff1880f,0xfffffffffffffffffffffffffffffffffe600d),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff2619f,0x2a10e),(0xfffffffffffffffffffffffffffffffff60271,0xfffffffffffffffffffffffffffffffffc5851),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def Zkf : List Za7 := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def ZnX : List (List Nat) := Zg1
def Zmd : Nat → Zah
  | 7 => ZtC
  | 6 => ZtB
  | 5 => ZtA
  | _ => Zbs
def ZnY : Nat → Nat → Option (Nat × Nat)
  | 7 => ZaH 23 29 4 12 4 4 Ztz
  | 6 => ZaH 2 11 1 10 2 4 Zty
  | _ => fun _ => none
def Zbq : Zaj := ⟨1213,7,fun j => Zkg[j]?.getD (0,0),Zkf,ZnX,Zmd,ZnY⟩
set_option maxHeartbeats 0 in
theorem ZdT : Zaz Zbq (Zat Zcc) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=1) ?_⟩,ZaF (d:=2) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zin : Nat := 0x1408410844300c
def Zim : Nat := 0x90448d05005
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk8 : Zaa Zbq 7 0 5 := by
  apply ZaD
  apply Zau (ar:=7) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZpK : Zaa Zbq 7 0 5 := Zk8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk6 : Zaa Zbq 6 0 3 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk7 : Zaa Zbq 6 3 7 := by
  apply ZbB (pos:=Zin) (neg:=Zim) (data:=fun _ => 0x25234363203201322034013214234010432405431423402114234021) rfl
  decide +kernel
theorem ZpJ : Zaa Zbq 6 0 10 := (@Zad Zbq 6 0 3 7 Zk6 Zk7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk5 : Zaa Zbq 5 0 3 := by
  apply ZbB (pos:=Zin) (neg:=Zim) (data:=fun _ => 0x242340404324053241324040) rfl
  decide +kernel
theorem ZpI : Zaa Zbq 5 0 3 := Zk5
theorem ZdL : ZbM Zbq 7 := by
  intro k hk
  interval_cases k
  · exact Zap Zbq 0 0
  · exact Zap Zbq 1 0
  · exact Zap Zbq 2 0
  · exact Zap Zbq 3 0
  · exact Zap Zbq 4 0
  · exact ZpI
  · exact ZpJ
  · exact ZpK
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zd5 : Zax false (Zac 1213) 7 (vars 1213).toFinset := Zcz (q:=189) (prior:=Zat Zcc) (Zai Zcc ZcZ) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrA : Zaf false (Zag 2237) (Zac 2237) 8 :=
  Zaw (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zd5
    (ZaM (g:=Zbq) (i:=0) rfl rfl (Zai Zcc ZcZ) ZdT ZdL (by decide +kernel))
def Zhe := Zan Zcc 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnJ : Zak false Zhe := Zao (m:=2237) ZcZ ZrA (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrw : Zaf false (Zag 1725) (Zac 1725) 8 :=
  Zaw (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zd5
    (ZaM (g:=Zbq) (i:=1) rfl rfl (Zai Zcc ZcZ) ZdT ZdL (by decide +kernel))
def Zha := Zan Zhe 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnF : Zak false Zha := Zao (m:=1725) ZnJ Zrw (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrE : Zaf false (Zag 2749) (Zac 2749) 8 :=
  Zaw (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zd5
    (ZaM (g:=Zbq) (i:=2) rfl rfl (Zai Zcc ZcZ) ZdT ZdL (by decide +kernel))
def Zhi := Zan Zha 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnN : Zak false Zhi := Zao (m:=2749) ZnF ZrE (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpY : Zaf false (Zag 43197) (Zac 43197) 8 :=
  Zaw (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zd5
    (ZaM (g:=Zbq) (i:=3) rfl rfl (Zai Zcc ZcZ) ZdT ZdL (by decide +kernel))
def Zgx := Zan Zhi 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlX : Zak false Zgx := Zao (m:=43197) ZnN ZpY (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp2 : Zaf false (Zag 44221) (Zac 44221) 8 :=
  Zaw (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zd5
    (ZaM (g:=Zbq) (i:=4) rfl rfl (Zai Zcc ZcZ) ZdT ZdL (by decide +kernel))
def Zdo := Zan Zgx 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zfi : Zak false Zdo := Zao (m:=44221) ZlX Zp2 (by decide +kernel)
def ZtR (i : Nat) : Nat := 0x60bfd31
def ZtS : Zah := (1,1,1,0,0,0,0,ZtR)
def Zkk : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffc91,0xfffffffffffffffffffffffffffffffffffc01),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),(0xffffffffffffffffffffffffffffffffffff8d,0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def Zkj : List Za7 := [(88,0,163,0,4),(8,0,243,0,7)]
def Zn1 : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def Zmf : Nat → Zah
  | 7 => ZtS
  | _ => Zbs
def Zn2 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def Zb2 : Zaj := ⟨1275,7,fun j => Zkk[j]?.getD (0,0),Zkj,Zn1,Zmf,Zn2⟩
set_option maxHeartbeats 0 in
theorem ZoH : Zaz Zb2 (Zat Zdo) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=0) ?_⟩,ZaF (d:=1) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zu1 : Nat := 0x14042108443003
def Zu0 : Nat := 0x68325248a381a0642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk9 : Zaa Zb2 7 0 1 := by
  apply ZbB (pos:=Zu1) (neg:=Zu0) (data:=fun _ => 0x50634340) rfl
  decide +kernel
theorem ZpL : Zaa Zb2 7 0 1 := Zk9
theorem ZlP : ZbM Zb2 7 := by
  intro k hk
  interval_cases k
  · exact Zap Zb2 0 0
  · exact Zap Zb2 1 0
  · exact Zap Zb2 2 0
  · exact Zap Zb2 3 0
  · exact Zap Zb2 4 0
  · exact Zap Zb2 5 0
  · exact Zap Zb2 6 0
  · exact ZpL
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZuM : Zax false (Zac 1275) 7 (vars 1275).toFinset := Zcz (q:=251) (prior:=Zat Zdo) (Zai Zdo Zfi) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp7 : Zaf false (Zag 48891) (Zac 48891) 8 :=
  Zaw (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZuM
    (ZaM (g:=Zb2) (i:=0) rfl rfl (Zai Zdo Zfi) ZoH ZlP (by decide +kernel))
def Zby := Zan Zdo 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZcH : Zak false Zby := Zao (m:=48891) Zfi Zp7 (by decide +kernel)
def Ztr (i : Nat) : Nat := 0x1948817fd30
def Ztu : Zah := (1,1,3,0,0,0,0,Ztr)
def Zts (i : Nat) : Nat := 0x8e80
def Ztq (i : Nat) : Nat := 0x24c269243a037eb0261df54530
def Ztt : Zah := (2,2,3,0,0,5,0,Ztq)
def Zke : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffff22a7,0xffffffffffffffffffffffffffffffffffa027),(0xffffffffffffffffffffffffffffffffff4759,0x4258),(0x942e,0x8424),(0xffffffffffffffffffffffffffffffffff99d3,0xffffffffffffffffffffffffffffffffff3bd3),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def Zkd : List Za7 := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def ZnV : List (List Nat) := [[],[16,66,101]]
def Zmc : Nat → Zah
  | 8 => Ztu
  | 7 => Ztt
  | _ => Zbs
def ZnW : Nat → Nat → Option (Nat × Nat)
  | 8 => ZaH 1 3 1 6 1 1 Zts
  | _ => fun _ => none
def ZbL : Zaj := ⟨1151,8,fun j => Zke[j]?.getD (0,0),Zkd,ZnV,Zmc,ZnW⟩
set_option maxHeartbeats 0 in
theorem ZoG : Zaz ZbL (Zat Zby) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=1) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def ZuZ : Nat := 0x10842110c0300c03
def ZuY : Nat := 0xe86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk4 : Zaa ZbL 8 0 1 := by
  exact ZaD (by decide +kernel)
theorem ZpH : Zaa ZbL 8 0 1 := Zk4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zk3 : Zaa ZbL 7 0 2 := by
  apply ZbB (pos:=ZuZ) (neg:=ZuY) (data:=fun _ => 0x2615312126154121) rfl
  decide +kernel
theorem ZpG : Zaa ZbL 7 0 2 := Zk3
theorem ZlO : ZbM ZbL 8 := by
  intro k hk
  interval_cases k
  · exact Zap ZbL 0 0
  · exact Zap ZbL 1 0
  · exact Zap ZbL 2 0
  · exact Zap ZbL 3 0
  · exact Zap ZbL 4 0
  · exact Zap ZbL 5 0
  · exact Zap ZbL 6 0
  · exact ZpG
  · exact ZpH
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZdA : Zax false (Zac 1151) 8 (vars 1151).toFinset := Zcz (q:=127) (prior:=Zat Zby) (Zai Zby ZcH) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrz : Zaf false (Zag 2175) (Zac 2175) 9 :=
  Zaw (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (Za0 (prior:=Zat Zby) (Zai Zby ZcH) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def Zhd := Zan Zby 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnI : Zak false Zhd := Zao (m:=2175) ZcH Zrz (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrr : Zaf false (Zag 1151) (Zac 1151) 9 :=
  Zaw (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (Za0 (prior:=Zat Zby) (Zai Zby ZcH) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def Zg5 := Zan Zhd 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnA : Zak false Zg5 := Zao (m:=1151) ZnI Zrr (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqa : Zaf false (Zag 52863) (Zac 52863) 9 :=
  Zaw (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (Za0 (prior:=Zat Zby) (Zai Zby ZcH) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def ZgF := Zan Zg5 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl5 : Zak false ZgF := Zao (m:=52863) ZnA Zqa (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp1 : Zaf false (Zag 44159) (Zac 44159) 9 :=
  Zaw (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (Za0 (prior:=Zat Zby) (Zai Zby ZcH) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def ZgA := Zan ZgF 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl0 : Zak false ZgA := Zao (m:=44159) Zl5 Zp1 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpZ : Zaf false (Zag 43647) (Zac 43647) 9 :=
  Zaw (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (ZaM (g:=ZbL) (i:=0) rfl rfl (Zai Zby ZcH) ZoG ZlO (by decide +kernel))
def Zgy := Zan ZgA 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlY : Zak false Zgy := Zao (m:=43647) Zl0 ZpZ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpU : Zaf false (Zag 42623) (Zac 42623) 9 :=
  Zaw (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdA
    (Za0 (prior:=Zat Zby) (Zai Zby ZcH) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def ZbE := Zan Zgy 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZbV : Zak false ZbE := Zao (m:=42623) ZlY ZpU (by decide +kernel)
def ZrT (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def ZrV : Zah := (10,1,7,0,0,9,0,ZrT)
def ZrU (i : Nat) : Nat := 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def ZtH (j : Nat) : Nat := (if j<1 then 0x4670b12533d10c75e8c8b58478714c78518d7ffe317a00012a9ac91478d191b210c32553e54c93f89481224ccae8c8db6fde254791fe4e848fbc887bfd7bf91489036fde2547dcf8012e849566e24b9fb14c8811a0e059e352b5153447cbd4232d7f49221033d272641407a231b409789c248c37effc18880013340f091678851c118ebe79ab9993d531d8dc499a05bd0c116be4b20866cfc8181973f508195bdbb50994f7c60a504f0c8428b9e9121c0ac4fc46a1120e04a60f4453fb885004944e5f860055bc6ff42c4127799d428024a1e7ce7ac1704adc7e20451ffc4244651f5f0228486f4f0a1954c1e8977ea4a053be12443c9c3c6580589afe03afe94c94489efffa830090fdb8d0417f449000ce5f928a32dffc2d0614d27f807b0a67cf1f4d91f647d4208fbfe3700101096bf0781268499f1f02000903ffe01040482fca44652ffe289a4fc122aff8d4941804bdf23604101297c7e2140124af7ee811a7f861011d78f7002c80953e381127d8e0211e7f299142fbf18650920df8cb8019cf270f30e0547938798702a5ebf9031120250f9f5818890128f270f30e05400fe351d6404a258208d1b924507a3c1d8e86f1d841349848218d86b128212494478f110820c0a8e62006815047c230948a42161f9088a0318c9c0a1707c9404221c0c881288b0503b15130a240108fc04381b1a0844030838cc0801088b84e07148944900150b4582b1787c010b2846416a08101e7fcbfa1f92fab7c5bddde64f0b778bb55d82e9e73db929c58e0c6f43739b5ad886b9b591a7ed1d68533b5996cb263d319988cc2b606af8d78aba05bcad9566ab10570ab25534a8d52fa8ed41e9ef4eba72935296e4a92505254906477a3591928ae444219908c8224009f80f6c78e3c09da0e727113711ad0d0066031e1840bdc5d52d89660ad254f29413e49b64b1247919c87c4161f88ef472036519c0c605f42df15609f849e22e105076437c19a0bf054424c0f9066025c0c4035000524114a83d264f4b885240f4b93d2a234983d2a4f4bb3d2e6f4b24d2813498352c034b1852c6d4902d242d4b93524094884d284d4aa3d26334a0bd2a614b0bd2c13498852eaf490352c734b1bd2a274b13d0e4f4b01d24134a13d2403499352e334b09d2407498b522014a8c52e2f4b08d2c114a84d26134ba4d2e8d4aa3528334b9b52e61498052c054384d0e4d4a0352a434a9152a474b84d282d4a8bd2c0f498bd24014a002ae4cab8c32846eb1caae10ab883282eab84aae22a393ca40cabb0c282cab91aae4aa3932ae0aab8caae2aab982aea4abb128e132983aaea6ab913a610ab8a3a612aba32ae6cabb1aae26abac2ae4eab822ae42caa3aaea2ababaae048b8a1ae462ba9a2e260bb192e660bb0ffffdfdfbfbeff7dbdddebf3f54d435011018c53100310c020 else 0x2a514f996be52268663fe3f325000b13ca8643f53090a16b2b1c08e6b231fc5008b7c382938e31a32317b310ffc6068f40910413efe1f6c01485ee44d9b654c87a249bf13a091bbf9e4f32ae0e4e3d3a92ab09fe26af3c9e651e04e8247ae7089a62f4408edf4ca44663e5120b04991818324)
def ZtQ : Zah := (122,2,7,720906,68,13,1115,ZtH)
def ZtL (i : Nat) : Nat := (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def ZtG (j : Nat) : Nat := (if j<1 then 0x6525d9a24904d89415292e2f4660a546a02949804e92e6012580e3841401982aa92a4d525c84a4901d496028e285512442340a129793064f2c6e9261e3aea93e49204ef2a521754a9a4b94249760e92407125d43a4bb2b5160ad12a2b066119c4a8b94954511aa4e1c508d249035714182e282f524812a4b9398d2068910f412482ca4b09d49727c92a44de58dc44409749204d1ac0e125825c4b0d4714236e2a8d866008a4c28e79317092e42925d820cc2b55d52a91ac2e1e4c2a24ba8349730292e8cd25d4224a8b6496366330539261d244a8ad8d845292e6cd248118cc2b4198224a2c03125ca7c6900b49406692e4f622063a4b954498244330ce125465bc982c4971871a60a52614a24a0598d2071110341e4c27a4b0351983511102dc6619a3cb1d44976583306a525c8424b88279537092407dc551724b0cb19855e92e42dc502a46c1a98d2034f2615d2614e82c1220487860b0e18161e182c33629523e090efd5551e8243be05821e0b06a0e5cc30243d75952a27ac274e480f36aa380580b20b0ec98212890b09039730a230754e20e282c14d05836682c270d50a6b4a0c20581408a4094160a314a94d05870a4302408585002c22821602c0b0ad8e4c260ac0b105802ceaa6e1048119ec01d05823e53047ca54878243b94572707b0a74858081c985904879e7ac0741604f9ca89e3d72328ae6a5b505c02c3ba40818a52c27ce548f02c14e21524042c0801605b20a0a861429052a538121e81aa12005849c130d38121d91aa11c4d63aaaaa50016013bea12935423eeac6e1654ab34a0ae21514082a2d0a480fba98504171307ae429a505c9cb1d805859882c0701606702c3835954ac52a23c848081cb09e05818c6ae500e580f20b8830487a6824070e4c268243ad41863882a471358ebb4a12f5554a70a82a41604810c0a005822a0b0ef0d5c9db2a117418538090ec0854483a904804878452a27c360600243b121204042a441d4c5c20b88929813e72e60ca580f9ea89d29522a8a40881604796a11e1d4240030d389508f98a11cffbfdff3fbfebf7fdbeffbbedfafe7f7fd7f3fbfedf7fdfb7ddef77dbf6dd9f5fd3f3fcbeffbf6f7bbebf9fe3f5c5535c1535915358d535815350553501534c5534c15348153441531c1535d5435c5435c14358143545434c143481435d5405c94058d405894058540581405514054940545405414050940505404c9404c5404c140481401c9405d1105cd105c91058d10551105091050510501104c9104c5104c11048510481101c9105c8635c4635c063480635c4535c053480535d8405d4405cc405c8405c44058440580405484054440480405d8315d4315c8315c03158031548315d8305d4305c8305c43058430580305483054430480305cc2058c2054c20500204c4204c0204802044020 else (if j<2 then 0x91681d011002a0fd070f4380c4270111f8940107c110cc0787d000a6000b8000b02b0bc2deb07517a69d25e8cf4179efcdae64f2cf94fc90e4271bb8b3c3fe1870a3833c0bdfe6fc77c5bd4ddceeb7743b8ddc2ede76c1b4bd966c7761faf6d6ceb0f569a9fd4aea174f7a6ad2de93b47ba2fd10e8273fb9e3ce566b3333987cbc65b32bb94cc9c64b72258fac6fe34f1898b1c4f625b101868c27e10b06d81fc065fdefc77d5be45ecaf3178dbbcddaeebb73eb925c2edf36ecb70db42d836b3b53da62cff673b2ed93ac8962fb0ad80ebe75dbae756d2b41595abed5d6adb553a9dd482a0b4eea6552be94f491a3cd19a883430a12503e8013f39f44f627953ac9cace1a6f135a99fccce63b30d97a4b9a5a52c29554a7650f27d934c97a49923a912c8624051e38e3c6ba34518e8c2c5b22b514289d448220b0f486b43261830ae84b421e0e506282b410e06701d807400dff6fee7f03f55f8efb77d5be7df2af827b83d89e9af367943c55e14efc7773b51d8ceb97513a4dcfce7272f3941c8ae39711b855c12df26f5377dba2dc56dd3689b18d776b5b579aa4d4769a34a1a2cd0a67933999a4cb6655b27190ec6c62f312186cc186052ffd7cebd25e12ec5740b8d5b62d3566ab28586ac0d5e8ae456a2af5556a9a53ca98d480a26503a7cd3cc9da4e026c534c98c4bf25b92b894749ea4892068ee46a231d1688a744821d90cc85341c20910207f43ef1f1cf5e79b3bd1d80e8c7383901c34df46db3659ad0d3869033f19acc94637311981cbe85d42dc16b8b445922be1574aa654229a9450a024ee26992dc94e494242117c87c42e2098fe07c43cf1d20e507043611a38ce864e31c1830bb05a42bd1508a0c4e425e12788fc456212101079c3a21b20d206342f81680aa84d424a10b079839016c08e03080cc00033031d25c9fc4b0bb71429292e21a3481924c3a1198262a2c111261e824b88549208c92ead525c6ba4904c71425e92403d2618e38a1188d20aa9304963481aa490228d2062f26142254578cc336198086910518660670cc32c71422ef2415925c8c0cc10c492096f24121248104440a45161831a413d2486324bb038d4253110284660d9a4b881498366330269c549dc4a8d249765a92e22925cd48cc22971418712a2ac6605224b09f493066baa501e4c24a4b94171423292c07466050a4b013893154e284c62204438a0c449529692e4dd25d5a0cc2b689525ee240edc551ca4bb2e1980191a4129754a4a4ba8289515d1a41046608da4b88b4920b092e22125ca224a9b35d529f12a20e25059bc9932198074930c4de4c5d46a8b849709e3305246601946902d49765e92e4312548a28b09a79609033012525cd50cc2ba89516a92e46521ca324c30d49202092c13125d8138904081207e3303112549a44408189516892e2 else 0x340a25a5322c508f112816314116c3de54064dca108c686c049ec18d808de0829e121cf18c88708802c913c053686908722a6065d5041b011814e2218030127c898cde1045fae0190e111e05df2863ef912326700c746877788680cc210053a42a3435615f2106c359147a03199093c85065f40630ff70992f091d6cc53108c84e116c50b5450d0144be0640f4a63c9700c86421c8b2da1d9923005f190e3e018ddc2106b41602dfc0867848d7a886ba887591588b5e282f71020d80ad4a19e0559147cba06417d1a0f6f8489bc215585808f90aad09a45a83b90a7f0488c046f0415a234057a887dfd531a78c4bc06dec8c6e021b3e9127810e9087b431800047f00c7de40c60f0020f47e8220fd0436fdb422651f810880159731d7a031d65625ffab00233cc0d8084f486748b682409780cb036fe60190bc0319c22c6073a780648790506c05730922f2153c2a0cb619e0431942af60636810f5886012d7219028958b78421d6a1d5867f443cfe000c8bfd44885f4a63302cf06200c7ca18cf2238fe26300e70020d7d79221ec0f3a78064581005af232f2863a703ba14336236020e0c4c7433e221eb8140400d02388980dc450684604c040147262de108b61677416403630d86eb91d21ac8ab222fc898de02581278463a3433d243d41da143b88a90981133c492c0a8147286300a43ec0a81521cf6663e2e18d7c486a05b415026026708d80bb262602ef806360213a43af362642048e06e1848ef10a0ee22a4c495ba625fd0811550340590e2c735843be223b11e6989f6022fe810118edf1613b79231b00efcc312a023810f888f88a78e219c84766235fd020232f848796c3d05967c0844edb498cb6e848c034039f021107021024fc218de029a42be08e62a86016d509453b7c584f35843ce68191c057109120798c18cbf80639a424ecc590e8190cb090cb0923c10193b3263ce48c75e24c72c904bfa04046ce68192fc402678083e018ee2121fa230fe404c97845b65511bc218cc0b78424ecc49dbe08655bc09b50863c8508bd0d8b035c91977fa0910023023e03ada98cedf16138047e0370147d309195f6021f023c8740c85fa44c97c44fb010b8133ca8100ccbfa0404698428f448c990e81917c2434ecc45fb1482819e690ad5245fd0202367340c96223e446808af9249f021127c08449ac21d72923227ca48c8bc4232c24ac467c0679c46be80443e039f5a089b2b221f790c26780b3a1319b810cb092f91187e1d0321f01b7ec0c7b59288708829e5ff3e22a9c6fd08248df7fcca0824053cbfe7c454be30c6f1a092a21088340e91013c2805841913414844b4961d8042140842076168d1128a002041230830042241c581bc54308404e071228552789d4186d154a02409604480450c))
def ZtP : Zah := (387,3,7,2359386,103,13,1105,ZtG)
def ZtK (i : Nat) : Nat := 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def ZtF (j : Nat) : Nat := (if j<1 then 0xcf10e13bf579aec5c2b756a2cd588b015e2b6560ab1536a0d39a634a690d19a21422804f49c9362684c39772ce52c8d8f91d23645c8a911e1d42e84d06608c057f4fc9f53da7a4f1ddfbb775ee8dcab8d6f6dadb1b4f684cdd9331961ac05792e65acb0d5baaf538a293f2744d09812aa464768bd13a0d40a7d4ef1cf38e6fcd91a933863cc39772de570aa1422684908e10b1f43c86f8d71922d85309b1242183e8710d0170268420660940d00f0001330942649c6ca0b0c541874ac3246645536a94785422c1330a026430ea90069c914e9a40da95064209034752033292241b508ce49842a9637a7930252481b8cc8a5119128790335f508906c899c930be52a544f206b8ccc250991c3ba413cf245206c91ad9417cfa844e250869e40a6d94158510f54e21ec0ccba19d601211318dc244b7098566d423052a54195806b2b08b85421213235e250829e48a9199501128433450821443dd6d4238c92274264a284c9533c984a1324d21480f4e48a38d510312e219f5088c4a0b128878cb28475b508dbea1145161327ae22275457b6ba8715911d324039c545ccc903919921b12c3136505704c95c6d422e2b243cf545598a11b7d730faa40d46644588c915454195192245b508b70984189710e2b303d9244164a0bfe52066bac251858471e40a230876ab2847cf206cc89857b154787b0eea2508518aa408942123930b784c26489014b952a942c983348192aa11dbd209c01300c1261290a952b520b6013080921f134a116348396f284470505d9643daad30bd028427fc7f4fe5fb3f57e9fd1f9bf2fe4fc5f6be97cef8dedbd6f87ef9debbcf76eebdb7b5f69ecfd8faf75de9fd2f9ef3be6fcbf95f1fdf9beb76e7ecfb9df3ae6fccf97f1be1fbf95f6bdd77abf1fe3ec3f4817154d635915321d6454d5458d535014154d54501535494054c87501535493054c844c15361d2054d304815321d2054c81481535491054d204415321d1054d861c1536107054d811c1535493050d424c14361d2050c8148143205725018158d405056250161581405c954501525454021d5150172505404c532501544c54054531500874c54058d30501614c14058130501524c1404c5305008148140549734408758d106095444181551105095444087551105494144142505105d94044184481105cd20441424811050520441404811060c72441541c9106017218d205c4634817018d87480634817114d825c0534817014d87480532052014d525d84054576101425d84048176101825d44060575101615d44058175101525d44054575101205d44058573101605cc4054973101515cc4048173101805c84058572101605c84061971101855c44058171101525c4404817110182584405096110142580405c5511008148040549760c1205d8305cd31081714c420 else 0x2a743e6105ac2095c0d7b8c6c040101078c50c0aaf41113c18a9815e610c03b2626c097a420000b213210020464200000000000100005023e22502001a0800026c21860c6f60300003e2200701380b50401682016424080000f88801808000004a0c3020152b14d2100078314584812e909c056432837488c866108be314a080073625f90ac8501b2100205748980990802c7a4880134853f090ee910000548802e02701004e210003762005e9093613e2200dd2168d08034c218058442710cec0e90804c8402c04016023244c04c91260748690992206610100a2784ed04271200030d019507a0004620e00c830008f90124ec020b004a828120fd1662d4548002c43e0b80002905e0ad0002dd73ac74e689ced99f28e46c7d8)
def ZtO : Zah := (137,4,7,3801188,103,11,1064,ZtF)
def ZtJ (i : Nat) : Nat := 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def ZtE (i : Nat) : Nat := 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def ZtN : Zah := (19,5,7,0,0,8,0,ZtE)
def ZtI (i : Nat) : Nat := 0x81900
def ZtD (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def ZtM : Zah := (2,6,7,0,0,3,0,ZtD)
def Zki : Array (Bits × Bits) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),(0xffffffffffffffffffffffffffff4ca8886101,0xffffffffffffffffffffffffffff8c0d9a00c9),(0xdc001a04a,0x12b065ab12),(0xffffffffffffffffffffffffffff815101844f,0xffffffffffffffffffffffffffffe94a0254e5),(0x2200761284,0xca4842b0f4),(0x0,0x0),(0xffffffffffffffffffffffffffff2220844287,0x31b2254f02),(0x0,0x0)]
def Zkh : List Za7 := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def ZnZ : List (List Nat) := Zfq
def Zme : Nat → Zah
  | 10 => ZrV
  | 9 => ZtQ
  | 8 => ZtP
  | 7 => ZtO
  | 6 => ZtN
  | 5 => ZtM
  | _ => Zbs
def Zn0 : Nat → Nat → Option (Nat × Nat)
  | 10 => ZaH 177 223 4 13 7 2 ZrU
  | 9 => ZaH 185 697 7 15 9 2 ZtL
  | 8 => ZaH 39 199 6 14 8 2 ZtK
  | 7 => ZaH 11 35 3 11 5 2 ZtJ
  | 6 => ZaH 1 3 1 7 1 2 ZtI
  | _ => fun _ => none
def Zal : Zaj := ⟨1215,10,fun j => Zki[j]?.getD (0,0),Zkh,ZnZ,Zme,Zn0⟩
set_option maxHeartbeats 0 in
theorem Zch : Zaz Zal (Zat ZbE) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=4) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Za4 (j : Nat) : Nat := 0x764260437506145074436550744365407443653074436254734362657236165272361651723616317236163071362652713626427136264170435540704355307042554070415550704155407003547070035450672465416714653065360765653607546536074360634121606341106060416160604121605341216050412160134121566307635663075453641483531322715313227053132261531022715310225051643070516430505135227147145542463462604606417142560343425603324256032142530343425303324246037342460371424603434246033242430376374316743743167337431663374316623743164337401475374014633734657337346572363562323635622136356210363462323634622135461480354614403546143035461420313522823135225231352232313522213134223231342221313122723131223231312221310522323101223231012221304656652434038317632675154630701546306015463050154630101545307015453010154230101541307015063460150630601506301014463010135322521313228213132275072455740724555207145574071455640606418106064161060541810605417103645676036456650364566403645483
def ZaZ (j : Nat) : Nat := 0x6453043210043201064500432100432010641306357005416106410043210043201064025174200502100640251742004610006402517420040210064025174200401700640251732003610006401517420050210064015174200301500640103457203042106324067501054021063200675010540210630120364103201006042537420030270052345207130072600523452071300523005234520713004270052344207130052400523052071300623005230520713005230052305207130042600523052071300412005046010432010421040351306420124300403113064201632004031130642012430040311306420123500315406417200162003120021053021061031200210530210310312002105301602103120021043021031030420315240103600304203152401034003041031524010340030410315240102300254064170302604002460057610056201024600576100341010241004321004320102036001674012501020340016740126010203400167400146101450057630012561014500576200451010145005761005620101450057610045201014500576100342010145005761003415101450057610012031014064135200402100140641352003021001402413520040210014024135200302100140241352003017001324023401034021013200234010630210132002340103402101304607241072010013046072410620100062435247003640000624352470034500006243524700273000062007561005620200620075610034102005123542700435000051235427003240000461735642056434004517156020561200045171460207412000412314602037120003247065140651000032470641202506000264362471037520002643624710365200026436247103462000214726531065320002147264310473200014236427104362000142364271043520001423642710325600014236427103251000134746530065400001257465300654000012474653006540000124746530054360001247465300543000012473654206543400124736542054324
def Za6 : Nat := 0x5021042110c0300c03
def Za5 : Nat := 0x24914891a0c85405
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zob : Zaa Zal 5 0 2 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x7570) rfl
  decide +kernel
theorem Zsc : Zaa Zal 5 0 2 := Zob
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zoc : Zaa Zal 6 0 19 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x6f311660000238033954395f3a36481e4dbfb1) rfl
  decide +kernel
theorem Zsd : Zaa Zal 6 0 19 := Zoc
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zod : Zaa Zal 7 0 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0xf456a7442354b2f19185c5c34004fc7ad00d8a4cf9f00a4be00d000a7a99000) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmn : Zaa Zal 7 32 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x6900281b446259441f4e1a250b186118056a663a0718715c536b661845495029) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmo : Zaa Zal 7 64 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x5b4500305300182327273c18131712683b18185d1118451800442b005c472337) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmp : Zaa Zal 7 96 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x1604440027000044006c5a5d511a583269584a182f1a180d1418491866454010) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkp : Zaa Zal 7 128 9 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x1818403d3232183c18) rfl
  decide +kernel
theorem Zse : Zaa Zal 7 0 137 := (@Zad Zal 7 0 64 73 (@Zad Zal 7 0 32 32 Zod Zmn) (@Zad Zal 7 64 32 41 Zmo (@Zad Zal 7 96 32 9 Zmp Zkp)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zoe : Zaa Zal 8 0 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x930097c585d69c0000848a00a4008f0000b6a88700820088b6808a0000000000) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmq : Zaa Zal 8 32 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0xb0d2a0cbd7a2000000b5b2a3bd008a84ca8981c4848e00829d00aa84c3bac898) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmr : Zaa Zal 8 64 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0xd5b5bfaaa4c00000b583a884d3c6bc84bbd984ac009fb400cc9e84cd92b8c100) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zms : Zaa Zal 8 96 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x8484a997a3a5d48484c3ce9ac58084a18497c5d1bfa4aa00a6a88080b6b9b6d1) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkq : Zaa Zal 8 128 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x2d5646645b00582828462842005b188684a4d6a4b9848b8a8484a3bf009600ae) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkr : Zaa Zal 8 160 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x181846063e5846581828564518155d28555b2863180a18185d00585b563e582a) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zks : Zaa Zal 8 192 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x282846734500004626235b5d465a5b27671815186e18185823092a2d5e181828) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkt : Zaa Zal 8 224 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x16582818181846464667581c5818462346241826185e18585b2c586d334c0046) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zku : Zaa Zal 8 256 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x58115842284618285b18211808181828465b5b410e732045082358005d15183e) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkv : Zaa Zal 8 288 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x2c6a4572183f581822416e585801235b083e182843461818232c0856575b1d6d) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkw : Zaa Zal 8 320 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x465d00452852112d0c4558461858232c56234658330818285b182a5b1846185b) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkx : Zaa Zal 8 352 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x2e2d5246235b43283f18185e6546286a01574546000027181818282d5d004618) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zky : Zaa Zal 8 384 3 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x181827) rfl
  decide +kernel
theorem Zsf : Zaa Zal 8 0 387 := (@Zad Zal 8 0 192 195 (@Zad Zal 8 0 96 96 (@Zad Zal 8 0 32 64 Zoe (@Zad Zal 8 32 32 32 Zmq Zmr)) (@Zad Zal 8 96 32 64 Zms (@Zad Zal 8 128 32 32 Zkq Zkr))) (@Zad Zal 8 192 96 99 (@Zad Zal 8 192 32 64 Zks (@Zad Zal 8 224 32 32 Zkt Zku)) (@Zad Zal 8 288 64 35 (@Zad Zal 8 288 32 32 Zkv Zkw) (@Zad Zal 8 352 32 3 Zkx Zky))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zof : Zaa Zal 9 0 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x0) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmt : Zaa Zal 9 32 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x8494bf9d84d6b6b6bba48c8dbfb381d600000000000000000000000000000000) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmu : Zaa Zal 9 64 32 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0xa49bc284d681a4d600d6d60000918184bdc5008484b4d697daa4ab9d8400c984) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmv : Zaa Zal 9 96 26 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x8cbf8495d68a94b7d6d6c9af94bfa4a481848481a499ccb48c) rfl
  decide +kernel
theorem Zsg : Zaa Zal 9 0 122 := (@Zad Zal 9 0 64 58 (@Zad Zal 9 0 32 32 Zof Zmt) (@Zad Zal 9 64 32 26 Zmu Zmv))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmm : Zaa Zal 10 0 10 := by
  apply Zar (pos:=Za6) (neg:=Za5) (kw:=Za4) (panels:=ZaZ) (data:=0x0) rfl
  decide +kernel
theorem ZqM : Zaa Zal 10 0 10 := Zmm
theorem Zce : ZbM Zal 10 := by
  intro k hk
  interval_cases k
  · exact Zap Zal 0 0
  · exact Zap Zal 1 0
  · exact Zap Zal 2 0
  · exact Zap Zal 3 0
  · exact Zap Zal 4 0
  · exact Zsc
  · exact Zsd
  · exact Zse
  · exact Zsf
  · exact Zsg
  · exact ZqM
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zcp : Zax false (Zac 1215) 10 (vars 1215).toFinset := Zcz (q:=191) (prior:=Zat ZbE) (Zai ZbE ZbV) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrI : Zaf false (Zag 6847) (Zac 6847) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=0) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zhm := Zan ZbE 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnR : Zak false Zhm := Zao (m:=6847) ZbV ZrI (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpQ : Zaf false (Zag 18111) (Zac 18111) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=1) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zgu := Zan Zhm 11 [(14143,[135,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlU : Zak false Zgu := Zao (m:=18111) ZnR ZpQ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpO : Zaf false (Zag 17087) (Zac 17087) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=2) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zgs := Zan Zgu 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlS : Zak false Zgs := Zao (m:=17087) ZlU ZpO (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrB : Zaf false (Zag 2239) (Zac 2239) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=3) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zhf := Zan Zgs 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnK : Zak false Zhf := Zao (m:=2239) ZlS ZrB (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrF : Zaf false (Zag 2751) (Zac 2751) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=4) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zhj := Zan Zhf 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnO : Zak false Zhj := Zao (m:=2751) ZnK ZrF (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrx : Zaf false (Zag 1727) (Zac 1727) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=5) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zhb := Zan Zhj 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnG : Zak false Zhb := Zao (m:=1727) ZnO Zrx (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpV : Zaf false (Zag 42687) (Zac 42687) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=6) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Zgw := Zan Zhb 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlW : Zak false Zgw := Zao (m:=42687) ZnG ZpV (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqe : Zaf false (Zag 58559) (Zac 58559) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=7) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def ZgJ := Zan Zgw 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl9 : Zak false ZgJ := Zao (m:=58559) ZlW Zqe (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqc : Zaf false (Zag 58047) (Zac 58047) 11 :=
  Zaw (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=8) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def ZgH := Zan ZgJ 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl7 : Zak false ZgH := Zao (m:=58047) Zl9 Zqc (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp3 : Zaf false (Zag 44223) (Zac 44223) 11 :=
  Zaw (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcp
    (ZaM (g:=Zal) (i:=9) rfl rfl (Zai ZbE ZbV) Zch Zce (by decide +kernel))
def Za8 := Zan ZgH 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZbW : Zak false Za8 := Zao (m:=44223) Zl7 Zp3 (by decide +kernel)
def ZrX (i : Nat) : Nat := 0x4c88f1a284060808057fc10
def Zr1 : Zah := (1,1,6,0,0,0,0,ZrX)
def ZrZ (i : Nat) : Nat := 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def ZrW (i : Nat) : Nat := 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def Zr0 : Zah := (11,2,6,0,0,10,0,ZrW)
def ZrY (i : Nat) : Nat := 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def ZtU (j : Nat) : Nat := 0x5e531855aca28df80d3485b10aff144a303b08ac2279015e40503fc243f74904e6f88cfe84131fd4095e405a6492532492f60487f42099e4055ba01ef5025bee9209cfec0916e8073ee9209c7a808879e449669080ff091d4057d0116e807bd81208116988c51b8c1680a003e0241874390b410783414020482f090886c0001070642100bd2d8b0ab2a8e8a9f66f9864f8f625819f3761bf6b59860d6e54d414ad153dcdf324ab2487719c4f0f42b054002c92cc12c983ca94cb84cc11eb80cca3ca134aa60cad8a94ab9b89846b856a15aaa38cbc0cbc4a168b846cad4986aa134b9e6c95a9836b9d0c958b9c8a146a956aa58aa46985aca3ffdbff7def7ddfafeffcff618106101060c10608105cc10550104c010
def ZtX : Zah := (36,3,6,524295,51,10,1055,ZtU)
def ZtV (i : Nat) : Nat := 0x4200118060050390014553e041769a0
def ZtT (i : Nat) : Nat := 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def ZtW : Zah := (8,4,6,0,0,8,0,ZtT)
def Zkm : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffa8c12191,0x7c002100),(0x100d1cae,0x38d1cac),(0xffffffffffffffffffffffffffffffc4146207,0xffffffffffffffffffffffffffffffec000203),(0x5308cf8,0x139088f0),(0xffffffffffffffffffffffffffffffa160574f,0xffffffffffffffffffffffffffffff806f560f),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def Zkl : List Za7 := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def Zn3 : List (List Nat) := Zfq
def Zmg : Nat → Zah
  | 11 => Zr1
  | 10 => Zr0
  | 9 => ZtX
  | 8 => ZtW
  | _ => Zbs
def Zn4 : Nat → Nat → Option (Nat × Nat)
  | 11 => ZaH 5 23 3 10 4 2 ZrZ
  | 10 => ZaH 27 69 6 12 6 2 ZrY
  | 9 => ZaH 2 13 4 9 3 2 ZtV
  | _ => fun _ => none
def Zbk : Zaj := ⟨1279,11,fun j => Zkm[j]?.getD (0,0),Zkl,Zn3,Zmg,Zn4⟩
set_option maxHeartbeats 0 in
theorem ZoI : Zaz Zbk (Zat Za8) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=3) ?_⟩,ZaF (d:=0) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zd4 (j : Nat) : Nat := 0x847465507548287565753010647580103578044026643171266431212664311026523060
def ZdR (j : Nat) : Nat := 0x760215268407140007602152684021500076021526800214000756214263002130007502157680021400075021526800214000724013674201273007012142630021400070121426300213000641207854107502106412078541065021064120785410640710641207854106402106412078501064021041620746810017200405707468100162002305817562075120023058175620651200230581756206417002305817562064120007214135200402100041202345103702100412023401073021
def Zd7 : Nat := 0xa04210842110c0300c03
def Zd6 : Nat := 0xd064a49147434114642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zog : Zaa Zbk 8 0 8 := by
  apply Zar (pos:=Zd7) (neg:=Zd6) (kw:=Zd4) (panels:=ZdR) (data:=0x304020102040392) rfl
  decide +kernel
theorem Zsh : Zaa Zbk 8 0 8 := Zog
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zoh : Zaa Zbk 9 0 32 := by
  apply Zar (pos:=Zd7) (neg:=Zd6) (kw:=Zd4) (panels:=ZdR) (data:=0x60002090900008096919089008e8f8c9300858b82898494888e8a810087838b) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmy : Zaa Zbk 9 32 4 := by
  apply Zar (pos:=Zd7) (neg:=Zd6) (kw:=Zd4) (panels:=ZdR) (data:=0x3050807) rfl
  decide +kernel
theorem Zsi : Zaa Zbk 9 0 36 := (@Zad Zbk 9 0 32 4 Zoh Zmy)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmw : Zaa Zbk 10 0 11 := by
  apply Zar (pos:=Zd7) (neg:=Zd6) (kw:=Zd4) (panels:=ZdR) (data:=0x9586008d00000000000000) rfl
  decide +kernel
theorem ZqN : Zaa Zbk 10 0 11 := Zmw
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmx : Zaa Zbk 11 0 1 := by
  apply Zar (pos:=Zd7) (neg:=Zd6) (kw:=Zd4) (panels:=ZdR) (data:=0x0) rfl
  decide +kernel
theorem ZqO : Zaa Zbk 11 0 1 := Zmx
theorem ZlQ : ZbM Zbk 11 := by
  intro k hk
  interval_cases k
  · exact Zap Zbk 0 0
  · exact Zap Zbk 1 0
  · exact Zap Zbk 2 0
  · exact Zap Zbk 3 0
  · exact Zap Zbk 4 0
  · exact Zap Zbk 5 0
  · exact Zap Zbk 6 0
  · exact Zap Zbk 7 0
  · exact Zsh
  · exact Zsi
  · exact ZqN
  · exact ZqO
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zcq : Zax false (Zac 1279) 11 (vars 1279).toFinset := Zcz (q:=255) (prior:=Zat Za8) (Zai Za8 ZbW) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrC : Zaf false (Zag 2303) (Zac 2303) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def Zhg := Zan Za8 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnL : Zak false Zhg := Zao (m:=2303) ZbW ZrC (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpP : Zaf false (Zag 17151) (Zac 17151) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def Zgt := Zan Zhg 12 [(17151,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlT : Zak false Zgt := Zao (m:=17151) ZnL ZpP (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrG : Zaf false (Zag 2815) (Zac 2815) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def Zhk := Zan Zgt 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnP : Zak false Zhk := Zao (m:=2815) ZlT ZrG (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrJ : Zaf false (Zag 6911) (Zac 6911) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def Zhn := Zan Zhk 12 [(17403,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnS : Zak false Zhn := Zao (m:=6911) ZnP ZrJ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zry : Zaf false (Zag 1791) (Zac 1791) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def Zhc := Zan Zhn 12 [(17405,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnH : Zak false Zhc := Zao (m:=1791) ZnS Zry (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrs : Zaf false (Zag 1279) (Zac 1279) 12 :=
  Zaw (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (ZaM (g:=Zbk) (i:=0) rfl rfl (Zai Za8 ZbW) ZoI ZlQ (by decide +kernel))
def Zg6 := Zan Zhc 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnB : Zak false Zg6 := Zao (m:=1279) ZnH Zrs (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqf : Zaf false (Zag 58623) (Zac 58623) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def ZgK := Zan Zg6 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zma : Zak false ZgK := Zao (m:=58623) ZnB Zqf (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqd : Zaf false (Zag 58111) (Zac 58111) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def ZgI := Zan ZgK 12 [(68863,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl8 : Zak false ZgI := Zao (m:=58111) Zma Zqd (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp4 : Zaf false (Zag 44287) (Zac 44287) 12 :=
  Zaw (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def ZgB := Zan ZgI 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl1 : Zak false ZgB := Zao (m:=44287) Zl8 Zp4 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpW : Zaf false (Zag 42751) (Zac 42751) 12 :=
  Zaw (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) Zcq
    (Za0 (prior:=Zat Za8) (Zai Za8 ZbW) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def Zb3 := Zan ZgB 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZcG : Zak false Zb3 := Zao (m:=42751) Zl1 ZpW (by decide +kernel)
def Zr4 (i : Nat) : Nat := 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def Zsa : Zah := (6,1,8,0,0,9,0,Zr4)
def Zr7 (i : Nat) : Nat := 0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def Zr3 (j : Nat) : Nat := 0x6ffff64904012a7fcc020224b7f64e130f024d2bfafe40a032481e0294604de32d22ffc68564541281bff0144081a63d8b819409fff785350254fffe02f017139c88000001547ebf703c5804a327e1f3e4c0082f1cf1be89c1b0004ec7062909778125ffe0ca5ec0085e09fb70ef058a20000dc5fff81aae0670005ffd7000400fcfea2002aaffec8001025157aa85702d1ae1e9c8400000003ff3fc7f8990414d7fe7f00184005c15620000af597d0ca8a688f6fe300022685f554114bff14d63033dff85f00ccb9c800caef024afe865044340378275f91338fb400f3f404a0073c6fbb0870004c004ff0178007139c9224a93c6a8dbca09400dffea8819f3f0e0085a338ff5f0360058d98227afe40ec8c00004fe7ff61784cbbc09000001f000000138ffe14e3f504e40cc185538033003cfc0464a86819c66172268a04d84e148820c8404551112469184211b10d424450f4fc3981c641855454d52428511404f1394b0a82900c2809c090941f0c00486a170520e0086017c5e16e06490464743a41c6518c6289d565552c42c2487612872188442d0320f8340b1303c1762a1695855d3d4084844d304b51c082018260882e2d96540436024cd324c51488e038120a0bd2b11e2c86d204404a88a210da2550438caf100d43b0f8371270f0b8348900001c0697a94f9158e38c58a386e83a81a7e378274c7106d06b169b6616155e45835535255044aa44941c3e83ca39b3563403132e32b02a526c2151e51b618713f11d0dc0c607204902300090414ae2e57352b8391cd48e6253032c3c90c14ae12560729829619cae3248352c189609ca632570329859605cae2647132a8b9589cb06a48172c0994c04a40d98306c1a32059b060c8126c3c36199b0251862641a8481c2e0d5418ec107482830c498202c18ffffefeff7fbfbfbfefbbdebf549404c1100c010
def Zr9 : Zah := (48,2,8,655366,67,12,1166,Zr3)
def Zr6 (i : Nat) : Nat := (if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def Zr2 (j : Nat) : Nat := (if j<1 then 0x53d58f2b3c28eb83a90e78393ce293768dc436c0d91359cd2233fccd432b8c9b31e8c563090c122ff0be22e5cb622d3cb392c18ada2a50a812994a3427f09d626f4992261496024dc8fa233c89b218c82b20607d21e947751d3c7121bb86c21a9467a198461f17d85bc162455014a050a13844ce128c480117842b0fd83d40e4037d0d102f70b4c29309a022507f01d106b417a053c118039c0da031c0b40284066016404600cc020003400095304255c6295717a5661894973e525d195317a5661095313e55c9595714e564629597725641695724a561d695654e55c4f94875a52618959072564df95718254c5595987e554d394918a55c5c95935255cd195515a55c9495315e565d4959872560569531825589795985a5641f95716a5662295656a55c0e9487565641894874652610949772558d394937da61d9688739a5cd169970da26102d9034b6622716559f4c5d698305a4c602d983645897698724b65d12d974a45c0f69516e45c012d9179a6055698744b261691604cb64cb68970cb641c91874e154d568972634c21716356164d490985da24e0688746364e17d9775a661669814da261f2d977235c9391206da649b699181a65d169811a154da91935da609490815da5c112d976a4605791725cb65cc7d7174b659391706da6608912060b655291315e45c1a698750b2614689744b65ce68816da65c969875a45c132d926da21d985313db5c5e689862324992d9649a605a7d4179a615369534a465d32d9169a61da698159a262269916da481b688169a6622689871a6155699381a4c112d987244857697180b646068874a154d3698121a604769706e421d3698569a24602d9189f64dd69816da21da8d718646593698704b644f69826e35c962d916cb64927d4181a6095698559a245b69874e35c9a90814e365e191514da66182d9131a61c769985245953716555a61c391814c465d11198004261035870c4660421932d765c21098604660d259784465c519954a04c571197384660f3d861cf604a81534c464d23d8618464e015963196053618120f644a59900d665c3119548a640d89724ca640051877595c1b5d8205625c3259235760805d820c42614119039764c23d8621d54611d9411e4c5d49850c465d2893085461017553844649b119820f244a59700d26141119180466223d86049648b019715061434d8408c61c305954816545458508264d2398609560830d9217ffffeff7febfbff6fdffb7edfbfeffbff7f6fddf7bdf79eefdd7b7f6ded7d7faef3fe77bff7fafddf7bdf77edfcff9f73de6fc7f4c1524815261d405c5405c140505404c5406193060930605305c5305c130589305813054530481302053060d105cd104c11020d101cd100c1100411061830604305c4305c0304c030204301c43060c10608104c0101cc10 else (if j<2 then 0x294b87d9e18125a4c0d94ff1102129ffd080042d275fc88cc7d08e32d5a4ca1d3e240ca037fc0042243d78c55d1318fe00895fff0e105d3009081b01d1fd4e20010e7b410dc82500e01ff0000d08c5060b310c019f4978ffef011359ed040b978a3df8cc2818025730485f341944407c3d214551e90632fde35400ce503bbfd64a14479ebd08198bf837d44a8044d40dfc218819dbe3fb489689a11fd4cfa8410a203b8c33a15081a8f482827f7a6d123c1044da94fef4220672ff8fda88267aebe1881981af92c46490191206189cd483f27d448490174c4a3c749363910d1e90630ef8780361ff911abdb383b610b5f13eba1b0203547ec9e824206907fb855000c14449c5d78852e1c8ad47cc58b8f0853da088ff1343221a0f764452011fdd10858604791431a4bbe9cd63940d22e1078c2057cbebd8aa49a3359ed0427c0af2080034400017c0bbe142f9501b60af51a91d3e015c308f48d5aaf7fb0e401527fcb0c8f4880466b0029f743c2871a470e26782bd46a479fea3fe0240932f282e30219bffe705d071346fc66140c0128a067b410f6821ed040efce05fa1e10d25033da087b410f6821ed04281c0e41a23c2e3080f21c82d0944b4cc4ab92ce2024c969130ec472814036174444546487c211c18800fa1ed3c6140189d9240742621c03786b6b0562abd2aa65822014464402444813026719d05a6686b1984442810b1861861dc22c9108c4700420840a0a125175b8d0fa8491844c10c39881a022281e0f2a006d41e96524896817824458500ca4084731d22819a8e88710c116154208188740800f0dc18d0622c43623134400c041dc3ab410e64af12e2d12b4c795a0211a4c89017184ac703384681383b00e220c8188a0d08a490d1a151cc378b28a70f0bc1ea0a42d09180e0385108e88686e0fc0813f0686165689024b11a661a3108784014819060ac461ff0584347c17695a070700e43604a0d216e0307c8499649f2066215043f30f06e0d2881070d40f81d83606a0bc2683ac4801c0004c00c0ba6cd9a72682994e633984a5e997565c39642569950a523942e4f4936a4c0925246e917643e908e4048f223ad8e4e3788d5a32f8c462db8aca27f895e23f88aa204874a1ba866e175854e13484520f9833a0b682ba09281f205780ae00f7fc9fd57ecdf9e7e21f357c11ef47b11ea87959e2c7871dfa7741da57601d607501d0e73d1ccf728dc83718dc4870b9c0b6f8db9f6dfdb596ccdb046b9dac76aa1a8a69c1a3267699c26695979652991363e18c86259878611981b5fd17d85eb57775d2d7275c216be5a8567e598962858455e256a558f559d51e53ad4d2529d49851f1456510541650013d74ead37c4d3d3384c4d2ee4b052a149c5249489120c47b91ce46bd18e455112744210ea430108b413901e402cfe43efcf8 else 0x2f02307bc14abdfc307b7cc69f38145081a23fe881901ef881084fe013a08547682bc08c9d1ec34420438ffa252847172f00810a97f7d114b9618fbd23190f884c4f4813469ff92003369f84009499a625fde088bd9571903cb803233ffc88b000204443891835f70913be00324f1dc2c8dded86c01980f500a327ffc4d185021e1eaea8810aefea20a20021c3a7c2c0199718110f88498f25040429bfca5410010e5d2cc70e2c3a137e3d9104747e100211bfe003255f98051aff1044a87d89218cffb7184019ca08c87321269f5983a927e8501b41251f09a0f6b1888a174c4a3578cfd210bcc0c3ed2197fffc5a3080e0854206d53f4482041535911d8fe7e60441647c503243e1da8c958204200811a1fe7da913334029feb118511ff95848330f73e7400488bfa10023cf83f022cfaa80230379971f140d0bd62a22ffcc0411b7fe140a09234f15091b7a4be1159fe903cc780896fed48a13dfa9b0021400d7b0dd44fa02228de1002133aacb806633f2003a90193ffd31033c7db499213760a107c56322af8e408a3437a247fe881e00c000d411ff87d00ad07f708804df7f90499f420643be040300a502e0cffc28cfdb7f8547a889a4efe012ede01555805373f061200010e3fa8822a3a7aa090010e1ff850001986fd2c68238d7c222ebfff2a428517fc9ba8410a1f71f44c041257e97c411b32a943297ffffd6190000804d75e700646fe1268cb5ff104ccfcff9208000445cd025064fff4c40ce5fc1be9a60a06959f41125d9df21a1483f1fded08000440da5ff84202501a17fb00de7c02061295c0253e904197a409b4cc798240ffe02840cc6e4128bfc82002175fe9da0021adfcfcc2a1437bfa24010219fec02de721f20a0b1e1050cc027924e7086cfd42065dbea0a2100a657b3a1c08577de82042d61ab1a8fe008b97fa808bb9e8091a5dd54108077c7d86cc024403fc56420a194fc88518f58c28b9e184a8033f3ff4214410a1e9ff6e9016358512bd7c54440093b110c3e3680033698595029012ff94541840888b876c06054c5fe564c819b9f40090801ff67a58611f58220371f4120e0af50952483fd0610217de28040850fffc0150dba624048da7c412d9a924df302a3bbec500))
def Zr8 : Zah := (259,3,8,2490403,102,14,1251,Zr2)
def Zr5 (i : Nat) : Nat := (if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def Zt2 (j : Nat) : Nat := (if j<1 then 0x5a2c6b4e344b82353242352c282e4709b5145eb04a292e47c9b4afc2152e1f2e2a66aa76942a4e8cb494622e2e0cb491c9950529240a0c34b454330e5eae4cc9b511e6aa4717ae4989b4ed1a346149b4f20f341467a633e32a2c54130ed41512c234ebe2ae0e9632a5c9b4748215244f344d8f34cd8f152ddeae490e342ca7a831e12e485eae50cab46ad634460f34e654130a02352b89b517142604941317e12e300e344409b4375432ea54b2e5cf150dd62ca9cf34a69a302c4f34c68234c9dc30f354130d669536692e474f34268e344a89b4751b2a2d1c30f30234e9d41517d41312c9b42fdeb4e0e5aa7709b4af57b245cf150e423525e3ac079eae48dda635692e48272a27c13524c13449c1344e811503c135255ba63384b4d544b4e341353110b4662626160e942981352d013475d394318894318d34665332e1c19526c134380db44686349516a832933440863483049522d594060bb4a644b4e390b2b112350290b2a588344547b470972616d0aa69c8344f4834021ca630982e01a1ae2e0834424bb4ad90aa38252a271e241764aa47013509891511552a69c5b4b04b34761ba8320134c9d534661d263145b4a259ae01592e238db4464a34ed81352cc135314134e9cd342705b4af90aca9daae0105b4b0a0ae289e2a48de2e48c934154115359032a0202e2e001522c0b4408fb0c292b040642a470734024334a346b44243b4834534a244344342b4e351328011b0807ff3febfdbfcffb7f7bf6ff6bf5ff5bf4ff4befbe7fdfbdf7df3defdebdd3bfbbf7befbebbdfbdbbd7bbfbb7b7fb7baffafbaf79ff9fb7ef7eb7b777f77b75f5ff3ff3f73ef3eb3bf3bb3af37f36f2beffaff2feefeafdafbef7ef7af6eefedfabfebfabf6beebdebdabcebbeb7eb5eafeaeeabea7e8fe7fe7fa3fe3ee2fd984c15264530549714c15226130548914c15265d20549714815254d205495148152645875013161d4024d875009161d4064d71500985c54024d71501715c1405057050187505405c541501315054065d31501904c5405c531500984c54025d3150192619305c1864c15161930481864c09161930205864c1726093021d824c0816093021d814c1985c530641714c0985c530589704c1315c130485704c0815c13061d624c18558930605624c17258930595624c15158930261624c08758930615604c18258130595604c08758130609514c17254530261514c1964813061d204c18548130605204c172481305c5204c17048130595204c16348130581204c15348130545204c08748130205204c195205305c8814c1532053021c814c17360d105c183440985cd105c530440974c11065c834419161830245860c09760430619710c1941c43025d83041976081064d82041874c01061930041854c01060930041981cc1064073041821cc10 else 0x36285bf610c3eb16a0f78313259a16018b360a9f1020ef08ac84e1493586087710ef811806dc08f490f0c6a2601ae5091c1046648f7d2431b843c342afe64645d2134087bd144b9847522ee8c4dc189c047018f390d40b2e8594b1081edd0b3e0241dec472b4246af906806788830d068cb760514584df0120f2e850c1058f0f0212ae845fa09e01cca15e22d910c023488b22f7a20b6b88720e689161514304a0dbca8c60e8e20d8076910fd81107a90d80738421704153cc4838e04c75c018cfa233c22ea4d147229c443187434d85e01bbdd050c0a029f98a7213bd9053f810ce11201bc030704135d0af090ef113809617a19e1120378896350dbae58d7e021a7f93416538447e035025020fac5622cfe9244cb3f121cd550c7b8864c89013b01d795318f350dd01ba037a03b66826fc0477920b7f311117f8218f421cb2d5070ea9419d9157940032cf021d52c5bc14368113221798506e80d0127f446265d68920dec0680a3e0631c422051e818c991172c18eb8031da118bc40835e821bf00c4f086ce0733429aa12fec110fc119028f818f734260200e30411f80c9b234047fc04859147c0c63a843c721a0e384719239fc10ce05bef922003ffe3641203e90c6650ff58992bf5c4c93f1c110003813ff024e7f081932f1432f4d18f39aa643fe2240373ed140dcfb45df7c91013c18dcad880270dc441c26b480c20266c458909250d2e0e8874ac26092b88420217891a0d54742281b6482c81d0747281a198119450c3dc381a4a5e26c27825823e0d20001d02301746741d4c4443144021780780c17119a25e1755c6c3c25749010c0d501824c2079640e40f813e19f0901b344081825016c0035060181340e81fc01801f8901f81f01a81300bc0bbe2fdd3d87d57ce7cabc77c23bb3b73b43af3aa3a53a079e39a79538fb8c788382f7e378b73b6fb68b6476135ab55f52b4df49345f4273d33a335f3172e72a72371ef1ab13f10f0d304eff6fc2f52f0eebee42e02db2d76d36cfacb2c8ac52c1abc2b6eb0eab6a529ee98294e9168b286282e7ea79672a6ce67262a5ea59655a50a4ba4824463ee3b638e3423062ae2522161e61aa1561160c2086051ff5fb5f8df51f01ea1e45db9d7dd39d09cd9c8dc59bcdb75b21acda91a65a259c59719358f98b98698197c17516f56a563d5d55955154c547d4293f53b934d3112e52591f11ad1811290e90bd061024fc0f64f24eb8e64e20dccd8cd48d04ca0c54c28bd0b88b58b34ae4aa0a58a2c9cc99493c8e888083c7f87a076c7046505c85504dc4703b43402e82802181b81400c80600002353797ae57d433049fb027d634c6141314d634e609b4cf68ae2729ae26deae4b142e3814130f1eae4d18ae0ea2263428952709b4efa924178c34b714152d49b4cfdeae4949b4355b14ad)
def Zub : Zah := (203,4,8,5505121,119,12,1118,Zt2)
def Zt6 (i : Nat) : Nat := 0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def Zt1 (i : Nat) : Nat := 0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def Zua : Zah := (28,5,8,0,0,10,0,Zt1)
def Zt5 (i : Nat) : Nat := 0x2022120a00481835bb4200000707b100030
def Zt0 (i : Nat) : Nat := 0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def Zt9 : Zah := (7,6,8,0,0,6,0,Zt0)
def Zt4 (i : Nat) : Nat := 0x78001b2d178400008
def ZtZ (i : Nat) : Nat := 0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def Zt8 : Zah := (3,7,8,0,0,5,0,ZtZ)
def Zt3 (i : Nat) : Nat := 0x1e0
def ZtY (i : Nat) : Nat := 0xd41d1505c4da54cb94817254530
def Zt7 : Zah := (1,8,8,0,0,0,0,ZtY)
def Zko : Array (Bits × Bits) := #[(0x840a108bec0006,0xd3584ac0e0a004),(0xffffffffffffffffffffffff24640550c50029,0xffffffffffffffffffffffff2c85b1021f1821),(0xffffffffffffffffffffffff61200154008957,0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),(0xffffffffffffffffffffffff000b70212005e1,0xffffffffffffffffffffffff28a2b4371545e1),(0xffffffffffffffffffffffff8880028a0a427f,0xffffffffffffffffffffffff04a7252e0a5a3b),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def Zkn : List Za7 := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def Zn6 : List (List Nat) := Zg2
def Zmj : Nat → Zah
  | 12 => Zsa
  | 11 => Zr9
  | 10 => Zr8
  | 9 => Zub
  | 8 => Zua
  | 7 => Zt9
  | 6 => Zt8
  | 5 => Zt7
  | _ => Zbs
def Zn7 : Nat → Nat → Option (Nat × Nat)
  | 12 => ZaH 35 135 6 13 6 3 Zr7
  | 11 => ZaH 470 589 6 16 9 3 Zr6
  | 10 => ZaH 338 423 6 15 8 3 Zr5
  | 9 => ZaH 9 55 5 12 5 3 Zt6
  | 8 => ZaH 3 13 3 10 3 3 Zt5
  | 7 => ZaH 4 7 1 9 2 3 Zt4
  | 6 => ZaH 1 3 1 8 1 3 Zt3
  | _ => fun _ => none
def Zaq : Zaj := ⟨1407,12,fun j => Zko[j]?.getD (0,0),Zkn,Zn6,Zmj,Zn7⟩
set_option maxHeartbeats 0 in
theorem Zdw : Zaz Zaq (Zat Zb3) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=4) ?_⟩,ZaF (d:=1) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def Zbd (j : Nat) : Nat := 0x965808769465755094657540946575309461755092462752855829948558298485582975855829648558295485582153824627738246275382462752823627738206276281756661817566518175664181756640817566206567401065614010656040106557417565574153655141856537501065374070653740106530401056854187568541655685314356784170567640705675419056754180567541705675316056752150560640805606407056064060560640405603408049568574495685734847668442482343424823324247233242452343424523324176809041768070318412323154128526783191267831212678311026763191267631212675412126184171261841612618412126083191260541812453237314678090146780101461801014608070146080501460801013451272
def Zbb (j : Nat) : Nat := 0x82306318240152300810252493100532008015021683021531076255694810653000762326318002751007620569180038400076202691800762000750208924604653107361519420050210070352810670142300703228196702845006783004321004311067136584900463000670365849004830006350690857005460063406918570054600634069185700485006340691857004350063200786120761310632007861206502106320078612057021063200786120541810632007861205402106320078612043021063200786020850210632007860207502106320078602065191063200786020650210630531470204312006012648130040260054077183620671200540771836205217005267091485008530042654735820407300426007658201073004260076582010630042600765820096200426007658200862004260076582007510041730756930017300370208612004017103407907562037050031569275130642300307214263002140003016947530075400030121426300214000301214263001830002765068950056411027600689500564010276006895004530102713352490039400027133524900384000271335249003450002710352490034500025800543290032410240691856207512002406918562065120024069185620641800240671856204716002106928531075320021069285310642800210692853105726002106928531053260020569485300754000205694853006840002056948530064380020569485300643000205694853005320002036012780029611020360127800236110201694853007540002016948530068400020169485300674000201694853006540002016948530064800020169485300643000201694853005730002016948530053260016720598600576010167205986004650101620263180032610015360168920045110132681962007621001326819620068210013268196200651000123683962005428000765826713056230007628269170451200067283674206743000621463581040610006214635800305100054601687200346100346006875004571003284135200402100032681962007621000326817620076210003268176200659100032681762006521000321413520040210002674730820407300025683764207643000256837642065320
def Zbf : Nat := 0x241408410842110c0300c03
def Zbe : Nat := 0x11489414e86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zoi : Zaa Zaq 5 0 1 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x43) rfl
  decide +kernel
theorem Zsj : Zaa Zaq 5 0 1 := Zoi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zoj : Zaa Zaq 6 0 3 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x2c1125) rfl
  decide +kernel
theorem Zsk : Zaa Zaq 6 0 3 := Zoj
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zok : Zaa Zaq 7 0 7 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x342d2111268edc) rfl
  decide +kernel
theorem Zsl : Zaa Zaq 7 0 7 := Zok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zol : Zaa Zaq 8 0 28 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xc392711360349312e3522002836140833a799cededfcfa894bde2bc) rfl
  decide +kernel
theorem Zsm : Zaa Zaq 8 0 28 := Zol
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zom : Zaa Zaq 9 0 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xb7bfcd9fa6b889a5b8cfa50098c8918700000000000000000000000000000000) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZmC : Zaa Zaq 9 32 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xcfd59c9d84b89aa3c5b89ae1a2cc009acf9e00e0aba6a4dba5c6d89fd0009ed1) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZmD : Zaa Zaq 9 64 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x36441a4c3a409f9f9f9f9fd992839fb88a009f9fa3a3d48b009fb4b290a99bb0) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZmE : Zaa Zaq 9 96 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x363638481036363624122438242f15383b2b1f1332194c3638301c3c0b383624) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkD : Zaa Zaq 9 128 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x638384d0d45381230171d41023836003c060f242016183e4b4718120b241c36) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkE : Zaa Zaq 9 160 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x5363715073a361e0b38361b1538123606363b060923361204013606004c3829) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkF : Zaa Zaq 9 192 11 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x3838382a1238123800000a) rfl
  decide +kernel
theorem Zsn : Zaa Zaq 9 0 203 := (@Zad Zaq 9 0 96 107 (@Zad Zaq 9 0 32 64 Zom (@Zad Zaq 9 32 32 32 ZmC ZmD)) (@Zad Zaq 9 96 64 43 (@Zad Zaq 9 96 32 32 ZmE ZkD) (@Zad Zaq 9 160 32 11 ZkE ZkF)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zmz : Zaa Zaq 10 0 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x0) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zkz : Zaa Zaq 10 32 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x0) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkA : Zaa Zaq 10 64 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xa6af00009fa60086c3b3c49fa68db6d6e500b09f9581c0a08cc0000000000000) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkB : Zaa Zaq 10 96 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x86e381b8d786889fc3a681a686beaa93868600b1869fcbb000c9b5a6b19fbb86) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjl : Zaa Zaq 10 128 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x84ca81d29586ca00b8b200cab000d300ca82d39fb8a6b9c3ca869f00dae485ae) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjm : Zaa Zaq 10 160 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xca81d286aa9f86009f9f86c0a19facadc7ca939f808fa68db0ddb6c1a6939f00) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjn : Zaa Zaq 10 192 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x364d3f36060036360f12000f0f4d4606ba9fb8b8b8879fc29686979f00b09f00) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjo : Zaa Zaq 10 224 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xf0f000f4e4600364d423d36420036004a060646063d0b4d0e0f4200000e4d) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjp : Zaa Zaq 10 256 3 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0xf0006) rfl
  decide +kernel
theorem ZqP : Zaa Zaq 10 0 259 := (@Zad Zaq 10 0 128 131 (@Zad Zaq 10 0 64 64 (@Zad Zaq 10 0 32 32 Zmz Zkz) (@Zad Zaq 10 64 32 32 ZkA ZkB)) (@Zad Zaq 10 128 64 67 (@Zad Zaq 10 128 32 32 Zjl Zjm) (@Zad Zaq 10 192 32 35 Zjn (@Zad Zaq 10 224 32 3 Zjo Zjp))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZmA : Zaa Zaq 11 0 32 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x0) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZkC : Zaa Zaq 11 32 16 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x0) rfl
  decide +kernel
theorem ZqQ : Zaa Zaq 11 0 48 := (@Zad Zaq 11 0 32 16 ZmA ZkC)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZmB : Zaa Zaq 12 0 6 := by
  apply Zar (pos:=Zbf) (neg:=Zbe) (kw:=Zbd) (panels:=Zbb) (data:=0x0) rfl
  decide +kernel
theorem ZqR : Zaa Zaq 12 0 6 := ZmB
theorem Zdp : ZbM Zaq 12 := by
  intro k hk
  interval_cases k
  · exact Zap Zaq 0 0
  · exact Zap Zaq 1 0
  · exact Zap Zaq 2 0
  · exact Zap Zaq 3 0
  · exact Zap Zaq 4 0
  · exact Zsj
  · exact Zsk
  · exact Zsl
  · exact Zsm
  · exact Zsn
  · exact ZqP
  · exact ZqQ
  · exact ZqR
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZdB : Zax false (Zac 1407) 12 (vars 1407).toFinset := Zcz (q:=383) (prior:=Zat Zb3) (Zai Zb3 ZcG) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZrD : Zaf false (Zag 2431) (Zac 2431) 13 :=
  Zaw (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=0) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def Zhh := Zan Zb3 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnM : Zak false Zhh := Zao (m:=2431) ZcG ZrD (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zrt : Zaf false (Zag 1407) (Zac 1407) 13 :=
  Zaw (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=1) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def Zg7 := Zan Zhh 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZnC : Zak false Zg7 := Zao (m:=1407) ZnM Zrt (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zqb : Zaf false (Zag 54143) (Zac 54143) 13 :=
  Zaw (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=2) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def ZgG := Zan Zg7 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl6 : Zak false ZgG := Zao (m:=54143) ZnC Zqb (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp5 : Zaf false (Zag 44415) (Zac 44415) 13 :=
  Zaw (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=3) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def ZgC := Zan ZgG 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zl2 : Zak false ZgC := Zao (m:=44415) Zl6 Zp5 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zp0 : Zaf false (Zag 43903) (Zac 43903) 13 :=
  Zaw (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=4) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def Zgz := Zan ZgC 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZlZ : Zak false Zgz := Zao (m:=43903) Zl2 Zp0 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZpX : Zaf false (Zag 42879) (Zac 42879) 13 :=
  Zaw (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ZdB
    (ZaM (g:=Zaq) (i:=5) rfl rfl (Zai Zb3 ZcG) Zdw Zdp (by decide +kernel))
def Zed := Zan Zgz 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZgT : Zak false Zed := Zao (m:=42879) ZlZ ZpX (by decide +kernel)
def Zvi (i : Nat) : Nat := 0x16ad2728c1ee6b16a4a0e629062082fff
def Zvj : Zah := (1,0,5,0,0,0,0,Zvi)
def Zoa : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffff8278ca9,0xfffffffffffffffffffffffffffffffe078829),(0x8c5796,0x1884792),(0xfffffffffffffffffffffffffffffff819b865,0x31b824),(0xfffffffffffffffffffffffffffffffe1200db,0xfffffffffffffffffffffffffffffffec400d9),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def Zn9 : List Za7 := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(42624,0,42879,0,13),(43648,0,43903,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(60032,0,60287,0,13),(69248,0,69503,0,13),(49168,0,49647,0,13),(55312,0,55791,0,13),(43072,0,43455,0,13),(58432,0,58815,0,13)]
def Zie : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def ZqL : Nat → Zah
  | 14 => Zvj
  | _ => Zbs
def Zsb : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Zaj := ⟨1535,14,fun j => Zoa[j]?.getD (0,0),Zn9,Zie,ZqL,Zsb⟩
set_option maxHeartbeats 0 in
theorem ZsV : Zaz xd (Zat Zed) = true := by
  simp only [Zaz,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=3) ?_⟩,ZaF (d:=2) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ZqB : block xd 14 0 1=true := by decide +kernel
theorem Zos : block xd 14 0 1=true := ZqB
theorem ZqC : ZbS xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xd 0 0 0 = true)
  · exact (rfl : block xd 1 0 0 = true)
  · exact (rfl : block xd 2 0 0 = true)
  · exact (rfl : block xd 3 0 0 = true)
  · exact (rfl : block xd 4 0 0 = true)
  · exact (rfl : block xd 5 0 0 = true)
  · exact (rfl : block xd 6 0 0 = true)
  · exact (rfl : block xd 7 0 0 = true)
  · exact (rfl : block xd 8 0 0 = true)
  · exact (rfl : block xd 9 0 0 = true)
  · exact (rfl : block xd 10 0 0 = true)
  · exact (rfl : block xd 11 0 0 = true)
  · exact (rfl : block xd 12 0 0 = true)
  · exact (rfl : block xd 13 0 0 = true)
  · exact Zos
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zso : Zax false (Zac 511) 14 (vars 511).toFinset := by
  have h : Zax false (Zac 1535) 14 (vars 1535).toFinset :=
    ZcW (g:=xd) (i:=0) rfl rfl (Zai Zed ZgT) ZsV ZqC (by decide +kernel)
  have e1 : Zac 1535=Zac 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Ztd : Zaf false (vars 511) (Zac 511) 15 := ZbN (hints:=13438558465) (by decide +kernel) Zso
def ZhI := Zan Zed 15 [(511,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZqF : Zak false ZhI := Zao (m:=511) ZgT Ztd (by decide +kernel)

def Zgj (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def Ze3 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< Zgj i)
def Ze1 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< Zgj i))

set_option maxHeartbeats 1000000 in
theorem ZfW :
    (∀ i : Fin 9, bit (Ze3 i) graph ≠ bit (Ze1 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (Ze3 i) (inputs.getD j.val zero) =
      bit (Ze1 i) (inputs.getD j.val zero)) := by decide +kernel


theorem ZqD (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 14 else 15) ∧ Zav u graph k inputs.toFinset := by
  have goalEq : (Zda C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (ZlJ C legal C.output r).trans ((congrFun computes (sample r)).trans (ZkN r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, ZbQ g=false) ∧ C.gates.countP (fun g => !ZbQ g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, ZbQ g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !ZbQ g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !ZbQ g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !ZbQ g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := ZdW (u:=u) (Zda C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [ZfM pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono Zf8
    (out.resolve_right (fun h => h Zf8))
  have ns : inputs.all Zbt = true := by decide +kernel
  rw [ZhX ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←Zfg] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply ZdG run inputs (inputs.getD i.val zero) sub (Ze3 i) (Ze1 i)
        (ZfW.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply ZfW.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem ZjE
    (m : ∀ k, k ≤ 15 → ¬Zav false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Zav true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := ZqD C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

abbrev Zd9 := Nat × Nat × Nat × List Nat
def Zfa (rows : List Zd9) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def ZfY (base : List (Nat × Nat)) (e : Zd9) :=
  (Zat base e.2.2.1 == e.2.1) && ZeF e.1 e.2.2.1 e.2.2.2
theorem ZgO {u base rows} (h : Zak u base)
    (cert : rows.all (ZfY base) = true) : Zak u (Zfa rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [ZfY,Bool.and_eq_true,beq_iff_eq] at hh
    exact Zhz hh.2 (hh.1 ▸ Zai base h r.2.2.1)
  · exact h e hb
def Zka : List Zd9 := [(151,5,94,[48,33,133,118]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(223,9,478,[80,16,33,50,116,131,100]),(239,9,127,[32,83,116]),(247,9,478,[48,33,133,118]),(254,8,251,[32,83,116]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(350,8,95,[128,49,100]),(369,5,94,[16,82,131,100]),(371,8,95,[16,82,131,100]),(375,9,127,[16,82,131,100]),(381,9,127,[48,129,82]),(440,5,94,[81,130,118]),(444,8,95,[32,49,128,81,116,100]),(446,9,127,[32,49,128,81,116,100]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(463,9,127,[16,32,48,128,100,80,116]),(471,8,251,[16,82,131,100]),(477,8,251,[48,33,133,118]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116]),(491,9,127,[128,81,32,49,100,116]),(493,9,127,[80,129,50,116]),(499,9,478,[32,83,116]),(501,8,251,[80,16,33,50,116,131,100]),(505,9,478,[16,82,131,100]),(506,8,251,[128,49,100]),(510,12,255,[32,49,128,81,116,100]),(1279,12,3579,[81,130,118]),(1407,13,28143,[32,49,128,81,116,100]),(1503,12,18911,[128,49,100]),(1527,12,3579,[16,32,48,128,100,80,116]),(1531,12,18911,[48,129,82]),(1791,12,17405,[48,129,82]),(1967,11,4927,[32,49,128,81,116,100]),(1983,13,17343,[48,129,82]),(2015,12,17403,[48,129,82]),(2039,12,17403,[80,129,50,116]),(2045,12,17151,[48,129,82]),(2431,13,9599,[16,82,131,100]),(2493,11,2239,[48,129,82]),(2495,13,9599,[32,49,128,81,116,100]),(3263,11,1375,[80,16,33,50,116,131,100]),(3391,11,1343,[81,130,118]),(3519,13,28143,[16,32,48,128,100,80,116]),(3571,9,11742,[32,83,116]),(4955,8,1725,[81,130,118]),(4991,13,17343,[16,32,48,128,100,80,116]),(5053,11,6847,[48,129,82]),(5111,12,17403,[16,32,48,128,100,80,116]),(5115,12,17405,[16,32,48,128,100,80,116]),(5117,12,17403,[48,33,133,118]),(6511,11,1343,[16,32,48,128,100,80,116]),(6606,8,1119,[16,32,48,128,100,80,116]),(6639,13,28143,[81,130,118]),(6654,12,18911,[80,129,50,116]),(7039,13,17343,[81,130,118]),(7150,11,6847,[128,49,100]),(7166,12,17403,[128,81,32,49,100,116]),(8167,11,1727,[16,82,131,100]),(8175,13,17343,[32,49,128,81,116,100]),(8183,12,17405,[32,49,128,81,116,100]),(8190,12,17151,[32,49,128,81,116,100]),(8679,11,2751,[16,82,131,100]),(9702,8,2237,[16,82,131,100]),(9710,11,2239,[128,49,100]),(11710,9,18814,[81,130,118]),(11711,13,28143,[16,82,131,100]),(11773,12,18911,[81,130,118]),(12716,7,2079,[32,49,128,81,116,100]),(12719,11,2367,[32,83,116]),(12733,11,2239,[80,129,50,116]),(12735,13,9599,[81,130,118]),(12781,9,2429,[32,83,116]),(12783,13,9599,[16,32,48,128,100,80,116]),(13310,12,27127,[48,129,82]),(13806,11,2751,[32,49,128,81,116,100]),(14191,11,4927,[128,81,32,49,100,116]),(14269,11,6847,[80,129,50,116]),(14303,12,17403,[16,82,131,100]),(14310,8,1725,[32,49,128,81,116,100]),(14319,13,17343,[16,82,131,100]),(14333,12,17403,[80,16,33,50,116,131,100]),(14334,12,17405,[16,82,131,100]),(17342,9,7038,[81,130,118]),(17406,12,17403,[32,83,116]),(18429,12,27127,[128,81,32,49,100,116]),(18779,8,11453,[81,130,118]),(18815,13,28143,[32,83,116]),(18939,12,18911,[16,82,131,100]),(18940,9,11742,[81,130,118]),(27623,11,2751,[80,16,33,50,116,131,100]),(28079,11,1343,[80,129,50,116]),(28134,8,11453,[16,82,131,100]),(28155,12,3579,[128,49,100]),(28157,12,3579,[80,16,33,50,116,131,100]),(28158,12,18911,[16,32,48,128,100,80,116]),(32750,11,2751,[128,49,100]),(37374,12,27127,[48,33,133,118]),(42719,9,48094,[80,16,33,50,116,131,100]),(42727,8,42679,[16,82,131,100]),(42867,8,42591,[16,82,131,100]),(42943,13,44927,[81,130,118]),(42951,7,42683,[16,82,131,100]),(42995,9,48094,[32,83,116]),(43003,12,44799,[81,130,118]),(43447,9,46455,[81,130,118]),(44287,12,58335,[48,33,133,118]),(44415,13,58239,[48,129,82]),(44479,13,58239,[48,33,133,118]),(44511,12,68863,[16,32,48,128,100,80,116]),(44539,12,58335,[48,129,82]),(44541,12,68863,[80,129,50,116]),(44791,9,48094,[128,81,32,49,100,116]),(44915,8,42679,[81,130,118]),(45039,13,44927,[80,129,50,116]),(45041,7,42711,[81,130,118]),(45047,12,42751,[80,16,33,50,116,131,100]),(45051,12,42751,[81,130,118]),(48063,13,44927,[32,49,128,81,116,100]),(48079,9,42623,[16,32,48,128,100,80,116]),(48095,12,42751,[16,32,48,128,100,80,116]),(48111,13,42879,[16,32,48,128,100,80,116]),(48126,12,44799,[32,49,128,81,116,100]),(48635,12,58623,[81,130,118]),(49403,8,43479,[16,82,131,100]),(49643,9,46455,[80,129,50,116]),(49662,12,58623,[32,49,128,81,116,100]),(50047,13,58239,[128,49,100]),(50143,12,58335,[128,49,100]),(50158,11,58047,[128,49,100]),(50159,13,58239,[128,81,32,49,100,116]),(50167,12,58335,[128,81,32,49,100,116]),(50174,12,68863,[32,49,128,81,116,100]),(51135,13,54143,[81,130,118]),(51151,9,43647,[16,32,48,128,100,80,116]),(53086,8,42679,[48,33,133,118]),(53183,13,42879,[32,49,128,81,116,100]),(53198,8,42679,[32,49,128,81,116,100]),(53215,12,42751,[48,33,133,118]),(53229,9,44925,[32,83,116]),(53231,13,44927,[32,83,116]),(53244,9,48094,[16,32,48,128,100,80,116]),(53245,12,44799,[48,129,82]),(53246,12,42751,[32,49,128,81,116,100]),(54206,9,43647,[32,49,128,81,116,100]),(54253,9,43647,[80,129,50,116]),(55039,12,58335,[80,16,33,50,116,131,100]),(55231,13,58239,[80,16,33,50,116,131,100]),(55279,13,58239,[80,129,50,116]),(55287,12,68863,[16,82,131,100]),(55294,12,58335,[80,129,50,116]),(55789,9,46455,[128,81,32,49,100,116]),(55799,12,58623,[16,82,131,100]),(58111,12,68863,[32,83,116]),(58301,11,44223,[48,129,82]),(58363,12,68863,[128,81,32,49,100,116]),(58814,9,46455,[48,33,133,118]),(60251,8,44733,[48,33,133,118]),(60380,7,42711,[128,49,100]),(60382,9,48094,[80,129,50,116]),(60396,8,42679,[128,49,100]),(60409,9,48094,[32,49,128,81,116,100]),(60411,12,44799,[128,81,32,49,100,116]),(60414,12,42751,[128,49,100]),(63871,13,64447,[81,130,118]),(69053,11,44223,[80,129,50,116]),(69055,13,58239,[32,49,128,81,116,100]),(69094,8,44221,[80,16,33,50,116,131,100]),(69111,12,58335,[32,83,116]),(69118,12,68863,[128,49,100]),(69561,8,42679,[80,129,50,116]),(69617,7,42711,[128,81,32,49,100,116]),(69619,9,48094,[48,129,82]),(69627,12,42751,[128,81,32,49,100,116]),(69628,9,48094,[81,130,118]),(69630,12,44799,[128,49,100]),(73703,11,64191,[16,82,131,100]),(73710,11,64191,[32,49,128,81,116,100]),(74214,8,44221,[128,49,100]),(74218,7,44155,[128,81,32,49,100,116]),(74222,11,44223,[128,49,100]),(74223,13,58239,[16,32,48,128,100,80,116]),(74238,12,58335,[16,32,48,128,100,80,116])]
def pri := Zfa Zka ZhI
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zvv : Zak false pri := by
  apply ZgO ZqF
  apply ZaF (d:=6)
  simp only [Zba]
  repeat' apply And.intro
  all_goals decide +kernel
def ZiA : List Zd9 := [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def ZfO := Zfa ZiA Zcw
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZuX : Zak true ZfO := by
  apply ZgO ZhS
  apply ZaF (d:=6)
  simp only [Zba]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (Bits × Bits) := #[(0xffffffffffffffff0247102040c820c0830811,0x3f03f81ff800001f8000),(0xffffffffffffffff04c1040881096109041223,0xffffffffffffffffffc000000007e000007fff),(0x888245902104218288206,0xfff800001ff81f8000),(0x111008902432803260844c,0xffffffffffffffff000000001fffe007e001ff),(0x302182060608060410c08,0xffc0fc07e0001ff8007e00),(0xa004820208841484826190,0xffffffffffffffff0000000000001fffe07fff),(0x4420410491010901141020,0x7fff81fffff8000),(0x280820430a040604082080,0xffff0007ffffe000000000),(0xd030c38414021802104140,0xfffffff800000000000000)]
def moC : List Za7 := [(43072,0,43455,0,13),(43010,0,43517,0,12),(42512,0,42991,0,13),(42624,0,42879,0,13),(42560,0,42943,0,13),(59905,0,60414,0,12),(43648,0,43903,0,13),(256,0,255,0,12),(42504,0,42999,0,12),(2,0,509,0,12),(42752,0,42751,0,12),(43536,0,44015,0,13),(69121,0,69630,0,12),(42500,0,43003,0,12),(49153,0,49662,0,12),(32,0,479,0,12),(42528,0,42975,0,12),(17,0,494,0,11),(53776,0,54255,0,13),(1152,0,1407,0,13),(50704,0,51183,0,13),(66,0,445,0,11),(52737,0,53246,0,12),(1056,0,1503,0,12),(4,0,507,0,12),(48256,0,48511,0,13),(8,0,503,0,12),(16,0,495,0,13),(1032,0,1527,0,12),(1,0,510,0,12),(1028,0,1531,0,12),(53824,0,54207,0,13),(128,0,383,0,13),(1600,0,1983,0,13),(132,0,379,0,11),(2180,0,2427,0,11),(0,1,460,50,8),(24,0,487,0,11),(69136,0,69615,0,13),(47617,0,48126,0,12),(48132,0,48635,0,12),(50816,0,51071,0,13),(55305,16,55782,0,8),(11265,0,11774,0,12),(9,16,486,0,8),(49168,0,49647,0,13),(55312,0,55791,0,13),(1280,0,1279,0,12),(12305,0,12782,0,11),(43584,0,43967,0,13),(58624,0,58623,0,12),(59920,0,60399,0,13),(34,1,460,16,6),(47633,0,48110,0,11),(68624,0,69103,0,13),(7,0,504,0,7),(36,128,347,0,8),(40,256,151,64,6),(58432,0,58815,0,13),(13825,0,14334,0,12),(13841,0,14318,0,11),(160,0,351,0,11),(260,8,227,16,6),(1538,0,2045,0,12),(18433,0,18942,0,12),(1544,0,2039,0,12),(1568,0,2015,0,12),(32,1,460,18,7),(10,4,369,128,6),(46208,0,46463,0,13),(60032,0,60287,0,13),(6145,0,6654,0,12),(27649,0,28158,0,12),(5,2,440,64,6),(27664,0,28143,0,13),(2112,0,2495,0,13),(1792,0,1791,0,12),(52753,0,53230,0,11),(44676,0,44923,0,11),(18560,0,18815,0,13),(47744,0,47999,0,13),(55304,0,55799,0,12),(43266,64,43197,0,8),(57984,0,58239,0,13),(16897,0,17406,0,12),(0,4,369,138,8),(0,8,227,276,8),(58373,0,58874,0,8),(12297,16,12774,0,8),(49161,16,49638,0,8),(54800,0,55279,0,13),(44608,0,44991,0,13),(2208,0,2399,0,11),(46084,128,46427,32,9),(0,2,440,69,8),(52800,0,53183,0,13),(42628,0,42875,0,11),(3,0,508,0,9),(44096,0,44479,0,13),(57920,0,58303,0,13),(2176,0,2431,0,13),(6657,0,7166,0,12),(44164,0,44411,0,11),(12304,0,12783,0,13),(0,64,189,258,10),(5,0,506,0,8),(2,4,369,136,7),(47632,0,48111,0,13),(69184,0,69567,0,13),(73233,0,73710,0,11),(4740,0,4987,0,11),(55297,16,55782,8,9),(258,64,189,0,8),(1,32,94,384,7),(47680,0,48063,0,13),(69128,0,69623,0,12),(2084,128,2395,0,8),(42532,128,42843,0,8),(40,0,471,0,8),(43048,0,43479,0,8),(8,4,369,130,7),(257,32,94,128,6),(52752,0,53231,0,13),(3136,0,3519,0,13),(54848,0,55231,0,13),(59968,0,60351,0,13),(53888,0,54143,0,13),(32273,0,32750,0,11),(54801,0,55278,0,11),(0,128,347,36,10),(1,16,486,8,9),(4,128,347,32,9),(46116,128,46427,0,8),(13840,0,14319,0,13),(50752,0,51135,0,13),(4736,0,4991,0,13),(6784,0,7039,0,13),(69248,0,69503,0,13),(7681,0,8190,0,12),(47624,0,48119,0,12),(73745,0,74222,0,11),(320,0,191,0,11),(2,64,189,256,9),(32,128,347,4,9),(264,0,247,0,9),(6153,16,6630,0,8),(15,16,480,0,4),(9232,0,9711,0,13),(54785,0,55294,0,12),(13826,0,14333,0,12),(69122,0,69629,0,12),(27656,0,28151,0,12),(8,16,486,1,9),(47625,16,48102,0,8),(48164,128,48475,0,8),(296,0,215,0,7),(64064,0,64447,0,13),(63616,0,63871,0,13),(44546,0,45053,0,12),(3076,0,3579,0,12),(44548,0,45051,0,12),(57888,0,58335,0,12),(47872,0,47871,0,12),(2114,0,2493,0,11),(68674,0,69053,0,11),(1216,0,1343,0,11),(1,2,440,68,7),(4,8,227,272,7),(11328,0,11711,0,13),(68672,0,69055,0,13),(73729,0,74238,0,12),(27650,0,28157,0,12),(52738,0,53245,0,12),(44552,0,45047,0,12),(46112,0,46559,0,12),(58112,0,58111,0,12),(6161,0,6638,0,11),(12354,0,12733,0,11),(2240,0,2367,0,11),(2368,0,2239,0,11),(0,16,486,9,10),(12,0,499,0,9),(18,0,493,0,9),(33,0,478,0,9),(256,64,189,2,9),(0,256,151,104,8),(13833,16,14310,0,8),(69129,16,69606,0,8),(7696,0,8175,0,13),(49680,0,50159,0,13),(12352,0,12735,0,13),(16960,0,17343,0,13),(9344,0,9599,0,13),(59906,0,60413,0,12),(44036,0,44539,0,12),(68616,0,69111,0,12),(13329,0,13806,0,11),(69144,0,69607,0,11),(64066,0,64445,0,11),(69123,0,69628,0,9),(27657,16,28134,0,8),(46090,0,46581,0,8),(59923,0,60396,0,8),(1060,128,1371,0,8),(69127,0,69624,0,7),(256,8,227,20,7),(130,1,332,48,6),(49792,0,50047,0,13),(68609,0,69118,0,12),(69124,0,69627,0,12),(47648,0,48095,0,12),(17152,0,17151,0,12),(9233,0,9710,0,11),(27160,0,27623,0,11),(144,0,367,0,11),(60064,0,60255,0,11),(4800,0,4927,0,11),(42688,0,42815,0,11),(64320,0,64191,0,11),(58368,64,58557,258,10),(58370,64,58557,256,9),(59910,0,60409,0,9),(49160,16,49638,1,9),(10,0,501,0,8),(59940,128,60251,0,8),(52897,0,53086,0,8),(257,0,254,0,8),(58626,64,58557,0,8),(260,0,251,0,8),(2,1,460,48,7),(8,256,151,96,7),(18,1,460,32,6),(136,4,369,2,6),(39,128,344,0,4),(0,0,511,0,15),(6160,0,6639,0,13),(44560,0,45039,0,13),(64,0,447,0,13),(44160,0,44415,0,13),(44672,0,44927,0,13),(11266,0,11773,0,12),(16898,0,17405,0,12),(44034,0,44541,0,12),(4612,0,5115,0,12),(27652,0,28155,0,12),(57860,0,58363,0,12),(4616,0,5111,0,12),(44064,0,44511,0,12),(59936,0,60383,0,12),(44288,0,44287,0,12),(6673,0,7150,0,11),(7704,0,8167,0,11),(68632,0,69095,0,11),(73240,0,73703,0,11),(80,0,431,0,11),(1616,0,1967,0,11),(1156,0,1403,0,11),(1168,0,1391,0,11),(58016,0,58207,0,11),(44544,64,44733,258,10),(47617,16,48102,8,9),(52739,0,53244,0,9),(42508,0,42995,0,9),(52754,0,53229,0,9),(48160,128,48475,4,9),(11297,0,11742,0,9),(48,0,463,0,9),(65,0,446,0,9),(50817,0,51070,0,9),(288,0,223,0,9),(0,32,94,385,8),(54793,16,55270,0,8),(69190,0,69561,0,8),(258,0,189,0,8),(17154,64,17085,0,8),(44802,64,44733,0,8),(49412,0,49403,0,8),(59911,0,60408,0,7),(69134,0,69617,0,7),(35,0,476,0,7),(42552,0,42951,0,7),(44700,0,44899,0,7),(256,32,94,129,7),(44812,0,44787,0,7),(53025,0,52958,0,7),(24,4,353,130,6),(160,1,332,18,6),(13,16,482,0,5),(152,4,353,2,5),(141,16,354,0,4),(73744,0,74223,0,13),(52864,0,53119,0,13),(12801,0,13310,0,12),(36865,0,37374,0,12),(49665,0,50174,0,12),(17922,0,18429,0,12),(18434,0,18941,0,12),(18436,0,18939,0,12),(26632,0,27127,0,12),(13856,0,14303,0,12),(18464,0,18911,0,12),(68864,0,68863,0,12),(49681,0,50158,0,11),(68625,0,69102,0,11),(8216,0,8679,0,11),(9240,0,9703,0,11),(42520,0,42983,0,11),(4674,0,5053,0,11),(13890,0,14269,0,11),(57922,0,58301,0,11),(12368,0,12719,0,11),(27728,0,28079,0,11),(4752,0,4975,0,11),(42640,0,42863,0,11),(18592,0,18783,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(3264,0,3391,0,11),(18624,0,18751,0,11),(44736,0,44863,0,11),(1856,0,1727,0,11),(3392,0,3263,0,11),(55104,0,54975,0,11),(52736,64,52925,258,10),(44546,64,44733,256,9),(18435,0,18940,0,9),(6,0,505,0,9),(3084,0,3571,0,9),(69132,0,69619,0,9),(12306,0,12781,0,9),(53778,0,54253,0,9),(55314,0,55789,0,9),(20,0,491,0,9),(59937,0,60382,0,9),(50736,0,51151,0,9),(11329,0,11710,0,9),(16961,0,17342,0,9),(53825,0,54206,0,9),(58433,0,58814,0,9),(43080,0,43447,0,9),(129,0,382,0,9),(130,0,381,0,9),(58624,64,58557,2,9),(272,0,239,0,9),(42784,0,42719,0,9),(9,0,486,0,8),(47625,0,48102,0,8),(55305,0,55782,0,8),(68617,16,69094,0,8),(36,0,347,0,8),(4644,128,4955,0,8),(18468,128,18779,0,8),(44068,128,44379,0,8),(57892,128,58203,0,8),(67,0,444,0,8),(134,0,377,0,8),(140,0,371,0,8),(4748,0,4979,0,8),(42636,0,42867,0,8),(44684,0,44915,0,8),(161,0,350,0,8),(52994,64,52925,0,8),(58114,64,58045,0,8),(42776,0,42727,0,8),(47944,0,47799,0,8),(14,0,497,0,7),(44558,0,45041,0,7),(21,0,490,0,7),(73749,0,74218,0,7),(47672,0,48071,0,7),(74,0,437,0,7),(12371,0,12716,0,7),(168,0,343,0,7),(268,0,243,0,7),(18,4,353,136,6),(48,1,460,2,6),(272,8,227,4,6),(272,32,78,129,6),(384,8,99,20,6),(21,2,424,64,5),(41,16,454,0,5),(50,1,460,0,5),(133,2,312,64,5),(138,4,369,0,5),(266,64,181,0,5),(321,32,30,128,5),(270,64,177,0,4)]
def moA : List (List Nat) := Zie
def Zvr (j : Nat) : Nat := 0x30a206102004e8a0e8c6c0b2eb28da986d9ada8efa1d3d389edfd2bf251de8cb5cd425c1206ddb62a531480c954d524c120661814c53048152605314c120
def ZuA (j : Nat) : Nat := (if j<1 then 0xad8b0aad8b06ad8aa6adc30aaacb30a6cb2aa6cb0aa6c96aa6c94aa5d302a1ab0299c3029603028ebb926ebb906ebb306eb9946eb9926ed306683b8534438b3212cb300b8b291b012502a524d34f20d34320bb4f1cbb4b1d4aa51cb35114bb4b101b83051309050aa7057260fcbb52f8bb40f94260f80b90f4e302f40b90f0ea60f00b90e8b350e4b340e53b02e53260e4bb70e0bb6ae0bb40e14260e00b90dcc30adceb62d87b82d5e994d26186d26b30caa2a6c92b02c48b8cc2a392bea382bc9382bea360bea342be8330bea322bea300bea220bea192bea174bea152bc2196b98172b02390ad538cad6b88ad7386ad72a6ad7330a97192a9bb6aa69330a6c2a4a52342a1b262a0fb429d53309d92629d134299a262983382951b4295733095db0291f2a28cbb708a0aa2880b8a840b8a800b8080daa480c2a67c0b8a78d2a6780b90740b8472a3066dcb666ab34a6ab39266b38666b36666b34666b32666b30666b17464bb6a600b8a5c5b8a58e35054a36a500b8a4e4b02480b8244a30244c39640c3663c738639636638cb70340b903223502c4b96284b9026430424539020db461c53861a2aa619e3461652a615fb461272a6121b460c73860a2b460a3346067aa606439402838a00299700ab6ee25b30a4119498038247ff8ffd3ff0ff6bfd8ff4ffd2fbf3ef4f7f3dd3f72fd5bf3ebcf6f3d3cdbe7d79f3e7bf9ebe76f9d7e6ef9afe67f97fe5ef95fe3fb8fbe1ff7fadfe37f6dfd37f2dfbb7e6defb7b6d7fb5fcd7df5f6d7bb5dbd6ff5bed6ef5b7d5f7577d3fb3facfdb3eecf7b3d7cefb1ffc7fb1fdc7ef1f7c7bf1dfc6ff17fc4ff0ffbfdafd3bedadfdb7daddbaffa9ffa7f69fba7de9efa6fe7f69dea5fe8ffa3ee87fe1fd2a563505602a542505606c8a9505606c8a9605306cda5245302cda4661206d8a3661206e99564d206dc93645206d893645206c553605206cca9605202e9545c1205cd425c1202e5a154d206d8a954d206c4a954d202e5a54c5202e1a54c5202e9944c5206dca94c5206d8a94c5206d4a94c5202e9984c1202cd984c120661814c12054d814c120549814c1206e5804c1202e5534c12054d524c120661514c120609514c120605514c1202e5514c1206d5314c120605314c1206c8a54c1206d8954c1206d0954c1206cc954c120661a724d2069d9524d206999524d206c8a960d102e993609106d4a9609106cca9609106e9954c9106e5a54c11054d52481106c951481105495148110659a2604306e9926043068991604306c55364420661a3604206e9936042064da154c202e99854c20655a3608106e995608106c99560810651a3548106e993548106d593548106a1935481068d935481068d92548106e582548106a58254810661825481065d825481065982548106558254810651825481064d8254810 else 0x3be9190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2305002fffec004058000000000000000000000007ffcb004a5200000000000000000000000000c0081c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff619148001ffc827bf200584e0ffbc0c200ffc80600f84dbc8c807710e102c029d632d006e32506181d0177035c0f361415300380572c00037f091a14989ae8940cc114815b81a749f0d3815ae10b841d133c21d08b411015c03900d3c0101e40490113a0be81bc00d8dafb5b696d1da1b3f676cdd99b2f656c9d91b1f636c5d89b0f616c1d81aff5f6bdd79aef5d6b9d71adf5b6b5d69acf596b1d61abf576add59aaf556a9d51a9f536a5d49a8f516a1d41a7f4f69dd39a6f4d699d31a5f4b695d29a4f49691d21a3f4768dd19a2f45689d11a1f43685d09a083d97a2f25e0bb9762ea5d0b99722e25c0b51692d059cb31652c858cb11612c057caf15d2b49652c2574ac9552a2534a49452824f49c9352624b4949252424748c915222434849052023f47c8f51e23b4748e51c23746c8d51a2334648c51822f45c8b51622b4548a51422744c895122234448851021f43c8750e21b4348650c217422c3204103c0023b0f30f30f2cf3031881930cf2a508f350fd7b06fd5b22f99a20f86392ec6b80ecf172ecf306ddc364cdd366c9d172c89b82c2ab02bd8972b6d364b29b04b2d2a4b28972b18b90)
def ZuG (j : Nat) : Nat := 0x6000005c000000000000000080000041000000000000428000000000000000000000000021ff0042000000002c0000080000000000007a03000000001
def ZuB (j : Nat) : Nat := (if j<3 then (if j<1 then 0x13747209b53804dc9bb864ca24aa65151b2272ecb91186588813743e71a21f3ad28f1d6887813743829b11c2ccc0d026e860db262a09ba142cd40a022e85043702425b31112dc081c6a040b3301c5d970e30cb071965438d3281c65ba0a62d9051b6e8201374106da30838d1839765c14c32c0a69940536dd01026e809836a046da80236d1811c6a004e3460225b90038d4802966001632e00b9960062ca803365001ab2600fd748002db3d016d9b22aa6c1215227025d10002e813ffdffdffe7fefff5ff8ffbffdbfebff4ff9ffbffddfeafef7f6ffb5fd8febff4ffa5fbffd7fdffefdf7afb57cffdfddffeff77f7bf7dfaefbf7dbbe7defef5f77fbb7dd7edff6efaffd7be7ff3fb9f7bffdff6ff77f7bf7defeeff6ffaffcffe7fb3fb9fbcfbe7bf3bf9bfcbfe3fefff7febfddfeafef7f6bf75efef7d5ffaff57f6bf75f7adfd5fe7ff3fe9fbc7fe37f17f69573581655c56058d71581715c16058d70581655096058d4158142505602a5415819864530655914c192645306a5814c152605302a5814c1a824530694914c1a224530660914c19524530648914c1a46612068598480a366120661944819864d2065d934819564d2026193481986452064d9148153645202619148093645206a58448195611206a581481986052054d81480a9605206898048131601206a174481985d12065d73481935cd2061d73481985c12064d70481845c1205cd70481715c12055170481535c12054570481425c12050570481a954d2068553481a054d2065153480a954d20695434819550d2061143481a75052066141481955052065141481845052054d41481a94c52069531481a04c52065131480a94c5206a130481a54c12068930481a14c12066130481954c12064530481824c12060530481804c12054d30481524c12054530481314c1202a530480a84c12029530480984c12025530481a32612068498481a824d2069c93481a624d2069493481a124d20660934819524d2025493481a564d10689934419864d1068d9244198649106559244193649106a583440a960d106a582441956091064d82440a96091064d8044131601106a552441935491060952440a9549106a532441a54c91065532440a94c91069530441984c11060130441534c1104c530441a84811069520441a34811066120441954811064d20441854811060d20441804811054d2044152481105452044150481104c120441a8644306a5810c1a26043065d810c19660430649810c191604306859808153644206a581081a3604206618108193604206a553081a854c20685530819854c2064d53081a564c106a192041a5648106a582041a36081066182041976081065982041956081065182041936081064982041a95481068d520419754810651520419354810649520418254810 else (if j<2 then 0xaa4bd48b95e6e5caf522d57a914abd48955e28dc2e946d570a364b851b15c28dc2d946c96ca362b651b55a28d9ad146c5693b42b451b85928d9ac946c5653b42b2ed98594898ac056cd5d3262ae81815642cc2aa1655550b02aa85515544cc2a226555112a2a87d985346a8a9856e1482b6aa47d98523ecaa9266054932a2a47da85118dc281f6a140fb4aa07da84e3ed4269f69534fb50967da54b18dc241f6c91cfaa48c7db3453ed2a29f68d14fb408a7d95453ec9a29f6e9106374887dba4318dd218c6d50cf9748631b5423ed2a11f68508fb40847d534218d9209f68cfcfb407e7d933f3edd1f0c6e8f863707c7cba3e72dc9eb96a4f5cb267b29533d725c9e9f6d4ecfb50767da53b3edc9d056e4e8fb30747cb93a3edd1c8c6e8e46370727da8393edc9b856e0dc2b626e7cb93718da9b0c6c8d9eb026b495335a4989ab76e4d1bb30691d52346e5c9a116d4cdbb306615b3320adc18a76a0c4fb30629da83018da97bb660b9db705a31b82d76da96bb6a0b4fb505aeda52d3ed296bb660b5db2a5aed852d28dd16146e4b0a3745651b92b76c99555548a8a3745215ba2928dc948c6e4a4a370532d8529a4c194d56e4a1cb725155b828aad994556a0a12b505155a328aacc1439660a2ab2650e59328aac1944a54ca2bb744f5db327aed193d764c9ebb064f5cba274ed4133b66099db264c51b5254ed412bb6609692a64b55522518d9121f6c88cfb44467db9220ada912d6e8856b4442bd52203edd0f8c6e87c636a3e7da51f72d10fba69479d3443ce9521e18d98e9f6e87063743831b81c74d88e1f6cc6cfb46367d531b3edc8d056d4695b4632ad53193edd0c0c6e860636a307da5186ea98c1f6e05cfb622e7da8173ed08b9f6e458fb722a7d98154cc08a9f6e850637428ada8146ed409b76844dbb7024ddb21272da88b96cc45cb7020e5b31072d4081f6a040fb6a1e7db30f3ed2879f68c3cfb721c7d950e56d286ab68c356b4a18b5a30c5aa9862f6942d7b4616c9ba0a3edd050c6e829936614e5b20a64d2853268c29917414d1a50968d184b454c25bb741031ba086eda840c6d421bb4a10dda3086ea984396d41dcb4a0ee5a30772a9839f6cc18fb460c7db9050adc02b46a00da34606ddba023edd010c6e809936a04dda8023ed4013768c09cb7002e5a80172d180b96e401cb520095a30072c9804a54c00c1536268a9b004d9d7826cabc13755809b2a906d9d3882ce883b6d4009ba9c0cdbcb076da5813672008b98d085d41c05ce026284fe61b67a0edb3d026c5e81172f208b976045cb7822e9b4336ed861b66c0edb36026d5b0f174ced8b36754cc318b6e58a32a6c02cb95f20daaf50605789364b635b6591eda2c906cd64bb30aa6198542ed3a8186994013749e61a64f04d923022e91011748609b54204d9a1026ccf else 0xc34db2612ad930d36c5869b04c34d8161acdc30566cd82b362c1598160aca9b0564c582b170c165b85fb2d9afd96c97ecb04bf64985f50caac28545614362aca1985650caab286055942a2aca1985350c0a9bc60541e2a498f1534a78c1a4bc61521e2a48ea1534578a822bc4c115e37488f1b34478d1a23c2e911e34a86f1a14378d021bc54905434480f1833f50c19fbc4c0fde3747cf1b83e78d41f3c684f9e3407d59b93dacd99ed66c4f6b3607b59a93dacd19ed6684f6b3407b59933dac989ed64c0f6b1727af1853b50dc9d286e0e9433074f1ba3978dc1cbc6a0e543046ea1813778a91b59548d69b70694db234a6d89a53608d29b02694d8233a6a919d9614c2cb0a5b65ba2cb2dc96596ccb2cb745765b92bb2da95d9694aecb2a5765532ab2dd14a86e8a6cb7252f1b929b2dc14956e0a6cb605365a82950d414d9660a5e3305364ba29b25c94d66e0a2b36650f1522378da8fbc6e871e37038f1a81c78da8c3c69461e3022ef1ba0a78d9853c68c282b616e7d98b77cb2da3e58ed0736366f973b31cd8d943596c0fae75e7da2ab3e51559f2a6a923674e7d98a746a953856d698fb314c7d95a63ed4529f6a290fb4b487da8a33ed2d19f68a8cfb4f447da4a13ed1d09f28e846363407da7a018d8cf8c6e274fb513a7da19d18dacd8c6c66cfb4b3631b99818d9cb8c6e258636b2c7d87953edd4a0c6c650f975287da3933ec9c99f24e4d5b2724ac9392185cc8856ce40fb27207d30900ad9c7856c63c29751c30b98e18d8c62d64e2c637114b5878a18d9c4146c62063631051b88728d8c3bb6621e0aeb0e51b98682c9c2c1612160b27090584849ac241946e608a361052d548228dc40d566202aaa70051b37f9ac23fc15cdfda168fc7da97d185cbe9f2a5f46372f87da97c3e54be1f6a5ec736cf431b17a3ed4bd1f6e9e06370f031b17868cabb8c6ddd4f974ea7dba7418dc3a1f2e9d1a32ae6d1957218dcb89f6a1c1a168e07ca8703e52b81f6e5bc2b72de7da96f3ecc379f2e5bc6172de7ca96f4ed43727695ba9326dc9ca96e4e543727295b8fb50da31b86c3edab60c6d5b0fb50d87da06c3ec2b61f541b0f90ad8ecb96b4e54b5a76a1a9d972d4ed98694ed43427695a1db30d1495368aaa9343b2e5a13950d09ca56876d9b3bb6c59d3974ceecb567a459b3bb661993974cced9865a4a9b2d5549953b42c8ed986428dd31946e58deb30c6f58263a4a9b1d55498ca172c651b2627ac0b1524c58a9372c231b961a4d930d26c5869360c31d5261a45cb0b72e5869152c355ba604add30556cd809b62c155b060aad4305566181cb30c13d536094a9b0552e982a952c154a860aa4c30146e97ca372bf49b35faad92fbb6617e5b2abf5d815fa4a9afbb2e57ca172bf49b95ea4daaf116d57a934abcdd985ea4caaf516057a7)) else (if j<5 then (if j<4 then 0xd65ad969659d965658d961657d95d656d959655d955654d951653d94d652d949651d945650d94164fd93d64ed93964dd93564cd93164bd92d64ad929649d925648d921647d91d646d919645d915644d911643d90d642d909641d905640d90163fd8fd63ed8f963dd8f563cd8f163bd8ed63ad8e9639d8e5638d8e1637d8dd636d8d9635d8d5634d8d1633d8cd632d8c9631d8c5630d8c162fd8bd62ed8b962dd8b562cd8b162bd8ad62ad8a9629d8a5628d8a1627d89d626d899625d895624d891623d88d622d889621d885620d88161fd87d61ed87961dd87561cd87161bd86d61ad869619d865618d861617d85d616d859615d855614d851613d84d612d849611d845610d84160fd83d60ed83960dd83560cd83160bd82d60ad829609d825608d821607d81d606d819605d815604d811603d80d602d809601d805600d8015ffd7fd5fed7f95fdd7f55fcd7f15fbd7ed5fad7e95f9d7e55f8d7e15f7d7dd5f6d7d95f5d7d55f4d7d15f3d7cd5f2d7c95f1d7c55f0d7c15efd7bd5eed7b95edd7b55ecd7b15ebd7ad5ead7a95e9d7a55e8d7a15e7d79d5e6d7995e5d7955e4d7915e3d78d5e2d7895e1d7855e0d7815dfd77d5ded7795ddd7755dcd7715dbd76d5dad7695d9d7655d8d7615d7d75d5d6d7595d5d7555d4d7515d3d74d5d2d7495d1d7455d0d7415cfd73d5ced7395cdd7355ccd7315c7f7081bbe6d49afa6aa1a5567819a2658993764318ba61d98165f197625cc16f25abd66458cd5e9567556954994e3525544c503d3c44de932c4b792a1497922047791a5455d12643bd0b141b90404034fc43e1cf453c28ecd3a58e50384cdcc35e4d3d33d4cab31d4c342fa4baa2d90b252ba8aa32964a1f278c9ac25dc93d24188d4226486720f87ff1f007871d1c6fb1b08690195c61217705a615c452d13e44b311b443f10103b00dec3380bb02b60a1023407f81b7055c118037c0b201cc03e000143056f1142b688aa5ac450ad622e7653987b078c0d73c54ab9e2435cf181ad7890d6bc616b1e30358f150ab78d4d52854aa143654ea152a750dad32854a99e2a54af152a478c3cf3c61679e3073cf1819e78c1ce3c60671e15138f1519b78c1cd3c61665e30732a1ba9878dccc3c66261e32730f0b99850c3cabc4c651430726f15093789849bc6e646c36322a1a99178dcc7156e238ab6b1d65b08e78a8c54264e26130913094189b2cc43596e60acb6105659382b2c2415954dfe7168fca1a97d785cbe956c9f1434ef8a1a27c50d0be3c6a5ecab62f539957778c3babc2e1d2732ae539877278dcb8bc655c5e30ae0f1507078cc37a864dbd4170dea0a86fb2c2b73c6059ec970cd64a866b24c33596e98ecb72c765b563b2d9b1d96c98ecb50c765a563b2d131d96618ecb2ac7658263b254b1d92958ec92ac7658262b2c0b1594c58a9b7 else 0x180081d40d58634b5a67040841c19b03581e04120b211506f04200e00c957b18c985045203482640b149f369029d0a4a2504c70400c2024a4f302014cc5ca0d5197044c18e2170ff085841a115130190e076060439839454a2450bc23403c3137ba81b610305c38cb8c8077d1b70c780c03806603700b3428307839a44a05204260ac137c1dc056022847a09d03e0ff453c4cc02d05d85e0e060770228a3440b0a01e7830078c11801f8b9c4ba20d03a82206805cb0ad82360782c01d686002ac06d0400ed815037c1d305109180700dc0bd415a0e01c685740502bd004092043022511d82b801d0cf02b843811e0bf0be813e2001f685345cc0503500e4068c09016015a819817e0e786f804055e02700f803a0bc0f687f425a06e09f0035f9d7c75e9d7875d9d7475c9d7075b9d6c75a9d687599d647589d607579d5c7569d587559d547549d507539d4c7529d487519d447509d4074f9d3c74e9d3874d9d3474c9d3074b9d2c74a9d287475d1b7465d177423d06f413d02f403cfef3f3cfaf3e3cf6f3d3cf2f3c3ceef3b3ceaf3a3ce6f393ce2f383cdef373cdaf363cd6f353cd2f343ccef333ccaf2f6cbbb2e6cb7b2d6cb3b2c6cafb2b6cabb2a6ca7b296ca3b286c9fb276c9bb266c97b256c93b246c8fb236c8bb226c87b216c83b206c7fb1f6c7bb1e6c77b1d6c73b1c6c6fb192c62b182c5eb172c5ab162c56b152c52b142c4eb132c4ab122c46b112c42b102c3eb0f2c3ab0e2c36b0d2c32b0c2c2eb0b2c2ab0a2c26b092c22b082c1eb072c1ab062c16b052c12b042c0eb032c0ab022c06b012c02b002bfeaff2bfaafe2bf6afd2bf2afc2beeafb2beaafa2be6af92be2af82bdeaf72bdaaf62bd6af52bd2af42bceaf32bcaaf22bc6af12bc2af02bbeaef2bbaaee2bb6aed2bb2aec2baeaeb2baaaea2ba6ae92ba2ae82b9eae72b9aae62b96ae52b92add0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562d50b522d40b4e2d30b4a2d20b462d10b422d00b3e2cf0b3a2ce0b362cd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22bc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2adbab4eacbab0eabbaacea79a9c6a69a986a59a946a49a906a39a8c6a29a886a19a846a09a8069f9a7c69e9a7869d9a7469c9a7069b9a6c69a9a686999a646989a606979a5c6969a586959a546949a506939a4c6929a486919a446909a4068f9a3c68e9a3868d9a3468c9a3068b9a2c68a9a286899a246889a206879a1c6869a186859a0aa7d99dfe7779dbe7679d7e7579d3e7479cfe7379cbe6f49bb26e49b726d49b326c49af26b49ab26a49a726949a3268499f267499b26649972654985a60e96) else (if j<6 then 0x99f821d9fa046c0068900008fcdf90b0602589153f02bb02c8617f96ae0f011c7b104702ad1020a18d6a29ffb4c883c046c0478a0fe1c136f683104a3543c2067c18404e219ffc9901060c2041c4a3f060df84b40800913effa61909c80c200bc50016ffdf823830806f1415fc2b51620536917e6fcfa24c202710005fae490101653835f3039ffa623d10027a64e8100587f7c0001bf97a610096280803ffe046cd27801594688e9800bc12344c025a70035f00baa097bb115e627be14b30baac6501e086f7c9c0c978000809c48bf87db188105a1c00d7fe3d42041588279c33ac4082f10017370d02041688020fe16008094c01ff690ee3200813563fc9c2888105a1c1cfffb96304081244821f37c5010488810958beffe6851900456837fdd6038708100389000000005f053fcca241eff66f38548608f82619e61e9b34d3f468e00a16d14428ae783ca0cd2d09d11cf073140cb30f3444fbf988157c0e7088e78382af81cd10fcf06300a616c8462279f8c02ab44321e128a073f1b3ef01aa1c801bf837e43a9a00006b885fad43c181c54bbeae9adfc18bbae09a8742ffec130946ce11fb0d0251b387c2bf61a049c6813d6aabf2d1200dbb91b3491fd32d517589d5a71fe4cac2f185e4457f2cb5dd6299a113fe8099798819a400f921e6244eb08162b7f8bac85e4ce9257f7733b3414eff17590bc99d279f8f2694e4404ad12cfeaf2d00c2c36f1cae8d240c933f75d86220849afff812050022106a3ee5f330a102ab7fc5a0718020822275f8f1715000420889b87e3c2820a73e1882501103b4817ffff0ae06c501103b66ffec2284941273d3fb3025011483513fd3808604002144c503ffba2003190d3f1c485a4324025eae9c044400213ac58dff1301c4b0922ff7602184e2096224000000003fc3bfb7970009bc00f100de0ef0b440057f0e847175a21f80c20150a6fcda028881042200017fa6db970c2fcdf310000c3c448c81c409a69484f414b8aac4a603a432c6c61d31c986324511e929346509a8162060870607c0d606116c88191348da45d25a909492816c1520a8053c2d401ae1d689b46614b0a5052791a0e8007aa58c30af0e0582ec28c0a2084c80652a14d94b58dacb562db35da16c2461a0671b0e89d84d36a9bf42260b500b04481c7a9396b589609b633d278c282c205d011da4c6020b0d22ea1cc6c84ed1ee80c2e0156d57ca874a760fb13592a9840df0b9051014082ab5720b099615908f886817472b37c0248e58e0f41185794e66ed074e3042ea114e04846f0200ca06380630cb00d83a917884690c951120d8778a366ab2282d943be11b08f019442623d06287ec220aff079880c6d08e12df05e0dd07090b022d01ed07c32d8ca8b740b90a806a0c4522a80d50e614316a8f409c14304740061670a30a8855 else 0x8df904283c4000000abf939119a6629800000000000000000000000000000000000000000000000000000000000000cffd08b59234a000000000000000000000000000000000000000000000000000000000000000000000000000001dbcb1665b880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe4d7eff252488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029fff80d9e40694eb01163000000000001e0f0a08946a87000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057fe4c20470a01d7e3fc33449620026c0031ffabfc400746100822c00000000000000000003b8ff24eac40ab400000000000000000000000000000000000000003bfec8060c202710000013fffebe900c1840028b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005be029164d068632a00000000013ff57fb60290460000f7fc0005393f0060c531a00000000010ff829f9e6940c91e00000affd3830a8b668d160013ffa603601cfa2b4500000055f9008296054aa000000001efffc852172c4b0093c8a5fdcf09c154574e009e17c019806b4f6396bc0371057195306620000023ffd96277022b14071f281c06400675000000047f01bcdb72b010f1a000bf829f1b7930049140000000025ff07be19040c31cf7d48d568e52cbff6a6a23bc650e0033db84bab0022240067e0fd7882c022c4c7edc0c302d9)))
def ZuH (j : Nat) : Nat := (if j<1 then 0x1caa00019150000000000000000000000000000000084ae2cf80b68a0000000000060accd2000100f800000000000000000000241400060be000609e00000000000000000000000000000000000000214a00044940000000000607603580000000000000641200040660000000000615c00000000000000000000123d000041b80010210000000000000061060000000000000000000000000000000000000001680578000000000083f0000000000120260500000000000000000000000000000000000000000000000097022a4a602d000000040b80448000000214000020e40000001841000000000000000001834800001680000000000000000101e000000000018068001b2ea15a0000001056000022e00000000000000000000000008178000000200400000000120eb782f26a2000000000000008388000000000000000000520001a398000150813800000a800040f60000000000000000000000000000000000000000000000000d508034000000000000010c1800000000010250eb8000000000062cc0000000000494000000000000000000000000000000000000000000094fc12200000900000001a3be03c000000000020298330000000000100940018230000000000000000000004162000000000000000000000000000080380004ad80000000000000000000060f2000000180892b40000000000204a00020d80000000000407400280000000000000000000000001038000848000025581660002143009a0a000000003ac8000000000000000000000000000000000032b800000000000000000000085900d00000c0800c00da0000000cd68001846c01c81c800200000000000000000000000000000004f5c00000000000000000000000000000000000000000000000000000000000013181b800103eeebc8238000000000000060ae0000000000000000000ea00000b7019000000048b600000000000000000000000000000000000000000000000000000000000614400041460000000000000000000000000000000207e000000000060700000000000000000000000000000000000104300000000000000000000060bb829331aa56800000000000000000000000000000000003094000000000000000000001843800023c00000000000000000000000000000000000000000040aa00000000000000000000000060438110000000011c0004010000095e00000f800000000000000000000080a80000000000000000085860a20000000000402e000000000000000000000000000101a00008058000baa60ee000000000000000000000822000000000000000000000006c000626200000000000000000000002c8000a46a06284f80008498000000000000000440182400c12288180091c125021a08803120000b00a200 else 0x401f853000084d8000000604c0000000000000000000f0000000000000018268434000000008160060000001840000000000000000000000205400000000000000000000000000000000000000245200060400000056811800131200000050000000094e0000000000000104b603600000000000000000000004c80000004f49847c108000000000000000000008000000000000000000000031204e000000000000000002058000000000041020000000000000084b800000000000000c6e030c1560000000000000000ec0de00028a800000018b080000538001bd40000000000000000000000000000000000000000000000000000000000000000000000213400040e600000000000000000000000000008458000916000000000000000000000000000000fe0000000000000000e00000000000000000000000000000000000000000000000000000224000080c8000000000102c00000000000000000000061100000001998800000000012520000398800000000000000000000000081e800010e84320000000000000000020c000022f800000000000000000000000000000000000000000000000000000000000209c0000000000000000020dc0000000115800083b0000000000110a80000000000000000000000000000000814800000060c6000000000000015ad000000000ce000607c0000000000205c00000000000000000000000000000000000000024d84a015400000000000000000000115020e800041520000001a30206a0000000000409800000000004018000000015100c800040d4000000000000000002f5a832a11584f0020144e2c890dce95042a0800b2e124020a69f004ec040000000000000185ae0920000000000000100300009be800000064380000f4a000000000000008298000854000104ee0e0000000022200f400000000000000000000000000000000000021800000000000006061046000)
def ZuC (j : Nat) : Nat := (if j<3 then (if j<1 then 0xd308fe9547f4cc3da54ded352ee9a1774d03ba651dd2e8ee8a9774cc39a655cd330de9956f4c3b7a5cdbd2a6de9a96b4d2b5a681ad32ad69946b4aa35a2a5ad14ad68956b4d2b3a6859d330ce995674c133a6059d2a6ce95267498b3a6617d32abe9a85b4d2ada6896d330b69a8574d2aba68d5d330ae995574c9aba60d5d352a69a94f4d2a7a68d3d3429e9a04f4caa7a64d3d2a69e8a94f4d125a64d2d2a6969524b498a5a6a51d3468e9a0474c9a3a60d1d34486993434c121a6a4fd34a7e9953f4c29fa694ed330769823b4c09da548ed3506e9a5374cc1ba64cdd2a66e9a22b4a915a68c6d2a6369a8174d08ba6941d3460e953074d180369706b317c187be4b2df258ef82e374963ba4b2d9258eb9a855b598a9acad4d64aa6b5348da8a06d2d0368a86b3143595a1ac950d69276b433b4a39dacc4cd66256b2f2b59595a4c4ad66246b272349891a49c836a636b2b1b5a9886d4c4e6622195310da2846d440d66201b52fc1977dac9bf061df82e8fe59879acc3d964decb08f41737a0b8bd9551ecaa6f65517b2a0bcd6a5d6952e8da571acc38d655c9b08e0da76dacc36d655b9b28dcd846dad4b43695acb40d359469a54b596a19cb4ace5a2672d0b3966196b30ce595672c8b396099cb02ce58066aa9b375499caa2cd53167254b392a19c94ace4986724ab2368d81b42c0da85c6d2ae368576b30bb5955da4aaed6a166b4ab35a259acc2cd6a156b46ab59855acaaad64d56b52a35a94c6d4a6d65536b269b4a94dac9a4d6a511b528b59346ec122d6a4f1b4a7b5953c6d29cd660ecb00755533aa989d96a0d1b506e5a5346d29b968cdcb306b598372ca9b964cd6b266e585372c19b9600dcaa66dd52372a81b94c0d6b505b5a9286d114d648a6b424b5a521ad40ed54c76b5230da319ac98cd6a451b5028da115acc0ad69436b50135a509ad482368c16b2a0b59305ad480368c06b2605d82000d4e0565ef8b09681a9b22b25602a6b0153481a98c054c406a610352f95977debabcf5d1e7ae6f3d717aca13c02a5d4328d80a9698cc33454d9b2a4cd131642d3ae269970352a00a9500d4a602a530152881a93c0549ec64cdb2a46e15134cd11806a4a2b2e51996296c89406a462330301a9152c98a568c44b4a1a9a8094d28406a4123300959704ccb027654143280a593054c90206a402b2e02194012c980a6480fffffeffcffbffaff7ff6feffbffaff7ff7eeffdffdfedfddfbdf7defddfdbfd7fcffbffbbfb7f9ff5cd605c5605c160591605096050560645306053024530661206512064d20645206112060520601205d1205cd205c12054d2050d20505204c5204c1202612024d2064d106491060d10609106011054910541104c9104c110481106583064430604306602064c20644206042054c2065c1064c10648106081054810 else (if j<2 then 0x1d02328b823c5cc4281508341160905ea25246a45614632208c4b43008f817409c09a2d21924f069c18a1f049044a2605882b80aa07a09a2ec0b83b21a059c31c2f039c06c0dc1703e40a05d80841541604340842802c40180c034e2003881e40e037c1d410c2182780ee1bc1ca2980581640ca12a19811a14c08a0b60f405c13c0a60702ac10a0680d024801c02c01c03c04c00ad375a4eb45d683acf759ceb35d663acb7594eb25d643ac7758ceb15d623ac37584eadf55b6ab5d569aacf5596ab1d561aabf5576aadd559aaaf5556aa9d551aa9f5536aa5d549aa8f5516aa1d5316a5ed4b5a95b5296a4ed495a91b50eea19d42ba847506e9c65384a6f94dd29b65364a6b94bbe941522aa35d44ca862508da10b41f683ad06da0cb41767e5cfc39f013de27b84f689ec13d627a84f489e813ce27984f289e413c62750ce999d233a26740ce799ce339a6730ce599ca33926720ce399c6338a6710ce199c233826700cdf99be337a66f0cdd99ba337266e0cdb99a7734ce695cd239a37344e685cd0399f733ce675cce399b7334e665ccc3997732ce655cca39937324e60ecc15981b30165fecbf597db2f965eecbd5979b2cfe5684a2d93692472433c7b08e011aa230cc5bd8ac313c624c444e87f50ec21b3c3148571090e0f0c18a82670322026bffa7f6afda9f91bee67d50f8c9ee4bd7f7a78f40de62bc627814ef15dab3af57516e89dcee397c7258e309c15b7af6ea6db1db2db5e96a96d37da47b4326794cda198332a86478c7158b7b10f6172c1b98132fb35eb8bc2d762ae6f5c56b7616bc2d2d59beb1e560f2baf56baabe1557aa6253eaa6dd4b6291c518ca17d40e27b24e909be136326764c7897f92dea5724a6893fd266249948da90ed1f8a3a746d28c5115f22744468879d0cea14041f482a50269feb3f387ce4f641e633bd076d4ebf9d533a0e7354e511c63386e7014dde1b65361c6a88d389a1f3370659cc8c98d1311460c8bee97962e965bb0b5696582bee56d0ab8952f29ae5224a2513fe27904de898d92e3252e49248f511942288442084e104820183e4c7a20ed71d0438dc6ec8d8e1a5433446378c1316fa2c405670a84148a28004df899b1266239444d086310641fec3e1077a0e7a1c4036786a80cd418882e4059a0aa4143c2660491089c106c1e9038e06a60c74173829304ba08240e7019b029804400678094007800034d4e1a6970d3097e942bf4c3d9a5cebd351569a5ab4d155a662ad32b56992ab45455a296ad145569a9a74d053a64a9d2a54e8a9a744953a6927d3473e9a19f451cfa6626d3512e9a7974d2cba6865d3312e997974cacba61e5d1512e8a59744c4ba6a24d34726998934c9c9a54e4d3311e9878f4d4c5a68e2d341169988b4c9c5a54e2d127169a2874d0c3a60a1d2630e998834cc3fa64df else 0x27f317c0c4100a442dfdd0d2280dffe2d584088135eea4016470197f03001883e0a6f524fffd90cf1020080a279f64531004b43eff3ea88241239fce441004b4381fef4880021698dffbb4208820080a249ffab1104012d0f3fc4820a24817ffd21801004fc45f99988227038005ed9d96b29c1eab0e002db6650e280007be0e717b2cf593518b440cf5932e141eab0e000e36650e2b3f9dbe68466caa3567f3b7cd08cd9456a260d10536fcd30e0d1053eece77212279e0b5bbac5431bff5a3f700656986241ffe1c220195a3a22bf1f1c81aab8b42c42c7b42eac92b10b1ed0bab2493f07bff76804a16e3a452c42c7b42eac926ff1fffc04a067034ad159f0050b705619a442f4744983a4bdff48802418e01a45a9133ef1a3217404a03aff302b8639553b4332d85a150869b7fffc0ce6940c301a3a8b133ae7a3217044a87027043823842cc0f16d17c16fc20a201768b04f04ac14517433cacfc8606810b33a181c7c1554b348c5420d845b0a42ef2872644a446c4a948647242147d4a813eaef0b28c488c49c47b1370ffa8513686daeb90b22e25a28508c06d07fc7b218c1a0adab1a96aab65a66b6850b917717f68964667e62963d61946011c6d367369715717941a11fad621b1671662c344d16533820330a6bc160a4f17e33b0cb30169333917a1784201718f520b2af17d8828fa3320df3314c217b0de18011616e2514526ae03b6a26f86d210d20a2d32900a000da7311446111b87510690590686504808a00852885455856bc48c5114844284c182c2b4b715dc05c0e93485b80087b82126b8042eba9d08d69dc8d16911311272d27e62e04e1091470200111642d51532fd4d045c10c8b316344843b4404658cb6202fc8a4c7247c4624310c644bc6c2452228aa41f8944686180c8a9511e46e8801202da61b0e81212812c03020e111911811daaf2a1aa1abc2360b041b0cd64a2fb0c9a1b81a82c4f44f30e941d8091174f18400400650542a283f11143f0e244c0dd110c15c47c63c62c7d22d0b8a7aa6b0e3aae01b10f4806c31000800c40918c10ca8514948a3c1e42f82f46d0b70a7a88c5f45f46343ac5b2962ab2012952b181d84d0ce60243c4352882d78660b4a930e703040760b8184d149f86e83c49e0278480e502b0b5441c220790e405506a267a670b6a4a06606e25324a4660188ac0c7075081841a22c1f0a5400209a8909aa7e2c50822ad4a00ba22540da188610a6c3a0bb23d060a8709b22600700f01a09081087f08e427c2342241c20661a84ea3244ec0701600c00500e830c1107605607120209923282262663604d625074098a1a297061423c64c41842417077a0f084860a0206f40f078847212a33a5a62d03c035273052070451c4cc3fa5083541805720f092207a36a46229250a53633612a3da030098280)) else (if j<4 then 0x7219fe1f007f080bb477f7fde5f082840286acbd5dce06080e38068a9006ff8ec55d8e204021aa81efe4f03bea90c0cd1e4049c685f80139fd76148a7a7fff240b56da0601f752017238dfd5ff86e9594189335c80bc8e43fc1ab202c9804071a9ead39ed40d59e2f47c49415555401cea5193f01ac183187dff14f3f1208092b7be9789ea9044e96efe1f0d210420080a2b7fc53cfc482024abff7ef01110155f9fe6022022adff500104a0937e660444a527fff30111294abfe3f6b788100405129ffff56bcf410103356feff3ea090440954f87bffa935220802108b47fdffd328c88820089e2c001ee87f43080085a8dec79627c482a24c164fee37c4384010b4507ffeff3100440442d4f71bcaf3069881020022aabf51fd20f30200822248fd6dbea084040045153efff37fbfe7510410054317afe9e847ffc10941040115c617ffefc7483a2202026bc7ffffe410a046882100405180f7ecf378048fba414310802248ff7fff1f1ee43848b384011446821f829e087ae9fb024041220084991dff50010446927fe7ef01111955f99811099497ffa364400010109b61fffcc0444653bfea00208152771f15d4004110265f9981112949fffcc0444a535ffb2742000202526b4bffbc134904004004475487ff292b8208008008e6a814f07800057fc42000020088e3ef8ff9c4446525fffff42364601010bb6025e2f0005fe4a00000802378e00affff3a100010111b673a3c13cd4c370633115deb0f5805b76e686d4025fc8b72f56e49aa1deafeb30e01465b66522309ffb43533e404641b2117e7f0a0449742b0caa15f97b435738a06b3c4c3f97a3f550879f0520d608ccfe7e6f346264ad277382cafdd484832427aa77eef02bfc9dc6410c6e2dc67054414dbb9dc83893391e8905567e695087245d4d45df99d401de8fa8749bb59cee42c613fa93ad1f209128b11404dff010629a369dde8f93f88806568622660858f617754963e4d64b5d27aa68dea5dff2d5fc7f012819c0d43460f10b1f449b02483fe0671172180d20454bff35e2570dd3b41314affff1f03058d2b4c0685a3002ffe7eff12ada1da688a01116fcdf9099c6d458a5bd8f7d6292e9a6000000000037e6fc7cd93cb508e37bb4626830e7f08d678b33e17a1ce6948a637e4f050dc70030c1aa759011a26c8d27afcbd020113e9266b6ffaf00f6c32f66afd20ca005b800009d0dee164e4c901ea89fe6fa7a84184001c4811fe36d9e51b89009016b1baffe546200af20212240aff5f013a6036d2e32024a37dfc0e8093652d81900e518015ebfe014b403b43da001b7eb8018fe14c42e342901946857ff847ff0f000cc00b0000e877f6c20026ee0023ffc44007bcc5e835520328f0be078358f2008a9f9f003f4e3671001889b7ece800904007100ff2cce0620802489 else (if j<5 then 0xe20022f3725ec44a491013ff8000020df1000ae2013e6d025ec44e59500006ffe00005aa749ad2c1e1495ce0858006db409c4e00000000000016ffc0001be28725d2f07a5c0aeb42519c000000000cffe9c10821e9a6a002ad9cae43c426539bdbe77b330a506c67aa42aa0000000008fffeead9ed349b273335010729cffa33ca2e6212ca07cc519cffa73c1c86212ca46cc7198ffffc5f0fb218842098c9acf51d27ff8189810c10140136aa00000b7d5fb29d102264fe00000017e62950c2a4000025f77eca744089dbf4f499e7314a9e54025f669c3fa8c4a74248a034fcbf36fb94308a5484ab000024fe47c2a90e9951060805157d9e241f0a5a3594760e00135937f97b380a534304024aab1fca4dccb24221840594628df013fcb2e529015338808c8f000000015ff27d5f67e836971013120afabdb420d64ce2026a2dcfa0ccafbd880274fd849b39ff1daa01d5ac936efc563b5404bb59adb6578a0000718024fb44580019c687e9fa452105b8c804de270807964414fffe53766eecef60e100711ba7fe909d46191012d4161fc553d9180046a6fc2bc7230173449ff0675d992274d0f9199be9e008340c4202523a5ffba91488c9c9a29a8a2d0f014fe8e7183334e0fffe68fc550aded0120120316381fcf1db20852d2d81901a51c000000c7fad825319100804c56957ce7f00a5a01da1ef2002380006ffcdb100c80328906bf0f164b89ef744280a88d0fd3a7ff00122440596b57f8b92782b95f8420ce2027a3d9ff0ffc410000c800280000781ef641000acb33fd5fc7c35654b0354b31462401248e3ff7370e551c6c189009c68008ffc6bedeb103120009013ee090008ca2be0b6001bd802837712a4004478000b7fff8035053055f8d500b71e003bff1e4c78f0201320012005196cdb3812acc0016fe087bf2eec13f1e6403cc771e4f38d02c647c02bd483dfc1e00640d5c582015e331fc80fffa45b3b590582025e340017c1cdea8b67707080658d03ae376c62ba11115c4019eb3adfd376c934e0bb7d80b36ed7f07dd77d00ab36bea2100d28e05bffc001228ecddd9c0e49201d1214f039a593189f3680414602da3a7a59333e6954800a4683de0fa1936dcfe20009179fa53a36be41600d9adeffd6f22e9c2007aa0000029fc1af03be4f30b2cd05d4780065d085f690cc98007aa97ffcc2ceca818e01a450bf0b3b2a8238069131ffffccefcd58327022b6774c74dd8327023b5cbff91aa80c012080378b87ff77f1120181812080038d2ffbf8cadd709c068d55fdffead81832703cb5e3fdbc12ffdf6e954241006d1b9763e34be80b8030e00eaac02ff87901e00001ff7088401247175cb8e0a0c19d0806edce07fff571047180c720809d8e67ffa044aa08e0324487e5f28640018f82a5ac14f03b013dfd43c954241000 else 0x61ffafe309544aa400000000000000000000000000000000000000000003ba27dcbf2c2100ecd4000000000000006fff79d6f98b308010458000000000dfffc9278bff8248110248018d0500699300000000000047f18006f655b6d759388e07d483aef17f42580a3c86041d200823c1e0e02a76ec09254829233dffffb7aaca4b0328e0d39c42001e411ffffc50979cea0c08e1ccc4202d643de2843078e0a644021196406f9093b6c96570590e00000000000000005ffe0355a7e307eab1f1a1004200134a001bffedab106a0068800000000000000000000000000effff3e39c0fcee1378089150112e400000000000000000000000000000000000000000000000000000000000023fff8386267fe8f101204a0105c80000000000000000000000000000000000000000001bffb75fe32842460c00004010912200000000000000000000000000001dffc5efed5880efde6f800a5c98000147fcc0c2040c696a2e8a3ae013ff814007a582d35a583c217b36001c69040d30000010f880c)))
def ZuI (j : Nat) : Nat := (if j<2 then (if j<1 then 0x4cc2da88830172831e002d02b281d3822485b0ad35c11a443bc1bfc2fa80de2ec2c2c98298826ceabb815c024ccc4e88e80d2582b9083602635225c116851d01b41c4d0577c05ec2a199d0014381e95c4fddfa8176a608831c82f8057841ff805a0122429d08f00160c2c0400bc4e390f742ef8016c1860729c19dc01ac0ce801800a0c266810c8333914e99fac03e42b61da642e1c86a992e402ec11fd1af413ec2c6c86f00f4031f412f429300000000821d001c826f0000d9e881ac10ee8d94c934a9030000000000008076000042c39e690000c09842614180d1ff0000000049940000ae81df0601e600004232000081a9c2010950821300ae424e919741bc1170000081ad902bc274c30142f409f00000c147020e2532813a0000010e91a48316000059dd403b81a1c1dd40f01804d1f0ae9592160d93c107018a81c8009dc03100004abb0090504ec50b4008c59b9db9812e0b25086c1a1a00051a5d5048000000ebc17321e8850140ed9f2b8525c0d1c899904a4d0981a6806841460000c26742f240d400008086051511710841915300000000c1a59c3300000325000000110000c2dfea0caaea66c142f642530000000042ee84fc893b00b3408ec1330000c896428801528ebbd0ea000000006e1300005172cd372226401400001038494825f800000000492504e1000042e0000000004538461b0300c0f71918031500b601de02cd52e4414e5f0f00c341054132c1b2d0605cd784d3c280d9300230803801c91e4a00000000015400c8000002dba305921f017f0a00405282d5d0500000ae8c9100c11182e2000002fd0037c2fe480dc135000000d808fd130b0000c81ecde3c007d02d826800008089804f00004637427d00a7c318c16781af000000000000c0e0019a863a42dec0bbc144c24f405b00004907526d52c3823c2e0609002302010a881c054a2502014110031026012e0b453e277704033e0011803e0700020910004f1c273a16170f6b0100090104001d1b0b0c122305130020012e1b0812000a1001035c4d0d070e0013043b032e1e200739100200000800051a3147000e0b2501000101020105000803112300100a02052202100217241a0f00090918000102004600001808186a056e353a250c1522074300030014031412190200280005101708000f080220001e43090a1e0e1a090a0f1006013f0601000b10390e3f00091e06190102061303002307000507002a0f09000b03010a1d0b0d60090004090520300e1e170c670409030b141707030b01261c000d2a061103310507020504101a0d0f040300380b010d02061318130103040505050e18050300170a00190806130d0829041a4e01010009063e0219220038001e0b03002d010515022001010500010400240302110500010c000702021d13000a051503021606 else 0x2cc126000002144071016c400ec00681484271102c125f828a82e68e054206c01580e3a250c312c27a8211088c00000000d83ac191dd0292ca4187e6c69985c32cc292972599389ef19c5c61e2000080f8c2a9846642eb0000a8fb023610f4486e827fc222000081f7d1bc1e7f8681ca020000c2c1427840b881c69980818b85ac41b3c1fb0f311e494219010d91914083810411b18294d042000000001839822100f5032640652d3c55041f26404a0de49223d98742ca000000c60000000092604ac20000a9441da76e4d00009986126c88975e6d000080e8000081ee00000000000000009efcc2814209480c411900006437426bef30000000000000c2d482570000000010f5d220000024ec1e7b42cba1e581cf0000c171c1f16e940000c192c25c8225c18d00000000c269584c0054830b000001490000830449b0c2834d284072405602d96d45e1d92d4d002741258323d5050073418f01c3c311c1fe80e202628168e10ba662000082e55a8140ee0000c03dca0102318d3bc1b8dd8dd2c200e982169ecb923901d622c28151000042aa4075294c02f0c60a0000c19f01f90725c2d682aec0db9f0e82b8c25b01c7813dd30f41e50000c1ed91a9c02a0000091395b08123c6094a9f0000000000000010000010cdc1cc00008cfc000005ae113b5928c0ecc1415ac2815390f626f300da48fc919d0000000080cc018907050000016f10c0ed339e7dc20a000000000000920901c00000000009270000429bca26401385c081ca50c700000000000082b700000000404100000000000051eb00002ac282ac0303000082720000c0340000c23400008ae3c04702730242000000d38917011852c8acf39ec6dec98170523a51b4030640fc83070000c1b041900000000042d7c85f0000429c998800000000000080b0424b0000024dda7a00000000809fc0ddc30800004a9c4202031452c481f0028b80b7e2a00000c0794208006cd16e9b05c1360000809201d5000029455e62e6c200006d2f41b6531712810000dd7b0000df1200001db0402200008d1c1ec8c10f1f08419c80e4000080590000009a40330000000000005ef60000814fdd7a813f82ea832702f30a855ef00000954bc30dc4e2407e828541a351a882e48036c06100000000000002ecc1280000e669c17b9da10000c09b021fc91bc032c1888243083c030c02a300008195416ad2c5c1fcd6a0a665032e49100000401f6dfa099201da00002f2e410900000000c2569d1a422d82b1c12d41210000021b00004181c30e00004094491a0137c1abc082d22251a00a4a0254c0b4027b021744d640f6c91ce85000b24d92dda98028c060c302d0bec28caebbc11d624a82a02d34008b00000320029e81650159c15f42a81b27c2b4c1d7844b41124062eaa5c24783175c35018c28ed6affc1) else (if j<3 then 0x40d2024985a1e2a148ea000081010023000041d8000001ce010000000000c3210000a6810000431d000082be020f5063a470000051991e08c26e0a6a40f342a681e340b5005f0265dcff41a7454b41e4c25f02288070881002ed4296c8148e48010643316d9bc14b4332889080fa80660134411c0244c8ecc27c44e002e7de7e80f282b3da7958cec83bc00a4cf7c0b152bb415bdacc00000000c087d97f803a11ae000000000000000059e2000066f0c2dd000011f9000002d80045000000fd80dfc01d80e700009ec2dc315d22d4fbe9b5c1b7000080cb99e50000014a0000088542904919d9dc02ff40bf0237022680968003ddc681db01a400000124403f0000402540bc0329400900000000018380350000c0c180fb00000000000010c80000c17e0000644fc0c081e8992fc06d00008019c1ef000081a201970000c0cd4812d50681df81bd513c829a817901b5401b486d00001d1800009d1c8115008000000000c83700000dfa822e82c7d19bd1a501c200005315000086e581f2819e000049b5e95100004309000c00005eca00000000c5c780cae94d11760000812a80a5820b832b8002c2230000c026c92919d81e6300e61d7cc1f8c8792117008101ecc88942339114ed2d01a80461c21e423e8064c20500001dcc8313402f000042c512f089440088800d0000a902022bc21cdae5821000004284000099a102158299000000000000000000e10000000081aa00000000000040f9cd3c00000030c2f5cd8bc039416b00002e911afe009e190b5de300914e81017c82c242cf00008c3b02480097c451521d431a82708204116bc16411be8220422c804349909ef95236c1eb828704e4425980c545ca0000422ac00f1e6500000000c255ddf8451f84679d88ca81464f807a02cc853702dc5681c32ac2f11dc300ea0000402b00000000000041a000005f0700001231423d91b3e1dd80c4420c000082290000e138c1829196c2ce4663c2bc000001c400006e8dd319d2265036c218030f8aa68108c1408156d3098142a66dd2bf01e2c0a882b58166c1174150c1ae1d51c139051b1dfe424a457902951d1b00000000413180d980d749e400f1828fc5c2c10a4103893cc94a815e4085521e01d98d29806f00004816432d80c745ccc8844069c264c10202bb41d0104dc238000002fb1ec1c90848e90000031b026d990c808a425a614500004638c68300460000c1750000019900008162e18600004004487c000042910000000040530c02c1f6e6cb40a90d8f11b90000c80ac5099f11472a817dc07712c60260c02980b940930057c80f4a4bc11e01fa5989c5864938e663c80b4130c15a422f00cfc08c0000c03cc196518cc04c827e40abc02442768a5596c2c2770000029f1aa046c240bdc12700000000420351c002a240fe8811c08f89 else 0x11a100afc23a000082ab9a1be29f0169621b4145428602d200000000821200a4d856c0ba12630000000000be426ac32f0000917481f401cb42af806a00000000000042fc0000e03901dc22e212e902ad40dc561b105f86e0ee930000c1140000881d025d41e181fd01bb81f3000040ad59d7829740c2d2f110ec46cd8ec205f30000c528000000001efa65fa428901130000020d516c91ba5e0700004310d1f8d8540809523880d00000c15d00000000e666ee909cd240a60048000059834178006302a48058c04dc2c8d18311925224000048399325ddc94319c1579da3de814044018ed30ac049023b407dde7c0000992742d0c30a0000c06bd2bd417a92c00000425e00000000408d81850000823f00005cd48240e990c07fc1b9c0ac81e0df1005fa000040d541c541bed97e00008817c2ba891d0406009c8818e1e6819840504055880e80a3819ba2814227016d0000aa2611fa00004279aa4a416e0000000024ff000080e5c252000090f38db045ad624906cc41d20158000002c4419300008095000010370000001ec20029b685c8d19e823542bfa1845262493a00000000c12bed4cdef28250c2821d25404b5ef348f7025841775ec7051742a7451e813b813802468239c11b1233e04c10f082a5092b866ee51a6e8f10495cdbc1b1d22dc021d98450f225a141948275c2f982e900748110c12990c30000c06702e381554120c099000049490084c91f421a41e7c12cdde940c94d8d82e84078d84d402083229e66024151c541741e2ec0ff82d1d9d5006e00002a810012818483300000926aed2ec52095ad014de6fcd2fc4c610f25807c00a29230000081c182b00a6340d681cd40a141f541ba0000d1ab0000c20700001234eec7c245000002d30000ae8800008328d86082f71eef000000000000c07b00000000c28d000042bdc1d1864800005da8000080aac02c9cdcdee4800101d4c10bc1ea000000004947805c000086a012f7000081612dbe83248042887300ef80400000428e904f192c004e005dc1634251000000008702c0515c34413c455a8305001700))
def ZuD (j : Nat) : Nat := (if j<1 then 0x99ff8fe7880a0e00018eec0cbbe6603945800007e0761dd4180851602fac46c0a44f8e2d41b00a483df013c0af006010662c3e1f5a5adc83308350ff9f0b1f8d1000804bea0ce0e7e965500318662b3feffe92f8480004004badc007bff2b4900108c51165e1ffe7881054a5d7ff1cdf102095cb80000392ada6fa910000bc82e3a85d04e2400f00b0c2007190c4805fa49a23320605120073c12905ef828ac56787c001b824009295d200ea1b900000000000bfc00001bfcf3d7bc035b9ffffe000000005e1557d71a0060baa96800000000005fe00000dfe79ebde01ad80000000000007dbfb7fc09be1bbc06a3301887aff5a413aa80182181f5bc0004e06d602c2e6fc00d5377af1541e980d4400beb11b02913e38b506c02933e38b11b1a91045f04f5b40b10536d91f0ca7cc0aa980a51b1be194f981553014a36027f3506f64d602936cefff8f4800562012a358f5fe00e16604a8960001f002f846b5b40b104d538817c33f00fde620122b6463d241140243691ff98016604a894bfc01c2cc09512a54cbf97d2a0a094017036840b2314912c998a52d0588978ff26a4b8b987052c80555a9503aac41505255cb5841a874c884d01aaf5423d549abc16101c86a0a5a6a8939a8b410a5c608ca0ea2785a8ac20b17211c5186110a20c2881810817c1685e05d0f93f1fc0981982e0241e81680b9f33de610f29dc3e8078180384c09312425449c92acf9391ec6348d05886104c1a580a21190610202cc6c06c1522703e01f0be218390be0fa1885f8a80962345a01a14613020c4c07e144550d41a02523e08e8c696a05c0610103c1b890015016070d98fb21a392bd50a99d4e85b0620e8318000081ec10a894fc940370230c10621f82203c11e3241c105026360b24f49ae312460cc1381407f83d05e2fa2282a2303442282294d0d4080ca22a2da3640507c1e22949f86e0ec0d01108436a2e40e1341aa4540c82c0683b05704e18a0fc409291e801874866080300901500a81142489919a2d81410013a1444b00e0100e02d00602005019002b9f587a75d14a771327944c7ee36f15b88843861230628143f19eecf1974f3891b34d6167d31dd858bf65d2ad4d64aaf155029654069b84ada42d19688c425a010f7a7773969b04c845bc29e937094444c1f90ed470e3531918b5c5182410fb06a42ce10105881d80760009663cb2fe584f2b9f95c7cae1e542f2a0f9646cb036491b2cc496524b27259192c2496064b01257492b9c95c24aa7254392a0c94c64a6124989249c964dcb24e58372c139601caa4e5507299394c1ca40e58152c09954ccb0425520acbf6597b2c9d963eea0e56622b29217090984564dab24e1206ac8a5660ab2655912ac9856480b2c819704ca0364c23243ffffefdfefeffdfbbef7bedfd7f581404c1204403008010 else 0x25fe2067259934a6b1ccffb7406a1e14a4f13bfffff9ff85c09f851030b02684d0060b0726ba37ffffc2fbf9c6df106850640b0b901f81125d004fffffa81fe04c2cc7da27100b9c86f8d6574003ff64f4a800270048252a141005d05e4f43ffffc4ffc2e04fe0a2068989a1340182c13f2f8077fc0be9f0048400a0926e000600822cf2003b043cd207231120f800066015b0d520722f1a00000001bf819fcca2425f35fe1423eef53135440180e0b7a8c5e16bfc03472f5cb20b170cda37fcfc21a1242880301c00f54b7cbb71810137a401a8b4ffffff60cd040010000436a7fff1f6d01241398a00018218014750ffff800006401a50028151b60039d0002bfc33e70094ab048205212602008d79c7c02c541810438037ffffe4411300060860c27000efff6f4e041204c02680006008018eeeff1c8da185c800822)
def ZuJ (j : Nat) : Nat := (if j<2 then (if j<1 then 0x8ae000001c40000000516800000000000000000000000000d8ea0001041a14ad94ba2f9110b467000184ac0000000d05054a506a80fa000180fc000204c49b7085c00042fcc1fe00030ae80000000000000054eba9e1317f16b00000001833e0a08000012a0000000000000000000000771488e40000000207400000000000000002fc047800070e6000001380000000000182480000000000000000000a5e00011186b3380000000000000000000000000000000000000000307e80000001525c0000000000000000000000000184b400000008150000000009538c4e232000000000000d55126300000000000000000000000000344600000000857d039c2b444c4000000060e4000131bc05680000000028000000008163817000000000000000103d40140001022400061240000000000000001166000000000000000000000000000000000070a800081fc232757300000000000000000002dfe000145e0000000000000006099c0cda2c874b80000001335400000000000000000000000000000095730720000000000000000001b4bf1868000e9f59a520148000401c04040000000000182060108000511c000000000000000810000000000000000000100001a660000000000000000001498c046d26600000006f70000000000000000109c000242d4f40c80400030a00000ca3600000000000985f051c0000000000000000000000000104c80000000000103300000000c1105be8000692a00000000000000082ac0000000408a00000000000000000000000000494e000000000000000000000000000000000000000000000000104f00000000000082d4000000000010600000606c000000020218148000005f000000000000b28400000000000000000000000000000004b00000000a19c00060d2000000000b00000000015f00000000c1be000000000000000000000000000001830800060390000000005a010ac15e000000000006e0e0000000011984da808c04d00000001005400000000000000000000000000000000000004091844c45680000001056c0000000000002c120d914b01900419a3d00008006025f21f4f714d68000005480000000000328880000000000000026310000bcdc00000000000bbb80000409124f8b0a00900000000000027c410000019c0d0550000000012c713a8959000034c745d80000000000000000000000392815b80000000000107a207708da908400040900460000303b00000000bd100000000d1a112a800000002d2880f4000600d34004122460351060000227330202013212740045132070000005072a301113130020210b81043010000000c000016100010064028024520010120056011014402310003150401010300103010012031250001300100100201006000220001001100210 else 0x200030ac0000516a5be3699000000008a3c00000000000000002a000000000002022c2e30000048400060a1000024a007c00009174000000000009d48000000000000000000000000000000000000008990000000000000000000b9744310000c2c2000000000004d48000233766b2000094140840000d9d1896646880f60000000341480005eb000024798000000000030a8e0dd0000000006c80000001807b419600c000083012a9e09b000000000000000ad3000000000000000000000000b0a0000256c00000000000000000060cd00000000000000000000000000208542d000016b80000c8dc000000000d60001102c000217b000082939a00000000084dc00000000000b3fc000000000000000000202f822a29d70b50000000000023498000022c000365e40056ae20d2c0000000000000024330000000003a66b68000000084da22d800002ed004c0000000c296000000000ea000000000000000106c09ac0000000e1e4000000041140000a26000001460000000000060172682000000000000000000300fc07d00000000000217ac8de00200000939407c000000060500001821d03cc11f000184cc000000002a000000000000009382ac00000000000000130d00005864000000e0000000120b805fe92300000001b15c14d00ac000000000004254000000016ec0001b1b800028970000000000051350000000102ee6f8c9e60000000609800000000000493a00012ce40006267000000030aba1281ca80000007800000000000000000000000002495800000000000000000000000000000000000000000000000000000000000685b00000000000000000000000000415381f7225400000000001bab80006b560001017800000000000829c0000000c29200000000000000139b000000000001db85002000042c6000000040a20000000119300000001cd10000245dd2ae000207be03000012b08759800000000000171000000012c340000000c25e840a0988e7b81580515a8c0000594483c800020e0000110fc00061674246000000000bd000000000000000594680a800000000000000000002b6000000000000000000081840000000004800010a78000000184b80000000d26f88b4000000000000000000000048c44baa086e03400000000062000000000001235000000000002697000000000000000000000000000000000040e4000000028bf000139aa00304790221a51055e0000407501fc0002084821c00000000000a8f0a88518500000000000001b000002980000000000000000000897e13000010412048cf420000d1b00006107822e45fa02b800000018298000610f0000000000000000000000218180000000011c06e2d350000000046580000001142eb397671000000000000000aa2925a000000000000000344e) else (if j<3 then 0x41d00000184b66e000000000000000000000000000000829c839e169800042da000201ac0b6000182380000000c61732da469349800000000000007c81ae00000000000ddda00000000000000000020b880000000000000000000000000000000000000000000020c700000000000000092c684600000000c1dc02c900500000000a04400000000000000323c0000000000000000000000000000004c700001ad2c0004152416e80880000000add200020380000c05c00000000000ccca000000000db00000000000000000000000000296c0000000102f800000000001221e0ce000181a811944fe00018129a89a064de30000041d00000000000000000650000000000000008a0e0000000000080d200036390000000000000948000000182e00000000000000020000000000180760ba0000000000000002ac1017c81f843f800000000000000286881f8000000060820000000000000180000000103a800000000001068e0bba1ca05700000000ae2a000000000000000000000022f800000000000211a00000000000000008003a8000000000000000000060d381dea5240000000000000000000000000000020b340372a8e0000000703c000000000000000d93d8183049b2b300000001052800088bc000229c800000013bca0310000614a000123649240001022c00000005d200327abf8000028400000004cfe20ea00030bbe89400000000000667400000002779804180b6000000020f1d28301e0a94095d5277c1df09a80b3000000000000000000083980000000000000000002f0b88ca000201d80000000000376be22ed10c000001980000001806d02a800000000000000294581c70278000000044d8000323180008948000000000000001d2990aa0051c0b00000000000098a9cbcc000000000000003634f6b90000814c0006962000183b220400000000000244deeaf00010059089530f86040000000000000000000031e03841b40000000000002bc000000000002ae00000000000000003ac20c0a08f00010564000600b0000000000000008146000000060eb82d680ad0b60000d5520000000606b000000010aaa0d000000003046000000000000000000000000000000044000000003a5ce493013a13d485ac06700000000000000094ce0000000000000000000000000000000000000000000000001972a746000002e6b1900000000a3da0008000020a000104300000000000160e004b4238048802200000000000374aa26eddf200000000000444e00024b58000000000020618000000005cc494c16e000000024b4f45d00000002649202540a424f0000029f81b050a59708000004f04e2418800000000000000000000000000000295480da00000002960c0b2000228528330000db7c000000042c800000000000827 else 0x544a7a0967a00d00000000000048b4049aa4dc81b266f832a755e4975a6891a603de0f30000000205d0000007800000006b0984ca937c08d8000c23a000172dc12082c485110bc0000d135004146a00009caa0ad712e422f02180000000000000b400000006020000090400000000000000018bf800000000001b8900000000000270c800000000000000000000008064000000000000003037a17f009a000202100000001842c00010e40000c96c0000032c11a000109d250600000000000000000000000b1f42724ae000020848000000083d449700000a5013ec1a6f63a000000000000080000103b40000000c27a0000000000000009029a3b80000000000309a000000000000000000000005ca4000000000000000000016f455284440000000000000033830000000005c80000000000000034268000c94c0001777ad7c000000010960672815c5bac00000009a96000000020c10000a07a443d02e0001a501018895100004a54770000042fa00030780000413800000000000000185c00000000418a0000000413f000000000000000024fa24c07c8000119b23c7274a8a98528000000000000000000067c402880dc00b40000000c85785e4000166f82cb849400000001dc48cb400000000000000104a440c0001c38f200a56d48e2809811e00000000a2e40000000000000000000ee4000085680004f6d000132500000000000000000000000409e000000000000000000000000000000827f003800041c5a33c0000000000000000000000000000000000000000180b000000002ada000000000000000000000040094ae391f800036770001a0c00000000c1ca00020658223000000000000000000105a4000000000012b4c00008f700000000000000041a92d3400005180000000106300004034000000000000000000079400000001838769c00000000000000000000000000209f6cbb000000010ba800009c000000000000d1e0000339300000000253f49e8103c28600014468000000083780000000000000000000000c022000105e0d80000184ec00))
def ZuE (j : Nat) : Nat := 0x7ffffe000017e010944e400000002fff97991d6494e800fff0000bf2a0c06404fe000b950499fc055100a38000fe26242400007ff2f09a1617fe00190c05617fe060020549117a2510a3384a4e9fc361524e0fa3e03e2f90c3917e5f1502d8f646c410d9f27b984791dc0c01203002050200401a01860138764508e288c86a0501f82c0f0261d0c613066170243d028168d6760620381e0d03a02096070421100a200a83101600004060900a823d1bacb1eeca4d18860005916050130481100c020043ff
def ZuK (j : Nat) : Nat := 0xd07800000000010b16ef035b8d00060d400000041c0000000000000000000100a00000000000000000000000000000247b7329af1074e2801b30d892800173a92a812c0b102511f000a24021bab101200006500000000001016000000002201800088e6a840008155ca08d000081c24b80024100000000002054000447800000000000000000000000000000000c3d456800107600000060f4000000000000204200048c2287204000000289800010be8a000000000000000000000000000e38000000000000300c2320000000000000c02800000000000060d20238200000000000000013800000000000480000000000000000000a1c0cb9688000000c19c4741080008018000a3000040200000000020000248000a2900060fc00000001f0000000000000401c000000e990cac65c000811808800000040c80000019054908003750000000000145c00000020c00000000000000536000516e8a80000000098003078000c8d000203a0000000002456000000000063b836000000000000000000000000000001058000000914000000000000000000000000000000000000c5cc274000bb9000000000000000020c5114000000000000000000000000000004830000000000000000000002600000000000005080ce400000069160ca1363b7017000102f039000645346000001480006151a0650000016e1010000001050000000206c0000144076040b30037c07c0022620000000000001bab88000af05a0000002cdc000000000000000012200042a315e000105800208308e0000000000000000406000000002060e80000000004c380000006c860bc24800008d8003534000000103503d10cc0b000000000091a80000000000000000000000000000000000000062e000088d000244800181f00c600880508000114000100510020081c0084222500080020
def ZuF (j : Nat) : Nat := 0x403103b437ff
def ZuL (j : Nat) : Nat := 0x3040022200000000000004200000000000006700107c08000000000000000000020500000000008cc000000000000951970000095f06002310000000000000005c40000000000000d000000000000000145000000000084c00000000000061c0000000000000000000000000000000000127000000000000000001140000000000000000037300000000004dc0000000894000000000000000000000000000000000000000090000000000000110000000000000000000000000000000000000000000000c44000000000024000000000000000edc000000085c0000000000000000000293000000000054000000000000000000d1c000000000318000005dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000e980000000000000000000000000000000000000003a70000000000000000000000000000000000000000000001c03000000000000024600000000000000000000c0c000000000000000000000000000000000000000000000000017400000000000012100253000000000000000001860000000000000000035100000000000000000000c04000000000000003080000000000000000000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000366000000000000000400
def Zqg : Nat → Zah
  | 9 => (7,6,9,393221,51,6,4096,Zvr)
  | 10 => (182,5,9,5963854,119,11,4144,ZuA)
  | 11 => (820,4,9,5898424,120,14,4465,ZuB)
  | 12 => (386,3,9,1769521,86,15,4664,ZuC)
  | 13 => (66,2,9,655368,67,13,4360,ZuD)
  | 14 => (9,1,9,65537,0,9,4180,ZuE)
  | 15 => (1,0,9,65537,0,0,4099,ZuF)
  | _ => Zbs
def ZrL : Nat → Nat → Option (Nat × Nat)
  | 10 => ZbT 3 61 1 8 3 3 ZuG
  | 11 => ZbT 65 977 3 14 8 4 ZuH
  | 12 => ZbT 353 1741 8 16 10 4 ZuI
  | 13 => ZbT 199 1993 4 15 9 4 ZuJ
  | 14 => ZbT 40 409 5 13 7 4 ZuK
  | 15 => ZbT 12 431 1 10 4 4 ZuL
  | _ => fun _ => none
def mo : Zaj := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,Zqg,ZrL⟩
def sgY : Array (Bits × Bits) := #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]
def sgC : List Za7 := [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def sgA := moA
def Zvs (j : Nat) : Nat := 0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910
def Zvt (j : Nat) : Nat := 0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110
def Zvu (j : Nat) : Nat := 0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000
def ZuN (j : Nat) : Nat := (if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))
def ZuS (j : Nat) : Nat := 0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916
def ZuO (j : Nat) : Nat := (if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))
def ZuT (j : Nat) : Nat := (if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)
def ZuP (j : Nat) : Nat := 0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def ZuU (j : Nat) : Nat := 0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c
def ZuQ (j : Nat) : Nat := 0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff
def ZuV (j : Nat) : Nat := 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def ZuR (j : Nat) : Nat := 0x10090e08185081808013ff
def ZuW (j : Nat) : Nat := 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def Zqy : Nat → Zah
  | 8 => (6,6,7,327686,51,6,4097,Zvs)
  | 9 => (69,5,7,2818098,102,10,4151,Zvt)
  | 10 => (373,4,7,4849791,119,14,4299,ZuN)
  | 11 => (216,3,7,1769495,85,14,4244,ZuO)
  | 12 => (30,2,7,327683,50,11,4144,ZuP)
  | 13 => (3,1,7,65537,0,6,4109,ZuQ)
  | 14 => (1,0,7,65537,0,0,4105,ZuR)
  | _ => Zbs
def ZrS : Nat → Nat → Option (Nat × Nat)
  | 9 => ZbT 1 113 0 8 3 3 Zvu
  | 10 => ZbT 26 127 7 13 7 4 ZuS
  | 11 => ZbT 159 691 9 15 9 4 ZuT
  | 12 => ZbT 102 467 8 14 8 4 ZuU
  | 13 => ZbT 16 163 4 11 5 4 ZuV
  | 14 => ZbT 3 59 0 8 2 4 ZuW
  | _ => fun _ => none
def sg : Zaj := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,Zqy,ZrS⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjc : Zaz mo (Zat pri) = true := by
  simp only [Zaz, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=6) ?_⟩,ZaF (d:=3) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZiN : Zaz sg (Zat ZfO) = true := by
  simp only [Zaz, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZaF (d:=6) ?_⟩,ZaF (d:=3) ?_⟩
  all_goals simp only [Zba]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zut : Zaa mo 9 0 6 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x7b44819a306751009a5093b784047230032800865a200437000b64002b510562020ba8451937002508043b60092163274655) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zuu : Zaa mo 9 6 1 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x31401265) rfl
  decide +kernel
theorem hb9 : Zaa mo 9 0 7 := (@Zad mo 9 0 6 1 Zut Zuu)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZsW : Zaa mo 10 0 5 := by
  apply ZaD
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZsX : Zaa mo 10 5 67 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x20159475300532700250885a2900592600801264a1300803700b6245194200471000253885a2900593600801264a130040870080359a7b6804235006308b089650630700801264a1300402700628b1807a20016800ba84519470050210020169475300894000201694753006540002016947530059400020159475300754000201a9475300754000b8262631a003261002018b4a5300743000201a94753006940002015947530075400060b214263002130002015947530075400020159475300754000801264a1300201600801264a13003917002018b4a13004716002018b4a13004716002018b4a1300471600601bb48230048160032844b36a001547002018b4a1300471600801264a1300271600801264ab32027160020159475300654000201594753007540002015947530064300060141426300193000601414263002140002015947530075400060141426300192000201594753007540002015947530075400020159475300684000201a947530069400060121426300713000801264a13004130006b02152690021400020159475300754000201a947530058300020159475300643000201594753006430006012142630091200008257691a0068510008257691a0068510060121426300813000801264a130041300008257691a0067510008214635a0030410065121426300713000851264a130041300006214135200307100801264a1300413000601214263007130002051374291082570008214635a1080310060121426300712000801264a130031200) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrf : Zaa mo 10 72 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrg : Zaa mo 10 73 13 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x32800865a20054800832008a602042081035a27a2986016750009457592140509700850265a190050490035a27a2986015690035a27a298601564000748a2867406417000748a286740641700064b0218a00176020630bb0896506309063b4003506917682506a84b25670028070) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrh : Zaa mo 10 86 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zri : Zaa mo 10 87 11 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xba84519470047100032800865a2006580032800865a200548000638006a820024510430b81a362057160032800865a2005480032800865a20054800628b1805a20175800862008a6020420810862008a6020420810862008a602042081) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrj : Zaa mo 10 98 2 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoK : Zaa mo 10 100 39 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x8045947b350654000810368a13b051370002844865a208063002015947530075400065021526900103900230881a5620681200b62451942004021006502152690021400065b2142630021400060121426300214000b4262037410290100201594753008540002015947530065400085709ab76804657007b8106ab90046301095b264a19004087000638006a85004681060121426300214000201594753006540000628a1862006821006014142630021400060141426300193000b68451942005021006308b089650740800b68051942005021002570945730058400025b09457300584000257094573004830000268a9867506584009a5093b78405634008351374892043620002814835a204073000268a9867506854006014142630021400060141426300214000601214263001038006a84b25a780361900ba845194700491000ba84519370036100) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoL : Zaa mo 10 139 39 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x65a530108746a23284b6838365ab401003ba0473656b4010a36b4872374672326561301009365573565a30707868a29109065573314312767b4b8964654b3196891b5ba3654131968786a2108786a2218786a2218786a221929b0761565630708786a280656030966565309665653096656530967868a2918786a2218786a29114a1901053341271533412715334127113ba04725334127126b43076) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoM : Zaa mo 10 178 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoN : Zaa mo 10 179 3 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x76b97121426b234314a59010) rfl
  decide +kernel
theorem Zvl : Zaa mo 10 0 182 := (@Zad mo 10 0 87 95 (@Zad mo 10 0 72 15 (@Zad mo 10 0 5 67 ZsW ZsX) (@Zad mo 10 72 1 14 Zrf (@Zad mo 10 73 13 1 Zrg Zrh))) (@Zad mo 10 87 52 43 (@Zad mo 10 87 11 41 Zri (@Zad mo 10 98 2 39 Zrj ZoK)) (@Zad mo 10 139 39 4 ZoL (@Zad mo 10 178 1 3 ZoM ZoN))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZsY : Zaa mo 11 0 7 := by
  apply ZaD
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZsZ : Zaa mo 11 7 96 := by
  apply ZaD
  apply Zau (ar:=10) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoO : Zaa mo 11 103 9 := by
  apply ZaD
  apply Zau (ar:=10) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoP : Zaa mo 11 112 96 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x201594753006430009102524b3100421006012142630021400060121426300214000201594753007540006018b485300854000601414263001830002015947530075400020159475300754000801264a13006140002015947530075400060141426300214000201594753007540000a814135700402100201594753007540002015947530075400020159475300754000801364a13006140000a81413570030210020159475300754000201594753007540006012142630021400060141426300214000601214263002140006014142630021400060141426300214000601414263001a30006012142630021400060121426300214000601214263002140006012142630021300060141426300213000601214263002130006012142630021300008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0040610008214635a0040610008214635a0040610008214635a0040610008214635a004061002015947530075400060b2142630021400008214635a0040610008214635a00406100851264a1300614000851264a1300614000851264a130061400008214635a1040910008214635a10409100801264a1300514000801264a1300614000801264a1300614000801264a1300514000801264a1300513000801264a1300514000801264a1300514000801264a13005140002b1035249003940002b40352490039400008214635a10905100801264a1300513000801264a1300614000801264a1300513000801264a1300614000801264a1300513000801264a1300513000801264a130051300008214635a0030510008214635a0030510008214635a0030510008214635a003051002018b4a53008540002018b4a530085400020159475300754000205137429104372002108b2a53107432002108b2a53107432002018b4a5300743000201594753007540002018b4a53008540002018b4a53007a40002018b4a5300743000201a94753007540002018b4a530074300008214635a0030510008214635a0030510008214635a0030510008214635a00305100801264a130051300020513742910326900801264a130051300008214635a1030410) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoQ : Zaa mo 11 208 96 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x2015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000250885a2900835000250885a2900835000a502257890012490065021526900103900a50225789001a39006502152690021400065021526900214000862008a602064191065021526900214000205887a29107a6200250885a290079400060b214263002140002016947530075400020169475300643a002016947530075400025043542900324a000248a386420864300801264a1300503800801264a13005038000892a368420684300801264a130050380068b4b358420473200b8262631a003261002016947530064380020169475300754000801264a1300503800801264a1300503800801264a130050380020169475300643900801264a130050390080b264a1300503900801264a1300503900a230690a570054600082b4631a002840002015947530064390020159475300754000801264a13005039000248a386420864300801264a1300503900801264a1300403800801264a13004028002018b4a530063280018202631a002851002018b4a53006328002018b4a53006328004986852a4b016730018202631a002a51000248a3864206421002018b4a530063280018202631a002851002018b4a530063280018202631a00285100801264a130040280008200a6b50046a120801264a1300492800436b84a26306172000248a386420642100801264a1300492800801264a13004928000248a38642064210020169475300643a00201694753006438002016947530064380020159475300643900850265a1900504a00250885a2900724800862008a6020640a10862008a6020640110201594753007540002015947530075400020159475300754000201594753007540002015947530075400080159475300954000201594753009540009102524b310053200801264a13006140002015947530075400020169475300754000801364a1300614000201594753006430008015947530064300) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoR : Zaa mo 11 304 94 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa6020a827606a141035a27a2986016750080359a7b680645700250885a2900693700630bb089650630700a6020a827607a2510250885a29006937006a84b25a7804729000268a98675064530026a00279500153910a6020a8276069a4100268a9867506453000268a986750756400250885a29006937006308b08965063070080359a7b680534600a230690a57005460032800865a20087200850265a1900504800250885a2900724800850265a1900504800250885a290072480080359a7b68064570032800865a20087200850265a1900504800250885a2900724800801264a130050380086a002795801642106308b08965074080080359a7b6806457006018b489300743800628b1807a200172000892a368420573a000892a3684206843000268a9867507564005890b3984205943009a5093b78405934009a6093b78405934009a5093b78405934000892a36b4806743009230631a2401934000248a3864207943000248a386420794300648b1807a201283000892a36b4805743000896a3684206843000892a36b4806843008b403584900345000201694753007540009a5093b78404623000892a36b480573200b6245194200502100201694753007540006012142630021400060121426300214000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002018b4a530085400020159475300754000201a947530075400020159475300754000b6245194200502100201594753007540002015947530075400020159475300754000801264a130061400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a1300614000201a947530075400020159475300754000b6245194200502100801264a130061400008257691a00726100201594753007540002016947530075400020159475300754000201594753007540002018b4a53008540002018b4a530085400020159475300754000801264a1300513000801264a1300513000801264a1300513000801264a1300413000801264a13005130002015947530075400) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoS : Zaa mo 11 398 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoT : Zaa mo 11 399 1 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x268a98675064590) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoU : Zaa mo 11 400 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoV : Zaa mo 11 401 20 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x628a186200752100832008a602064091032800865a2007610018202631a0028510032800865a2007610008257691a0068510032800865a2007610032800865a20076100862008a6020640110628b1807a20197200832008a6020641a102308b1a56206a170032800865a20076100832008a60206401102308b0a562063070032800865a20076100250885a2900724800250885a2900724800a6020a827606a1410205887a290061570) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoW : Zaa mo 11 421 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoX : Zaa mo 11 422 10 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x268a986750756400a230690a57005460026a0027958016421026a00279580153a1032800865a20076900250885a290083500032800865a200769000638006a85004671032800865a20076900832008a602064191) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoY : Zaa mo 11 432 3 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZoZ : Zaa mo 11 435 68 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x601414263002140006012142630021400020169475300754000601214263002140006012142630021400060121426300219000b9452637a10326100b9262637a1032610020169475300754000206887a2910837200206887a29108372006890b35842047830021069275310643200a5022578900235000201594753007540002015947530064a0002015947530075400020159475300754000601414263002140000248a38642086430060141426300214000064b0218a00238120b6040a8276083261080359a7b6807568001328a4b6530860400801364a1300503800601bb485300743800250885a29006837001328a4b6530758300801264a1300503800801264a1300503800b68151942005021008015947b3507540001328a4b65308604001328a4b65308604001368a4b65308604001328a4b6530860400801a947b3507540001328a4b65308604000268a986750867500250885a2900724a000892a368420573200250885a2900724800250885a2900724a00850265a1900504a0080b264a130050380020159475300643800850265a1900504a0032800865a20076a0032800865a20076100250885a2900724a00801264a1300503800801264a1300503800850265a1900504900850265a19005049006894b358420473200628b1807a20017200b8245693a003840008306907b650640a000248a386420753200850265a1900504a00862008a6020640a10862008a6020640110801264a1300503800850265a1900504a00250885a2900724800250885a29007248006a84b25a78049120) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo0 : Zaa mo 11 503 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo1 : Zaa mo 11 504 5 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x601414263002140006012142630021400020159475300754000601214263002140001628a1b620086210) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo2 : Zaa mo 11 509 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo3 : Zaa mo 11 510 83 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x2048b3a5420654340062ba1862007821005a80b198700562100026ba9867507865007412079541054021020b71ba576085213020159475300754000201594753007540002018b4a5300854000205887a29107a620060b214263002140002308b1a5620791200250885a290083500080b264a13006140002015947530075400060b214263002140002015947530075400060121426300214000204594753007540002054374291043720020459475300754000b62451942005021001628a1b620086210020459475300754000601214263002140004b8609b837058371065b214263002140001628a1b62008621005628a18620086210025b4945730057400025b49457300574000804a9475300754000204594753007540002015947530075400020159475300754000201594753007540006012142630021400060121426300214000b62151942005021002016947530075400065021526900215000801264a13006140002015947530075400020459475300754000201594753007540005890b398420594300ba8451947005021008015947b3007540000892a36842068430008244635a0040610008257692a007261000248a3864208643000248a3864208643000248a3b64208643009a5093b7840573400651214263002140005628a1862007621002048b4a53008540006502152690021500065b2142630021400085b264a130050380065b2142630021400085b264a130050380085b264a13005038006894b35842047320008244639a003850006891b35842047320008244639a003850007b8106ab9005640100a644639a00385000a9462587b402148007b8106ab9004630100248a3864207532000248a3864207532007b8006ab90046901085b364a1300503800a9462587b401938005278006a84004671095036ba1980504700a9462587b4021380090359a4b6808456006012142630021a0006014142630021400) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo4 : Zaa mo 11 593 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo5 : Zaa mo 11 594 2 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x1a80813b700382100ba635694a0050610) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo6 : Zaa mo 11 596 96 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x8796a2328746a2328746a23214a190103183123214ab901065ab401076b8612165ab301076b8612165a1401070b9a12165ab301065ab301065ab301065ab301065ab301070b8a12170b8a12126183121754b297565ab301076b8612165a5301065ab301065ab301065ab3010658b301065a1301070b8a19170b8a19170b8a19170b8a19170b8a191133912a2133912a2133912a270b8a19135ab043070b8a19170b8a19165ab301076586121765861217658612165ab301065ab301065ab301070b8a12170b8a121a1b68661a1b6865076b86121765861213146129270b8a12170b8a12190a055403bb618978796a2218786a2218796a2218796a2218796a2218796a2218796a2218796a2218796a2218796a221a1b68650531a04937658612153ba0493a1b6866153ba04938796a232531a0493a1b6865076b8612153ba0493a1b6866103ba049353ba0493133912921339129214ab901014ab901031461232314612323146123214ab901014ab901014ab9010426b234335ab0440426b2343) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo7 : Zaa mo 11 692 7 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x8786a2218796a2328796a2328796a2328796a2328796a2328796a232) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo8 : Zaa mo 11 699 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zo9 : Zaa mo 11 700 39 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xb67b0a8656b6308070b9a121560a3080560a3080560a30808786a2218786a2218786a2218786a221093a55848786a2218786a2218786a2218786a2218786a221093a55848786a2218786a2218786a221a1b786508786a221754b29648786a2a2a1b78651a1b78661b67b0a75a1b786518786a2a22619318126193181261931817868a2a226193181b67b0a75261931818786a221b67b0a75a26a2872) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpa : Zaa mo 11 739 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpb : Zaa mo 11 740 31 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x754b296426543121b4a49550b4a49550b4a495508796a221a1b78650a1b78650a1b7865046ba7080a1b79650a1b78651b67b0a86b67b0a86a1b786618746a23242642343b67b0a8665a14010b67b0a86b4a495408796a232319612328796a2328796a2323146123231461232656b301065613010b464b550b67b0a86) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpc : Zaa mo 11 771 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpd : Zaa mo 11 772 3 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa1b68661929b07728796a232) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpe : Zaa mo 11 775 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpf : Zaa mo 11 776 44 := by
  apply ZbB (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x70b9a121946475503746723294a4755076b9712176b9712170b8a12165ab30108785b23270b8a1213185123265a530107058a12170b9a12114ab901065a530102659312126193121658530106585301026193121261931218796a2328796a2328796a2328796a23265a0301014a0901065a030102654312165ab401065a5401065a54010a1b6866165a5401065ab401065a5401065ab40108796a232656130108796a23270b9a12170b9a12114a59010) rfl
  decide +kernel
theorem Zvm : Zaa mo 11 0 820 := (@Zad mo 11 0 504 316 (@Zad mo 11 0 399 105 (@Zad mo 11 0 112 287 (@Zad mo 11 0 7 105 ZsY (@Zad mo 11 7 96 9 ZsZ ZoO)) (@Zad mo 11 112 192 95 (@Zad mo 11 112 96 96 ZoP ZoQ) (@Zad mo 11 304 94 1 ZoR ZoS))) (@Zad mo 11 399 23 82 (@Zad mo 11 399 2 21 (@Zad mo 11 399 1 1 ZoT ZoU) (@Zad mo 11 401 20 1 ZoV ZoW)) (@Zad mo 11 422 13 69 (@Zad mo 11 422 10 3 ZoX ZoY) (@Zad mo 11 435 68 1 ZoZ Zo0)))) (@Zad mo 11 504 195 121 (@Zad mo 11 504 89 106 (@Zad mo 11 504 5 84 Zo1 (@Zad mo 11 509 1 83 Zo2 Zo3)) (@Zad mo 11 593 3 103 (@Zad mo 11 593 1 2 Zo4 Zo5) (@Zad mo 11 596 96 7 Zo6 Zo7))) (@Zad mo 11 699 72 49 (@Zad mo 11 699 40 32 (@Zad mo 11 699 1 39 Zo8 Zo9) (@Zad mo 11 739 1 31 Zpa Zpb)) (@Zad mo 11 771 4 45 (@Zad mo 11 771 1 3 Zpc Zpd) (@Zad mo 11 775 1 44 Zpe Zpf)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zs0 : Zaa mo 12 0 62 := by
  apply ZaD
  apply Zau (ar:=10) (rows:=0) (d:=3)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrk : Zaa mo 12 62 96 := by
  apply ZaD
  apply Zau (ar:=11) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpg : Zaa mo 12 158 75 := by
  apply ZaD
  apply Zau (ar:=11) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zph : Zaa mo 12 233 10 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x201594753007540009102524b310053200201594753007540000a814135700402100601214263002140006014142630021400008214635a1040610008214635a1040610008214635a104061002108b2a531085320) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpi : Zaa mo 12 243 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpj : Zaa mo 12 244 21 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x2018b4a53008540002018b4a53008540002018b4a53008540002018b4a5300854000801264a1300614000201694753007540002016947530075400020169475300754000201594753007540002015947530075400020159475300754000801264a1300614000250885a2900835000250885a2900835000850265a1900615000a5022578900235000862008a60208613106894b3584205843000248a3864208643000892a36842068430008b2a36842068430) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpk : Zaa mo 12 265 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpl : Zaa mo 12 266 29 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x832008a60208613100268a9867508675009a5093b78405734009a6093b7840573400201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a13006140009a5093b7840573400801264a1300614000801264a1300614000801264a1300614000801264a1300614000b8262631a0032610008257691a0072610008257691a0072610018202631a0032610) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpm : Zaa mo 12 295 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpn : Zaa mo 12 296 13 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x268a9867508675000268a9867508675000268a98675086750090379a7b6807568000268a9867508675000268a98675086750080359a7b6807568000268a9867508675000268a986750867500a230690a5701657000268a986750867500a230690a57016570026a0027958027531) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpo : Zaa mo 12 309 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpp : Zaa mo 12 310 1 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x268a98675086750) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpq : Zaa mo 12 311 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpr : Zaa mo 12 312 6 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa230690a5701657000268a986750867500a9462587b40325000a9462587b40325000a9462587b4032500095046ba198061580) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zps : Zaa mo 12 318 7 := by
  apply ZaD
  apply Zau (ar:=12) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpt : Zaa mo 12 325 6 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa9462587b4032500086406b0a58016580085026ba09806158007b8106ab9006851107b8006a83006831106894b35842058430) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpu : Zaa mo 12 331 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpv : Zaa mo 12 332 4 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x9a5093b78405734009230631a2401634009260631a2401634009230631a24016340) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpw : Zaa mo 12 336 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpx : Zaa mo 12 337 7 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa9462587b40325000a9462587b403250005890b3984205843005890b3984205843005890b398420584300a9462587b403250005890b39842058430) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpy : Zaa mo 12 344 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zpz : Zaa mo 12 345 22 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0xa50225789002350005a80b1987005821006894b3584205843006894b3584205843006894b358420584300a230690a5701657006894b3584205843000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a3864208643000248a3864208643005896a3684206843000248a3b64208643000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a38642086430) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZpA : Zaa mo 12 367 1 := by
  exact ZaD (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZpB : Zaa mo 12 368 18 := by
  apply ZaV (pos:=ZaJ) (neg:=ZaI) (data:=fun _ => 0x5a80b198700582100634ab489350854000a43752874903205304687b58294083506076835894a3050834059471b98670581230250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000650215269002150000628a186200862100250885a2900835000a5022578900235000a5022578900235000a502257890023500) rfl
  decide +kernel
theorem Zvn : Zaa mo 12 0 386 := (@Zad mo 12 0 311 75 (@Zad mo 12 0 265 46 (@Zad mo 12 0 233 32 (@Zad mo 12 0 62 171 Zs0 (@Zad mo 12 62 96 75 Zrk Zpg)) (@Zad mo 12 233 10 22 Zph (@Zad mo 12 243 1 21 Zpi Zpj))) (@Zad mo 12 265 31 15 (@Zad mo 12 265 1 30 Zpk (@Zad mo 12 266 29 1 Zpl Zpm)) (@Zad mo 12 296 13 2 Zpn (@Zad mo 12 309 1 1 Zpo Zpp)))) (@Zad mo 12 311 25 50 (@Zad mo 12 311 14 11 (@Zad mo 12 311 1 13 Zpq (@Zad mo 12 312 6 7 Zpr Zps)) (@Zad mo 12 325 6 5 Zpt (@Zad mo 12 331 1 4 Zpu Zpv))) (@Zad mo 12 336 9 41 (@Zad mo 12 336 1 8 Zpw (@Zad mo 12 337 7 1 Zpx Zpy)) (@Zad mo 12 345 22 19 Zpz (@Zad mo 12 367 1 18 ZpA ZpB)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zs1 : Zaa mo 13 0 5 := by
  apply ZaD
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zs2 : Zaa mo 13 5 18 := by
  apply ZaD
  apply Zau (ar:=10) (rows:=0) (d:=1)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zrl : Zaa mo 13 23 43 := by
  apply ZaD
  apply Zau (ar:=11) (rows:=0) (d:=3)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zvo : Zaa mo 13 0 66 := (@Zad mo 13 0 5 61 Zs1 (@Zad mo 13 5 18 43 Zs2 Zrl))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zs3 : Zaa mo 14 0 9 := by
  apply ZaD
  apply Zau (ar:=10) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zvp : Zaa mo 14 0 9 := Zs3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zs4 : Zaa mo 15 0 1 := by
  exact ZaD (by decide +kernel)
theorem Zvq : Zaa mo 15 0 1 := Zs4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zqh : ZbM mo 15 := by
  intro k hk
  interval_cases k
  · exact Zap mo 0 0
  · exact Zap mo 1 0
  · exact Zap mo 2 0
  · exact Zap mo 3 0
  · exact Zap mo 4 0
  · exact Zap mo 5 0
  · exact Zap mo 6 0
  · exact Zap mo 7 0
  · exact Zap mo 8 0
  · exact hb9
  · exact Zvl
  · exact Zvm
  · exact Zvn
  · exact Zvo
  · exact Zvp
  · exact Zvq
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Znu : block sg 8 0 6 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZrQ : block sg 8 0 6 = true := Znu
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Znv : block sg 9 0 21 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=2)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlE : block sg 9 21 48 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=3)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ZrR : block sg 9 0 69 = true := (@ZaR sg 9 0 21 48 Znv ZlE)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zlw : block sg 10 0 3 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zlx : block sg 10 3 128 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjh : block sg 10 131 111 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zji : block sg 10 242 128 = true := by
  apply Zau (ar:=11) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjj : block sg 10 370 3 = true := by
  apply Zau (ar:=11) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zqt : block sg 10 0 373 = true := (@ZaR sg 10 0 131 242 (@ZaR sg 10 0 3 128 Zlw Zlx) (@ZaR sg 10 131 111 131 Zjh (@ZaR sg 10 242 128 3 Zji Zjj)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zly : block sg 11 0 2 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zlz : block sg 11 2 62 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=3)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zj6 : block sg 11 64 123 = true := by
  apply Zau (ar:=11) (rows:=0) (d:=4)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zjk : block sg 11 187 29 = true := by
  apply Zau (ar:=12) (rows:=0) (d:=2)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zqu : block sg 11 0 216 = true := (@ZaR sg 11 0 64 152 (@ZaR sg 11 0 2 62 Zly Zlz) (@ZaR sg 11 64 123 29 Zj6 Zjk))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlA : block sg 12 0 1 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlB : block sg 12 1 12 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=1)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zj7 : block sg 12 13 17 = true := by
  apply Zau (ar:=11) (rows:=0) (d:=1)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zqv : block sg 12 0 30 = true := (@ZaR sg 12 0 1 29 ZlA (@ZaR sg 12 1 12 17 ZlB Zj7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlC : block sg 13 0 3 = true := by
  apply Zau (ar:=10) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zqw : block sg 13 0 3 = true := ZlC
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlD : block sg 14 0 1 = true := by
  apply Zau (ar:=9) (rows:=0) (d:=0)
  simp only [Zab,Zas]
  repeat' apply And.intro
  all_goals decide +kernel
theorem Zqx : block sg 14 0 1 = true := ZlD
set_option maxHeartbeats 0 in
theorem Zqz : ZbS sg 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block sg 0 0 0 = true)
  · exact (rfl : block sg 1 0 0 = true)
  · exact (rfl : block sg 2 0 0 = true)
  · exact (rfl : block sg 3 0 0 = true)
  · exact (rfl : block sg 4 0 0 = true)
  · exact (rfl : block sg 5 0 0 = true)
  · exact (rfl : block sg 6 0 0 = true)
  · exact (rfl : block sg 7 0 0 = true)
  · exact ZrQ
  · exact ZrR
  · exact Zqt
  · exact Zqu
  · exact Zqv
  · exact Zqw
  · exact Zqx
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem Zqi : Zax false graph 15 inputs.toFinset := by
  rw [show graph = ZaN mo by decide +kernel]
  exact Zhr (g:=mo) (top:=15) (i:=0) (Zai pri Zvv) Zjc Zqh (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ZlF : Zax true graph 14 inputs.toFinset := by
  rw [show graph = ZaN sg by decide +kernel]
  exact Zfh (g:=sg) (top:=14) (i:=0) (Zai ZfO ZuX) ZiN Zqz (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_670

theorem PEqualNP.Outside.L_meta_670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 :=
  PEqualNP.Outside.L_meta_670.ZjE PEqualNP.Outside.L_meta_670.Zqi PEqualNP.Outside.L_meta_670.ZlF
