import PEqualNP.Defs
-- First-gate certificate by freeedolin, adapted from dsgallups and the project L_meta_1667 extraction.
namespace PEqualNP.Outside.L_meta_670.Zhi
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def Zap (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def Zbo (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem Za1 {u d} (h : Zap u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem Zdf {u d} (h : Zap u d) (a b : Sig) : bin d a b = bin (Zbo d) b a := by
  rcases Za1 h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,Zbo,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : Zap u d) : Zap u (Zbo d) ∧ Zbo (Zbo d)=d := by
  rcases Za1 h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [Zbo,Zap]
def Zae (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), Zap u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Zae u target k (insert (bin d a b) U)
theorem Zae.stop {u} {target : Sig} (hp : proper target) : Zae u target 0 {target} := ⟨rfl,hp⟩
theorem Zae.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : Zap u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zae u target k (insert (bin d a b) U)) :
    Zae u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Zae.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Zae u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Zae.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : Zap u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Zae u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Zae.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Zae u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma ZdY {u target k S} (h : Zae u target k S) : ∀ a ∈ S, proper a := by
  induction h using Zae.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma Zdc {u target k S} (h : Zae u target k S) : S.card ≤ k+1 := by
  induction h using Zae.ind with
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
private lemma ZbC (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma Zbn (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem ZaT {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem Zif (a : Sig) : nrm false a = a := rfl
theorem ZiP (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,ZbC]
theorem Zdw {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem ZeG (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,ZbC,neg_neg']
theorem ZhX {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem ZhY {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact ZhX h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem ZbL (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem Zig (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply ZaT
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,ZbL,ha,hb,Zbn,ZbC,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,ZbC,ZbL]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def ZaN (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def Za2 (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := Za2 w (nrm u v)
private lemma Zet (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply ZaT <;> intro i <;>
    simp [Zbn,bit_zero,bit_one]
private lemma Ziz : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma ZdK {w : List Sig} {a : Sig} (h : Za2 w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def ZbR (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, Zap u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b
private lemma ZeE {u w a b} (d : Nat) (hd : Zap u d) (ha : Za2 w a) (hb : Za2 w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    Za2 w (bin d a b) ∨ ZbR u w (bin d a b) := by
  have rz : Za2 w zero := Or.inr (fun h => h.1 rfl)
  have ro : Za2 w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := Zet a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := Zet b
  by_cases he : a=b
  · subst b
    left
    rcases Za1 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases ZdK ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases Za1 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases Za1 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases ZdK hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases Za1 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases Za1 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem Zd2 (a : Sig) : nrm true a ≠ one := by
  intro h
  have := ZiP a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem Zer {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ ZbR u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := ZeE (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [Zif] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := Zig d a b
    unfold Repr
    rw [eq]
    exact ZeE e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨Zd2 a,Zd2 b⟩)
theorem Zb0 {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := ZhY hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma Zb8 {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Zb0 (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem ZiD {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [ZeG]
def ZaP (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma Ziw (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ZaP g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (ZaP g=false ∧ ZbR u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      ZbR u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply ZaT
      intro i
      cases d <;> simp [ZbL,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (Zb0 (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (Zb8 w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact Zer d (Zb8 w i) (Zb8 w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [ZaP])
    left
    cases l with
    | nil => exact Zb0 (Or.inr (by simp [gv,Ziz]))
    | cons i l => exact ZiD (Zb8 w i)
private lemma Zes {u target} {w : List Sig} {z : Sig} {k S c} (h : Zae u target k S)
    (hz : Za2 w z ∨ (c=1 ∧ ZbR u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Zae u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := ZdY h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Zae u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Zae.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, ZaP g=false)
    (hp : proper target) (hout : target ∈ (ZaN gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !ZaP g) ∧ Zae u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Zae.stop hp,by simpa [ZaN] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := Ziw u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : Za2 (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if ZaP g then 0 else 1)=1 ∧ ZbR u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := Zes ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : ZaP g <;> simp [hn] at hl ⊢ <;> omega
private lemma ZeK (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma ZiQ (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [ZeK]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [ZbL]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [ZbL]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [ZbC,bit_zero]
    | cons a l => exact ZbC _ _
private lemma Zg4 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (ZaN gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (ZaN gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,ZiQ i g w (hg g (by simp))]
abbrev Zac (R : Type) := R → Bool
def inv {R} (a : Zac R) : Zac R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Zac R) : Zac R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Zac R) : Zac R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Zao {R} (a : Zac R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def Zaq {R} (a : Zac R) : Nat := by
  classical exact if Zao a then 1 else 0
noncomputable def Zaz {R} (xs : List (Zac R)) : Nat := (xs.map Zaq).sum
def Zag {R} (u : Bool) (pool : List (Zac R)) (v : Zac R) : Prop :=
  v ∈ pool ∨ Zao v ∨ (u=true ∧ inv v ∈ pool)
def ZbE {R} (u : Bool) (pool xs : List (Zac R)) := ∀ a ∈ xs, Zag u pool a
def Zah {R} (u : Bool) (roots : List (Zac R)) : Nat → List (Zac R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Zac R)) (a b : Zac R), Zah u roots p bank ∧ Zag u bank a ∧
      Zag u bank b ∧ c=combine op a b :: bank
theorem Zah.start {R u} {roots : List (Zac R)} : Zah u roots 0 roots := rfl
theorem Zah.two {R u} {roots : List (Zac R)} {p bank a b} (op : Bool) (h : Zah u roots p bank)
    (ha : Zag u bank a) (hb : Zag u bank b) : Zah u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Zah.ind {R u} {roots : List (Zac R)} {motive : ∀ p bank, Zah u roots p bank → Prop}
    (start : motive 0 roots Zah.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Zah u roots p bank) (ha : Zag u bank a)
      (hb : Zag u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Zah.two op h ha hb))
    {p bank} (h : Zah u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Zac R) : Nat → List (Zac R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Zac R) (rest : List (Zac R)), Zap u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Zac R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Zac R} {s : Nat} {xs zs : List (Zac R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Zac R} {s : Nat} {a b : Zac R} {rest : List (Zac R)} (op : Nat) (hd : Zap u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Zac R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : Zap u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem ZbM {R} (a : Zac R) (xs) : Zaz (a::xs)=Zaq a + Zaz xs := by
  simp [Zaz]
theorem Zep {R} (a : Zac R) (xs) (k : Bool) : Zaz xs ≤ Zaz (kept k a xs) := by
  cases k <;> simp [kept,ZbM]
theorem ZcT {R} {a : Zac R} (h : Zao a) : Zao (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Zac R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem Zev {R} (a : Zac R) : Zaq (inv a)=Zaq a := by
  have : Zao (inv a) ↔ Zao a := ⟨fun h => inv_inv' a ▸ ZcT h,ZcT⟩
  by_cases h : Zao a
  · simp only [Zaq,if_pos h,if_pos (this.mpr h)]
  · simp only [Zaq,if_neg h,if_neg (fun x => h (this.mp x))]
theorem Zc8 {R u} {bank : List (Zac R)} {a} (hu : u=true) (h : Zag u bank a) : Zag u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (ZcT h))
  · exact Or.inl h
theorem ZgC {R} {a b : Zac R} (op) (h : Zao a) (g : Zao b) :
    Zao (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem ZgG {R u} (op) {a b : Zac R} {bank}
    (h : Zao a ∨ Zao b) (ha : Zag u bank a) (hb : Zag u bank b) :
    Zag u bank (combine op a b) := by
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
theorem ZdE {R u} {bank v} (w : Zac R) (h : Zag u bank v) :
    Zag u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem ZhP {R u} (roots : List (Zac R)) {p bank a b} (op) (hp : Zah u roots p bank)
    (ha : Zag u bank a) (hb : Zag u bank b) :
    ∃ q next, Zah u roots q next ∧ Zag u next (combine op a b) ∧
        (∀ v, Zag u bank v → Zag u next v) ∧
        q+Zaq a+Zaq b ≤ p+1+Zaq (combine op a b) := by
  classical
  by_cases c : Zao a ∨ Zao b
  · refine ⟨p,bank,hp,ZgG op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Zao a <;> by_cases cb : Zao b
    · simp [Zaq,ca,cb,ZgC op ca cb]
    · simp [Zaq,ca,cb]
    · simp [Zaq,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Zao a := fun h => c (Or.inl h)
    have cb : ¬Zao b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Zah.two op hp ha hb,Or.inl (by simp),fun _ h => ZdE _ h,
      by simp [Zaq,ca,cb]⟩
theorem Zd4 {R u} {bank : List (Zac R)} {d a b} (hd : Zap u d) (ha : Zag u bank a) (hb : Zag u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Zag u bank x ∧ Zag u bank y ∧ Zaq x=Zaq a ∧ Zaq y=Zaq b := by
  rcases Za1 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,Zc8 hu hb,rfl,Zev b⟩
  · exact ⟨false,inv a,b,rfl,Zc8 hu ha,hb,Zev a,rfl⟩
theorem ZhA {R u} (roots : List (Zac R)) {p bank a b} (d) (hd : Zap u d) (hp : Zah u roots p bank)
    (ha : Zag u bank a) (hb : Zag u bank b) :
    ∃ q next, Zah u roots q next ∧ Zag u next (comb d a b) ∧
        (∀ v, Zag u bank v → Zag u next v) ∧
        q+Zaq a+Zaq b ≤ p+1+Zaq (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := Zd4 hd ha hb
  rw [e,←cx,←cy]
  exact ZhP roots op hp hx hy
theorem ZeB {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Zac R} (nc : ¬Zao goal) {s ws}
    (h : Run u goal s ws) (roots : List (Zac R)) {p bank}
    (hp : Zah u roots p bank) (hs : ZbE u bank ws) :
    ∃ q next, Zah u roots q next ∧ Zag u next goal ∧ q+Zaz ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [Zaz,Zaq,nc]⟩
  | perm eq _ ih =>
    have hsub : ZbE u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [Zaz,←(eq.map Zaq).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := ZhA roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : ZbE u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases ZeB hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (ZeB hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := Zep a (kept kb b rest) ka
    have hlen' := Zep b rest kb
    rw [ZbM] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [ZbM,ZbM]
    omega
def Zai {R S : Type} (rows : S → R) (a : Zac R) : Zac S :=
  fun r => a (rows r)
theorem ZgI {R S : Type} (rows : S → R) (k : Bool) (a : Zac R) (ws) :
    (kept k a ws).map (Zai rows) =
    kept k (Zai rows a) (ws.map (Zai rows)) := by
  cases k <;> simp [kept]
theorem ZdL {R S : Type} (rows : S → R) (d) (a b : Zac R) :
    Zai rows (comb d a b) = comb d (Zai rows a) (Zai rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem Zg8 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (Zai rows goal) s (ws.map (Zai rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,ZgI,ZdL] at ih ⊢
    exact Run.two op hd ka kb ih
theorem ZcK {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Zao (Zai rows goal)) {roots : List (Zac S)} {p bank L}
    (hp : Zah u roots p bank) (hs : ZbE u bank (ws.map (Zai rows)))
    (hl : ∀ q bs, Zah u roots q bs → Zag u bs (Zai rows goal) → L ≤ q) :
    L + Zaz (ws.map (Zai rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (Zg8 rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def observe (a : Sig) : Zac Row := fun r => bit r a
def table (f : Zac Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem Zbi (f : Zac Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem ZcP (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact Zbi (observe v) ⟨j,hj⟩
theorem ZgH (f : Zac Row) : observe (table f) = f := by
  funext r
  exact Zbi f r
theorem ZeI (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact ZbC _ _
theorem ZeH (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,Zbn,comb]
  split_ifs <;> rfl
theorem ZeA {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem ZcD {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem Zcz (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem Zdm {u} {T : Sig} {k S} (h : Zae u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Zae.ind generalizing v with
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
    have bm := ZcD kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := ZcD ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [Zcz,Zcz,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,ZeA,ZeA,ZeH] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem Zil (f : Zac Row) : table (inv f) = neg (table f) := by
  rw [←ZcP (neg (table f)),ZeI,ZgH]
theorem ZhG (d : Bool) (f g : Zac Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply ZaT
  intro r
  rw [Zbi,ZbL,Zbi,Zbi]
  cases d <;> rfl
theorem ZcM {u} {bank : List (Zac Row)} {a} (h : Zag u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply Zb0
    cases b
    · exact Or.inl (ZaT fun i => (Zbi _ i).trans (bit_zero i).symm)
    · exact Or.inr (ZaT fun i => (Zbi _ i).trans (bit_one i).symm)
  · have := Zil a
    refine Or.inl ?_
    rw [←ZeG,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem Zgi {u} {roots : List (Zac Row)} {p bank}
    (h : Zah u roots p bank) {T k S} (run : Zae u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Zae u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Zah.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,ZhG] at sub
    have rep := Zer d (ZcM ha) (ZcM hb)
    obtain ⟨k',S',hk,run',sub'⟩ := Zes (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def ZaB (a : Sig) : Bool := !(bit 0 a)
theorem ZeF {u} {w : List Sig} (h : w.all ZaB=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact Zdw (by simpa [ZaB] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem Zco {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : ZaB T=true) (nR : roots.all ZaB=true)
    (h : Zah u (roots.map observe) p bank) (hit : Zag u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Zae u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := ZcM hit
  rw [ZcP] at hm
  unfold Repr at hm
  rw [Zdw (by simpa [ZaB] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := Zgi h (Zae.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,ZcP]
  rw [e,ZeF nR] at hs
  exact hs
theorem Zdy {u T k S} (h : Zae u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Zae.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [Zbn,Zbn,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem Zci {u T k S} (h : Zae u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := Zdy h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def Za0 : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem ZhO : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem Zh2 : ∀ r : Row, bit r Za0 = (sample r 0 || sample r 3) := by decide +kernel
theorem ZdQ : proper graph := by unfold proper; decide +kernel
theorem Zha : Za0 ≠ zero := by decide +kernel
theorem Zd6 : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem ZiR (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←Zd6]
  rw [List.map_ofFn]
  rfl
theorem Zeb (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((ZaN C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←ZeK,Zg4 _ _ _ (fun g hg => (h g hg).1),ZiR]
  rfl
theorem Zg3 (gs : List Gate) (ws : List Sig) : ∃ l, ZaN gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [ZaN]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [ZaN,List.append_assoc] using hl⟩
theorem Zi5 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ u k S, k ≤ (if u then 13 else 14) ∧ Zae u graph k S ∧ ∀ a ∈ S, a ∈ inputs++[Za0] := by
  have headEq : (ZaN C.gates inputs).getD 9 zero = Za0 := by
    apply ZaT
    intro r
    exact (Zeb C legal 9 r).trans ((first (sample r)).trans (Zh2 r).symm)
  have goalEq : (ZaN C.gates inputs).getD C.output zero = graph := by
    apply ZaT
    intro r
    exact (Zeb C legal C.output r).trans ((congrFun computes (sample r)).trans (ZhO r).symm)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (Zha headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = Za0 := by
      rw [hgs] at headEq
      change (ZaN gs (inputs++[gv inputs g])).getD 9 zero = Za0 at headEq
      obtain ⟨l,hl⟩ := Zg3 gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at goalEq
    change (ZaN gs (inputs++[gv inputs g])).getD C.output zero = graph at goalEq
    rw [eq0] at goalEq
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    have mode : ∃ u : Bool, (u=false → ∀ g ∈ gs, ZaP g=false) ∧ gs.countP (fun g => !ZaP g) ≤ (if u then 13 else 14) := by
      by_cases hn : ∀ g ∈ gs, ZaP g=false
      · refine ⟨false,fun _ => hn,?_⟩
        have := List.countP_le_length (p:=fun g => !ZaP g) (l:=gs)
        simp only [Bool.false_eq_true,ite_false]
        omega
      · refine ⟨true,by simp,?_⟩
        push Not at hn
        obtain ⟨g,hg,hx⟩ := hn
        have lt : gs.countP (fun g => !ZaP g) < gs.length := by
          rcases Nat.lt_or_ge (gs.countP (fun g => !ZaP g)) gs.length with h | h
          · exact h
          · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
            simp only [Bool.not_eq_true'] at eq
            exact absurd eq hx
        simp only [ite_true]
        omega
    obtain ⟨u,mono,count⟩ := mode
    have out := Zb8 (u:=u) (ZaN gs (inputs++[Za0])) C.output
    rw [goalEq] at out
    unfold Repr at out
    have pg : bit 0 graph=false := by decide +kernel
    rw [Zdw pg] at out
    have targetIn := out.resolve_right (fun hn => hn ZdQ)
    obtain ⟨k,S,hk,run,hs⟩ := extract gs _ tailLegal mono ZdQ targetIn
    have ns : (inputs++[Za0]).all ZaB=true := by decide +kernel
    rw [ZeF ns] at hs
    exact ⟨u,k,S,by omega,run,hs⟩
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem Zbg (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := Zbi _ _
theorem ZbV (f : Row → Row) (a : Sig) :
    observe (rename f a) = Zai f (observe a) := by funext r; exact Zbg f a r
theorem Zh0 (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply ZaT
  intro r
  simp only [Zbg,Zbn]
theorem Zh1 (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [Zbg,Zbg,hr] at he
  exact he
theorem Zfa (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (Zbg f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (Zbg f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem ZhC {u T k S} (h : Zae u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Zae u (rename f T) k (S.image (rename f)) := by
  have inj := Zh1 f onto
  obtain ⟨fz,fo⟩ := Zfa f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Zae.ind with
  | stop hp => simpa using Zae.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,Zh0] at fresh ih ⊢
    exact Zae.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem ZeP {u T k S} (h : Zae u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Zae.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [Zbn] at hp hn
      subst none
      rcases Za1 hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Zak (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Zah u (roots.map observe) p bank → Zag u bank (observe T) → L ≤ p
theorem ZiC {R u} {roots : List (Zac R)} {p bank} (h : Zah false roots p bank) : Zah u roots p bank := by
  have up {bank : List (Zac R)} {a} (h : Zag false bank a) : Zag u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Zah.ind with
  | start => exact Zah.start
  | two op h ha hb ih => exact Zah.two op ih (up ha) (up hb)
theorem ZhV {u roots T L} (h : Zak true roots T L) : Zak u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (ZiC hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Zae u T k S
def Zcq (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem ZcI {u roots T L} (hp : proper T) (nT : ZaB T=true) (nR : roots.all ZaB=true)
    (essential : ∀ a ∈ roots, Zcq T roots a)
    (noRun : Impossible u T L roots.toFinset) : Zak u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := Zco hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact Zci run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem ZcL {v : Sig} (hv : proper v) : ¬Zao (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply Zb0
    cases b
    · exact Or.inl (ZaT fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (ZaT fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : Za2 [] v := hr
  exact (hr'.resolve_left (by simp)) hv
theorem ZhE {R} (a b : List (Zac R)) : Zaz (a++b) = Zaz a + Zaz b := by
  simp [Zaz]
theorem Zgh {R} (xs : List (Zac R)) (hc : ∀ x ∈ xs, Zao x) :
    Zaz xs = xs.length := by
  induction xs with
  | nil => simp [Zaz]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [ZbM,List.length_cons,Zaq,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem Zd0 {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : ZaB T=true) (nR : roots.all ZaB=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Zag u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Zcq T roots a)
    (constant : ∀ a ∈ singles, Zao (observe (rename r a)))
    (L : Nat) (prior : Zak u other G L) : Zak u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := Zco pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact Zci run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := Zdm run front nd fe
  have gc : Zai r (observe T) = observe G := (ZbV _ _).symm.trans (congrArg observe eq)
  have supp : ZbE u (other.map observe) ((front.map observe).map (Zai r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←ZbV]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := ZcK r run' (gc ▸ ZcL pG) Zah.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ Zaz ((front.map observe).map (Zai r)) := by
    simp only [front,List.map_append,ZhE]
    let xs := (singles.toList.map observe).map (Zai r)
    have only : ∀ v ∈ xs, Zao v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←ZbV]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := Zgh xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ Zaz xs + _
    rw [sz]
    omega
  omega
def ZaZ (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem Zek {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem Zia {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, Zap u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (ZaZ ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (ZaZ ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Zae.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := ZdY tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,Zek (hn.erase _) b,
        Zek hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [Zcz,Zcz,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := ZcD kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (ZaZ ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,ZcD ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (ZaZ ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := Zdc tail
    have len : (ZaZ ws a b d ka kb).length ≤ cap := by
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
theorem Zhy {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem Zhx {u T k S} (h : Zae u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (Zhy (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := Zdy h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := ZeP h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem Zge {u T ws k} (h : Zae u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply Zhx h rfl correct
  simp
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Zag u (roots.map observe) (Zai f (observe a))) ∧
    ¬Zao (Zai f (observe T)) ∧
    ∀ p bank, Zah u (roots.map observe) p bank → Zag u bank (Zai f (observe T)) → L ≤ p
def Zan (d a : Sig) := a &&& d
def Zaw (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := Zan d a
  m == zero || m == d || (pool.map (Zan d)).any (fun v => v==m) ||
    (u && (let c := Zan d (neg a); (pool.map (Zan d)).any (fun v => v==c)))
theorem Zeo {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : Zan d a = Zan d b) :
    Zai f (observe a) = Zai f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,Zan,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem Zd1 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : Zan d a = zero) : Zai f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,Zan,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem Zd7 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : Zan d a = d) : Zai f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,Zan,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def Zbv (u : Bool) (f : Row → Row) (bank : List (Zac Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Zag u bank (Zai f (observe a))
theorem ZbG {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : Zbv u f bank pool)
    (check : Zaw u d pool a = true) : Zag u bank (Zai f (observe a)) := by
  simp only [Zaw,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,Zd1 dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,Zd7 dom ho⟩)
  · exact Zeo dom he ▸ supplyB v hv
  · have h := Zc8 hu (Zeo dom he ▸ supplyB v hv)
    rw [ZeI] at h
    have e : inv (Zai f (inv (observe a))) = Zai f (observe a) := by
      funext r
      simp [inv,Zai]
    rwa [e] at h
abbrev Choice := Nat × Sig × Sig
def Zay (c : Choice) := bin c.1 c.2.1 c.2.2
def ZbN (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem Zhj {u d} (h : ZbN u d=true) : Zap u d := by
  simpa [ZbN,Zap] using h
def Zbw (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  ZbN u c.1 && (Zaw u d pool c.2.1 && Zaw u d pool c.2.2)
theorem Zd9 {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Zah u roots q bank) (hs : Zbv u f bank pool)
    (c : Choice) (valid : Zbw u d pool c = true) :
    ∃ next, Zah u roots (q+1) next ∧ Zbv u f next (Zay c :: pool) := by
  simp only [Zbw,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := Zd4 (Zhj valid.1) (ZbG dom hs valid.2.1)
    (ZbG dom hs valid.2.2)
  refine ⟨_,Zah.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [Zay,ZeH,ZdL,e]
    exact Or.inl (by simp)
  · exact ZdE _ (hs _ hm)
def Zby (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if Zbw u d pool c then Zby u d (Zay c::pool) cs else none
theorem ZdH {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Zah u roots q bank) (hs : Zbv u f bank pool)
    (cs : List Choice) {result} (ok : Zby u d pool cs = some result) :
    ∃ next, Zah u roots (q+cs.length) next ∧ Zbv u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [Zby] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := Zd9 dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def ZaG (d a : Sig) := Zan d a == zero || Zan d a == d
theorem ZdB {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (ZaG d) ≤ Zaz ((ws.map observe).map (Zai f)) := by
  classical
  induction ws with
  | nil => simp [Zaz]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,ZbM]
    cases h : ZaG d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Zao (Zai f (observe a)) := by
        have hh : Zan d a = zero ∨ Zan d a = d := by simpa only [ZaG,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,Zd1 dom hz⟩
        · exact ⟨true,Zd7 dom ho⟩
      simpa [Zaq,hc,Nat.add_comm] using Nat.succ_le_succ ih
def Zca (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (ZaG d)) && ws.all (Zaw u d pool)
theorem ZcO {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : Zby u d raw cs = some pool)
    (nd : ws.Nodup) (cut : Zca u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := ZdH dom (Zah.start (roots:=roots.map observe)) base cs built
  simp only [Zca,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : ZbE u bank ((ws.map observe).map (Zai f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact ZbG dom hs (List.all_eq_true.mp all a ha)
  have b := ZcK f (Zdm h ws nd rfl) nc hr coveredS lo
  have massLo := ZdB dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev ZaL := Sig × Sig × Row
def ZcE (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def Zee (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def Zdu (m : ZaL) (r : Row) : Row :=
  if bit r m.1 then ZcE m.2.2 r else if bit r m.2.1 then ZcE (Zee m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def Zdq (m : ZaL) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (Zee m.2.2).val) a)
theorem Zh6 (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (ZcE d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [ZcE,h,r.isLt]
theorem Zir (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem ZiG (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact Zir _ _ _
theorem Ziq (r : Row) (m : ZaL) (a : Sig) : bit r (Zdq m a) = bit (Zdu m r) a := by
  simp only [Zdq,ZiG,Zh6,Zdu]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def ZaI (ms : List ZaL) (r : Row) := ms.foldl (fun j m => Zdu m j) r
def ZaA (ms : List ZaL) (a : Sig) := ms.foldr Zdq a
theorem Zb3 (ms : List ZaL) (a : Sig) (r : Row) :
    bit r (ZaA ms a) = bit (ZaI ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (Ziq r m _).trans (ih _)
theorem ZcJ (ms : List ZaL) (a : Sig) : ZaA ms a = rename (ZaI ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (Zb3 ms a ⟨j,hj⟩).trans (Zbg _ _ ⟨j,hj⟩).symm
def Zdi (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem ZhB {u roots w} (ok : Zdi roots w = true) :
    Zag u (roots.map observe) (observe w) := by
  simp only [Zdi,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def Zbk (ms : List ZaL) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  ZaA ms T == G && raw.all (fun a => Zdi base (ZaA ms a))
theorem ZcX {u ms raw T base G} (ok : Zbk ms raw T base G = true) :
    rename (ZaI ms) T = G ∧
    ∀ a ∈ raw, Zag u (base.map observe) (observe (rename (ZaI ms) a)) := by
  simp only [Zbk,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,ZcJ] at ok
  exact ⟨ok.1,fun a ha => ZhB (ok.2 a ha)⟩
theorem Zid {u ms raw T base G L} (ok : Zbk ms raw T base G = true)
    (pT : proper T) (nT : ZaB T=true) (nR : raw.all ZaB=true) (pG : proper G)
    (hL : Zak u base G L) : Zak u raw T L := by
  obtain ⟨eq,supp⟩ := ZcX ok
  simpa using Zd0 pT nT nR pG (ZaI ms) eq supp ∅ (by simp) (by simp) L hL
theorem ZgM {u ms raw T base G L d} (ok : Zbk ms raw T base G = true)
    (all : ZaA ms d = one) (properG : proper G) (hL : Zak u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := ZcX ok
  have obs : Zai (ZaI ms) (observe T) = observe G :=
    (ZbV _ _).symm.trans (congrArg observe eq)
  refine ⟨ZaI ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←Zb3,all,bit_one]
  · intro a ha
    rw [←ZbV]
    exact supp a ha
  · rw [obs]
    exact ZcL properG
  · rw [obs]
    exact hL
def Zdp (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem ZgB {T roots a rs} (ok : Zdp T roots a rs = true) : Zcq T roots a := by
  simp only [Zdp,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def ZaR (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  ZaB T && raw.all ZaB && xs.all (fun a => Zdp T raw a.1 a.2)
theorem ZbH {T raw xs} (ok : ZaR T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Zcq T raw a := by
  simp only [ZaR,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ZgB (List.all_eq_true.mp ok.2 _ hm)
theorem ZaQ {T raw xs} (ok : ZaR T raw xs = true) :
    ZaB T=true ∧ raw.all ZaB=true := by
  simp only [ZaR,Bool.and_eq_true] at ok
  exact ok.1
theorem ZdZ {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : ZaR T raw xs = true) :
    Zak u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := Zco properT (ZaQ ok).1 (ZaQ ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := ZbH ok a ha
    exact Zci run raw a sub r s hd iso
  have bound := Zdc run
  omega
def Zc9 (ms : List ZaL) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  Zbk ms raw T base G && ZaR T raw xs &&
    xs.all (fun a => ZaA ms a.1 == zero || ZaA ms a.1 == one)
theorem ZiN {u ms T raw base G xs L} (ok : Zc9 ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Zak u base G L) :
    Zak u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [Zc9,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := ZcX ok.1.1
  apply Zd0 properT (ZaQ ok.1.2).1 (ZaQ ok.1.2).2 properG _ eq supp _ (ZbH ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,ZcJ] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def Zb7 (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (Zb7 m).map Prod.snd
def Zal (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [Za0] else vars m
def Zcd (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def Zaf (m : Nat) : Sig :=
  let x := Zcd m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def ZiU : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def ZiV : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def ZiW : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def Zba (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((ZiU (fixed &&& 7)*ZiV ((fixed >>> 3) &&& 7)*ZiW ((fixed >>> 6) &&& 7)) <<< o)
def Zdt (z o : Nat) : List ZaL :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : ZaL :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def ZdR (w : Bool) (mask : Nat) : List (Sig × Row × Row) :=
  (Zb7 mask).map fun (i,a) =>
    let r := if w && i==0 then 8 else if w && i==3 then 1 else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def ZbJ (m hints : Nat) : List (Sig × Row × Row) :=
  (Zb7 m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def ZaC (T : Sig) := T != zero && T != one
theorem ZaS (T : Sig) (h : ZaC T = true) : proper T := by
  simpa only [ZaC,proper,Bool.and_eq_true,bne_iff_ne] using h
def Zd3 (m hints L : Nat) :=
  let xs := ZbJ m hints
  ZaC (Zaf m) && ZaR (Zaf m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem ZiS {u m hints L} (h : Zd3 m hints L = true) :
    Zak u (vars m) (Zaf m) L := by
  simp only [Zd3,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (ZdZ (ZaS _ h.1.1) _ h.1.2 p bank hr ha)
abbrev Zbt := Nat × Nat × Nat × Nat × Nat
def Zds (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def Zbj (m : Nat) : Sig := Zaf m
def Za9 (m : Nat) (c : Zbt) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def ZbO (m : Nat) (c : Zbt) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := Zdt z o
  let raw := Za9 m c
  let free := Zds raw z o
  let G := ZaA ms (Zbj m)
  let xs := ZdR (free.testBit 9) s
  let count := (xs.map Prod.fst).toFinset.card
  ZaC G && Zbk ms (Zal raw) (Zbj m) (Zal free) G &&
    (ZaA ms (Zba z o)==one) &&
    (if q=0 then ZaR G (Zal free) xs && decide (L ≤ count-1)
     else ZaC (Zaf q) &&
       Zc9 (Zdt (Zds free q 0) 0) G (Zal free) (Zal q) (Zaf q) xs &&
       decide (L ≤ prior q+count))
theorem Zcr {u} {m : Nat} (c : Zbt) (prior : Nat → Nat)
    (valid : ∀ q, Zak u (Zal q) (Zaf q) (prior q))
    (ok : ZbO m c prior = true) : Slice u (Zal (Za9 m c)) (Zbj m) (Zba c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := Zdt z o
  let raw := Za9 m (z,o,q,s,L)
  let free := Zds raw z o
  let G := ZaA ms (Zbj m)
  let xs := ZdR (free.testBit 9) s
  change (((ZaC G && Zbk ms (Zal raw) (Zbj m) (Zal free) G) &&
    (ZaA ms (Zba z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply ZgM ok.1.1.2 ok.1.2 (ZaS _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [ZbO,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ZdZ (ZaS _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [ZbO,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ZiN hh.1.2 (ZaS _ ok.1.1.1) (ZaS _ hh.1.1) (valid q) p bank hr ha)
def Zdd (old rep : Nat) (swaps : List Nat) :=
  (ZaC (Zaf old) && ZaB (Zaf old) && (Zal old).all ZaB) && ZaC (Zaf rep) &&
    Zbk (swaps.map swapRows) (Zal old) (Zaf old) (Zal rep) (Zaf rep)
theorem ZhZ {u old rep L swaps} (ok : Zdd old rep swaps = true)
    (h : Zak u (Zal rep) (Zaf rep) L) : Zak u (Zal old) (Zaf old) L := by
  simp only [Zdd,Bool.and_eq_true] at ok
  exact Zid ok.2 (ZaS _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (ZaS _ ok.1.2) h
def ZcR (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem ZgZ {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Zak u (Zal e.1) (Zaf e.1) e.2) (q : Nat) :
    Zak u (Zal q) (Zaf q) (ZcR entries q) := by
  unfold ZcR
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev Zax := Sig × Nat × Nat × List Sig
def Zax.domain (c : Zax) : Sig := c.1
def Zax.bound (c : Zax) : Nat := c.2.1
def Zax.Zav (c : Zax) : Nat := c.2.2.1
def Zax.wires (c : Zax) : List Sig := c.2.2.2
def Zbh (u : Bool) (raw : List Sig) (T : Sig) (c : Zax) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Zac Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Zao (Zai f (observe T)) ∧
    (∀ q ws, Zah u (roots.map observe) q ws → Zag u ws (Zai f (observe T)) → c.bound ≤ q) ∧
    Zah u (roots.map observe) c.Zav bank ∧ Zbv u f bank c.wires ∧ True
theorem Zhl {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : Zby u d raw cs = some ws) : Zbh u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := ZdH dom (Zah.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [Zax.Zav] using hr,hs,trivial⟩
theorem ZgO {u raw T c} (valid : Zbh u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (Zav : Bool)
    (known : ∀ a ∈ rest, Zaw u c.domain c.wires a = true)
    (buy : if Zav then Zbw u c.domain c.wires choice = true
       else Zaw u c.domain c.wires (Zay choice) = true)
    (bound : k+c.Zav+Zav.toNat <
      c.bound+(Zay choice :: rest).countP (ZaG c.domain))
    (nd : (Zay choice :: rest).Nodup) :
    Impossible u T k (Zay choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := Zay choice::rest
  have done (n : Nat) (out : List (Zac Row)) (reach : Zah u (roots.map observe) n out)
      (zs : Zbv u f out (Zay choice::rest)) (le : n = c.Zav+Zav.toNat) : False := by
    have covered : ZbE u out ((ws.map observe).map (Zai f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := ZcK f (Zdm run ws nd rfl) nc reach covered lo
    have cm := ZdB dom ws
    change k+c.Zav+Zav.toNat < c.bound+ws.countP (ZaG c.domain) at bound
    omega
  cases Zav with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact ZbG dom hs buy
    · exact ZbG dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := Zd9 dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Zag u out (Zai f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact ZbG dom point (known _ hm)
def Zbd (u : Bool) (c : Zax) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := Zay op
  let extra := !(Zaw u c.domain c.wires z)
  ((k+c.Zav+extra.toNat < c.bound+(z::rest).countP (ZaG c.domain)) &&
    rest.all (Zaw u c.domain c.wires)) && (!extra || Zbw u c.domain c.wires op)
theorem ZeQ {u raw T c} (valid : Zbh u raw T c) {k rest op}
    (nd : (Zay op::rest).Nodup) (cut : Zbd u c k rest op = true) :
    Impossible u T k (Zay op::rest).toFinset := by
  let extra := !(Zaw u c.domain c.wires (Zay op))
  apply ZgO valid k rest op extra _ _ _ nd
  · simp only [Zbd,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [Zbd,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : Zaw u c.domain c.wires (Zay op) <;> simp_all [extra]
  · simp only [Zbd,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def ZcY (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option Zax :=
  (Zby u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem ZeX {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : ZcY u raw cs d L = some c) : Zbh u raw T c := by
  unfold ZcY at h
  cases he : Zby u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact Zhl slice cs he
abbrev Bits := BitVec 91
abbrev ZcB := Bits × Bits
abbrev Zab := Sig × ZcB
def ZaV {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem Za3 {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ZaV r v).getLsbD i.val = bit (r i) v := by
  simp only [ZaV,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def Za5 (r s : Fin 91 → Row) (a : Sig) : ZcB := (ZaV r a,ZaV s a)
def ZbI (T : Sig) (r s : Fin 91 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem ZiA {T r s} (h : ZbI T r s) : Sep T 91 r s (Za5 r s) := by
  exact ⟨h,fun a i => ⟨Za3 _ _ _,Za3 _ _ _⟩⟩
def ZaK (r s : Fin 91 → Row) (x : Zab) := x.2 = Za5 r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def Zat (d : Nat) (x y : Zab) : Zab := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem Zc4 {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ZaV r (bin d a b) = bv d (ZaV r a) (ZaV r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := Za3 r (bin d a b) ⟨j,hj⟩
  rw [Zbn,←Za3 r a ⟨j,hj⟩,←Za3 r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem ZdO {r s x y} (d) (hx : ZaK r s x) (hy : ZaK r s y) :
    ZaK r s (Zat d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [ZaK,Zat,Za5,Zc4,hx,hy]
def Zbs : Zab := (zero,0,0)
theorem Ze9 (r s) : ZaK r s Zbs := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ZaV r zero).getLsbD j
    rw [show (ZaV r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from Za3 _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ZaV s zero).getLsbD j
    rw [show (ZaV s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from Za3 _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem ZdP {r s ws} (all : ∀ v ∈ ws, ZaK r s v) (i : Nat) :
    ZaK r s (List.getD ws i Zbs) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact Ze9 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def Zc0 (n : Nat) (bits : Nat) (ws : List Zab) : List Zab :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) Zbs
    let b := ws.getD ((bits >>> 4) &&& 15) Zbs
    Zc0 k (bits >>> 10) (ws++[Zat ((bits >>> 8) &&& 3) a b])
theorem Zfu (n bits) (ws) (r s) (base : ∀ v ∈ ws, ZaK r s v) :
    ∀ v ∈ Zc0 n bits ws, ZaK r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact ZdO _ (ZdP base _) (ZdP base _)
def ZaJ (ZaE : Nat → Bits) (i : Fin 91) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (ZaE j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem Zhm : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem Zhn : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem Zho : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem Zhp : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem Zhq : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem Zhr : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem Zhs : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem Zht : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem Zhu : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem ZcS : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact Zhm r
  · exact Zhn r
  · exact Zho r
  · exact Zhp r
  · exact Zhq r
  · exact Zhr r
  · exact Zhs r
  · exact Zht r
  · exact Zhu r
theorem Zc7 (ZaE : Nat → Bits) (i : Fin 91) (j : Fin 9) :
    bit (ZaJ ZaE i) (inputs.getD j.val zero) = (ZaE j.val).getLsbD i.val := by
  rw [ZcS]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (ZaE h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def ZeC (m : Nat) (p q : Nat → Bits) : List Zab :=
  (Zb7 m).map (fun (j,a) => (a,p j,q j))
theorem Zgz {m j a} (h : (j,a) ∈ Zb7 m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem Zg7 (m) (p q : Nat → Bits) :
    ∀ a ∈ ZeC m p q, ZaK (ZaJ p) (ZaJ q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := Zgz hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (Zc7 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (Za3 _ _ ⟨i,hi⟩).symm
  · exact (Zc7 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (Za3 _ _ ⟨i,hi⟩).symm
def Zdl (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem ZhM (m : Nat) (v : Nat → Bits) (i : Fin 91) (j : Fin 9) :
    bit (ZaJ v i) (Zcd m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [Zcd,hh] using Zc7 v i j
  · simp [Zcd,hh,bit_zero]
theorem Zg1 (m : Nat) (v : Nat → Bits) (i : Fin 91) :
    bit (ZaJ v i) (Zaf m) = (Zdl m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (Zcd m j).getLsbD (ZaJ v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := ZhM m v i ⟨j,hj⟩
  simp only [bit,Zaf,Zdl,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits
def ZaO (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def Zau (d : Bool) (v : List Zab) : Cov :=
  v.foldr (fun a c => ZaO (column d a.2) c) (0,0,0)
def Zbb (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def ZbQ (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem ZiH (c : Cov) (a : Bits) : Zbb (ZaO a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Zbb,ZaO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem ZiI (c : Cov) (a b : Bits) : ZbQ (ZaO a (ZaO b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ZbQ,ZaO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem Zin (c : Cov) (a b : Bits) : ZaO a (ZaO b c)=ZaO b (ZaO a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ZaO,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [ZaO,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem Zew (d : Bool) {l r : List Zab} (h : l.Perm r) : Zau d l=Zau d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (ZaO (column d a.2)) ih
  | swap a b t => exact Zin _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem Zit (d : Bool) (v : List Zab) {r s} (good : ∀ a ∈ v, ZaK r s a) :
    (Zau d v).1 = covered d (Za5 r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (Zau d v).1) = column d (Za5 r s a.1) ||| _
    rw [show a.2=Za5 r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def ZaU (ws : List Zab) (a : Zab) (keep : Bool) :=
  if keep then ws else ws.erase a
def ZaD (ws : List Zab) (a b : Zab) (ka kb : Bool) :=
  ZaU (ZaU ws a ka) b kb
theorem ZcV {ws : List Zab} (a : Zab) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem Zei {ws : List Zab} (d : Bool) (a : Zab) (ha : a ∈ ws) (keep : Bool) :
    (Zau d (ZaU ws a keep)).1 =
      (if keep then (Zau d ws).1 else Zbb (Zau d ws) (column d a.2)) := by
  cases keep
  · change (Zau d (ws.erase a)).1 = Zbb (Zau d ws) _
    rw [Zew d (ZcV a ha)]
    exact (ZiH _ _).symm
  · rfl
theorem Zhz {ws : List Zab} (a b : Zab) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (ZcV a ha).trans (List.Perm.cons _ (ZcV b hm))
theorem Zh8 {ws : List Zab} (d : Bool) (a b : Zab) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (Zau d (ZaD ws a b ka kb)).1 =
      (if ka then (if kb then (Zau d ws).1 else Zbb (Zau d ws) (column d b.2))
       else if kb then Zbb (Zau d ws) (column d a.2)
       else ZbQ (Zau d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (Zau d ((ws.erase a).erase b)).1 = ZbQ (Zau d ws) _ _
    rw [Zew d (Zhz a b ha hb ne)]
    exact (ZiI _ _ _).symm
  · exact Zei d a ha false
  · exact Zei d b hb false
  · rfl
def Zcv (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem ZdC {xs ys} (h : Zcv xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [Zcv,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def ZiL (v : Sig) :=
  let n := v.toNat  %  2305843009213693951
  (n*(n+971))  %  2305843009213693951
def ZiT (xs : List Sig) := xs.foldl (fun v x => v+ZiL x) 0
def ZbZ (u : Bool) (pools : List Zax) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := Zay op::rest
  (links (ZiT ws)).any (Zcv ws) || pools.any (fun p => Zbd u p k rest op)
theorem Ze8 {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, Zbh u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (Zay op :: rest).Nodup)
    (h : ZbZ u pools links k rest op = true) :
    Impossible u T k (Zay op :: rest).toFinset := by
  simp only [ZbZ,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [ZdC ok]
    exact lValid _ _ hx
  · exact ZeQ (pValid _ hp) nd ok
abbrev ZeD := Cov × Bool
def Zcc (u : Bool) (ws : List Zab) : ZeD := (Zau (!u) ws,u)
def ZbD (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else Zbb v b) else if kb then Zbb v a else ZbQ v a b
theorem Zc1 (ws : List Zab) (a : Zab) (k : Bool) : (ZaU ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem Zdj (ws : List Zab) (a b : Zab) (ka kb : Bool) :
    (ZaD ws a b ka kb).Sublist ws := (Zc1 _ _ _).trans (Zc1 _ _ _)
theorem Zez (ws : List Zab) (a b : Zab) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (ZaD ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [ZaD,ZaU,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def Za6 (op : Nat) (a b : Zab) : Choice := (op,a.1,b.1)
def ZbY (s : BitVec 6) : Nat :=
  let b := s.getLsbD
  let a0 := b 0 != b 1
  let a1 := b 3 != b 4
  let c0 := b 0 != b 2
  let c1 := b 3 != b 5
  if !(a0 || a1 || c0 || c1) then 0
  else if !(a0 || a1) || !(c0 || c1) then 1
  else if a0 && a1 && c0 && c1 && (b 0 != b 3) then 3 else 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zd5 : ∀ (d : Fin 4) (a b : BitVec 6),
    ZbY (bv d.val a b) ≤ ZbY a+ZbY b := by decide +kernel
theorem ZcU {u T k S} (run : Zae u T k S) : S.card≤k+1 := by
  induction run using Zae.ind with
  | stop => simp
  | @binary k U a b d hd _ _ ne fresh _ ih =>
    have free : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem free] at ih
    have h₁ := Finset.card_insert_le (a:=a) (s:=insert b U)
    have h₂ := Finset.card_insert_le (a:=b) (s:=U)
    omega
theorem Zec {u T k S} (run : Zae u T k S) (w : Sig → Nat)
    (sub : ∀ d a b, Zap u d → w (bin d a b) ≤ w a+w b) :
    S.card=k+1 → w T ≤ ∑ x ∈ S, w x := by
  induction run using Zae.ind with
  | stop => simp
  | @binary k U a b d hd _ _ ne fresh tail ih =>
    intro sat
    have free : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := ZcU tail
    rw [Finset.card_insert_of_notMem free] at cap
    have h₁ := Finset.card_insert_le (a:=a) (s:=insert b U)
    have h₂ := Finset.card_insert_le (a:=b) (s:=U)
    have aN : a∉insert b U := by
      intro ha
      rw [Finset.insert_eq_of_mem ha] at sat
      omega
    have bN : b∉U := by
      intro hb
      rw [Finset.insert_eq_of_mem hb] at sat
      have h := Finset.card_insert_le (a:=a) (s:=U)
      omega
    rw [Finset.card_insert_of_notMem aN,Finset.card_insert_of_notMem bN] at sat
    have n : (insert (bin d a b) U).card=k+1 := by rw [Finset.card_insert_of_notMem free]; omega
    have h := ih n
    rw [Finset.sum_insert free] at h
    rw [Finset.sum_insert aN,Finset.sum_insert bN]
    have hb := sub d a b hd
    omega
def ZaX (r : Fin 6 → Row) (v : Sig) : Nat :=
  let p := bit (r 0) v
  let q := bit (r 3) v
  let a0 := p != bit (r 1) v
  let a1 := q != bit (r 4) v
  let c0 := p != bit (r 2) v
  let c1 := q != bit (r 5) v
  if !(a0 || a1 || c0 || c1) then 0
  else if !(a0 || a1) || !(c0 || c1) then 1
  else if a0 && a1 && c0 && c1 && (p != q) then 3 else 2
theorem ZdN (r : Fin 6 → Row) (v : Sig) : ZaX r v=ZbY (ZaV r v) := by
  have read (i : Fin 6) := Za3 r v i
  simp only [ZbY,ZaX]
  rw [←read 0,←read 1,←read 2,←read 3,←read 4,←read 5]
  rfl
theorem Zhv (r : Fin 6 → Row) {u T k S}
    (n : S.card=k+1) (more : (∑ x ∈ S, ZaX r x) < ZaX r T) :
    Impossible u T k S := by
  intro t ht run
  have size := ZcU run
  have same : t=k := by omega
  subst t
  apply Nat.not_le_of_gt more (Zec run (ZaX r) (fun d a b hd => ?_) n)
  have lt : d<4 := by rcases hd with h|h <;> omega
  simp only [ZdN]
  rw [Zc4]
  exact Zd5 ⟨d,lt⟩ _ _
abbrev Zar := Nat × Nat × List Zab × ZeD × List Zax × (Nat → List (List Sig)) × Bool
def Zbl (c : Zar) (op : Nat) (a b z : Zab) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links,flag) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else if (len==cap) && flag then true else
    let d := !cov.2
    let rs := ZbD cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 91 then true else
    if !ZaC z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (ZaD ws a b ka kb).map Prod.fst
      ZbZ cov.2 pools links (cap-1) rest (Za6 op a b)
def ZaH (ws : List Zab) (op : Nat) (a b : Zab) (ka kb : Bool) :=
  (Zat op a b).1 :: (ZaD ws a b ka kb).map Prod.fst
def Zcm (code : Nat) (i : Fin 6) : Row := Fin.ofNat 512 ((code >>> (9*i.val)) &&& 511)
def Za7 (codes : List Nat) (v : Sig) := (codes.map (fun c => ZaX (Zcm c) v)).sum
theorem ZdD (codes : List Nat) {d : Nat} (hd : d<4) (a b : Sig) :
    Za7 codes (bin d a b)≤Za7 codes a+Za7 codes b := by
  induction codes with
  | nil => simp [Za7]
  | cons c cs ih =>
    have one : ZaX (Zcm c) (bin d a b) ≤
        ZaX (Zcm c) a+ZaX (Zcm c) b := by
      simp only [ZdN]
      rw [Zc4]
      exact Zd5 ⟨d,hd⟩ _ _
    simp only [Za7,List.map_cons,List.sum_cons] at ih ⊢
    omega
def Zcf (codes : List Nat) (T : Sig) (cap : Nat) (ws : List Sig) :=
  !codes.isEmpty && ws.all (fun v => Za7 codes v ≤ 1) &&
    decide ((ws.map (Za7 codes)).sum + (cap+1-ws.length) < Za7 codes T)
theorem ZdJ (w : Sig → Nat) {xs : List Sig} (nd : xs.Nodup) :
    (∑ x ∈ xs.toFinset, w x)=(xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hp := List.nodup_cons.mp nd
    have no : x∉xs.toFinset := by simpa using hp.1
    simp [no,ih hp.2]
theorem Zc2 (f : Zab → Nat) {xs : List Zab} {x : Zab} (mem : x∈xs) :
    ((xs.erase x).map f).sum + f x = (xs.map f).sum := by
  have eq := (List.Perm.map f (List.perm_cons_erase mem)).sum_eq
  simpa [Nat.add_comm] using eq.symm
theorem Ziy (f : Zab → Nat) {xs : List Zab} {a b : Zab} (ha : a∈xs) (hb : b∈xs)
    (ne : a≠b) (ka kb : Bool) (ba : f a≤1) (bb : f b≤1) :
    ((ZaD xs a b ka kb).map f).sum+f a+f b ≤ (xs.map f).sum+ka.toNat+kb.toNat := by
  have ba' : b∈xs.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e₁ := Zc2 f ha
  have e₂ := Zc2 f hb
  have e₃ := Zc2 f ba'
  cases ka <;> cases kb <;> simp [ZaD,ZaU] <;> omega
theorem Zgj {codes u T cap ws a b d ka kb}
    (ready : Zcf codes T cap (ws.map Prod.fst)=true)
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (hd : d<4)
    (fresh : (Zat d a b).1∉ws.map Prod.fst) (pos : 0<cap)
    (len : (ZaH ws d a b ka kb).length=cap) :
    Impossible u T (cap-1) (ZaH ws d a b ka kb).toFinset := by
  let w := Za7 codes
  let f := fun v : Zab => w v.1
  have sub : ∀ op a b, Zap u op → w (bin op a b) ≤ w a+w b := by
    intro op a b ok
    apply ZdD codes _ a b
    rcases ok with h|h <;> omega
  have ab : a≠b := fun h => ne (congrArg Prod.fst h)
  have inc := (Zdj ws a b ka kb).map Prod.fst
  have ndc : (ZaH ws d a b ka kb).Nodup :=
    List.nodup_cons.mpr ⟨fun mem => fresh (inc.subset mem),nd.sublist inc⟩
  have minlen : 2≤ws.length := by
    cases ws with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons => simp
  have len' := Zez ws a b ka kb ha hb ab
  simp only [ZaH,List.length_map,List.length_cons] at len
  have number : ka.toNat+kb.toNat=cap+1-ws.length := by
    cases ka <;> cases kb <;> simp_all <;> omega
  simp only [Zcf,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ready
  have aa : f a≤1 := ready.1.2 _ (List.mem_map_of_mem ha)
  have bb : f b≤1 := ready.1.2 _ (List.mem_map_of_mem hb)
  have raw := Ziy f ha hb ab ka kb aa bb
  have Zaq := ZdD codes hd a.1 b.1
  have start : (ws.map f).sum+(cap+1-ws.length)<w T := by
    simpa [w,f,Function.comp_def] using ready.2
  have smaller : ((ZaH ws d a b ka kb).map w).sum<w T := by
    simp only [ZaH,Zat,List.map_cons,List.map_map,List.sum_cons,Function.comp_def]
    change w (bin d a.1 b.1)+((ZaD ws a b ka kb).map f).sum<w T
    change w (bin d a.1 b.1)≤f a+f b at Zaq
    omega
  intro t ht live
  have size:=ZcU live
  rw [List.toFinset_card_of_nodup ndc] at size
  have actual : (ZaH ws d a b ka kb).length=cap := by simpa [ZaH] using len
  have sat : (ZaH ws d a b ka kb).toFinset.card=t+1 := by
    rw [List.toFinset_card_of_nodup ndc]
    omega
  have h:=Zec live w sub sat
  rw [ZdJ w ndc] at h
  omega
theorem Zgf {u raw T r s ws pools links cap a b op ka kb flag}
    (pairs : ZbI T r s) (faith : ∀ w ∈ ws, ZaK r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, Zbh u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (shortcut : flag=true → (ZaH ws op a b ka kb).length=cap →
      Impossible u T (cap-1) (ZaH ws op a b ka kb).toFinset)
    (pro : proper (Zat op a b).1) (fresh : (Zat op a b).1 ∉ ws.map Prod.fst)
    (test : Zbl (cap,ws.length,ws,Zcc u ws,pools,links,flag) op a b (Zat op a b) ka kb = true) :
    Impossible u T (cap-1) (ZaH ws op a b ka kb).toFinset := by
  let z := Zat op a b
  let rest := ZaD ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := Zdj _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : ZaC z.1 = true := by simpa [ZaC,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,Zez _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := Zdc h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold Zbl at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  by_cases fast : ((child.length==cap) && flag)=true
  · simp only [Bool.and_eq_true,beq_iff_eq] at fast
    exact shortcut fast.2 fast.1 k hk h
  rw [if_neg fast] at test
  have sep := Zge h (ZiA pairs)
  let d := !u
  have g : (Zau d rest).1 = covered d (Za5 r s) (rest.map Prod.fst) :=
    Zit _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (Zau d rest).1 = ZbD (Zau d ws) (column d a.2) (column d b.2) ka kb :=
    Zh8 d a b ha hb ne ka kb
  have hf := ZdO op (faith _ ha) (faith _ hb)
  change column d (Za5 r s z.1) ||| covered d (Za5 r s) (rest.map Prod.fst) = _ at sep
  change z.2 = Za5 r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((ZbD (Zau (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 91) = false := by
    simpa using sep
  change (if (ZbD (Zau (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 91 then true else if !ZaC z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact Ze8 (op:=Za6 op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def ZbB (ctx : Zar) (a b : Zab) (op : Nat) :=
  let z := Zat op a b
  let attempt := Zbl ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def ZbF (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem Zeq {u d} (h : Zap u d) : d ∈ ZbF u := by
  rcases Za1 h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [ZbF]
  · cases u <;> simp [ZbF]
  · simp [ZbF]
  · simp [ZbF]
def Zdv (ctx : Zar) (a : Zab) (bs : List Zab) :=
    bs.all (fun b => (ZbF ctx.2.2.2.1.2).all (ZbB ctx a b))
def Zbc (ctx : Zar) : List Zab → Bool
  | [] => true
  | a::bs => Zdv ctx a bs && Zbc ctx bs
theorem ZhL {ctx ws} (h : Zbc ctx ws=true) {a b : Zab} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, Zap ctx.2.2.2.1.2 d → ZbB ctx a b d=true) ∨
      (∀ d, Zap ctx.2.2.2.1.2 d → ZbB ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [Zbc,Bool.and_eq_true,Zdv,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (Zeq hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (Zeq hd)
      · exact ih h.2 haTail hbTail
theorem ZhH {ctx a b d} (h : ZbB ctx a b d = true) (ka kb : Bool) :
    Zbl ctx d a b (Zat d a b) ka kb = true := by
  simp only [ZbB,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem Zey {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem Zd8 {v : List Zab} (nd : v.Nodup) (a w : Zab) (k : Bool) :
    w ∈ ZaU v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [ZaU,nd.mem_erase_iff,and_comm]
theorem ZdS {ws : List Zab} (nd : (ws.map Prod.fst).Nodup) {a b : Zab}
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
theorem ZhU {ws : List Zab} (nd : (ws.map Prod.fst).Nodup) {a b : Zab}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (ZaD ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (Zc1 ws a ka)
  simp only [ZaD,List.mem_map,Zd8 wn,Zd8 dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (ZdS nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (ZdS nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem Zg0 {ws : List Zab} (nd : (ws.map Prod.fst).Nodup) {a b : Zab}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (ZaH ws d a b ka kb).toFinset =
      (ZaZ (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [ZaH,ZaZ,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    ZhU nd ha hb,Zey,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,Zat]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem ZgD {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : Zap u d) (ka kb : Bool) :
    (ZaZ v a b d ka kb).toFinset = (ZaZ v b a (Zbo d) kb ka).toFinset := by
  ext x
  simp only [ZaZ,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    Zey,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,Zdf hd a b]
  tauto
theorem ZhW {u raw T r s ws pools links cap flag}
    (pairs : ZbI T r s) (faith : ∀ w ∈ ws, ZaK r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, Zbh u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (shortcut : ∀ a∈ws, ∀ b∈ws, ∀ d, Zap u d → ∀ ka kb,
      a.1≠b.1 → (Zat d a b).1 ∉ ws.map Prod.fst → flag=true → (ZaH ws d a b ka kb).length=cap →
      Impossible u T (cap-1) (ZaH ws d a b ka kb).toFinset)
    (checks : Zbc (cap,ws.length,ws,Zcc u ws,pools,links,flag) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply Zia nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Zab) (d : Nat) (opOK : Zap u d) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : ZbB (cap,ws.length,ws,Zcc u ws,pools,links,flag) a b d = true) :
      Impossible u T (cap-1) (ZaZ (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←Zg0 nd aa bb ne']
    exact Zgf pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      (shortcut a aa b bb d opOK ka kb ne' fr) pr fr (ZhH test ka kb)
  rcases ZhL checks haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb pro fresh (hh d hd)
  · rw [ZgD _ nd _ _ d hd]
    exact one b a (Zbo d) (flip_flip hd).1 hbW haW (Ne.symm ne) kb ka (Zdf hd a.1 b.1 ▸ pro)
      (Zdf hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
theorem ZgW (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← Zd6]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (ZcS i r).symm.trans ((h _ hm).trans (ZcS i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def ZcZ (p q : List ZaL) := inputs.all (fun a => ZaA p (ZaA q a) == a)
theorem ZdW {p q} (h : ZcZ p q = true) (r : Row) :
    ZaI q (ZaI p r) = r := by
  apply ZgW
  intro a ha
  rw [←Zb3,←Zb3]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def ZbS (T : Sig) (p : List ZaL) :=
  (ZaA p T == T) && ZcZ p p.reverse && ZcZ p.reverse p
theorem Zfw {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List ZaL) (ok : ZbS T p = true) : Impossible u T n (ws.map (ZaA p.reverse)).toFinset := by
  simp only [ZbS,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (ZaI p) := fun r => ⟨ZaI p.reverse r,ZdW ok.2 r⟩
  intro k hk h
  have run := ZhC h (ZaI p) onto
  have goal : rename (ZaI p) T = T := (ZcJ p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (ZaI p) (ZaA p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [Zbg,Zb3,ZdW ok.1.2]
  have back : (ws.map (ZaA p.reverse)).toFinset.image (rename (ZaI p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev Zbm := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def Zg2 : Zbm := (0,0,0,0,0,0,0,0,fun _ => 0)
def Zaa (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos  %  8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def Zja (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h  %  nb
  let sh := Zaa data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := Zaa data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev Zad := Nat × Nat × (Nat → Bits × Bits) × List Zbt × List (List Nat) ×
  (Nat → Zbm) × (Nat → Nat → Option (Nat × Nat))
def Zad.mask (g : Zad) : Nat := g.1
def Zad.mode (g : Zad) : Bool := !(g.1.testBit 10)
def Zad.cap (g : Zad) : Nat := g.2.1
def Zad.samples (g : Zad) : Nat → Bits × Bits := g.2.2.1
def Zad.ZaE (g : Zad) : List Zbt := g.2.2.2.1
def Zad.ZbT (g : Zad) : List (List Nat) := g.2.2.2.2.1
def Zad.levels (g : Zad) : Nat → Zbm := g.2.2.2.2.2.1
def Zad.index (g : Zad) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def Zcb (g : Zad) :=
  let ws := ZeC g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem ZgA (g : Zad) : ∀ a ∈ Zcb g,
    ZaK (ZaJ fun j => (g.samples j).1) (ZaJ fun j => (g.samples j).2) a := by
  exact Zg7 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def Zaj (g : Zad) := Zbj g.mask
def ZbX (m : Nat) (v : Nat → Bits) :=
  Zdl m v
theorem Zh7 (m : Nat) (v : Nat → Bits) (i : Fin 91) :
    bit (ZaJ v i) (Zbj m) = (ZbX m v).getLsbD i.val := by
  exact Zg1 m v i
theorem ZdT {m : Nat} {p q : Nat → Bits}
    (hp : ZbX m p = BitVec.allOnes 91) (hq : ZbX m q = 0) :
    ZbI (Zbj m) (ZaJ p) (ZaJ q) := by
  intro i
  simp only [Zh7,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def Zb1 {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::Zb1 (bits >>> 1) ws else Zb1 (bits >>> 1) ws
theorem Zgy {α : Type} (bits : Nat) (ws : List α) : (Zb1 bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold Zb1
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def Zi7 (_g : Zad) (depth : Nat) := depth
def ZdM (iw ow : Nat) : Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | n+1,packed,i =>
    if packed &&& ((1 <<< iw)-1) = i then
      some ((packed >>> iw) &&& ((1 <<< ow)-1))
    else ZdM iw ow n (packed >>> (iw+ow)) i
def Zdh (g : Zad) (k : Nat) : Nat :=
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  (if depth=0 then 0 else pw+10)+(Zcb g).length+depth
def Zdr (g : Zad) (k i : Nat) : Nat :=
  let (_,_,_,_,_,_,_,_,data) := g.levels k
  Zaa data (i*Zdh g k) (Zdh g k)
def Zeh (g : Zad) (k i : Nat) : Nat :=
  let (_,_,_,pw,_,_,_,_,_) := g.levels k
  Zdr g k i &&& ((1 <<< pw)-1)
def ZeL (g : Zad) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,k,i =>
    let (_,depth,_,pw,iw,_,ec,ex,_) := g.levels k
    match ZdM iw (10*depth) ec ex i with
    | some ops => ops
    | none =>
      ZeL g fuel (k+1) (Zeh g k i) |||
        (((Zdr g k i >>> pw) &&& 1023) <<< (10*(depth-1)))
def Zdn (g : Zad) (k i : Nat) : Nat × List Zab × List Zab :=
  let raw := Zcb g
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  let len := if depth=0 then 0 else pw+10
  let recp := Zdr g k i
  let ops := ZeL g depth k i
  let bank := Zc0 depth ops raw
  (ops,bank,Zb1 (recp >>> len) bank)
def Zel (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def ZdU (bank : List Zab) (ops Zav : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := ZdU bank (ops >>> 10) (Zav >>> 1) n
    if Zav &&& 1 == 0 then more else
      (Zel ops 8 2,(bank.getD (ops &&& 15) Zbs).1,
        (bank.getD (Zel ops 4 4) Zbs).1) :: more
def buildRule (g : Zad) (ops d : Nat) (bank : List Zab) (idx Zav : Nat) : Option Zax :=
  (g.ZaE[idx]?).bind fun ci =>
    ZcY g.mode (Zal (Za9 g.mask ci)) (ZdU bank ops Zav d) (Zba ci.1 ci.2.1) ci.2.2.2.2
theorem Zft (g : Zad)
    (ZaE : ∀ ci ∈ g.ZaE, Slice g.mode (Zal (Za9 g.mask ci)) (Zaj g) (Zba ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank Zav c} (h : buildRule g ops depth bank i Zav = some c) :
    Zbh g.mode (vars g.mask) (Zaj g) c := by
  unfold buildRule at h
  cases e : g.ZaE[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply ZeX _ h
    exact ZaE ci (List.mem_of_getElem? e)
def Zex (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := Zaa data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: Zex data w v n (pos+w+v)
def ZdV (g : Zad) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,ow,_,_,data) := g.levels k
  let start := num*Zdh g k
  let pos := start+num*ow+Zaa data (start+i*ow) ow
  let nr := Zaa data pos 5
  Zex data cw depth nr (pos+5)
def Zdg (g : Zad) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,k,i => ZdV g k i
  | fuel+1,k,i =>
    let parent := Zeh g k i
    let fresh := ZdV g k i
    if parent < (g.levels (k+1)).1 then
      fresh ++ Zdg g fuel (k+1) parent
    else fresh
def ZbA (g : Zad) (k i : Nat) := (Zdn g k i).2.2.map Prod.fst
def Zck (g : Zad) (k i : Nat) : Bool :=
  let z := 32*g.mask+k
  let bits : Nat := (if z<53221 then (if z<12264 then (if z<6055 then (if z<997 then (if z<996 then 0x0 else 0x1) else (if z<6053 then 0x0 else (if z<6054 then 0x1 else 0x3))) else (if z<6119 then (if z<6118 then 0x0 else 0xfff) else (if z<6120 then 0xf9ff3f5e5f3b6e72faebeafff8000 else (if z<12263 then 0x0 else 0x3)))) else (if z<16362 then (if z<12266 then (if z<12265 then 0xf700000000000 else 0x881800000000000000000000000000000) else (if z<16360 then 0x0 else (if z<16361 then 0x3f else 0x3ffffffffff0000))) else (if z<49129 then (if z<16363 then 0xf7dabf5ffffdffff800000000000000000000000000000000000 else (if z<49128 then 0x0 else 0x1)) else (if z<49130 then 0x1fa else (if z<49131 then 0x8d213000 else 0x0))))) else (if z<61417 then (if z<60903 then (if z<58854 then (if z<53223 then 0x1 else 0x0) else (if z<58855 then 0x3 else (if z<60902 then 0x0 else 0x40))) else (if z<61414 then (if z<60904 then 0x2382c3e80 else (if z<60905 then 0x104021800248100000000000 else 0x0)) else (if z<61415 then 0x4 else (if z<61416 then 0x73fffec0 else 0xac657e9f3789bbf79c9bfd58000000000000)))) else (if z<65002 then (if z<64999 then (if z<61418 then 0x10834aa80688eae7652a0861e60416b61185d49332816b40034402e1d310486ee3173729605c146994c0000000000000000000000000000000000000000000000000000 else 0x0) else (if z<65000 then 0x1 else (if z<65001 then 0x1fffff0 else 0x56efcffbfffffefff8000000000000000000000))) else (if z<65514 then (if z<65512 then 0x0 else (if z<65513 then 0x3e1fc else 0x2fbf7eeffdfffbd3fbff1ffffff800000000000000)) else (if z<65515 then 0x3deffbf7af69bcebcbffcf3efffdfdffddff3fffffb277edf7ffd7fffacdef57fdffef7feffb3bfbbf7efeeffbff53f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if z<65516 then 0x6715d046453c72c5e59799b0d5c07678347b96444cf7ca58fd3512d64be264040f703d29211e24acc12d11b230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x0))))))
  bits.testBit i
def ZaM (g : Zad) (k i : Nat) : List Sig :=
  if Zck g k i then [] else ZbA g k i
theorem Zej {u T cap} : Impossible u T cap ∅ := by
  intro t _
  cases t with
  | zero => simp [Zae]
  | succ n =>
    rintro ⟨U,a,b,d,_,eq,_⟩
    have h : a ∈ (∅ : Finset Sig) := eq.symm ▸ Finset.mem_insert_self a (insert b U)
    exact Finset.notMem_empty _ h
def Zb6 (g : Zad) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.ZbT[pair.2]?).map fun perm => (ZaM g k pair.1).map (ZaA (perm.map swapRows).reverse)
theorem Zfv (g : Zad) (k : Nat)
    (names : ∀ x ∈ g.ZbT, ZbS (Zaj g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (Zaj g) k (ZaM g k i).toFinset)
    {pair out} (h : Zb6 g k pair = some out) :
    Impossible g.mode (Zaj g) k out.toFinset := by
  unfold Zb6 at h
  split at h
  · contradiction
  next valid =>
    cases e : g.ZbT[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact Zfw (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def Zhc (i : Nat) : Nat := (if i<2 then (if i<1 then 0x211221d0881100840945824041403055069141024060d834320404830150681410100c0541a050404030150601410100c0441a01040141985c460410040605834120401018160d00810000c0541a0502a050aa8160a00a8142a884c2202a050aa0130800a2412cd22b14028904b168ac500a2412ac12290028904aaa45a280a2412a890682028904aa049a000a2412a812280028904aa041a000a2410cd22b1402890431c8ac500a2410c5a2b140289019348ac500a240648a070202890192201c080a2010cc22b14028502a78149a00a140a8e05228028502a1a058280a140a868060a028502a18058200a0906e270b81028241b88c2e040a0906e230980028241b83c2e040a0906c2a0d02028241a984a2400a0906a610880028241a83c2e040a09068e86c32028241a3a130c80a09068e82c32028241a1a1b0c80a09068682c12028241a1a030480a09068680c02028241a180b0480a09068602c10028241989c2e040a09066270981028241988c2e040a09066230980028241983c2e040a090620f0b81028240789c2e040a08066230b81028201883c2e040890422c84c320220108e8161a00880422c84c320220108aa170a80880422a058280220108a2130880880422880c22020241a1a0b0480809066270981020201989c2e040808066230981020201988c260008080642a0d0202020190883408080806261289002020183a1b0c80808060686c3202020181a0b0480808060682c1002020181a0b0080808060680c0202020180b030080800422884c2201180854181c04044021706078101100855483450044021516070501100854483410044021512070401100854185c04044021506070101100854101c040424031b0946801024160d018040405030582212010140c0e058280404036170781010100cc4613000404031b0d468010100c6c251a0040403184d468010100c4c251200404030341609010100c0d018240404030309408010100c0c058240404030301608010040669351a00401018a4d46801000854181c04029008a68168a00a0806160a850022810aa9068a00880433088c40022010ac122900088042aa45a28022010a89068a0088042a241a08021408868160a008402278149a00210088e0522800840221a05828021008868160800840221a01828021008860160800828066a349a0020a019a8c26800828062c129a0020a018582a140080807168ac500202019a8d26800808066a349200202019a85268008080662349a0020201988c26800808066230980020201948a25000808065228840020201948a2000080806361a8900202018984a240080806160a8500202018582a100080806160a8100202018582a0000808060e0681002020181c1805008080606128900200088e8160a00800221a058280000000000000 else 0x9351a04424131a49468110904c61351a04424131849468110904c4c351a04424131309448110904c0d058244424130340609110904c0c058244424130301608110904c0c0182044240331184c0110900c6c351a04424031b09468110900c69351a0442403184d468110900c4c351a04424030341609110100c4c351a0410090629548a10402418854220410090514ca4510402414132914410090504c245104024141309044100904245209104024109108244080506524914102014184924104080503144a451020140c5109144080502144a0510201408510814400110a0d548a0a24128b21b0c828904a28058200a0142a0b0d02828050a82c32090a004220b0d0282414031309448090500c0d0582420080c0342a050540a1544060101502854c874320540a1520160801502844c874320540817321d0c8150201cc874320540806161d0c81500844c07432054021124160901468255160f05051a09544834101448255160f0505120954581c141448255120d0405120954181c041448255020d0005120954081c0014320d0541a0505048351184c0414120d0541a050504834150601414120d0441a01050403415068141409059a4d468050241661351a0140905930d468050241629351a01409058944c24050240669351a01409019a4c468050240661351a0140901930d468050240629351a0140501984d46804c08062612890130201818182404c06134526914130184d14984504c06134426110130184c90782404c06132416090130184c88742204c0613201e080130184c80702004c06114526914130184514984504c06114426914130184510984404c061124160901301841949a4504c0610472691413018401c9a4504c040745269141300845149a4504c021144269141300844c8743204a29166a349a0128a458182a04048a0533088c40122814c8a2702048a0532281c08122814c822300048a0532081c00122814aa9168a048a052aa41a28122814a892682048a052a241a08122814a812280048a042aa45a28122810aa9068a048a042a245a281228062a9168a0482817168ac50120a05c1a2b0404828166a349a0120a059a8c26804828166230980120a05958aa5404828165228940120a05948221004828164208800120a058986a340482816261a890120a058984a240482816160a850120a05858221404828161608840120a058184a240482816060a810120a058182a0004828160608850120a05818220004828066a349a0120a019a8c26804828066a261a0120a01988d2680482806160a8501208058182a04048141b85c4e041205066171381048141985c46041204068180602044061145269141101845149845044061145161141100845149a450440211452611411008451098450440211442611011008449058240440) else (if i<3 then 0x52050101944a4508140406150b05204240303006098108a40aac522a0422032ab148a8102a142592092040a840ea64328102a103a980ca0310888e0522880c42221a0582a030281c5a2b1480c0a066a349a20302819a8526880c0a066a148a2030281988c26080c0a065208842030281948220080c0a0626128920302818582a1480c0a0606128920302818184a0480c0807168ac52030088860520880828062c12892020a0189a4824808280626128920209849368a4580826124ca291602098491e8a4580826104da291602098411e8a4580824424da29160208841328a4580102804a8502a0020901868a4580082404ca29160008841328a4544a2916061a811128a059a8d2684424130150681510904c0441a0140a41229a45a290290488e0522840a41221a05829029048860520840a412218058210282418582a1440a09060612811028048a69168a408150a6a741a10202018984a24400814025428150004420994422400110821540a0a0482c0342a0528104a20b0d028a0412880c340a24140b01506814900a25617838122950aa78349a08a4926c2a0d02229249a1a0b0488a09068682c1222412890a250288904a2420940a22020181a0b0488301a0c28940a20c0682aa652288250289e0526820940a238148a0825028868160a20940a21a018288100a0488e432204028122310888100a0428940a20402800b250288100a000c940a190904d85c1e046424131309448190900c4c25120548a556124904152295485128145468355160f05151a0d54581c145468355060701150c874150681454321d05418051422150851281450301c0541a051409042361d0c850241085834121409018361d0c8500914c1a450214024528b55228500914a0d548a14024428b55228500910a0d548a140044286512085001108304a0512412494532914490492514c24512412494132914490492504c24112412490914824490403514ca45120a0590a834084828160e86c32120a0581a1b0c84828160682c12120a0183a1b0c84828060e82c32120a0181a0b0484822135209848120884d08068244822131a8d868120880c6a361a04808060686c3212020181a0b04848080600c2c12120144b159a450480512c466914120144b0a91408480512c2245021201443159a450480510c46611012014430a91408450291629548a1140a458854220450291514ca451140a454132914450291504c2411140a45091482445029142442091140a45081082045029122d548a1140a44835522845029103452091140a418a55228450290621548a114024188552284482516124904112094485128144460315520d1411180c544834104460315060701110904d85c1e044424133108440110904c85418044424132140601110904c6c351a04424131b09468110904c6 else 0xc04130829540a30104c20855028894520c4c2512221018882c340a82e070aaa170aa0b148a868160a8260708aa170aa0980c22a85c2a8260308a21308a09028360f0b818240a0c69269260902830a41a09824080d83c2e0609020320f0b81824080c83c2a2a0824921868a45820924047a29160504836170781814120d8541e0605048331184c0814120c6c351a20504831a4d468814120c4c251220504830341609814120c0c250220504830301609814100d85c1e060504036150781814100cc4613020504031309448814100c0d05826050181c562d1481406066c13192050181944a4508140407158b4))
def Zcl (i : Nat) := Zaa Zhc (54*i) 54
def ZgJ (i : Nat) : Nat := 0x30
def ZhJ (k i : Nat) : Nat := if i < 0 ∨ 0 < i then 0 else Zaa ZgJ (9*(i-0)) 9
def ZgK (i : Nat) : Nat := 0x75
def ZgL (i : Nat) : Nat := 0x12449
def ZhK (k i : Nat) : Nat := (if k<5 then if i < 0 ∨ 0 < i then 0 else Zaa ZgK (9*(i-0)) 9 else (if k<6 then if i < 0 ∨ 1 < i then 0 else Zaa ZgL (9*(i-0)) 9 else 0))
def Zhd (k i : Nat) : Nat := (if k<6 then 0 else 0)
def Zgk (i : Nat) : Nat := 0xc2
def Zgl (i : Nat) : Nat := 0xac92
def Zgm (i : Nat) : Nat := 0x440981e
def Zhe (k i : Nat) : Nat := (if k<6 then if i < 0 ∨ 0 < i then 0 else Zaa Zgk (9*(i-0)) 9 else (if k<7 then if i < 0 ∨ 1 < i then 0 else Zaa Zgl (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else Zaa Zgm (27*(i-0)) 27))
def Zgn (i : Nat) : Nat := 0x3ae8438ad521d504813c20cee75
def Zgo (i : Nat) : Nat := 0xc875241dcccad782bcccad332b6209224e5eb59423ac4d007321d4ca1a
def ZfV (i : Nat) : Nat := 0x24812093b87620003bac460924666cc8210ec41e29204954ea7543315de863b9552468569a3379e14219179a3bc421430341a0004c99024ea68049a0ec89881d4ea095896a20773a9a03ac53b82738772aa4b2c772499a20090f1e0d08c2d122210c3ac43331010a184e1d341d460783ab022110
def Zgp (i : Nat) : Nat := 0x110321d60c550b440ccad
def Zgq (i : Nat) : Nat := 0x2209234026209288248aa868824a204900000921d2482460c58807524b11830cd809362c892b288248d07788249e4b188074000018318619b1866c619b248749809ad2c8928624e60aab118076b409340900000881dc0000cf824aac5ad2c800001830492b13430c00002aac493982630ed25524b0e204945ac4601e3782516b1000009277000022049362c8d0c32a875248626026201d
def ZfW (i : Nat) : Nat := 0x609200440015c2a8006000881262068ae43524002a9552510000022068494422110634418c1d340773a00630746110
def Zgr (i : Nat) : Nat := 0x440921d
def Zhf (k i : Nat) : Nat := (if k<8 then (if k<7 then if i < 0 ∨ 11 < i then 0 else Zaa Zgn (9*(i-0)) 9 else (if i<13 then if i < 0 ∨ 12 < i then 0 else Zaa Zgo (18*(i-0)) 18 else if i < 13 ∨ 115 < i then 0 else Zaa ZfV (9*(i-13)) 9)) else (if k<9 then (if i<3 then if i < 0 ∨ 2 < i then 0 else Zaa Zgp (27*(i-0)) 27 else (if i<70 then if i < 3 ∨ 69 < i then 0 else Zaa Zgq (18*(i-3)) 18 else if i < 70 ∨ 111 < i then 0 else Zaa ZfW (9*(i-70)) 9)) else (if k<10 then if i < 2 ∨ 2 < i then 0 else Zaa Zgr (27*(i-2)) 27 else 0)))
def Zgs (i : Nat) : Nat := 0x190c8
def Zgt (i : Nat) : Nat := 0x1f879a300498dcccad1f8789209790230bb9480f3a2c819b208620490fdb6066d2aa0c2fe888120b0332b492b6832952eab332b520b024edc920d24ecdb6ac24a9492b6198089205848e53020248751cb07e880e0141f894d1b246ac061b06a8c5e614
def Zf7 (i : Nat) : Nat := 0x1d15e3203cc8646f426c8
def Zgu (i : Nat) : Nat := 0x116790222c6656c58ccad
def Zgv (i : Nat) : Nat := 0x340520230188789c091887892091e075c2bb24aec601d482ee2eb18b3c9c233d4ba62cbb490c493b7382ec921d248f0d1bc34324d005382edc2bb24875c2bb7ba8124312487c92bb29bdcd0141f879c2bb343d45e1b24aece0bb1fb20d01424ecc8af74c0822c4918075243127050d1bc2485520b04a8b93020b20c1302024a947e1e248747e1e1f87a2c6882080ccbb1fb20ccbb8b925b230708c093bc8b2c0920933320923c82f4520b077b1c93bc8ba95c2bb3401092bd498dce0bb24af4e009670c1b2308232492bd8b1987eca8b1a07ec91eb25b4bb790b0921f790509215be546f952783d892a5822ef523c81aec93bc482c22ca924ec49c148b2ec7ec8332ed3014
def Zfq (i : Nat) : Nat := 0x923c8bd0fa468386f49dd338138d03f
def Zf6 (i : Nat) : Nat := 0x11634052f84964c58601d000000000000022c490e92479bd0000000681fb25c23064a61eec9
def Zfp (i : Nat) : Nat := 0x708c0621e1887800008b1a0000024ef00000490c4000000001c23f70aee2c490000208bb8b8c530bb70aec93bc248240000820fe2c68708fc92bb
def Zhg (k i : Nat) : Nat := (if k<10 then (if k<8 then if i < 0 ∨ 1 < i then 0 else Zaa Zgs (9*(i-0)) 9 else (if k<9 then (if i<44 then if i < 0 ∨ 43 < i then 0 else Zaa Zgt (18*(i-0)) 18 else if i < 44 ∨ 52 < i then 0 else Zaa Zf7 (9*(i-44)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else Zaa Zgu (27*(i-0)) 27 else (if i<119 then if i < 3 ∨ 118 < i then 0 else Zaa Zgv (18*(i-3)) 18 else if i < 119 ∨ 132 < i then 0 else Zaa Zfq (9*(i-119)) 9)))) else (if k<11 then (if i<19 then if i < 6 ∨ 16 < i then 0 else Zaa Zf6 (27*(i-6)) 27 else if i < 19 ∨ 44 < i then 0 else Zaa Zfp (18*(i-19)) 18) else (if k<12 then 0 else 0)))
def Zgw (i : Nat) : Nat := 0x2071e004783c
def Zgx (i : Nat) : Nat := 0xbe4409c0a332b4d015d58f0d00c340308cb322331e238b3154d1b6346e4ccb53702ad63c
def Zgc (i : Nat) : Nat := 0x20162007aea29a57878c2610f078ad63004020703aec02142f8f0783c00e300ecd9b0a468c299cc8c7bc2e0515a3c
def Zf8 (i : Nat) : Nat := 0x8ce8b09537c885af563c
def Zf9 (i : Nat) : Nat := 0x34050d1b978c98d00aa0c96627770ca4ccb3332b5b4ad3430ce80f79024d1b51a004920979024ccbb3402cabb4346d4d0f78838262013401de409346f5e409318f1b4072aaa1e409346f2205f6c740d00a6e9dcd014332b4ccad989ddc329be59c92096e9dde3314f498d007340509209318f0c63c24824d1bc700f1e2f7340509209332ecd1bd2a853a2c634051b3d2b3f40cc01318f0c63c31ba4d00a332cdc137a4154aca83a2ecd0c3ae024d00b78bdcc6e734028d00a88741bc07508f09db44f0d1b8ad88748d0c3318f0aaba346d4ccbb2aaee8528700f0c6f7492c492098d970e8bb276d0aac0332cc68c22abdeb8091a9ddc230703dcd01488740d00aa41a1180731b9e7326318f1e40988380ccbb788fdb48224824b936332ecd0f7a41a1e5346cf5cc23c332cde52931bdcdcbb332ce6e01343dcccf7
def Ze7 (i : Nat) : Nat := 0x283f0a308680130b19d2011e004c6e1510fe6c7700cc4683cdeb1878a2988247e341e31976d998b10283c4fb1812c31f8f1ee143a775ee1498ef0c6e11f88ceec6008fcc6c6ec050143c
def Zga (i : Nat) : Nat := 0x440d0149c9a01510318fe20680a440d0f76d4c4028cec30a20665dc40ccbb8818dd31024826ce631e440d1bc899a01539262ee20637b9447e77be2318510318f220d9ebdf221d0881a029103a3dedef21a440c63cbe44145394f49a845554441e409
def Zfr (i : Nat) : Nat := 0x794c4e8bb31bdde531346f0e9373a2ecd0146e9dcc63cb708e20632aaea2063346f0e8bb70aece8bba44c5c234318f1e43f3a2ede414362efb0c6790d4d0141fb0cd01470cc4d01470b193d31318f290633a2ece0bb39bdca27788364d01479051ba77318f220633a2ece8f7
def Zfs (i : Nat) : Nat := 0xc698b198ce1
def Zgb (i : Nat) : Nat := 0x440e8bb
def Zhh (k i : Nat) : Nat := (if k<11 then (if k<9 then if i < 0 ∨ 5 < i then 0 else Zaa Zgw (9*(i-0)) 9 else (if k<10 then (if i<16 then if i < 0 ∨ 15 < i then 0 else Zaa Zgx (18*(i-0)) 18 else if i < 16 ∨ 57 < i then 0 else Zaa Zgc (9*(i-16)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else Zaa Zf8 (27*(i-0)) 27 else (if i<143 then if i < 3 ∨ 142 < i then 0 else Zaa Zf9 (18*(i-3)) 18 else if i < 143 ∨ 208 < i then 0 else Zaa Ze7 (9*(i-143)) 9)))) else (if k<12 then (if i<30 then if i < 1 ∨ 29 < i then 0 else Zaa Zga (27*(i-1)) 27 else (if i<78 then if i < 30 ∨ 77 < i then 0 else Zaa Zfr (18*(i-30)) 18 else if i < 78 ∨ 82 < i then 0 else Zaa Zfs (9*(i-78)) 9)) else (if k<13 then if i < 5 ∨ 5 < i then 0 else Zaa Zgb (27*(i-5)) 27 else 0)))
def Zfx (i : Nat) : Nat := 0x3c
def Zfy (i : Nat) : Nat := 0x221dc
def Zfz (i : Nat) : Nat := 0x51578783c3ce30fe7a
def Zfb (i : Nat) : Nat := 0x1537c886c6d055
def Zfc (i : Nat) : Nat := 0x2205fbe59de2f724826521e30ba621047f091b1ce
def ZeY (i : Nat) : Nat := 0x900000683c1e3a478a2c60f0014b0480029dd7b850c64e
def Zfd (i : Nat) : Nat := 0x881a029103402400000000000008818dd3102482719044459cc63c8818def106cf5ef91051441b1d0
def ZeZ (i : Nat) : Nat := 0x4502478883a220c6f73a2c4d1bc7ba222009340527268b792e20632aae8e8bb00000e8bb3a220e1b4881a290683402abe742a85000003a2ede414881a0d8bb386d0d01434024d014000007880881d20488881d0e0bb1e222207439bdd1409289de20d91e220000034024c63c823ba20633405620681e1e29068
def Ze0 (i : Nat) : Nat := 0x3c9c95400c61e4c4016fbe319248845001143c6338478f2
def Zfe (i : Nat) : Nat := 0x5f0e8883a0f11000000000000000000000be440d000000000000000000000881d1760000000e83c445f22068
def ZgP (k i : Nat) : Nat := (if k<11 then (if k<9 then if i < 0 ∨ 0 < i then 0 else Zaa Zfx (9*(i-0)) 9 else (if k<10 then (if i<1 then if i < 0 ∨ 0 < i then 0 else Zaa Zfy (18*(i-0)) 18 else if i < 1 ∨ 8 < i then 0 else Zaa Zfz (9*(i-1)) 9) else (if i<2 then if i < 0 ∨ 1 < i then 0 else Zaa Zfb (27*(i-0)) 27 else (if i<11 then if i < 2 ∨ 10 < i then 0 else Zaa Zfc (18*(i-2)) 18 else if i < 11 ∨ 31 < i then 0 else Zaa ZeY (9*(i-11)) 9)))) else (if k<13 then (if k<12 then (if i<12 then if i < 0 ∨ 11 < i then 0 else Zaa Zfd (27*(i-0)) 27 else (if i<66 then if i < 12 ∨ 65 < i then 0 else Zaa ZeZ (18*(i-12)) 18 else if i < 66 ∨ 86 < i then 0 else Zaa Ze0 (9*(i-66)) 9)) else if i < 5 ∨ 17 < i then 0 else Zaa Zfe (27*(i-5)) 27) else (if k<14 then 0 else 0)))
def ZfD (i : Nat) : Nat := 0x19316
def ZfE (i : Nat) : Nat := 0x22c30
def ZgR (k i : Nat) : Nat := (if k<7 then if i < 0 ∨ 1 < i then 0 else Zaa ZfD (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else Zaa ZfE (18*(i-0)) 18)
def ZfA (i : Nat) : Nat := 0x31
def ZfB (i : Nat) : Nat := 0x31
def ZfC (i : Nat) : Nat := 0x603a
def ZgQ (k i : Nat) : Nat := (if k<7 then (if k<6 then if i < 0 ∨ 0 < i then 0 else Zaa ZfA (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else Zaa ZfB (9*(i-0)) 9) else (if k<8 then if i < 0 ∨ 1 < i then 0 else Zaa ZfC (9*(i-0)) 9 else 0))
def ZfF (i : Nat) : Nat := 0x1ad
def ZfG (i : Nat) : Nat := 0x3443c4b0cd3231
def ZfH (i : Nat) : Nat := 0x7e00001af
def ZfI (i : Nat) : Nat := 0x3563c000019e334c0cdac304d8f15316
def ZfJ (i : Nat) : Nat := 0x3d9233188506231000f000308ced5a6311f8036bb518eeee8a91fee00033
def ZfK (i : Nat) : Nat := 0xe014700f1c0f700001bb304d0f1303f382ed38146eac89c0a6c8c352e96b8c1c23000002d4e0276d530316b8f13234c50522ce9678fe2ca9382eef9303803e2ca96eac9c2144c0c4e00a708cd3034aeaa1b2304e0ff563c
def Zff (i : Nat) : Nat := 0x3c000f2fb3164aec00ee64bb992c90a0fc2814e9cc4003098384280095375640064ac965164c00062d970aedbe001e0c460b97755152148b001c0d9
def ZfL (i : Nat) : Nat := 0x458e014
def ZfM (i : Nat) : Nat := 0x70aedc2bb00001c23f708c1c33170aedc2bb70aedc2bb000000000708f1c230
def ZgS (k i : Nat) : Nat := (if k<8 then (if k<6 then if i < 0 ∨ 0 < i then 0 else Zaa ZfF (9*(i-0)) 9 else (if k<7 then (if i<3 then if i < 0 ∨ 2 < i then 0 else Zaa ZfG (18*(i-0)) 18 else if i < 3 ∨ 6 < i then 0 else Zaa ZfH (9*(i-3)) 9) else (if i<7 then if i < 0 ∨ 6 < i then 0 else Zaa ZfI (18*(i-0)) 18 else if i < 7 ∨ 33 < i then 0 else Zaa ZfJ (9*(i-7)) 9))) else (if k<9 then (if i<40 then if i < 1 ∨ 39 < i then 0 else Zaa ZfK (18*(i-1)) 18 else if i < 40 ∨ 92 < i then 0 else Zaa Zff (9*(i-40)) 9) else (if k<10 then (if i<7 then if i < 1 ∨ 1 < i then 0 else Zaa ZfL (27*(i-1)) 27 else if i < 7 ∨ 20 < i then 0 else Zaa ZfM (18*(i-7)) 18) else 0)))
def ZfN (i : Nat) : Nat := 0x13231
def ZfO (i : Nat) : Nat := 0x31
def ZfP (i : Nat) : Nat := 0x132314c0c53231be422fc31
def ZfQ (i : Nat) : Nat := 0x150a905c01ae190c6f89418c5c797dbe4207f17bde9af7c518d40629d
def ZfR (i : Nat) : Nat := 0x7bbd8c529a61fdb22e3c
def ZfS (i : Nat) : Nat := 0x1534c1f8753c318b8634c31be5253c33198740000d20fef930490ff563c00003638e000013c31830bc7e1dbe4b0761ebe4ab4c3f83294661dd5beef52a4f423626924a9400004f0cc941d8b8612433be0c6f6314f0fc661f3e0c4661dbe4aaf8e6bdcc1aa314f0c47e1d
def Zfh (i : Nat) : Nat := 0x13c9218f2a2e3c98801a43fbe4c2a5174ea7a460098548677c954b952333bc01d231974aa549ebdcc2f892188c068314f0038a34efa7878300021e54310054e2f1da7caaf97c1e0cb4d170052aae31918013dba0000062fcaf0fcef4d984ab511718800627e9b8ff8231
def ZfT (i : Nat) : Nat := 0xb5eac796c8b8f2949e1fe9eb83c
def ZfU (i : Nat) : Nat := 0x34051bab11f874781dd4cac781d1e074601d700edc03fd8d54681db09dc7e1d0000000006e9dde41418e0400001887712148b3b8d00ac829a2e1819874661dbe4a9e40f00001c121490fe9ee07ce0496b1d8b4f1bc7382dc000024824d00ed4cc07e1d00001ba776e8f1bf8079039c0414f0c62c3f78bdc0000248252430be0cce0bd8cac5b1d0790393c3f4c2c5c03f8b295e9308b3c45e1b6fadeb83c6a0c12433c68c0621ea70f1c2bb4f0cc7e1f6cf1e2c49700fc92a518874d0b1276c6618025ac86381343dd3d318c8f1771619874d9c734056f8a91f875b2304f4c720a624a947e1d6c0f0661d1987467bd18e047e788b5fd2433d48bd53bc00001bab16c8ce447700001e414c40487e78700f0661d8b2c4661d700f1b03026875c03fd60f0618279050d8b2198971a30be0cdc03fbe4c232b1272f53d2f8c0f31a3019e00681d4f0c47fbebe0c71214700fc621dbe0cc6381c83a1b23f708c00000443831ab7700fdc03f1f8947e1d6c8ec97b424824e0b7276d284e71f9dc661d6c8c62d7f18b2c96b1b0ac467801f9e124347010400008b3a5e2f7a7b81c1d078bde2ca98caa5c1371e07476781fa207e1d6e9df1ab7700ec9cb100000e0bb
def Ze2 (i : Nat) : Nat := 0x17614188c4ee146c9dfa4778c8ad76330a0f067bd00600018b3b8ac0077b0aec00f71f8f1d2e91f85078b73bf480116a78c697310a4a8000e12ac400307a54c63c75b9dc2800180f29f161e36467614f2ec289f000c461611e0c6b92a6c8f2327718850637c182ec61beac8c063ac588d260e11e1dc63235d8755231180c77a000a4c38f31000c069ab1848eb97cab0007931180cc62bb5d8c174d90a0d078341e58564344f8c4003c00779c37c4f0f02892362eddc0018826f834000fc0031002a462921f8c6f959be0f260311e0c46345e553d7609770fc609eb0f28780098bddc03f7bda879ac180c701301e1dc60bb914c4001da78c4623f188f262301885028318b8c428779f2c46600ba748ef2a1d8f0783f748cc7e3f0a48c00e98d0c77aa9d52ec63ca748c029165dd3c794fb087577d44f2c4292a18e0078ee19ba963603bbd28a3cb70f2b6d91a46828140cc5cf0778b8c5623f981a47e1d1fef4623f7b8c4623c1e0c2543f7b9dc123049001c077
def Zfg (i : Nat) : Nat := 0x286680a00000000000000000000308705d8000000000000000000022c300e80000008b124131678bdc00000000000004c0d03a0000002c23c3be3dae300000000991a0762c92180000000000000000000009c3c0ed2dc03cd4d707800000022d8d58c58e0bb00000000000000000000458d00e00000015f25ac4000000459e414
def Ze1 (i : Nat) : Nat := 0xe0bb7bb25b331ae2c463be00001c2bb00001c2bb8b2ec00006cf2a9ee01f9e289d3b02ec00006eac5b2308d2ec00000000263806c8c4d0f78b1a1c230be2c69ee070aec00008b3b9c230793247e1dbe2e9c03cd60c1c23c70aee2c30708c6f9316c8c1ba77700fc0000c6ac5e4f78b0c1c329708c4d014708c2c23ca7bb9c0f7c6addbab134051383000000d014be2ea2ca96e9dc63816c8fcd0f74f4c5ba77be2a62d8d8b2a5c2bbc68c1b2f7000000000a7b8000000000078776c8c07e1d70aec0000708d00000000031ab76c8f29e3c79051c23434051bf8034051c2bb708c1c2bb6c8c07fbd00001c2bb00000000000001c2bb708c5c23070aedba3c703b9c3316eac6dc3ca78f07e1d700f2f8ee1e1dd243f70d522ebb70aedc2bb7905000001f894000070aef1ab7c6bdc7e776eac5c2bb6fe01c23f708c6dc306eac400000000208bb6e9dc0000c6ade08f7708c1c234708c0d180490fc7e1dd60f1c230000031a30d60fcd01470aec7e1d6eaca2c30beac5e41470aeefab170c8f1ab7a7b8000008b1a1beb8b0aec7e1d70aedc23f708f1bb8b6eac5bf8000000d0144e0c1b33100002c2bb700fc000070aec0000000022c928b2edc23f708c1e531703b9c230703de2cbb
def ZeS (i : Nat) : Nat := 0x18001777c000fef831000c1c20070d8ec630002ec60bb5db85c2001fb8400bb00385ee0070b85c2e15d8022c0070801c23f5dc5a2ce1182ec78301f8f262e1184c5c2bb98cc5c2bb1838400008b2ed76e170802623070cc576e170800000070cc5c2bba338478bb5d8f060317080177315d8022d16a20f000bb708fe2c00000c5c230000c00131
def ZgT (k i : Nat) : Nat := (if k<9 then (if k<7 then (if k<6 then 0 else (if i<2 then if i < 0 ∨ 0 < i then 0 else Zaa ZfN (18*(i-0)) 18 else if i < 2 ∨ 2 < i then 0 else Zaa ZfO (9*(i-2)) 9)) else (if k<8 then (if i<6 then if i < 0 ∨ 4 < i then 0 else Zaa ZfP (18*(i-0)) 18 else if i < 6 ∨ 30 < i then 0 else Zaa ZfQ (9*(i-6)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else Zaa ZfR (27*(i-0)) 27 else (if i<51 then if i < 3 ∨ 49 < i then 0 else Zaa ZfS (18*(i-3)) 18 else if i < 51 ∨ 144 < i then 0 else Zaa Zfh (9*(i-51)) 9)))) else (if k<11 then (if k<10 then (if i<8 then if i < 0 ∨ 3 < i then 0 else Zaa ZfT (27*(i-0)) 27 else (if i<207 then if i < 8 ∨ 205 < i then 0 else Zaa ZfU (18*(i-8)) 18 else if i < 207 ∨ 536 < i then 0 else Zaa Ze2 (9*(i-207)) 9)) else (if i<40 then if i < 2 ∨ 39 < i then 0 else Zaa Zfg (27*(i-2)) 27 else (if i<243 then if i < 40 ∨ 242 < i then 0 else Zaa Ze1 (18*(i-40)) 18 else if i < 243 ∨ 362 < i then 0 else Zaa ZeS (9*(i-243)) 9))) else (if k<12 then 0 else 0)))
def ZfX (i : Nat) : Nat := 0x3c
def ZfY (i : Nat) : Nat := 0x87156cc55678d356f7
def ZfZ (i : Nat) : Nat := 0x15e1e05078143193f1814318f8783c5178d7c3f07971d2a9
def Zf0 (i : Nat) : Nat := 0x1537c882fb563c
def Zf1 (i : Nat) : Nat := 0xe83c380289e14f16d6f82238050aa113a2e49e141a88ce63cd444116bbbe18c9e3c8d970a203318f06a23288f09e3f886d4aa0f28ac8aa0f70486f91031ba621d7270289c0a4c4c4a23c31bba20e098a15b31e392ecc63c31bdcc6e7318ee206345ac8e4bb8e13cc63c3a2c9b3d2398f0e8ae6eac8a8ba678d09cb2678fcc63c313dcaa14703ddc03f3a2c8e0bb31908aac0707409e1428ac8c64231bddb3d231bace6ee704dcac3c8817c9db5678d4a20f2b2e6d0551f88ef8104e0d5c03c
def Zfk (i : Nat) : Nat := 0x5d8f078149a98c683c288f3ba3f283a5b29a31d4d443c5faeda03c5d8f130bb050518cbb1f98ca2341fa8acf361e08f6a342a8f177315daec29365f95544852b2ee6e3427850e8f7118507823
def Zfi (i : Nat) : Nat := 0x1393802a20745dc58aabb881c17710380522c745dd08aaa8881d0791031bde20d9ebc409db5881381510708c2ce631e440e8bbbe154217c8828af8745da607e23881d1771031ba530551fc419e35
def Ze3 (i : Nat) : Nat := 0x3a2edbb313a2edba84ec30ce0bb70b0d3331a41c0e8b9278fe21d83a2ec7e23a44c5303f70aedc2148818cc63c2aae8e8bb318f0c63c3805138234e0d4a23c3a2ece0c338050e6f73a2ee20633a2edc2349e9d290551a88dba23a418ce01438050c63c8818dc23c3a2eca2b231bba20e03a2efb02388366905131bdcaa0f318f1c21438050e63c
def Ze4 (i : Nat) : Nat := 0x4c576bb003198c7463387b0e15db1976c6
def Zfj (i : Nat) : Nat := 0x440e8bb000000110708c220745dc40e8bb
def ZgU (k i : Nat) : Nat := (if k<10 then (if k<8 then if i < 0 ∨ 0 < i then 0 else Zaa ZfX (9*(i-0)) 9 else (if k<9 then (if i<4 then if i < 0 ∨ 3 < i then 0 else Zaa ZfY (18*(i-0)) 18 else if i < 4 ∨ 24 < i then 0 else Zaa ZfZ (9*(i-4)) 9) else (if i<2 then if i < 0 ∨ 1 < i then 0 else Zaa Zf0 (27*(i-0)) 27 else (if i<87 then if i < 2 ∨ 86 < i then 0 else Zaa Zf1 (18*(i-2)) 18 else if i < 87 ∨ 154 < i then 0 else Zaa Zfk (9*(i-87)) 9)))) else (if k<11 then (if i<23 then if i < 0 ∨ 22 < i then 0 else Zaa Zfi (27*(i-0)) 27 else (if i<83 then if i < 23 ∨ 82 < i then 0 else Zaa Ze3 (18*(i-23)) 18 else if i < 83 ∨ 97 < i then 0 else Zaa Ze4 (9*(i-83)) 9)) else (if k<12 then if i < 4 ∨ 8 < i then 0 else Zaa Zfj (27*(i-4)) 27 else 0)))
def Zf2 (i : Nat) : Nat := 0x388ff
def Zf3 (i : Nat) : Nat := 0xee389c7db
def Zf4 (i : Nat) : Nat := 0x2e694b9532b80000e4006974a8f2b16cb85c
def Zf5 (i : Nat) : Nat := 0x3e8ed3d77be3b30729be398ac3ca413af8e68d9594fbfc1c7800002780f563f88186f91fbe43e8f788817a1e4027028b9c62782af91fbe450fba5a3cab563fb37713dcc2b72783102702b07074f0ff062f8a172f8ec2b0ef231be0c489c21a3caa365c887709e0a8d9735641c1ca72661be3993c4088a7a2699d58fd3230d5906365c
def Zfo (i : Nat) : Nat := 0x288797c2e52e274700098761d1f87479a5a45f078633197276318e96400c12e1707753884d6212f1e0db4a55d2dd74a781e0c4b85c9c74ef97cf418ef83fa3df2277c9e973c3c331c427b3c1e0f0b85c1a164845ca38f082009e80297e02e5f078e9b28f0c63ce40f0ade71ff94683c89c407e5c881c7b947
def Zfl (i : Nat) : Nat := 0x363662ac4ca43c
def Zfm (i : Nat) : Nat := 0x25ac4e8bb34028d8bb2b0f2b0a8398f0e8c6be440e8bb382ca0510b4957531ebe443bac0510ecaaa8b3c1d16b1aeed2f8634f7306a1d2b0f123d06c0fce83cb7748d8b23f289300ac9985e2f7b415621d02702b855ed5bb2d77c4f420d6b400000681d362caf91025ac6365c8a18cfb7c3a2ee90f18d98ed055880b4d8b2b3f48000078dcd4542a44c624741a874d4ae2b2ef2b7c28e81c2302a83addd23a0f1c2308b0c28f2a2a2e8c6e7880607678a4154e8bbb30bdc03f318fcc2e72b0f0e8bbbe4413cf93a2ecc6e7d2c40c71524825c124b74a5c30725ac6b9b52a8762030c3441b1d78b3bace3f88742b2a8392e4c2e93edf2ce3f382ece8bbb58f284e745ac6f9208a383195f2b0f2243028ac40000318f0b83b24826621d00000d8b2707370635a44b52435b74a4d8b29e155e2f770c7add1e2a2ee20bb700b4c6f724824c63c4f0d1c230319068e5cbe47ca2784f0c4aaa88d97096b125ac4c6edd58f220612caee84e72b2ca7855c998c9c0a35ad3191031908c642881d0e0b28918ca23c27828c6e9390f0c0f76c741b3078d9722ce989f4f25481f874a2b1be441c03c392ee904e390f0aca8a3caaf91087b8116a930ba62a2d4903af85c88411c041b8740c242289e0d4ae2a86cc6e7be440c62ab4956c4ee6c74092a5708c2205f00002905c8d958e83c1a874e8bb6cc1ef9103190a365c8d972912d3a2ecb2a86c73b563cb70c0e63c8818ce43c8d9722c42d58f2cfd2700fde2f72b2ee365cbe3b4ac3c31bdce63c3a318e8b2392eea6e16c741b2346c8d22c594f10383106cca6cfd0700fe368f3a02b19108d972ce638817e243c31c59b3d2318ecb0a83a0f3191b2a2e93c319d9713d2ad298ce8e7b38d4e8bb6cc78acba31bdef9392b31a206d3a2ec9cb13a318c6e78818e8f2ac6459c2bb8d98f19103a0f0b0bb3a2ecc6e570485bab16cca4adc9318f3563cb80b7463c362c93c3489382dcb1b88c0b2a8be443563f70104980e8a170e8c6ae02ac4e93a2eef86330904e8b9a5b80acba3382af85c8b2ee7e552c2a0c641b70d53d21700fef96f
def ZeT (i : Nat) : Nat := 0xf285163d87488c28340a4f6977c3ba883bd81e319efe97be4cc63c1f8f07929dea89d72f0e8f02935988f0001d4f1d2f86300520ef3d1e3acee85eee31763c60d003a003a15429362a9d3ab471df3a201d1e0f028c131cc447bd78802f9361e4d93d53a38f0ee3f5dd2012f71faedd7790a5becd10630507e144f3818a1404da58c3f98d9d8c140e970792f5ca14e81497850783bbe0758d7c6c9d2214718c40ab10209d879100ea8976c131bdc783cde8f07e3f510f0841d514407f672acda2767a41725e5604ac460c674ba478710a52079a5a40753eb92f8edee1d7595620637bc40783c1f98ef8c11b0f25ec61e4d8c67821026f8771e2e81e3c8f0d0797c0ea7ae214d4279d21d1a0503a74988f10a3f3b9d3b375f0077c2f71e3ae621d3a0d1ee77880ec461d1e440ab31886f428747bbebc8f7eb59ef81d1fa2e53101f956f8632acc6903c3bcc484559b8f0ec55319dcabe1de98c78741e08e9e141e1c58c71de85078008874ef9595def4e8550a2ecbe09b4cc67263608f03a6358800c63c0a00028c18847c29d3be3dc79d83a170b8c19bcd446f20e852903c4f075877c3a0f2f9bd608502874
def Zfn (i : Nat) : Nat := 0x440d0149c9a014a9be4428455545bcd8b2be59a516dd58f220631e458a2b1881cc797c2aaa3277c31df0d4ae0000001936cc7b81102fc40c63c88383a11645ac5457cb3c41b3d22edf2211024826f86c59441c03c8818ddd6fb775e204904c4096b14c0fc3b103190620631e42ca23c8818def7c883c620725dc41240ef31c8791031bde20e01fd08c6e7f28f03b1231bae206374c58c642881cc7914318f00000006962063df955811645ac4000000440a2b18a98c796f3a0f2de745cc41b3078818c77106c8d6206320c41c03fb3958796f35ad2204e58a60681d88367a5a52b2ea20dd58c41b1d08b18c857c2a2e8000000610e4bb
def Ze5 (i : Nat) : Nat := (if i<1 then 0xe20302aaee36633405220e0700f1b3298818dba7700002f91070c7a3663708c0c63c31bdcd014700f290558818caaba1fef4c6f7be5a5c12f318f0e8bb4f4aa20a28d0f22ca2882ee96a21ab18c6f76eac400001aef4e8f73a0f1e40ab128c9cb1b8aec92098838469bda415620630000236a231ba5c33198a12e2b13a2ecd021346c6dc30be440e8bb2aaa220f83a0f0e8a8a41d0e8bb88762f834ad2c8aaba6eac6905688365c3d27905220687903e20ee318f0aabb708c2621b24824687731bdc7e23a41a0c63c31bdce8bb1fb04981d45aee84a83a0f2f863708c1c3296eac620748230caac698876203c883dde414708d4e8bba4288e8bb2aaede5d23a0f2f834318f2907470ca5b2343a2ee2074881a0e63c3a0f0d1bd00000c63c28ac40000883b8d0148b0f0e83c8b0f0a2b1bb0d238743a2edc03cb38d6d2f74c074e83c880d691311e318aaba3a0f3b0c66cf5cc6f7318f1c3313a2ec0000881d0e8bb318f22074700b5e414a44c4aabb3a2edc1d09c9a1c02d79052f8a331ba62063318f0d8bb3a2ecaaa83a2ee20e0318f2206145aec92093a0f0e8c628ac4e43c3a0f0e8bba1154d00abe1b1e41470c79c2bbbe440c736ad2a0c6f71e1dde5743a2ecc6edbe1d06ac62b052de3c881d1c2303a2ecaa1470f2dc23c882ecc6f73a0f2f8ed340530f103a0ee2074b7dba209c340523663be300a8bb398f0d014700f286bb318f0e8b91ab18d00a1f9de621d882ee9055362c8a23c6c8c4d01488380e83c1a88c7e77880f0e8bb881d0d014881c6d255be050e0bb9c828e8bba1ba4d8bba41a2f8c68818ce8bb6e9de9063884d4d8bbb70d5c0ee340529074318f0c63cb70d0c6f728ac8e8f7308fcacbb8818e6277be18caac31ab0620bb1ab047ec6882edc3233a3de20e0b8a16365c700f2f863be440e8bb4f0d1e414883ba20e0318f078779ef762074288f1c35370b1a2014382ec93bc318fcd8b21e220c6f731bdc6a1d700fdb23f1aef5e2f77074220f2708d5c23034053c2146c740d0f7ec318e83c28ac4e6f779051c3d2343ded23c708c1e414703dcc6f734050d8b228ac4e83c3a0f2913170aece84239bdcd00a1a075e4141e220e97c79051c12731bdca2b18818cd0096c8d5321d3a3ddc3238818ede7400000c63c881d35830823b87e778d970e0bbbe1d0c6f7882efb43c3a2edc2308d9d0e83c708d4d014a43c8e8bba4171c331af98ce83fbe18cd8bb708c1c32934050981d34050e8c63a2ef087028ac67a63318f0d814880f116a8a418cc6f77902a20683a2e67a682aaa0920934050c6f7700fce83c24826c4eebe441e488708fef9103402977102b0f1e414318fcc63c318f1b3d2708c286ee382f4aa143a2ecd8b21a87478783a2eef96788386f86324ef0ac3cbe0c0e83ca418cc63c3a0f220e06c742203c3a0f06ac6 else 0xe8bb700fe91311e074e8bba5b807888794c4d0142b0f3b0c6a3ca916b2790506ac631bddc03f882ede4211ab18681d2aaa4c6f71a874c63c2a850e8bb88380e0bb3a2ece83c1fb1a8474898c1c230b8aee20e03a2c6f9103a2edc03cb7b81e4f7318f0d8b21f8769ee031ba4c6e93a0f0c63c386f0c63c25ac5c337289e2f939989dce8bb7ba20ac3c2482492096c8c1c2bb398f0e8bb3a028e8423a3def8748875caabb3a0f07ec13a4d9381d9cb8220f7883822c3031bb916b139bddc231be440e8bb31bde872931ba5e430a5b80d8f79e954c63c70cc4e8bb883c4c63cbe156907400002f830883dc6ac6a41d22049510f0d01428ac5c2bb70f4a21d21ab18aaa8be440c63c3a2ece8bb1f9d)
def ZeU (i : Nat) : Nat := 0xec4c5761d31ef662f76cdf03b6e88761c0c61e4c5823c2abc878e1be0dbc0741e050e9101e6f4783cde07662345198cd0bb5da158c632af6046bb1e1d176e06374a20e098cc576141e5d2de3c6c955c2141e522203c70aedee3f1e4c4ab3163387b0f794b842856632edb23f5daecc7317705220e11e1dcc6745d9d3b03f2a8f27274184c6e4c6be0fe6ec698946f948341566dd82acc4e8f23a2737a3c2ab0d8cf25d802203cec0fe6f1000386903cb4ef57710791de21d8632ecaabb2ab8621e4aa31878513ba14e8001e1d078f71b3df9ee15d9d286743ba2d76e11fbc801311a1553f6e7b8f07855deb8478c651bc8d17cec1d220b9183187ee1f0b18aa63453dd76741f9558c001fb677b31ec1566c632a9dcee14be366637cec3ddc3486cb19c36f8831829d2709dc283c4f6f620bb1b157a4c61fdbe9ee16cb850ae10a3c8c63c1e4e828f23a520783c61df3c2e12aa718c8b1f9a0697c2ab18c748630f176301e050aac158aedc23c318f226771e520783c0a318ab3600520e8c11e364e8145d95446c6700f3c8f2be5207ef7
def Ze6 (i : Nat) : Nat := 0x290f298c10aabbbe440e94879155e4557bc40c6f700000017c7930e2068de00000004ccc43b6e1a88ef83560df220142abdd8710708c220680a441ba7779154297c8818e20631e440e8bbbe441dc741e31a20745ddf220a3881d17710708f236631e0000000883c8291031bba20e15dc40d0f78b155771028ac686555dce4e8bb708fd8d1079052de6c5d80000009c9d176511f9de72680a440e8bb881d07910708c220741e440d014be154295f318f2f91077440c63c8818c797c3a2ee20d91a800000088387a510398f220705dc40c63c8818c7910708c226680a5bcc63c00000000000002205158c40a2770000001103a2ec0000005f220638818c7f10318f220745d8000000709547e9c1aef62073e5440d01400000016f3a2e6f91034440e8f7
def ZeV (i : Nat) : Nat := 0x70aee9131000000000881d22074a41d1c23070cc6de743a2ec0000880f220743a2ec6ac63a3dc00003a2ece8bb3a0ffb0c6be441c331881d1c23500001c2bba4154e8bba41d0000070cc4e8bb3a2edc23f3a2ee20e13a2eef9103a3dc0000a41d0e8bb3a0f0aabb70b18e8c63a0f0e83c3a0f22c553a2efb0c670b1a9074880c1c3313a2ec6ac61fb1a207488760e83c881d220748838672743a0f2207470b19c2c68838672e100000e83c88762f855881d221d88838400003a0f0e8bb0000290742aaee2074
def ZgV (k i : Nat) : Nat := (if k<11 then (if k<9 then (if k<8 then if i < 0 ∨ 0 < i then 0 else Zaa Zf2 (18*(i-0)) 18 else (if i<2 then if i < 0 ∨ 1 < i then 0 else Zaa Zf3 (18*(i-0)) 18 else if i < 2 ∨ 17 < i then 0 else Zaa Zf4 (9*(i-2)) 9)) else (if k<10 then (if i<59 then if i < 0 ∨ 57 < i then 0 else Zaa Zf5 (18*(i-0)) 18 else if i < 59 ∨ 165 < i then 0 else Zaa Zfo (9*(i-59)) 9) else (if i<4 then if i < 0 ∨ 1 < i then 0 else Zaa Zfl (27*(i-0)) 27 else (if i<342 then if i < 4 ∨ 341 < i then 0 else Zaa Zfm (18*(i-4)) 18 else if i < 342 ∨ 721 < i then 0 else Zaa ZeT (9*(i-342)) 9)))) else (if k<13 then (if k<12 then (if i<77 then if i < 4 ∨ 76 < i then 0 else Zaa Zfn (27*(i-4)) 27 else (if i<652 then if i < 77 ∨ 651 < i then 0 else Zaa Ze5 (18*(i-77)) 18 else if i < 652 ∨ 1007 < i then 0 else Zaa ZeU (9*(i-652)) 9)) else (if i<110 then if i < 24 ∨ 109 < i then 0 else Zaa Ze6 (27*(i-24)) 27 else if i < 110 ∨ 197 < i then 0 else Zaa ZeV (18*(i-110)) 18)) else (if k<14 then 0 else 0)))
def Zc5 (m k i : Nat) : Nat := (if m<1535 then (if m<189 then (if m<31 then ZhJ k i else (if m<111 then ZhK k i else Zhd k i)) else (if m<383 then (if m<191 then Zhe k i else Zhf k i) else (if m<511 then Zhg k i else Zhh k i))) else (if m<1903 then (if m<1663 then ZgP k i else (if m<1839 then ZgQ k i else ZgR k i)) else (if m<2031 then (if m<1919 then ZgS k i else ZgT k i) else (if m<2047 then ZgU k i else ZgV k i))))
def ZhN (m k i : Nat) := Zcl (Zc5 m k i &&& 511)
def ZdI (m k i : Nat) : List Nat :=
  let w := Zc5 m k i
  if w<512 then [] else
    let a := Zcl (w &&& 511)
    let b := Zcl ((w >>> 9) &&& 511)
    if w<262144 then [a,b] else [a,b,Zcl ((w >>> 18) &&& 511)]
def Zcg (g : Zad) (k i : Nat) := decide (512 ≤ Zc5 g.mask k i)
def Zbr (g : Zad) (k i : Nat) :=
  !(Zcg g k i) || Zcf (ZdI g.mask k i) (Zaj g) k (ZbA g k i)
theorem ZhI {g k i} (v : Zbr g k i=true) (w : Zcg g k i=true) :
    Zcf (ZdI g.mask k i) (Zaj g) k (ZbA g k i)=true := by
  simpa [Zbr,w] using v
def ZcQ (g : Zad) (k i : Nat) :=
  let raw := Zcb g
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := Zdn g k i
  let values := ws.map Prod.fst
  let rules := (Zdg g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zb6 g (k-1))).toList
  Zbr g k i && (decide values.Nodup && !(values.contains (Zaj g)) &&
    (if k=0 then true else Zbc (k,ws.length,ws,Zcc g.mode ws,rules,ls,Zcg g k i) ws))
theorem ZeR (g : Zad) (k i : Nat)
    (samples : ZbI (Zaj g) (ZaJ fun j => (g.samples j).1) (ZaJ fun j => (g.samples j).2))
    (ZaE : ∀ ci ∈ g.ZaE, Slice g.mode (Zal (Za9 g.mask ci)) (Zaj g) (Zba ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.ZbT, ZbS (Zaj g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (Zaj g) (k-1) (ZaM g (k-1) j).toFinset)
    (checked : ZcQ g k i = true) : Impossible g.mode (Zaj g) k (ZaM g k i).toFinset := by
  by_cases gone : Zck g k i=true
  · simpa [ZaM,gone] using (Zej (u:=g.mode) (T:=Zaj g) (cap:=k))
  rw [ZaM,if_neg gone]
  simp only [ZcQ,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have audit := checked.1
  replace checked := checked.2
  have hN := checked.1.1
  have hT : Zaj g ∉ ZbA g k i := by simpa [ZbA] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (ZbA g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply ZhW (raw:=vars g.mask) samples _ hN hT _ _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply Zfu _ _ _ _ _ (ZgA g) v
    exact (Zgy _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact Zft g ZaE h
  · intro tag xs hx
    have e : ((g.index k tag).bind (Zb6 g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact Zfv g _ names (prior (by omega)) h
  · intro a ha b hb d hd ka kb ne fr ready len
    have lt : d<4 := by rcases hd with h|h <;> omega
    exact Zgj (ZhI audit ready) hN ha hb ne lt fr (Nat.pos_of_ne_zero h0) len
def Zcx (g : Zad) (k i : Nat) :=
  if Zck g k i then true else
    let code := ZhN g.mask k i
    let r := fun t : Fin 6 => Fin.ofNat 512 ((code >>> (9*t.val)) &&& 511)
    let ws := ZbA g k i
    decide (ws.length=k+1 ∧ ws.Nodup ∧ (ws.map (ZaX r)).sum<ZaX r (Zaj g))
theorem Zgd {g k i} (h : Zcx g k i=true) :
    Impossible g.mode (Zaj g) k (ZaM g k i).toFinset := by
  by_cases gone : Zck g k i=true
  · simpa [ZaM,gone] using (Zej (u:=g.mode) (T:=Zaj g) (cap:=k))
  rw [ZaM,if_neg gone]
  simp only [Zcx,if_neg gone,decide_eq_true_eq] at h
  apply Zhv _
  · rw [List.toFinset_card_of_nodup h.2.1,h.1]
  · rw [ZdJ _ h.2.1]
    exact h.2.2
def Zbe (g : Zad) (k i : Nat) := Zcx g k i || ZcQ g k i
theorem Zdz (g : Zad) (k i : Nat)
    (samples : ZbI (Zaj g) (ZaJ fun j => (g.samples j).1) (ZaJ fun j => (g.samples j).2))
    (ZaE : ∀ ci ∈ g.ZaE, Slice g.mode (Zal (Za9 g.mask ci)) (Zaj g) (Zba ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.ZbT, ZbS (Zaj g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (Zaj g) (k-1) (ZaM g (k-1) j).toFinset)
    (h : Zbe g k i=true) : Impossible g.mode (Zaj g) k (ZaM g k i).toFinset := by
  simp only [Zbe,Bool.or_eq_true] at h
  rcases h with analytic|standard
  · exact Zgd analytic
  · exact ZeR g k i samples ZaE names prior standard
def block (g : Zad) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => Zbe g k (start+n) && block g k start n
theorem Zeu {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    Zbe g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem Zhk {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def ZbW (g : Zad) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def Zbu (g : Zad) (prior : Nat → Nat) :=
  (ZbX g.mask (fun j => (g.samples j).1) == BitVec.allOnes 91) &&
  (ZbX g.mask (fun j => (g.samples j).2) == 0) &&
  g.ZaE.all (fun c => ZbO g.mask c prior) &&
  g.ZbT.all (fun p => ZbS (Zaj g) (p.map swapRows))
theorem ZhQ (g : Zad) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Zak g.mode (Zal q) (Zaf q) (prior q))
    (geometry : Zbu g prior = true) (rows : ZbW g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (Zaj g) k (ZaM g k i).toFinset := by
  simp only [Zbu,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply Zdz g 0 i (ZdT geometry.1.1.1 geometry.1.1.2)
      (fun x hx => Zcr _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact Zeu (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply Zdz g _ i (ZdT geometry.1.1.1 geometry.1.1.2)
      (fun x hx => Zcr _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact Zeu (rows _ hk) i (by omega) (by omega)
def Zcj (g : Zad) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && Zcv (ZaM g k i) ws
theorem Zea {g top prior k i ws} (low : ∀ q, Zak g.mode (Zal q) (Zaf q) (prior q))
    (geom : Zbu g prior = true) (blocks : ZbW g top) (le : k ≤ top)
    (idx : Zcj g k i ws = true) : Impossible g.mode (Zaj g) k ws.toFinset := by
  simp only [Zcj,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←ZdC idx.2]
  exact ZhQ g top prior low geom blocks _ le i idx.1
theorem Zi6 {g prior i hints} (low : ∀ q, Zak g.mode (Zal q) (Zaf q) (prior q))
    (geom : Zbu g prior = true) (blocks : ZbW g g.cap)
    (idx : Zcj g g.cap i (vars g.mask) = true) (hp : ZaC (Zaj g) = true)
    (ess : ZaR (Zaj g) (vars g.mask) (ZbJ g.mask hints) = true)
    (all : (ZbJ g.mask hints).map Prod.fst = vars g.mask) :
    Zak g.mode (vars g.mask) (Zaj g) (g.cap+1) := by
  apply ZcI (ZaS _ hp) (ZaQ ess).1 (ZaQ ess).2 _ (Zea low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply ZbH ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem Zi4 {g prior ci hints} (low : ∀ q, Zak g.mode (Zal q) (Zaf q) (prior q))
    (ok : ZbO g.mask ci prior = true)
    (hp : ZaC (Zaj g) = true)
    (ess : ZaR (Zaj g) (vars g.mask) (ZbJ g.mask hints) = true)
    (all : (ZbJ g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : Zca g.mode (Zba ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (Zal (Za9 g.mask ci)) (vars g.mask)=true) :
    Zak g.mode (vars g.mask) (Zaj g) (g.cap+1) := by
  apply ZcI (ZaS _ hp) (ZaQ ess).1 (ZaQ ess).2 _ (ZcO (Zcr ci prior low ok) [] rfl nd cut)
  intro a ha
  apply ZbH ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Zbq (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Zak u (Zal e.1) (Zaf e.1) e.2
def ZcW (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem ZdF {u old L m relabels} (previous : Zbq u old)
    (main : Zak u (Zal m) (Zaf m) L)
    (ok : relabels.all (fun v => Zdd v.1 m v.2) = true) :
    Zbq u (ZcW old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact ZhZ (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem Zh5 : Zbq true [] := by simp [Zbq]
theorem Zi9 {u es} (h : Zbq true es) : Zbq u es := fun e he => ZhV (h e he)
def ZaF (v : Nat) (upper : Nat) := 2^92*upper+v
def Zam {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => ZaF (f x).toNat (Zam f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => ZaF 1 (units n)
theorem Zdb (x : Bits) : x.toNat < 2^92 :=
  lt_trans x.isLt (by decide +kernel)
theorem Zii (a b : Bits) (u v : Nat) :
    ZaF a.toNat u &&& ZaF b.toNat v = ZaF (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZaF,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (Zdb _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem ZiB (a b : Bits) (u v : Nat) :
    ZaF a.toNat u ||| ZaF b.toNat v = ZaF (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZaF,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (Zdb _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem Zij (a b : Bits) (u v : Nat) :
    ZaF a.toNat u ^^^ ZaF b.toNat v = ZaF (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ZaF,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (Zdb _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem Zb5 {α} (f g : α → Bits) (xs) :
    Zam f xs &&& Zam g xs = Zam (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [Zam]
  | cons a xs ih => simp only [Zam,Zii,ih]
theorem Zdk {α} (f g : α → Bits) (xs) :
    Zam f xs ||| Zam g xs = Zam (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [Zam]
  | cons a xs ih => simp only [Zam,ZiB,ih]
theorem Zct {α} (f g : α → Bits) (xs) :
    Zam f xs ^^^ Zam g xs = Zam (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [Zam]
  | cons a xs ih => simp only [Zam,Zij,ih]
theorem Zjc {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = Zam (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,Zam]
  | cons v xs ih => simp only [List.length_cons,units,Zam,ZaF,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def Zcs (r packed : Nat) := ((packed+r) >>> 91) &&& r
theorem ZiF (n i : Nat) (hi : i<n) : (units n).testBit (92*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,ZaF,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^92)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 92*(i+1)-92=92*i := by omega
      have ge : ¬92*(i+1)<92 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem Zix (a : Bits) : (a.toNat+1).testBit 91 = (a==BitVec.allOnes 91) := by
  by_cases h : a=BitVec.allOnes 91
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^91-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^91 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem ZiO {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (Zcs (units xs.length) (Zam f xs)).testBit (92*i) =
      (f xs[i]==BitVec.allOnes 91) := by
  simp only [Zcs,Nat.testBit_and,Nat.testBit_shiftRight,ZiF _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [Zam,List.length_cons,units,ZaF]
    have sum (u v x : Nat) : 2^92*u+x+(2^92*v+1)=2^92*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^92 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using Zix (f a)
    | succ i =>
      have ge : ¬92*(i+1)+91<92 := by omega
      have di : 92*(i+1)+91-92=92*i+91 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev Zb2 := Nat × Nat
abbrev Zc6 := Nat × Nat × Nat
def ZaY {α} (s : α → ZcB) (xs : List α) : Zb2 :=
  (Zam (fun x => (s x).1) xs,Zam (fun x => (s x).2) xs)
def Zcu {α} (c : α → Cov) (xs : List α) : Zc6 :=
  (Zam (fun x => (c x).1) xs,Zam (fun x => (c x).2.1) xs,
   Zam (fun x => (c x).2.2) xs)
def Zbf (d : Bool) (a : Zb2) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem ZcA (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem ZcN {α} (s : α → ZcB) (xs : List α) (d : Bool) :
    Zbf d (ZaY s xs) = Zam (fun x => column d (s x)) xs := by
  cases d <;> simp only [Zbf,ZaY,column,Bool.false_eq_true,ite_false,ite_true,Zb5,Zct,ZcA]
def Zbz (op : Nat) (a b : Zb2) : Zb2 :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem Zih {α} (a b : α → Zab) (xs : List α) (op : Nat) :
    Zbz op (ZaY (fun x => (a x).2) xs) (ZaY (fun x => (b x).2) xs) =
    ZaY (fun x => (Zat op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [Zbz,h0,ite_true,ZaY,Zb5,Zat,bv]
  by_cases h1 : op=1
  · simp [Zbz,h1,ZaY,Zdk,Zat,bv]
  by_cases h2 : op=2
  · simp [Zbz,h2,ZaY,Zb5,Zct,ZcA,Zat,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [Zbz,h0,h1,h2,ite_false,ZaY,Zb5,Zct,ZcA,Zat,bv,e]
def Zcp (c : Zc6) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem ZgN {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    Zcp (Zcu c xs) (Zam a xs) (Zam b xs) ka kb =
    Zam (fun x => ZbD (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [Zcp,Zcu,Zb5,Zdk,Zct,ZcA,ZbD,Zbb,ZbQ,
      Bool.false_eq_true,ite_false,ite_true]
def Zas (c : Zar) (i : Nat) := c.2.2.1.getD i Zbs
def Za8 (c : Zar) (i j op : Nat) (ka kb : Bool) :=
  let a := Zas c i
  let b := Zas c j
  Zbl c op a b (Zat op a b) ka kb
def Zda (c : Zar) (d ka kb : Bool) (op i j : Nat) :=
  let a := Zas c i
  let b := Zas c j
  ZbD c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (Zat op a b).2
def Zb9 {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && Zb9 f (mask >>> 92) xs
theorem Zie {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (92*i)=true) (ok : Zb9 f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [Zb9,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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
      apply ih (mask:=mask >>> 92) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List Zb2 × Zc6
def Za4 (k n : Nat) (xs : List Zar) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => ZaY (fun c => (Zas c i).2) xs),
    Zcu (fun c => c.2.2.2.1.1) xs)
def ZbP (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem ZdX (k n) (xs) {i : Nat} (h : i<n) :
    ZbP (Za4 k n xs) i = ZaY (fun c => (Zas c i).2) xs := by
  simp [ZbP,Za4,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def ZdA (u : Bool) (p : Zax) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (Zan p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (Zan p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem ZhD (d x : Sig) : Zan d (neg x) = d ^^^ Zan d x := by
  apply ZaT
  intro r
  simp only [Zan,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem Zce (u) (p : Zax) (x : Sig) :
    Zaw u p.domain p.wires x = ZdA u p (Zan p.domain x) := by
  simp only [Zaw,ZdA,ZhD]
def ZaW (p : Zab → Bool) (a : Zab) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem Zem (p : Zab → Bool) (ws : List Zab) (a : Zab) (keep : Bool) :
    ws.countP p ≤ (ZaU ws a keep).countP p + ZaW p a keep := by
  cases keep
  · simp only [ZaU,Bool.false_eq_true,ite_false,ZaW,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [ZaU,ZaW]
theorem Zic (p : Zab → Bool) (ws : List Zab) (a b : Zab) (ka kb : Bool) :
    ws.countP p - ZaW p a ka - ZaW p b kb ≤
    (ZaD ws a b ka kb).countP p := by
  have h1 := Zem p ws a ka
  have h2 := Zem p (ZaU ws a ka) b kb
  simp only [ZaD]
  omega
abbrev Zed := Zax × Nat × Bool
def Zch (u : Bool) (ws : List Zab) (p : Zax) : Zed :=
  (p,ws.countP (fun w => ZaG p.domain w.1),
     ws.all (fun w => Zaw u p.domain p.wires w.1))
def Zcy (s : Zed) (k : Nat) (a b : Zab) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let const := fun w : Zab => ZaG p.domain w.1
  let z := Zay (Za6 op a b)
  let zm := Zan p.domain z
  let zc := ZaG p.domain z
  let cm := s.2.1 - ZaW const a ka - ZaW const b kb + zc.toNat
  let free := zc || zm==Zan p.domain a.1 || zm==Zan p.domain b.1
  decide (k+p.Zav+(!free).toNat < p.bound+cm)
theorem ZgE {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (al : ZbN u op=true)
    (h : Zcy (Zch u ws p) k a b op ka kb=true) :
    Zbd u p k ((ZaD ws a b ka kb).map Prod.fst) (Za6 op a b)=true := by
  let z := Zay (Za6 op a b)
  let const := fun w : Zab => ZaG p.domain w.1
  let free := ZaG p.domain z || Zan p.domain z==Zan p.domain a.1 ||
      Zan p.domain z==Zan p.domain b.1
  let rest := ZaD ws a b ka kb
  have ck := Zic const ws a b ka kb
  change ws.countP const - ZaW const a ka - ZaW const b kb ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => Zaw u p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → Zaw u p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [Zaw,ZaG,Bool.or_eq_true] at zc ⊢
        exact Or.inl (Or.inl zc)
      · rw [Zce,za,←Zce]
        exact hav _ ha
      · rw [Zce,zb,←Zce]
        exact hav _ hb
    have extra : (!Zaw u p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : Zaw u p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (Zaw u p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((Zdj ws a b ka kb).subset hw)
    have opOK : Zbw u p.domain p.wires (Za6 op a b)=true := by
      simp [Zbw,Za6,hav _ ha,hav _ hb,al]
    simp only [Zcy,Zch,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.Zav+(!free).toNat < p.bound+(ws.countP const - ZaW const a ka -
        ZaW const b kb+(ZaG p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [Zbd,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.Zav+(!Zaw u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if ZaG p.domain z then 1 else 0)
    cases hc : ZaG p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [Zcy,Zch,all] at h
def ZeJ (c : Zar) (i j op : Nat) (ka kb : Bool) :=
  let a := Zas c i
  let b := Zas c j
  (c.2.2.2.2.1.map (Zch c.2.2.2.1.2 c.2.2.1)).any (fun s => Zcy s (c.1-1) a b op ka kb)
theorem Zg6 {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (al : ZbN c.2.2.2.1.2 op=true)
    (h : ZeJ c i j op ka kb=true) : Za8 c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : Zas c t ∈ c.2.2.1 := by
    simp [Zas,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := ZgE (mem _ hi) (mem _ hj) al ok
  have cut : c.2.2.2.2.1.any (fun p => Zbd c.2.2.2.1.2 p (c.1-1)
      ((ZaD c.2.2.1 (Zas c i) (Zas c j) ka kb).map Prod.fst)
      (Za6 op (Zas c i) (Zas c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [Za8,Zbl,ZbZ,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def ZcC (c : Zar) (ka kb : Bool) :=
  (1+(c.2.1-(if ka then 0 else 1)-(if kb then 0 else 1))==c.1) && c.2.2.2.2.2.2
theorem ZgF {c i j op ka kb} (fast : ZcC c ka kb=true) : Za8 c i j op ka kb=true := by
  rcases c with ⟨k,n,ws,cov,pools,links,flag⟩
  simp only [ZcC,Bool.and_eq_true,beq_iff_eq] at fast
  simp [Za8,Zbl,fast.1,fast.2]
def Zc3 (c : Zar) (i j op : Nat) (ka kb : Bool) :=
  if ZcC c ka kb then true else
  (if (i<c.2.2.1.length ∧ j<c.2.2.1.length) ∧ ZbN c.2.2.2.1.2 op=true then ZeJ c i j op ka kb else false) ||
    Za8 c i j op ka kb
theorem Zgg {c i j op ka kb} (h : Zc3 c i j op ka kb=true) :
    Za8 c i j op ka kb=true := by
  by_cases early : ZcC c ka kb=true
  · exact ZgF early
  rw [Zc3,if_neg early] at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact Zg6 yes.1.1 yes.1.2 yes.2 h
    next => contradiction
  · exact h
def Zef (u : Bool) (b : Batch) (xs : List Zar) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else if (len==k) && (xs.all (fun c : Zar => c.2.2.2.2.2.2)) then true else
    let a := ZbP b i
    let b' := ZbP b j
    let z := Zbz op a b'
    let mask := Zcs r (Zcp cov (Zbf (!u) a) (Zbf (!u) b') ka kb ||| Zbf (!u) z)
    Zb9 (fun c => Zc3 c i j op ka kb) mask xs
theorem ZgX {u} (k n) (xs : List Zar) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (pass : Zef u (Za4 k n xs) xs i j op ka kb=true) :
    Za8 xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : Za8 xs[q] i j op ka kb =
      if len>k then true else if (len==k) && xs[q].2.2.2.2.2.2 then true else if Zda xs[q] (!u) ka kb op i j != BitVec.allOnes 91 then true
      else if !ZaC (Zat op (Zas xs[q] i) (Zas xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(Zat op (Zas xs[q] i) (Zas xs[q] j)).1)
      then true else ZbZ u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2.1 (k-1)
        ((ZaD xs[q].2.2.1 (Zas xs[q] i) (Zas xs[q] j) ka kb).map Prod.fst)
        (Za6 op (Zas xs[q] i) (Zas xs[q] j)) := by
    simp only [Za8,Zbl,budget,arity,mode,len,Zda] <;> rfl
  by_cases early : ((len==k) && xs[q].2.2.2.2.2.2)=true
  · by_cases tooLong : len>k <;> simp [eval,tooLong,early]
  have notAll : ((len==k) && (xs.all (fun c : Zar => c.2.2.2.2.2.2)))≠true := by
    intro all
    simp only [Bool.and_eq_true,List.all_eq_true] at all
    apply early
    simp only [Bool.and_eq_true]
    exact ⟨all.1,all.2 _ (List.getElem_mem hq)⟩
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := ZbP (Za4 k n xs) i
    let b := ZbP (Za4 k n xs) j
    let cov := Zcu (fun c : Zar => c.2.2.2.1.1) xs
    change (if len>k then true else if (len==k) && (xs.all (fun c : Zar => c.2.2.2.2.2.2)) then true else Zb9 _ (Zcs r
       (Zcp cov (Zbf (!u) a) (Zbf (!u) b) ka kb |||
        Zbf (!u) (Zbz op a b))) xs) = true at pass
    rw [if_neg small,if_neg notAll] at pass
    have ca : a = _ := ZdX k n xs hi
    have cb : b = _ := ZdX k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,Zih,ZcN,ZcN,ZcN,ZgN,Zdk] at pass
    by_cases hit : Zda xs[q] (!u) ka kb op i j = BitVec.allOnes 91
    · apply Zgg
      apply Zie _ _ _ q hq _ pass
      rw [ZiO _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_neg early,if_pos (bne_iff_ne.mpr hit)]
def Zeg (u : Bool) (b : Batch) (xs : List Zar) (i j op : Nat) :=
  let f := Zef u b xs i j op
  f false false && f true false && f false true && f true true
def Zcw (u : Bool) (b : Batch) (xs : List Zar) (i : Nat) (js : List Nat) :=
    js.all (fun j => (ZbF u).all (Zeg u b xs i j))
def ZbK (u : Bool) (b : Batch) (xs : List Zar) : List Nat → Bool
  | [] => true
  | i::js => Zcw u b xs i js && ZbK u b xs js
theorem ZgY {u} (k n) (xs : List Zar) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : ZbK u (Za4 k n xs) xs js=true) :
    Zbc xs[q] (js.map (Zas xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [ZbK,Bool.and_eq_true,Zcw,List.all_eq_true] at allRows
    simp only [List.map_cons,Zbc,Zdv,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @ZgX u k n xs i j op
    simp only [Zeg,Bool.and_eq_true] at pass
    simp only [ZbB,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode pass.1.1.1,check hi hj' hq budget arity mode pass.1.1.2⟩,
      check hi hj' hq budget arity mode pass.1.2⟩,check hi hj' hq budget arity mode pass.2⟩
def Zdo (u : Bool) (k n : Nat) (xs : List Zar) :=
    ZbK u (Za4 k n xs) xs (List.range n)
theorem ZhF {u k n} {xs : List Zar} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (hn : xs[q].2.2.1.length=n)
    (pass : Zdo u k n xs=true) : Zbc xs[q] xs[q].2.2.1=true := by
  have all := ZgY k n xs hq hb ha hm (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (Zas xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [Zas,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def Zb4 (g : Zad) (k i : Nat) : Zar :=
  let raw := Zcb g
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := Zdn g k i
  let rules := (Zdg g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (Zb6 g (k-1))).toList
  (k,ws.length,ws,Zcc g.mode ws,rules,ls,Zcg g k i)
def ZeM (T : Sig) (c : Zar) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem Zg5 (g : Zad) (k i : Nat) (valid : Zbr g k i=true)
    (h : (ZeM (Zaj g) (Zb4 g k i) &&
      (if k=0 then true else Zbc (Zb4 g k i) (Zb4 g k i).2.2.1))=true) :
    Zbe g k i=true := by
  rw [Zbe,Bool.or_eq_true]
  apply Or.inr
  change (Zbr g k i && _) = true
  rw [Bool.and_eq_true]
  exact ⟨valid,h⟩
theorem Zen {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → Zbe g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def Zhw (g : Zad) (k start n : Nat) :=
  (List.range n).all (fun j => Zcx g k (start+j))
theorem ZeW {g k start n} (all : Zhw g k start n=true) :
    block g k start n=true := by
  apply Zen
  intro i low high
  have one := List.all_eq_true.mp all (i-start) (List.mem_range.mpr (by omega))
  rw [Zbe,Bool.or_eq_true]
  exact Or.inl (by simpa only [Nat.add_sub_of_le low] using one)
def Zbx (g : Zad) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (Zb4 g k)
def header (g : Zad) (k start n ar : Nat) :=
  ((List.range n).all (fun j => Zbr g k (start+j))) &&
  (Zbx g k start n).all (fun c => c.2.1==ar && ZeM (Zaj g) c)
def Zbp (g : Zad) (k start n ar lo len : Nat) :=
  let xs := Zbx g k start n
  let b := Za4 k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    Zcw g.mode b xs i (List.range' (i+1) (ar-(i+1))))
theorem Zde {g k start n ar lo len} (h : Zbp g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    Zcw g.mode (Za4 k ar (Zbx g k start n)) (Zbx g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem Zg9 {g k start n ar lo a b}
    (h : Zbp g k start n ar lo a=true) (t : Zbp g k start n ar (lo+a) b=true) :
    Zbp g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact Zde h (lo+j) (by omega) (by omega)
  · exact Zde t (lo+j) (by omega) (by omega)
theorem ZiJ {g k start n ar} (h : Zbp g k start n ar 0 ar=true) :
    Zdo g.mode k ar (Zbx g k start n)=true := by
  let xs := Zbx g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      ZbK g.mode (Za4 k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,ZbK,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := Zde h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold Zdo
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem Zh9 {g k start n ar} (hd : header g k start n ar=true)
    (h : Zbp g k start n ar 0 ar=true) : block g k start n=true := by
  apply Zen
  intro i lo hi
  let xs := Zbx g k start n
  have hm : Zb4 g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  rw [header,Bool.and_eq_true] at hd
  have audit := List.all_eq_true.mp hd.1 (i-start) (List.mem_range.mpr (by omega))
  have valid : Zbr g k i=true := by simpa only [Nat.add_sub_of_le lo] using audit
  have one := List.all_eq_true.mp hd.2 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  apply Zg5 _ _ _ valid
  rw [Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ ZhF hq hb ha hm hn (ZiJ h)
def ZcH (g : Zad) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => Zbp g k start n ar lo num=true
  | d+1 => ZcH g k start n ar lo (num/2) d ∧ ZcH g k start n ar (lo+num/2) (num-num/2) d
theorem Zis {g k start n ar lo num d} (h : ZcH g k start n ar lo num d) :
    Zbp g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := Zg9 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def Zdx (g : Zad) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ ZcH g k start n ar 0 ar rows
  | d+1 => Zdx g k start (n/2) ar rows d ∧ Zdx g k (start+n/2) (n-n/2) ar rows d
theorem Zi8 {g k start n ar rows d} (h : Zdx g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact Zh9 h.1 (Zis h.2)
  | succ d ih =>
    have v := Zhk (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def Zcn {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => Zcn f (xs.take (xs.length/2)) d ∧ Zcn f (xs.drop (xs.length/2)) d
theorem ZdG {α f xs d} (h : @Zcn α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem Zh3 {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Zak u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,ZcL pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)
theorem Zjf {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Zak u (Zal q) (Zaf q) (prior q))
    (e : (Zaf q == Zaf m && (Zal q == vars m) && (prior q == cap+1) && ZaC (Zaf m) &&
      decide (vars m).Nodup && Zca u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (Zaf m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact ZcO (Zh3 (ZaS _ e4) h) [] rfl e5 e6
def ZbU (m : Nat) : List Sig := vars m ++ [Za0]
theorem Zjd {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Zak u (Zal q) (Zaf q) (prior q)) (ci : Zbt)
    (ok : ZbO m ci prior = true)
    (cut : (decide ws.Nodup && Zca u (Zba ci.1 ci.2.1) ci.2.2.2.2 cap 0 (Zal (Za9 m ci)) ws)=true) :
    Impossible u (Zaf m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact ZcO (Zcr ci prior low ok) [] rfl cut.1 cut.2
theorem ZhT {u} {g : Zad} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Zak u (Zal q) (Zaf q) (prior q))
    (geom : Zbu g prior = true) (blocks : ZbW g cap)
    (idx : Zcj g cap i ws = true) : Impossible u (Zaf m) cap ws.toFinset := by
  subst hm
  subst hu
  exact Zea low geom blocks (Nat.le_refl _) idx
def ZeO (m hints : Nat) : Bool :=
  let xs := ZbJ m hints
  ZaC (Zaf m) && ZaR (Zaf m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem Zik {u} {m hints cap : Nat} (ok : ZeO m hints = true)
    (a : Impossible u (Zaf m) cap (vars m).toFinset) : Zak u (vars m) (Zaf m) (cap+1) := by
  simp only [ZeO,Bool.and_eq_true,beq_iff_eq] at ok
  apply ZcI (ZaS _ ok.1.1) (ZaQ ok.1.2).1 (ZaQ ok.1.2).2 _ a
  intro v hv
  apply ZbH ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def Zh4 (l : List (Nat × Nat)) : List (Sig × Row × Row) :=
  l.map fun (i,r) => (inputs.getD i zero,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def ZcF (m : Nat) (l : List (Nat × Nat)) : Bool :=
  let xs := Zh4 l
  ZaR (Zaf m) (ZbU m) xs && (xs.map Prod.fst == vars m) && ZaC (Zaf m)
theorem Zhb {u} {m l} (ok : ZcF m l = true) {k : Nat} {S : Finset Sig}
    (h : Zae u (Zaf m) k S) (sub : ∀ v ∈ S, v ∈ ZbU m) :
    S=(vars m).toFinset ∨ S=(ZbU m).toFinset := by
  simp only [ZcF,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := ZbH ess v (List.mem_toFinset.mpr hv)
    exact Zci h (ZbU m) v sub r s hd hi
  by_cases hs : Za0 ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact rest v hv
    · rwa [List.mem_singleton.mp hv]
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases List.mem_append.mp (sub v hv) with hv' | hv'
    · exact hv'
    · exact absurd (List.mem_singleton.mp hv' ▸ hv) hs
theorem Zjb {u} {m l cap} (ok : ZcF m l = true)
    (a : Impossible u (Zaf m) cap (vars m).toFinset)
    (b : Impossible u (Zaf m) cap (ZbU m).toFinset) :
    Zak u (ZbU m) (Zaf m) (cap+1) := by
  have ok' := ok
  simp only [ZcF,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := Zco (ZaS _ ok'.2) (ZaQ ok'.1.1).1 (ZaQ ok'.1.1).2 hr ha
  by_contra! small
  rcases Zhb ok run hs with e | e
  · exact a k (by omega) (e ▸ run)
  · exact b k (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zi3 : Zak true (vars 3) (Zaf 3) 1 := ZiS (hints:=1) (by decide +kernel)
def ZcG := ZcW [] 1 [(12,[49,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ZeN : Zbq true ZcG := ZdF (m:=3) Zh5 Zi3 (by decide +kernel)
def ZiX (i : Nat) : Nat := 0xf
def ZiY : Zbm := (1,0,1,0,0,0,0,0x0,ZiX)
def ZhS : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffff,0x7ffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def ZhR : List Zbt := []
def Ziu : List (List Nat) := [[],[48,33]]
def Zib : Nat → Zbm
  | 3 => ZiY
  | _ => Zg2
def Ziv : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Zad := ⟨15,3,fun j => ZhS[j]?.getD (0,0),ZhR,Ziu,Zib,Ziv⟩
set_option maxHeartbeats 0 in
theorem ZiK : Zbu g15 (ZcR ZcG) = true := by
  simp only [Zbu,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,ZdG (d:=0) ?_⟩,ZdG (d:=0) ?_⟩
  all_goals simp only [Zcn]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ZiE : block g15 3 0 1=true := by
  exact ZeW (by decide +kernel)
theorem Zio : block g15 3 0 1=true := ZiE
theorem Zim : ZbW g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact Zio
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zi2 : Zak true (vars 15) (Zaf 15) 4 := Zik (hints:=8449) (by decide +kernel) (ZhT (g:=g15) (i:=0) rfl rfl (ZgZ ZcG ZeN) ZiK Zim (by decide +kernel))
def ZiM := ZcW ZcG 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(270,[131,115,99,83,50,33,16,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(420,[131,33,114,99,32,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem Zje : Zbq true ZiM := ZdF (m:=15) ZeN Zi2 (by decide +kernel)
def Zi1 (i : Nat) : Nat := 0x11a20bf
def Zjk : Zbm := (1,0,3,0,0,0,0,0x0,Zi1)
def Zjh (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def Zi0 (i : Nat) : Nat := 0x3f481fa20
def Zjj : Zbm := (2,1,3,1,1,0,0,0x0,Zi0)
def Zjg (i : Nat) : Nat := 0x300
def ZiZ (i : Nat) : Nat := 0x5dd45
def Zji : Zbm := (1,2,3,2,0,0,0,0x0,ZiZ)

end PEqualNP.Outside.L_meta_670.Zhi
