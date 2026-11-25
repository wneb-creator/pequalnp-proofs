import Mathlib
import PEqualNP.Defs

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
-- First-gate bound and verified certificate from Daniel Gallups, L-meta-1674 (PR 8766).
namespace PEqualNP.Outside.L_meta_5146
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
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
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
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

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
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
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 2 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 2) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ u k S, k ≤ (if u then 13 else 14) ∧ Live u graph k S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply bit_ext
    intro r
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at goalEq
    change (execute gs (inputs++[gv inputs g])).getD C.output zero = graph at goalEq
    rw [eq0] at goalEq
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    have mode : ∃ u : Bool, (u=false → ∀ g ∈ gs, isNot g=false) ∧ gs.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
      by_cases hn : ∀ g ∈ gs, isNot g=false
      · refine ⟨false,fun _ => hn,?_⟩
        have := List.countP_le_length (p:=fun g => !isNot g) (l:=gs)
        simp only [Bool.false_eq_true,ite_false]
        omega
      · refine ⟨true,by simp,?_⟩
        push Not at hn
        obtain ⟨g,hg,hx⟩ := hn
        have lt : gs.countP (fun g => !isNot g) < gs.length := by
          rcases Nat.lt_or_ge (gs.countP (fun g => !isNot g)) gs.length with h | h
          · exact h
          · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
            simp only [Bool.not_eq_true'] at eq
            exact absurd eq hx
        simp only [ite_true]
        omega
    obtain ⟨u,mono,count⟩ := mode
    have out := get_rep (u:=u) (execute gs (inputs++[seed])) C.output
    rw [goalEq] at out
    unfold Repr at out
    have pg : bit 0 graph=false := by decide +kernel
    rw [nrm_id pg] at out
    have targetIn := out.resolve_right (fun hn => hn graph_proper)
    obtain ⟨k,S,hk,run,hs⟩ := extract gs _ tailLegal mono graph_proper targetIn
    have ns : (inputs++[seed]).all plainWord=true := by decide +kernel
    rw [nrm_map ns] at hs
    exact ⟨u,k,S,by omega,run,hs⟩

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
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

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut g.mode (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
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
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (u : Bool) (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (masked p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem available_mask (u) (p : BoundPool) (x : Sig) :
    availableB u p.domain p.wires x = availableMasked u p (masked p.domain x) := by
  simp only [availableB,availableMasked,masked_comp]

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

abbrev QuickPool := BoundPool × Nat × Bool
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
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

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {u} {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
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
theorem strong_full {u} {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible u (graphGoal q) cap (vars q).toFinset)
    (b : Impossible u (graphGoal q) cap (varsX m).toFinset) :
    Lower u (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) (essential_plain ok'.1.1.1).1 (essential_plain ok'.1.1.1).2 hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47473,0x173652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe97a7f,0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg15_3 : block g15 3 0 1=true := sg15_3_0
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact allg15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound [] baseKnown) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd15d16630b273,0x11525c6a12412),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe90c286464e7f,0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_6 : block g31 6 0 1=true := sg31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_5_0 : block g31 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_5 : block g31 5 0 2=true := sg31_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_4_0 : block g31 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_4 : block g31 4 0 1=true := sg31_4_0
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact allg31_4
  · exact allg31_5
  · exact allg31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))
def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known47 := extendKnown known31 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffad506dc8c692839f653,0xf04d190d4828112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9aa3b7e53917e26487f,0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def g111autos : List (List Nat) := [[],[32,83]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg111_6 : block g111 6 0 1=true := sg111_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_5_0 : block g111 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg111_5 : block g111 5 0 1=true := sg111_5_0
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact allg111_5
  · exact allg111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac458a9750042f2dc84f,0x4c61e4544061425c84a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9958e417a60021ce0f8f,0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_7 : block g189 7 0 1=true := sg189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_6_0 : block g189 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_6 : block g189 6 0 2=true := sg189_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_5_0 : block g189 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_5 : block g189 5 0 1=true := sg189_5_0
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact allg189_5
  · exact allg189_6
  · exact allg189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))
def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def known127 := extendKnown known189 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda8e80efa31334f8b77110a294fa2c140112476e217263,0x1a8204e622010a10823154424006181028000900212202),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe550613dee46b171e50184200e13000163a237ccc4483f,0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_10 : block g191 10 0 1=true := sg191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_9_0 : block g191 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_9 : block g191 9 0 12=true := sg191_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_0 : block g191 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_3 : block g191 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_39 : block g191 8 39 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_70 : block g191 8 70 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_106 : block g191 8 106 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_8 : block g191 8 0 113=true := (@block_merge g191 8 0 106 7 (@block_merge g191 8 0 70 36 (@block_merge g191 8 0 39 31 (@block_merge g191 8 0 3 36 sg191_8_0 sg191_8_3) sg191_8_39) sg191_8_70) sg191_8_106)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_13 : block g191 7 13 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_49 : block g191 7 49 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_85 : block g191 7 85 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_7 : block g191 7 0 116=true := (@block_merge g191 7 0 85 31 (@block_merge g191 7 0 49 36 (@block_merge g191 7 0 13 36 sg191_7_0 sg191_7_13) sg191_7_49) sg191_7_85)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_6_0 : block g191 6 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_6 : block g191 6 0 12=true := sg191_6_0
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact allg191_6
  · exact allg191_7
  · exact allg191_8
  · exact allg191_9
  · exact allg191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)
def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe383f541a14f4a486b2153ac6cc220d9a4c042882144400812c1a03824014a3e21f653,0x3835041a0c802027c003361601060690134460c209508104109022004008a24212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc798b2d38f019ccd955a0208a2083da20800120c010a1d5456e25c86f4208c8c6481f,0x1c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x7f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0x3d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0x80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x8003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0x167c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x147c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x183c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x18382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x119338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x11338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xfc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x6c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_12 : block g383 12 0 1=true := sg383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_11_0 : block g383 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_11 : block g383 11 0 6=true := sg383_11_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_0 : block g383 10 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_6 : block g383 10 6 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_19 : block g383 10 19 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_10 : block g383 10 0 47=true := (@block_merge g383 10 0 19 28 (@block_merge g383 10 0 6 13 sg383_10_0 sg383_10_6) sg383_10_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_0 : block g383 9 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_3 : block g383 9 3 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_39 : block g383 9 39 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_75 : block g383 9 75 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_111 : block g383 9 111 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_119 : block g383 9 119 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_9 : block g383 9 0 136=true := (@block_merge g383 9 0 119 17 (@block_merge g383 9 0 111 8 (@block_merge g383 9 0 75 36 (@block_merge g383 9 0 39 36 (@block_merge g383 9 0 3 36 sg383_9_0 sg383_9_3) sg383_9_39) sg383_9_75) sg383_9_111) sg383_9_119)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_0 : block g383 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_36 : block g383 8 36 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_44 : block g383 8 44 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_8 : block g383 8 0 53=true := (@block_merge g383 8 0 44 9 (@block_merge g383 8 0 36 8 sg383_8_0 sg383_8_36) sg383_8_44)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_7_0 : block g383 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_7 : block g383 7 0 2=true := sg383_7_0
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact allg383_7
  · exact allg383_8
  · exact allg383_9
  · exact allg383_10
  · exact allg383_11
  · exact allg383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
def xud13 (i : Nat) : Nat := 0x10d0b09070402007ffd20
def xul13 : Packing := (1,1,7,0,0,0,0,xud13)
def xuh13 (i : Nat) : Nat := 0x82c001211a40ba2c8152031078233800802004121800100650280000000000004a3b107c04f47e80710100d000601cc192100000003c1c000a0480000000740940801058018
def xud12 (i : Nat) : Nat := 0x700f84c2c050d824dc0028a0b05f0c86c2e0e0289800200eb0d0502b84c1a0f050003e31270107b4338403e0c308680c01181452480f860960d09018023020a00e1707820524c0e7c28460a8503e0e06830821a028980021d84c321b06830383e028c8002178341e181c0a06a300e8c302f0b8305226000803a70a07c360e0300449c2f85c360c0e0080a25004c360c0f0146400f84c360d190180180015c2617078280a4d01703e170d8344c06001648570985c1a1a0382800513850960c0e86c1406008b9158273487850f91b0af9558959091c53025187c8a309a003ffaa6907ff64520ffec9a41ffd83483ffb02907ffe4d20ffe98a41ffd98483fff30907ffe4520bffc8a41ff910482fff30905ff66120ffc982417fd91482ffb26905ffe4d20
def xul12 : Packing := (18,2,7,0,0,11,0,xud12)
def xuh12 (i : Nat) : Nat := 0x10891c12ae1080001805a263d80ac4110000060fc00000001e89380362813a05d006740851407a876a021c0b7e0bc0014600cc07bc026c0e2c093681600005099825a8cc3210ce0ef4048808720a2a8c2209680d9e0db68efe0ae002a007e8018204ba04fc0b820e800016924c1264a6b00cc289f08fee8e3802828f728f96e69e129c867e0c06051491ae0b1482100782c2c80bb8009c82b0f27c045010f40d060300001a6d94099a1146060e080e0422133687a8cb20001a888000100ce689ccc980000205520596898010a001180eb40a580de201ee1188ce2883780c7005660034038206f20b360e18e4a20c5a905208d80cb026bc0e548d8691f48ce803e2e842f2aa0948c49c12f4f2200d628fda103af0e609b08a5e8cc0000000120f320620001006c00000000009ec101608348b3008ec8a241200001e83f6113e91200002064000048090104c0c268e5690c001200010124412dc8f200008a1da0b520a9411ee0a6201b201ce0d5eadc080f40dd28c80894611c603aaa43611688aeac79812362e3e07c0001483ae00e0000000000000001af32000000000000a8e62928000142dc002c0ef0000010c2a005002f8ea46073605e000000000000004c000100fa000000000000c83840320001e074e00aa9190040213180340001487c0000600600018071af2ce0fe68c400000eb80000606880ec0000000108d70c720001a11a204762420000e88c40f920bfc8ca000120a000000001808800f400002016000060232076000160f7a00120c8021d92a4a03d8886a1076091c0f1009da053080600016848a06a000068fbacfa0000000128ece8d0000080e60001e0aa60d20001008be02400002a5a0000000014484000ea9918a421d12251001e5c99a00041000e480012e2401510205a5000ca95026000110e8200422022906080000034006082c0830000080105c0861008a8f02040180c40001
def xud11 (i : Nat) : Nat := (if i<1 then 0x626088a61de85d614883ce0b281c603a7fbdfc27e2df547c4ded27a6de5a78b5df676fdd7e74cdcd4724dc66706dbd06e65b766d25b126b6da906915a0e670d98c655590a632586a60a57f25eed78e5d3570c5b2d68a585d5e0567d522538546e50653c44dbd3384c052ca4a2525247f51d046dd18044fd0fe431d0543ffcfbe3dccf503c3cea63944dfc364cd3433ccc9e314cbf42eccb682bfcaaa297ca1426d494c23b48b6215c8021edc76c1c846c21a0464017fc5c81554500128447e10cc3de0e2433e0b7c28008841cc058c11803340780104000fff54f98483ffd8154d20fff6a553483ffea954d20fff54d98483ffd9360520fff54f91483ffd854c520fff54d91483ffea960d20fff61793483ffda960d20fff60d91483ffd83e4520fff69583483ffca954d20fff61593483ffda160d20dff54d914837fd9366120bff6a1914837fea960520bffe95934837fd95e4d20ffe68530482fffa960520dff64d914837fd83e4520bff68d914837fda3e4520dff607934837fda164d20ffe4c3984837fd53e6120dff61593483ff93064520bffe9583483ff9a84c120bff68f98483ff930e4520dff4c5984837fda5e4d20eff605984837fda166120bffea1934837fd51e4d20bff68f91483ff9a844120dff6a391483ff99544120ffb54b934837fd98e4d20dff64f98483ff98544120dff6a5814837fd93e4520dff655314837fda960d20dff66191482fffa960d20bff697934837fea954d20dffaa5834837fda864d20dff4c7984837fda864520bffe8d814837ffa564d20fbfe99814837fda564d20ffd60791483ff95344120ffb54993483ff99344120dff68f98483ffba066120dff66391483ff5814c520ffe68d10482ffda366120dff61793483ff99844120ffe695304837fd8364520bffe85934837fd8164d20ffe615304837fda954d20ffe60d104837ffa864d20dffe85934837fda364520ffe4c198483ff9a04c520ffe4c1814837fda8e4d20dffaa531483fbfa464d20bffe8583482ffda8e4d20dffe85984837fd53e4520bffe8d98482ffda8e4520dff65593483ff9a544120bffe85984827fda564d209ff68598482ffba14c120defe91934827fca94c5209ff2a5534837dd93e4d209ff6a391482effa6605209ffe97934827ffa3e45209ff69793483fd9304c5209ffe85984827fda1e61209ff68d91483ff15144120ff64c153482ffba0661209ff68f914827ffa864d209ff687934836fda6e61209ffea391482ff9a344120ffc44391482ffba344120dfde4591483fbba44c120ffa549304837f930e61209ffe95934833fd98e61209ffea1914827fda8e4d209ffe8f98483fd930e4d209ff68f98482fbfa464d20ffa549104837f581e4520bbf69b984827ffa364520dfe4c1984827ffa164d209bf69b984827bfa464d20 else (if i<2 then 0x6140e02081002c1706611140180007020332830c1c000400e121818a0d834001aa302f3c2e07b0b008110005f44b3690b28c0300704027305a07034079285415010b583c0008386082200038500c04e76140503c07020a0c010110c3a0ac0a0908082080386214143942428060272860c2e00800301401e70b28580c07044100bcec600a0780e04140fc0c0761b00c04923e00c18060785e523027c0092040a18600c18060a050079c04e1b83c018c040d0030b008100851210326cda414a14230540f090c0a86c0a05e07968c0180709c1a280f428101110126140703c0e020d81b0b436020c05460b41501c360bc0f306000031428101118070420402026c03010d433a4d8c5831008100381e5084250c0140d022342d0bb0c03d098085012e0019848c630186101501c10020c0c42a03b060d04e0960380050c4ae158000fc042f6329366d019060820100382818850885e006140703e89c05934600c280a1405e5c018401c1a03ca8005a0385e07941840486a1408088c0a8100385a1515150568501c0fc0593a2500280e1404840202a102a0a1260d044501f0320c2a060103010429061480e121a856100703c082e00c184ec284c0381e12d1380b26bc0586e0c8306300a3024403e428300400e111a856158308c140202238421001e307c18610070400830641850d80f04093378007c04282c01c2562700c041009d1c280fc1b13808200402a80a382e13830500fe33010c008570a1c81c190340b0560880e90b00c0380a0940730280780e0a868198100723010940aa2440c00083f0d837074250a4960380020901693e099b0a007370612814c9d121400e70cb01c038266c3f01e930f80852001680f44e021805007a1840940fc068cc00083f0c0370780e014600e70c02d01e890ed93c042803d3c370a10020c19130000f8081ea40025e0807a0f010c02803d203a018081e0c14300200709701c02890a00f4d0c1004f8060217b180d23850178362701a4c073f0dc1919806021380e70b185c001ca2427028e16c014480e1860207850042489e31000ac0801cd80b0dcd80e1406e603f00e302b020073035c66020782a54ba00406150b815e319ba4c0f02160a80f4632617e02138508e1700e0812c069366c0f06938084e038f0000d8c0670109c07380f4304013e02c660004202c00d93a30190282701d1c66020a80e1401e071c28c000309d93c0407a301a4c0fc1709c181fc66020406094bb850ba00a240766c0f021203925c370780e00c60208e1b832b010c03010ac8c06807570612e02c9f041400e706100a170164c2803cfc2e0012d2780844c48348e1b83c07000f0bc1707c4f19808606a8ae9f4a656954a4268bea1f6850a03e7e29ed67749cf67069b666a299ae62a96b656c94ae4f492f649090ee40e8f8636e8cde30a8ad else 0x27a30071b18891241382051083a0cc30104140682802121884e0780e1401060f42703e8506007020e0d22b4203003854041c0f80600a1007020d034000801040b68403e1701c083050460100c1201a180801c81c060142000d030685a8485c0801cb00403420100394b509428060812850c601003961506293068082924c103c0403a0c182d85c270a185c0025a240801d9b64d88002b4290a04044604a84230070202230594601813820560c1501c0f0bca12a021984840b43080007404150a00f4508428201111930bc0703c80c30d8000f420502081f80834c62c300002d0bc22280c0703407920360e8663012040070a9016860c26008000e1401e8e0e8302a8c0bca1282104e0003e02139e15810180981a0970108a9363140be020381e40400801c99c259bc00184031000600a050079806e0c83a300a0bcc800000381e17960360f010b685c00083806050661211840141001c082b138000e0404e501b8320c1a6302f340a03841498660818180c01a038222824c60118080e07980f))
def xul11 : Packing := (154,3,7,0,0,14,0,xud11)
def xuh11 (i : Nat) : Nat := (if i<1 then 0xc2c4045c00c782260000805c8000281f7808a5073a830740fe0000e4454814c0001e04500002823c0016c0308029701b40000a109477c5825d003a00f89a2ea23add0faa0c8e00c88089409c0000a055d803fc08d603b60107045f11dc000000000000240de0000a451c007ac1ea00004080e0976d1e680d4000000002801820f4e0394018c0000e8f6f670a0209c1400000805ab819e80070088505900001409f089d000030439813a80e6000058090c0b8000000004820e812ac06a1076ea3a200994027b06f423861e0f20fdc067883d8000000007485201781100c01200004011f80cba017d0002005a81372075d401383eb9175c0d8000070384000168fe0000000000000e0cc00000000211a400000000721a3c0f860ee00006017c000000000000302a011e40000b4022840cc0d26118840740123419aa67c644d100cc019200002008500e000004064f4810830c009a204300000000141b3e8d5802ea815381676822b00f80000ddce40fec08c92264000080ada071000038010000000000b33ed03600000000080a2c0f408d1e07f8000041a60000000000000000190913644a208f814c8c45000020164000140040000500bc404c0000101e00002acb68014c473e00e681b68815445ea81a000000000605b38068c1c600000000000000000000040760000301600000a08b3005400018081c0605a4042804e0c6d413da29b81700000802ad82674135927d373e5042d422000ef80550000000000073111f0000000000000606a881b80001c00e01668000000000000975e882240000000080420000000010005906500000c084000040610000000000000a4108000281960000f6490004c0000000000004d2d3949a2105701e800c801ef80a784298219191da247c00000000198858092206d6219f820ee01c446f180d3404ac8a9404028160412c28360000382f300b5280a4035c0a4358f2000010721a24380a00000000000001c10a000000000000041ae00000000000015050000000000000191c400000000482f8400200005078c01f9007f40bf8058a001c0219c847342d184521071003700003806dd12e60bba0469a0c8800428c81869d018b11296eaa703b0821f519628c0104a7828a90da0077a40378047005aa049404fa80a40001c079c68280000a5140000d73b7bb400001209e701d5043c00000000c04300002dde40000d06938400c1f3887e0000682300000a8fb0000402dd421400008082483ab8123a8d35015a80b8000000af00000000180f1285620888000000000000a010e02b280c240fc00007516c0000c0e50000c200da4dd8068b0020c5123a4b54e00b4001c000200d7421830032923030ce3075c90221c08430e21c40041c00812c10061424538010c734b0a334020204104100608e2010020010c2082 else 0x1407d40225a27e4126000080745833a58fc00002074a8198192200005482d03c800f60000545b8000080ac0000d083281d08c03290d0052903c24211e0f3200c00000000c0000482d7a433d1bf400900006a0cc0000000000000000000018e7d802000002103060706020800008058000000000000000000000000000003d07b60a1a4267831282040000000000000000120eb906fa8380114ea0517477b23aa11b268a8b03608372d1e3210d5a498a3dc01748023c05a000000000a00af047703164097c0bde4608000300540000000058034000000007408582a440c1a07100000000000000000b01f00002822400000000083740001404a000000002006a20c7000000000415c0000a4894835a41a200a3000000002c0af4115537e13178000080a4d43b3824358bac819b439a80db01a14098000052111c1380000002d80000)
def xud10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe959348337ed3347cc2419fd607a164d20ddf260d37309047fdba617934833dec0f48c9a415f76cea954d20ef7768983309067f7a168593483fe8c0a6098a41cfe4c198e6120afbf66d4b069047ffb8e95934833dfd274ac9a415f76cea94c520afeb6354b02907f695254d104823ffdab46c8a419fde47a960520edef23d33029067bfa468593482affdbb4ac9a411ff6c7a864d20dedaa5d2b26906fafa4549934823fedd55298a41ff24c152e4d208ffb73d0b06906fe95268d104833bed2f4ac9a411ff6d5a3645208fff70d1f229057fbb0695934823feda95298a419efe91a564d20bfd764d2a609077d93054f984823ffd8b51c9a411ff6d7a3e6120ddf261d3302906fd930e8d98483fcdda260a9a415bfed9a864520ff3768982629057f5b1aa531482bfdd8350c8a413fe6c3a960d20cdff6cd0b309066feb9e99814837f4a974688241afee818166120cdfb26d37309063fd816a3934827fcd8f40cc2411ff6cda8e4520af7f68c9b229057efb26a1934823fedc742c9a411ff6e3a3e4520cf7f48d43269077d531e8593483bec98a60cc2411ff6e3a564d20c7fb51d4326907fe12168131483bddda261cc2419efe93a164d20efd2a4987309067f5a360791482bf7d9342c9a417eeed19344120cf7f48cab269047ffb8697934837ec9834bc9a417faec9a84c120bfe762c9a209053fdb8aa5814839fac0f42cc241bfae8930661209fdb65d4b069047fdb8e97934823ffd8b47cc2419f768d31e6120bbf76ecaa20904fefb268d914837ddda346882411ff6cfa8e45209fdf64d1b309067f5812a531482ff5d9350882411ffec5a5e4d208ffb73d1b029073f9814c1984837f888742cc2419bf6e7a660520bfb766d42609047ffb1ea193482ff5d9342982419efed1a564d20bfe762d42209076f93069b98482bfbd8b26c8a411ff6d7a864d209ff760d43229067bd51e9193482beed9d52c1a419bf54da6e6120afef62cc3229047fdb568793482bdfda326cc241df64c131e6120e7eb02d4722907f9bb44c3934823fedaf42c9a411ff6cda1e6120ffc242987229047fdb5e8d914833dfda347c8a414ff6e2a960d20bfd764cc2209047fdb3e85984837f4a9742982411ffed5a3e61208ffb74a9f30905febb268d104823fed8f4ac9a411ff6d7a3e4520cfeb03d1f229056ffb6685984833becaf4ac9a413fe6c3a960520af7f68d1b229057bfb468f91482affdbb2bc9a411ffed5a3e45208fff6ad47269057bfb464f984823fedcf4ac1a41feae91524c120efb260cc726906fe521e8593482bf7d9346c8a419fd687a166120df7748d0a609057dfb36a55348337fd3552c0a4157fedda5e4d208ffb71d1b229073fbb0663984832ffdbb4bc9a415bfed981e4d20cfbf46c9b309057fbb068598483fb0a92a288241fd25493054d20 else 0xa80e853950e39384cded3748da13618d6b3540d353410ce93338ca831dcc5130acbfa2f7cbc42ea4b8e2dccb582cf4b222c1cacb2a94a7f2964a3328609f227049a6260095a24d091923f88e3229c88c216c840209480a1fbc7c91e607721cd871b1ba86c41aa468e19cc642189c601174059f161056914b451213b04d112d849b11a8439104c3ed0f1c3ac0e443760d6c3400c3c2e90b0c2a80a34272093022608001e507281af0624163049c0f603400680002bfedc2a6c8a415ff6d53166120afff62d4aa69057ffb854f914833fec295298a419ff6a58154d20efef22a9b229067fd95e8d81483bfac0f42c9a41bbf54da6e61209ffb6ad1f30905efdb62a5534837f690f4ac1a41bfb54ba160d20b7ff70d2b069067fd9568f984833fed42a3c9a417bfed98154d20afff70a9b229067fca96a553483bf6a9263cc241bfe617a344120ffb260c2a62906effa664d81483fec98152a9a41fee607a44c120ffd302a92609067fda54c798482bfed8d52c1a41ffc60d5144120efef22c1b22905effb6685834827fe5d2a6cc241dfde458154d20ffca42c1f22906ff58168f91483feca9b06882419ffea6a954d20dfdaa4d1f309077dd8354f914833fecaf42c1a41bfbea15264d20ffd2a4c1a209057ffb566393483bfac0b27c8a419ff647a560d20cffb0bd1b229067fd8568d914827fedaf46c0a41dbf64fa660520ffb260a9f309057fdb1aa553483fddd230a98241fde6155344120cffb0ad0f269067fd8568f914833ffd0b0bc9a419ff54da1e6120efeb02d1f22907ff11054f914827fedaf50c9a41def607a464d20ffd2a4987309067fd85e85934833ffcaf46c0a41bfe617a14c120dff221d2b06904ffeba54d98483bf7cc2a4c9a41df7e4d8564d20efeb02caa62907ef930e9981483fec98302a9a419ffe85a954d20dff30ad1a20905ffbb36a1104833fea9f42cc241ffc44183e4520cffb50caa62905fbfb464d814833ffc8f4ac1a41ffc60530e4520ef7f48c2b26905fddb3aa5834827ffdab51c9a415ffec5a960d209fff74a9f30905fdfb36a5834837f6a9746c0a41ff9549814c520cffb4ac0f26906fbfa461593483beec1aa6c8a419ff607a564d20bdfb6d54b069057ffb865531483fec9830bc9a413ff6d7a160d20cfff50cab269047fdbaaa553482bfad8b31c8a411ff6e7a960d20e7eb02cc722905fbbb468d104833bed2aa3c9a415fdec5a960520cdff4cd4b02906feba2e81984829ffdc352c1a415fbec9a564d208ffb70d0f269047ffb1695934823ffd9b51c8a41bf9485a3e4520cdfb27d33029047ffb3e85984833dfda346c8a415efed193e45208fff66d0b309047fdba54f914833dfd2750c9a41de7e4fa464d20fbd76ea9220905efbb66a1104823fed9f50c8a413bfed9a864520cf7b0bd23269047ffb1) else (if i<3 then 0xc1109c633a010104803c08082002f103e7180a008100502705e30640041f0082384051c0417822718600e03c140e0302801e300e0bc040c08045100701e204e060228c2002f100f05e200e0a0178c038271023048201e0bc401c080a46205020306c0bc040f8002801e305e0a040bc04088000f04830600001400f200800e0886040040800808044300e03c040c1903002803c14141402f100701003c60cc1f0811d0105003c041404022102708a20100a040cc138b42685727c0598010302801e201e0a0501c04081400f05e300e020178c0400710180442018040138c138101007048202003c4c001cf010800bca01c13880c02410300000a0079203808100701e0a06e1407808182801020320a007808200805e205003c40f807880c028110100e0a017901402f100805e200ec04138c1f01801e0d0801c0402f1e0180e03c76168080f010404e0cc40cc110814022100701e200e04040401388208221018044205009c40b00600704e068ba30038281a0180e03c601c0782f180fe020bc609c140803841048307c01c1e04420070442020020198f80027010301009c078c0380f101004e205003c40b00602804e068a01c110b8080007c020801c07882002f1007010204e0a0401c040101f010500200790138180503021c078003304e500e04040c80a033020480e03c040c1402f1008020280e03c40c80083e010405e0a0401c0782f18320020cc041014000034020806013880402210300000a007808280f048205e09c0d0c138281007044205e03c40c80083e010408601414010240701e020601c078081807010040701c040a03808100805620860bc409c140a03e8c01e0689c00040271d0142a088601c0788038081007010251801c080e8080f05e300e0cc140c138101008056205002040200380f18010660207a1ac2f0186a0a8b4000380f0504e0201c040d80820c000ebc60070660a804258082500e10e1803a9260a0042646290f2421901a3ca8e0e3738d623328c5e2fc8b862d18b062b18a5a27b8982245887e20487fe1fa87521b9864e18385a214d852213884760ec831a0c1829a08b81c2060814201f803e00a7fbdfc97eb9f937de1f5d7cddf1c7c05ee67b2deb07a55e7a797de4478d1e1977a1dcd76c9d977649d827571d4174c5d0b7395cca7239c7e71b9c537139c287009be76f31ba66e59b7b6d81b3a6ca9b1a6bfdace6acdaa36a21a62691da42689da0c674199f65b994864b590763598bb625587a61518185ff57e25f1d7755d697345c656fe5b096a75a31671595963b58815ef57515b9562156254c54ea531149e51e145d510941c50053e64f013a54e2936f4d5132e4c212e24b1d2ac4a1925548bd21447b91c84631171452d13043d10d942f90a34221041409900b3fc0fca3e90f893db8f483cb4f123bdcebb3 else 0x800e204e0a0040c13828100800e207d0b01d02709054648c00800804e11cc804209c140b80007068304e01c402003881380713000b0008070827050205009c409e03880400710080560686040040800a61060150c0380f1028e0203c602020a004080c02810100860c02810ac01e01c0412c64850503000800e201f804403c04080384078423033010040809c2000e02040b607008180800e201001c410413880400710080240a8601c0788138281028e022c020204020038820827100800e202001c5038040804040400713848000681a10040071010010201e01c40602101e01c040c0d0271200082d0100a0609c04010182801e28650c004007828580210501020020400660a0040f42407010301001c401c04090001a010300e100e020406014080780800e30101600102002048c804012020401101c460c203c218a0c02800e30500204001001c40601408190300280f80414c600500e04080c00002801e4024040040e0b80f10070200cc7a3003827020402009c5a1404022181808a200e020078c1600c00e09c0414080081008050200e0205c018070166009c22010380805020000bc040e03808100805020640c00a00f05050500bc4c04178812033141701e204e0a0501))
def xul10 : Packing := (282,4,7,0,0,14,0,xud10)
def xuh10 (i : Nat) : Nat := 0xc04c000e09a8050000000000181a647a00d705042f000341e00b68040001c29001c80aa42b41f749891f909c42c77b8420e004519a00e1838071c18502ed2a9064112242f82a709642300005290000000c658000805c19bd35c000d009dc0f0319d80001015248e81df4914246041c22f0a0c30485a000c0ba0210002808c03cc098432443146d80ec0ae012b058000601901b0001411010000021d000000c0202000050002040c0001600010200000002011500000600020020
def xud9 (i : Nat) : Nat := 0x138078040e8ca8c2850786586182830028c02050010200140040801c0204000708000560342632601100404020200600040a0200280803804081a0210080ac60040bc0420008080404000000bc306001e05030000000040404003c40101001f0140138ef4b2ea2a7698a1e6a996488ae268561082dee745c06bdaa6959460d7e5b55052d3a4a50c3ecf6394d433cca314c02bc862047c1dc721b45c0fc2e0a40087fcca6d53166120c6ffb66a58154d20a6fdc6e85a954d2087fdcbea6a954d20eee9524c3a660520fdabb7e91524c120ffc130549814c520a5ffc7657a360520ff49524c18154d20ff49524c0a954d20ded9b64c0a954d20eee9a654930e6120a5ffc7655a3e6120dedbb64c18154d20a6fdc62a5a954d20c6fda5ed981e4d20e7b581e93a164d20d5f7b7605954c520c5ffb7ea19564d20cebfb4e999360520b6bfc6607a464d20f7c9524c131e6120e7afa4e615264d20f7a952ed130e6120ff495354930e6120ff615260d5144120a6ffc66a1954c520b6bfc464fa660520e3f7a8e458154d20bebbc6607a44c120e6f7b668d81e4520d7b7b460593e4520d7b581ed1a3e4520ff495254d8344120e7e552604a94c520a6ffc6607a564d20eed9a64c153e6120ff8121ed1304c520ff0952ed13054d20c5bfb7e91a564d20c5bfb7ed1a564d20a6bfc464da6e612086fecbe99a960520a6bfc464fa66052087f5cbe47a960520f3d131605306612086fdcbe9aa960520c5bfb7e919564d20f749524c153e6120
def xul9 : Packing := (49,5,7,0,0,10,0,xud9)
def xuh9 (i : Nat) : Nat := 0x40682001610005030028
def xud8 (i : Nat) : Nat := 0xc180410b8b8a0613fedfc66a1954c520ef24a936c98152a9a41de4952ed93060553483fa17aea9768982a6907b92549a64c153e6120
def xul8 : Packing := (5,6,7,0,0,6,0,xud8)
def xusamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5d08196a6ab94f2cc0a2ac25680a4208344800af404600baf816401410012b19a81841c60c000c42020805074b337509a3308401433e21f673,0xd0800682ea0c92840000c0048172150480931233116251411ce40830401291860184746083044020a0801024b220801232884808224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd845701f1d11913202dc0733613022d37320007400800ad1afe020260200042200c22a0182ce0e23c1a30c625943a822604c0ef4400c8c6487f,0x180450191c01810002588723414c8c02232008a5840c9da018e001c34a80042210c21a81837c418141120c6259418c644008042442088c44829),(0x24838aa0756a21466e610150ba833388387300602bdb8190000420200120421c041c13c6063acc2b68c012038e7c000204603082518f1078f9c,0x24038ba0014e004660200050988072894082174842410058c50060381174421c001c0546040082603ee110010028109a0470218011471038514),(0x197c742262611d0db214d4442210696c0a51cd90211b80201007090088c098c000603967fd2100181402e03c0e0000a007807e0da9f01f80fe0,0x194874026221140882068084264d01702b41c810a41a00a00a3e0f44420a18c0026020a1513105064002e2580e0024208300de050ab00b00ae0),(0x24239f791d94e161f9b06f2bd910880890006d8ccca42002000100228941cd201b010e18010000c4004c003fe000c10007ef000dbc401fff000,0x24230b791d14e16179b06f3bd91288089008248d48e49506b4c100b38d95c52019101b08040c4ab9965d0027d000d35c04cd0100b44014ed000),(0x9292ca9480cd64d0bf20125add4044a265eb203100058084008c4f9441f200001eec0000000b000005efd800080df7bf810800597bfe000000,0x12924a94800904c0bb20102a85c0548225204a14442950806e00b35419b280001ea60000530a0a7504b5b4000000132e8000105959da000000),(0x336b26e0e8f854fcc5a748cca028013148c3c0162820064c00763206330137dfe00020000004b300ab010000010001267fef3ff000000000000,0x236b24a0e0f8547cc5a748cca0231131484bd7126873001c271e2e14151bbac94a0024000401bc3eb801020000002392bff7bbd008000000000),(0x3adc5057929368b0852dfca4026310028d2dc2073ae461020007108a80325000041000800010f000294effbfef7fc8090000c00262000000000,0x1ad45056929168b0840dfca4022300168d2dc806b9bc62a7381f94c2ae0090001e011080000f5d188114a4beffd7ee450000c00a6a000000000),(0x696cb5c93062b8b3008b689c98c626490e3304010243c24501a9b52b4ad77dfe1eeca3ffac10110161000000100c8850000410260000000000,0x4948b5411062b8330081610118062869480204813042a41d000d08a28644536b4159b5eaace424006b000001180d84d0000000a60400000000)]
def xucolumns : List ColumnInfo := [(17,0,494,0,11),(132,0,379,0,11),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(8,0,503,0,12),(7,0,504,0,7),(202,4,305,0,4),(66,0,445,0,11),(133,0,378,0,7),(28,0,483,0,8),(320,0,191,0,11),(181,0,330,0,4),(21,0,490,0,7),(114,1,396,0,4),(197,2,312,0,4),(74,0,437,0,7),(322,0,189,0,8),(24,0,487,0,11),(156,0,355,0,7),(25,0,486,0,8),(198,0,313,0,7),(3,0,508,0,9),(268,0,243,0,7),(344,0,167,0,7),(141,16,354,0,4),(160,0,351,0,11),(56,0,455,0,7),(128,256,23,104,7),(266,64,181,0,5),(273,0,238,0,7),(35,0,476,0,7),(33,0,478,0,9),(178,1,332,0,4),(49,0,462,0,8),(154,4,353,0,4),(296,0,215,0,7),(128,32,94,257,7),(120,256,135,0,4),(404,8,99,0,4),(324,0,187,0,7),(85,2,424,0,4),(53,128,330,0,4),(2,64,189,256,9),(14,0,497,0,7),(164,0,347,0,8),(31,0,480,0,4),(9,16,486,0,8),(193,32,30,256,5),(32,128,347,4,9),(39,128,344,0,4),(324,8,163,16,5),(416,0,95,0,8),(19,0,492,0,8),(83,0,428,0,7),(265,16,230,0,5),(256,64,189,2,9),(36,128,347,0,8),(352,0,159,0,8),(258,64,189,0,8),(289,0,222,0,7),(401,32,78,0,4),(480,0,31,0,7),(232,256,23,0,4),(297,16,198,0,4),(188,0,323,0,4),(449,32,30,0,4),(270,64,177,0,4),(340,8,163,0,4),(264,128,83,36,6),(390,64,57,0,4),(482,0,29,0,4)]
def xuautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xulevels : Nat → Packing
  | 13 => xul13
  | 12 => xul12
  | 11 => xul11
  | 10 => xul10
  | 9 => xul9
  | 8 => xul8
  | _ => emptyPacking
def xuindex : Nat → Nat → Option (Nat × Nat)
  | 13 => lookupWord 26 37 3 13 5 4 xuh13
  | 12 => lookupWord 83 313 7 16 8 4 xuh12
  | 11 => lookupWord 102 597 6 17 9 4 xuh11
  | 10 => lookupWord 71 89 4 14 6 4 xuh10
  | 9 => lookupWord 5 9 1 11 3 4 xuh9
  | _ => fun _ => none
def xu : Forest := ⟨511,13,fun j => xusamples[j]?.getD (0,0),xucolumns,xuautos,xulevels,xuindex⟩
set_option maxHeartbeats 0 in
theorem geomxu : graphValid xu (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_13_0 : block xu 13 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_13 : block xu 13 0 1=true := sxu_13_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_12_0 : block xu 12 0 8=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_12_8 : block xu 12 8 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_12 : block xu 12 0 18=true := (@block_merge xu 12 0 8 10 sxu_12_0 sxu_12_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_0 : block xu 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_2 : block xu 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_38 : block xu 11 38 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_47 : block xu 11 47 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_83 : block xu 11 83 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_119 : block xu 11 119 17=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_136 : block xu 11 136 18=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_11 : block xu 11 0 154=true := (@block_merge xu 11 0 136 18 (@block_merge xu 11 0 119 17 (@block_merge xu 11 0 83 36 (@block_merge xu 11 0 47 36 (@block_merge xu 11 0 38 9 (@block_merge xu 11 0 2 36 sxu_11_0 sxu_11_2) sxu_11_38) sxu_11_47) sxu_11_83) sxu_11_119) sxu_11_136)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_0 : block xu 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_2 : block xu 10 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_38 : block xu 10 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_74 : block xu 10 74 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_110 : block xu 10 110 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_146 : block xu 10 146 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_182 : block xu 10 182 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_183 : block xu 10 183 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_219 : block xu 10 219 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_255 : block xu 10 255 27=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_10 : block xu 10 0 282=true := (@block_merge xu 10 0 255 27 (@block_merge xu 10 0 219 36 (@block_merge xu 10 0 183 36 (@block_merge xu 10 0 182 1 (@block_merge xu 10 0 146 36 (@block_merge xu 10 0 110 36 (@block_merge xu 10 0 74 36 (@block_merge xu 10 0 38 36 (@block_merge xu 10 0 2 36 sxu_10_0 sxu_10_2) sxu_10_38) sxu_10_74) sxu_10_110) sxu_10_146) sxu_10_182) sxu_10_183) sxu_10_219) sxu_10_255)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_0 : block xu 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_12 : block xu 9 12 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_48 : block xu 9 48 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_9 : block xu 9 0 49=true := (@block_merge xu 9 0 48 1 (@block_merge xu 9 0 12 36 sxu_9_0 sxu_9_12) sxu_9_48)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_8_0 : block xu 8 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_8 : block xu 8 0 5=true := sxu_8_0
theorem tablesxu : checkedTables xu 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xu 0 0 0 = true)
  · exact (rfl : block xu 1 0 0 = true)
  · exact (rfl : block xu 2 0 0 = true)
  · exact (rfl : block xu 3 0 0 = true)
  · exact (rfl : block xu 4 0 0 = true)
  · exact (rfl : block xu 5 0 0 = true)
  · exact (rfl : block xu 6 0 0 = true)
  · exact (rfl : block xu 7 0 0 = true)
  · exact allxu_8
  · exact allxu_9
  · exact allxu_10
  · exact allxu_11
  · exact allxu_12
  · exact allxu_13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseUB : Impossible true (graphGoal 511) 13 (varsX 43519).toFinset :=
  index_root (g:=xu) (i:=0) rfl rfl (before_sound known383 valid383) geomxu tablesxu (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseUA : Impossible true (graphGoal 511) 13 (vars 511).toFinset :=
  cut_root (prior:=boundsBefore known383) (before_sound known383 valid383) (128,0,383,0,13) (by decide +kernel) (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def x31d6 (i : Nat) : Nat := 0x1a230180fd10fc20
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def x31d5 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec04a3a21f673,0x2a912c2212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8a05bac6487f,0x56291cc44829),(0x2f8585078f9c,0x309c463038514),(0x135b045f80fe0,0xb41b88b00ae0),(0x3507a41fff000,0x142e4354ed000),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 11 1 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_0 : block x31 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_6 : block x31 6 0 2=true := sx31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_5 : block x31 5 0 5=true := sx31_5_0
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x31 0 0 0 = true)
  · exact (rfl : block x31 1 0 0 = true)
  · exact (rfl : block x31 2 0 0 = true)
  · exact (rfl : block x31 3 0 0 = true)
  · exact (rfl : block x31 4 0 0 = true)
  · exact allx31_5
  · exact allx31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : Impossible false (graphGoal 1055) 6 (vars 1055).toFinset := plainA (q:=31) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1567 : Lower false (varsX 1567) (graphGoal 1567) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=0) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known1567 := extendKnown known383 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1567 : Known false known1567 := extendKnown_ok (m:=1567) validF low1567 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42527 : Lower false (varsX 42527) (graphGoal 42527) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=1) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known42527 := extendKnown known1567 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42527 : Known false known42527 := extendKnown_ok (m:=42527) valid1567 low42527 (by decide +kernel)
def x111d6 (i : Nat) : Nat := 0x1040a3fa21fd51
def x111l6 : Packing := (2,1,1,0,0,3,0,x111d6)
def x111h6 (i : Nat) : Nat := 0x40000
def x111d5 (i : Nat) : Nat := 0x102de54110
def x111l5 : Packing := (1,2,1,0,0,0,0,x111d5)
def x111samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1c017c36792839f673,0x6456218245928112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc38e7cc981ff26487f,0x1021104810085244829),(0x627e830e1e31c78f9c,0x474a42a0e1430838514),(0x207083f01fc1f80fe0,0x38b5bd5f00bc1780ae0),(0,0),(0x21c0103ffe001fff000,0x1ba9de7dba001eed000),(0x5818003fffffe000000,0x6fdeefb7eff7a000000),(0,0),(0,0)]
def x111columns : List ColumnInfo := [(96,0,15,0,4),(1,32,78,0,4)]
def x111autos : List (List Nat) := [[],[32,83]]
def x111levels : Nat → Packing
  | 6 => x111l6
  | 5 => x111l5
  | _ => emptyPacking
def x111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 x111h6
  | _ => fun _ => none
def x111 : Forest := ⟨1135,6,fun j => x111samples[j]?.getD (0,0),x111columns,x111autos,x111levels,x111index⟩
set_option maxHeartbeats 0 in
theorem geomx111 : graphValid x111 (boundsBefore known42527) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx111_6_0 : block x111 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx111_6 : block x111 6 0 2=true := sx111_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx111_5_0 : block x111 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx111_5 : block x111 5 0 1=true := sx111_5_0
theorem tablesx111 : checkedTables x111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x111 0 0 0 = true)
  · exact (rfl : block x111 1 0 0 = true)
  · exact (rfl : block x111 2 0 0 = true)
  · exact (rfl : block x111 3 0 0 = true)
  · exact (rfl : block x111 4 0 0 = true)
  · exact allx111_5
  · exact allx111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl111 : Impossible false (graphGoal 1135) 6 (vars 1135).toFinset := plainA (q:=111) (prior:=boundsBefore known42527) (before_sound known42527 valid42527) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low49775 : Lower false (varsX 49775) (graphGoal 49775) 7 :=
  strong_full (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=0) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known49775 := extendKnown known42527 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid49775 : Known false known49775 := extendKnown_ok (m:=49775) valid42527 low49775 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42607 : Lower false (varsX 42607) (graphGoal 42607) 7 :=
  strong_full (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=1) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known42607 := extendKnown known49775 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42607 : Known false known42607 := extendKnown_ok (m:=42607) valid49775 low42607 (by decide +kernel)
def x63d7 (i : Nat) : Nat := 0x344640ac3f865fc10
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def x63d6 (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := 0x24f9400060ba8030352
def x63d5 (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := 0x20034000
def x63d4 (i : Nat) : Nat := 0x3b04813058432
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def x63samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc87d813f01c73e21f673,0x765c43000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe10600dd66a4c8c6487f,0x3601a1ac64a488c44829),(0x238268c08738f1078f9c,0x9aa0e13831071038514),(0x16807e00f83f01f80fe0,0x125451e4502f00b00ae0),(0x1c109622ffc001fff000,0x2d89a218afc0014ed000),(0x690100fffffe000000,0x3f89a3bcfffdda000000),(0,0),(0,0),(0,0)]
def x63columns : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def x63autos : List (List Nat) := [[],[65,50]]
def x63levels : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => emptyPacking
def x63index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 x63h7
  | 6 => lookupWord 2 9 1 8 3 1 x63h6
  | 5 => lookupWord 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => x63samples[j]?.getD (0,0),x63columns,x63autos,x63levels,x63index⟩
set_option maxHeartbeats 0 in
theorem geomx63 : graphValid x63 (boundsBefore known42607) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_7_0 : block x63 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_7 : block x63 7 0 2=true := sx63_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_0 : block x63 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_7 : block x63 6 7 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_6 : block x63 6 0 12=true := (@block_merge x63 6 0 7 5 sx63_6_0 sx63_6_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_5_0 : block x63 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_5 : block x63 5 0 6=true := sx63_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_4_0 : block x63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_4 : block x63 4 0 1=true := sx63_4_0
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x63 0 0 0 = true)
  · exact (rfl : block x63 1 0 0 = true)
  · exact (rfl : block x63 2 0 0 = true)
  · exact (rfl : block x63 3 0 0 = true)
  · exact allx63_4
  · exact allx63_5
  · exact allx63_6
  · exact allx63_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : Impossible false (graphGoal 1087) 7 (vars 1087).toFinset := plainA (q:=63) (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6719 : Lower false (varsX 6719) (graphGoal 6719) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def known6719 := extendKnown known42607 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6719 : Known false known6719 := extendKnown_ok (m:=6719) valid42607 low6719 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1087 : Lower false (varsX 1087) (graphGoal 1087) 8 :=
  strong_full (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=0) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known1087 := extendKnown known6719 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1087 : Known false known1087 := extendKnown_ok (m:=1087) valid6719 low1087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low11327 : Lower false (varsX 11327) (graphGoal 11327) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=1) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known11327 := extendKnown known1087 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid11327 : Known false known11327 := extendKnown_ok (m:=11327) valid1087 low11327 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1599 : Lower false (varsX 1599) (graphGoal 1599) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def known1599 := extendKnown known11327 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1599 : Known false known1599 := extendKnown_ok (m:=1599) valid11327 low1599 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47679 : Lower false (varsX 47679) (graphGoal 47679) 8 :=
  strong_full (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def known47679 := extendKnown known1599 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known false known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower false (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def known42559 := extendKnown known47679 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42559 : Known false known42559 := extendKnown_ok (m:=42559) valid47679 low42559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52799 : Lower false (varsX 52799) (graphGoal 52799) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def known52799 := extendKnown known42559 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52799 : Known false known52799 := extendKnown_ok (m:=52799) valid42559 low52799 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def x189l7 : Packing := (5,1,3,0,0,7,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def x189d6 (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def x189l6 : Packing := (10,2,3,0,0,7,0,x189d6)
def x189h6 (i : Nat) : Nat := 0x700009040000000000ddd0800002
def x189d5 (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def x189l5 : Packing := (3,3,3,0,0,5,0,x189d5)
def x189samples : Array (Bits × Bits) := #[(0x98543c01121d833f4fc,0x1e6c550011215802a4ac),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc268201f82067f2cc8cf,0xa9854a582041528c8ca),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6400c361c3861cf0f0f,0x146729421c3060870605),(0x25004de0e03f81f00ff0,0x219082bde00e81700950),(0x18979200ffc001fff000,0x9328e7ca8001fd5000),(0,0),(0x103ab009fffffe000000,0x35648318357bea000000),(0,0)]
def x189columns : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 23 29 4 12 4 4 x189h7
  | 6 => lookupWord 2 11 1 10 2 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨1213,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore known52799) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_0 : block x189 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 5=true := sx189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_3 : block x189 6 3 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_6 : block x189 6 0 10=true := (@block_merge x189 6 0 3 7 sx189_6_0 sx189_6_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_5_0 : block x189 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_5 : block x189 5 0 3=true := sx189_5_0
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x189 0 0 0 = true)
  · exact (rfl : block x189 1 0 0 = true)
  · exact (rfl : block x189 2 0 0 = true)
  · exact (rfl : block x189 3 0 0 = true)
  · exact (rfl : block x189 4 0 0 = true)
  · exact allx189_5
  · exact allx189_6
  · exact allx189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl189 : Impossible false (graphGoal 1213) 7 (vars 1213).toFinset := plainA (q:=189) (prior:=boundsBefore known52799) (before_sound known52799 valid52799) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2237 : Lower false (varsX 2237) (graphGoal 2237) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=0) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2237 := extendKnown known52799 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known false known2237 := extendKnown_ok (m:=2237) valid52799 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower false (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=1) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known1725 := extendKnown known2237 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known false known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower false (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=2) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2749 := extendKnown known1725 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2749 : Known false known2749 := extendKnown_ok (m:=2749) valid1725 low2749 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43197 : Lower false (varsX 43197) (graphGoal 43197) 8 :=
  strong_full (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=3) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known43197 := extendKnown known2749 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43197 : Known false known43197 := extendKnown_ok (m:=43197) valid2749 low43197 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44221 : Lower false (varsX 44221) (graphGoal 44221) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=4) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known44221 := extendKnown known43197 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44221 : Known false known44221 := extendKnown_ok (m:=44221) valid43197 low44221 (by decide +kernel)
def x251d7 (i : Nat) : Nat := 0x60bfd31
def x251l7 : Packing := (1,1,1,0,0,0,0,x251d7)
def x251samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0021ee01fffe490e402109fc2670e40ff27f,0x208080808080490a402108a80450a401222a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe488e110001fe0033fcc6313cd9833fca4c4f,0x156067666666600212cc63114910212ca4c45),(0,0),(0x1000fe000071c380f83e331e1c38f38f8c,0x66caaaaaaaaa718380f82c321e1838a38b0c),(0x1000fffe0181fc0f003fc3e01fc0fc0ff0,0x199355555555580740f001341e007405c04d0),(0x1b761ee000001fe000fffc003ffe000fff000,0x1036e0f1e1e1f24000a948003fba000fed000),(0x488e11000001fffff0000003ffffff000000,0xa9f989999999ffded00000036efded000000),(0x1b74000000001fffffffffffc000000000000,0xfc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
def x251columns : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def x251autos : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def x251levels : Nat → Packing
  | 7 => x251l7
  | _ => emptyPacking
def x251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨1275,7,fun j => x251samples[j]?.getD (0,0),x251columns,x251autos,x251levels,x251index⟩
set_option maxHeartbeats 0 in
theorem geomx251 : graphValid x251 (boundsBefore known44221) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx251_7_0 : block x251 7 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx251_7 : block x251 7 0 1=true := sx251_7_0
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x251 0 0 0 = true)
  · exact (rfl : block x251 1 0 0 = true)
  · exact (rfl : block x251 2 0 0 = true)
  · exact (rfl : block x251 3 0 0 = true)
  · exact (rfl : block x251 4 0 0 = true)
  · exact (rfl : block x251 5 0 0 = true)
  · exact (rfl : block x251 6 0 0 = true)
  · exact allx251_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl251 : Impossible false (graphGoal 1275) 7 (vars 1275).toFinset := plainA (q:=251) (prior:=boundsBefore known44221) (before_sound known44221 valid44221) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low48891 : Lower false (varsX 48891) (graphGoal 48891) 8 :=
  strong_full (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl251
    (index_root (g:=x251) (i:=0) rfl rfl (before_sound known44221 valid44221) geomx251 tablesx251 (by decide +kernel))
def known48891 := extendKnown known44221 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid48891 : Known false known48891 := extendKnown_ok (m:=48891) valid44221 low48891 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x1948817fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0x8e80
def x127d7 (i : Nat) : Nat := 0x24c269243a037eb0261df54530
def x127l7 : Packing := (2,2,3,0,0,5,0,x127d7)
def x127samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc30c1fc403f090d9a33c9401c73e21f673,0x3301d20130c00091222c94000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4b18000fff1632604c0ff66a4c8c6487f,0x8d421c20c30420400804264a488c44829),(0x30400032fc098c38470f188738f1078f9c,0x2322c82492498838470a18831071038514),(0x3842603b000e0fc0780fe0f83f01f80fe0,0x1ccd1659659407c03005e0502f00b00ae0),(0x9026ec9000ff0007ff000ffc001fff000,0x3229a68a2bf0004dd000afc0014ed000),(0x20c1104000fffff800000fffffe000000,0xcfe2dfecf3fff6e800000fffdda000000),(0x4b18000000fffffffffff000000000000,0x372bde3df3cfbdfbff7fbd000000000000),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | _ => fun _ => none
def x127 : Forest := ⟨1151,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore known48891) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_8_0 : block x127 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_8 : block x127 8 0 1=true := sx127_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_7_0 : block x127 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_7 : block x127 7 0 2=true := sx127_7_0
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x127 0 0 0 = true)
  · exact (rfl : block x127 1 0 0 = true)
  · exact (rfl : block x127 2 0 0 = true)
  · exact (rfl : block x127 3 0 0 = true)
  · exact (rfl : block x127 4 0 0 = true)
  · exact (rfl : block x127 5 0 0 = true)
  · exact (rfl : block x127 6 0 0 = true)
  · exact allx127_7
  · exact allx127_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl127 : Impossible false (graphGoal 1151) 8 (vars 1151).toFinset := plainA (q:=127) (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2175 : Lower false (varsX 2175) (graphGoal 2175) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def known2175 := extendKnown known48891 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2175 : Known false known2175 := extendKnown_ok (m:=2175) valid48891 low2175 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower false (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def known1151 := extendKnown known2175 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known false known1151 := extendKnown_ok (m:=1151) valid2175 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52863 : Lower false (varsX 52863) (graphGoal 52863) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def known52863 := extendKnown known1151 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52863 : Known false known52863 := extendKnown_ok (m:=52863) valid1151 low52863 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44159 : Lower false (varsX 44159) (graphGoal 44159) 9 :=
  strong_full (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def known44159 := extendKnown known52863 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44159 : Known false known44159 := extendKnown_ok (m:=44159) valid52863 low44159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower false (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def known43647 := extendKnown known44159 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43647 : Known false known43647 := extendKnown_ok (m:=43647) valid44159 low43647 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42623 : Lower false (varsX 42623) (graphGoal 42623) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def known42623 := extendKnown known43647 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42623 : Known false known42623 := extendKnown_ok (m:=42623) valid43647 low42623 (by decide +kernel)
def x191d10 (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def x191l10 : Packing := (10,1,7,0,0,9,0,x191d10)
def x191h10 (i : Nat) : Nat := 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def x191d9 (i : Nat) : Nat := (if i<1 then 0xc845e2d1218282a8801c24251480104a170b0541d28c2411f02104a1f15004282d1700020915c80581f207008240f85e2d150d894222f00304a1f088046607001c0633148045e2e160a9108128a88e1f1681c008088a80f00000845a2f40a88e250f8cc0e0038045f1e19874a0415044022d120a4000248105c111500428400000923114910570008840e26128c8562f93800e1b1289054010387052411680161412046040702004800048984a240f8ac5f220020222a0607c4a290380110703c845a2f28a8502b900b03e6154045f200f944a1f1501c021c0d8545c2d002c381b8a87c54071285852005094481f15044722f1588920180002512715981e1f150045207001c08240f844020f0a44066005002502b13901e2d150045200081c55281589c48503014550203810022900249a4c0e8943e07001c2e1c0d8904a1f8b4542200505c381b120943f168a84400a2407036251207e8315088014430e06c4a240fd062c110028381b0b894481f8b454220050d86a14078903e108904400af98fbdbd0be5cf07f72fb57d79e9af3eb9c7c57e00ef1b73bb74d9cec1f551a6dd1de7df379978c9ee4531d789ec2460a2fed7a0bc05c86df16bdb4a59aec2b5daacb554aa654e5a50d10a8213c39d64d7e65b2e994e49f24cb22a8dcc61e2e115088ac3d61750a3838c0da008fd27d03d4de0ce9e728b8e9c22db26a9b3f593cc3f606af4970ab535952b51556a3a4fb26a52b890f465a2650867ed3d49d94dfa6a732d1834bb65a02b7141894e45120b0f486e634a1830b504fc23a0ed85f023a0be02f8003fe90287ff54140ffa64a07fd71083fe90281ff5c940ffaa2187fd30503fea9281ff5d940ffae6a07fd6454ffea02a7ff4c110ffac0187fd63083feb1a21ff48063ffa42887fd72443fe900a7ff44153ffa84887fd54503fe98aa7ff50540ffaa6107fd61503feb02a7ff4c420ffaeaa07fd20443feb1aa7ff58d40ffaa2207fd62503fe39281ff58040ffa40a9ffd42503fe90061ff4c910ffae2a9ffd61103fe90081ff4c510ffa20107fd5150ffeb8a81ff58430ffac0a1ffd5054ffe982a7ff5d153ffae8887fd54443fea0aa7ff5cd10ffae6107fd30083feb0063ff1c153ff8e4887fd40443fea9061ff54831ffaa4207fd7054ffea0a21ff54540ffac0a07fd31503fe90041ff50020bfae4885fd7150fdea1081f758d53bfae0a1dfd71083dea0a817f5c153bfae2185fc72503fc902217f5d830fea82885fd72102feb90c77f1c910bfae031dfd7154efeb88c77f5cc20bfaea18dfd760c6fe382a7fe4c140bfaea205fd720c7ee982877f5c453fba60a9dfd74442feb9a217f5d840bfae2205fd7550efeb92817f5c053bfae4187bd54502feba8617f5d540bfae018df57114ef6b90815f5d440beae2204fd76102eeb98813f5d830 else 0x4963e2311400a4a1a0a4582712184c241287c662c158bc84270e801840148cc584020aa002813c1c560040d250001449c4e2b3c00522d18903e00190acb0116c005c2b1609ce34940b858271598642b11084c021089c484b1c0b8562d178880e0078d0421f1c0bc582413801230100bc53070f987e10800b482a160b85e4181145e2c1007cd258f8220f0028187c051412440250f80c08a1801240208f87cd258f8320f0028c04238178b0401f38805707178a43e60e8d059010009c5672241c5a21038bcc1f008b0564150b05a2f20d08100170b0502b13a02020138ba020717c005a9150cc5e31a4a058271594602a900823e1f83c00089039145e31a07c5901130ac5e4613801411800a45a4170ac802c1309cc34170c85841f906002d2010222a83c00422d228bd22c808744f0715987e128f8c4522d801c4033210f85e290f9c422d178e3616928bc5c2916c0103f0b47c622916c00e0518080422f1f01053070fa85c2f180a45859247c5e2d1588c450040b0562094524a33170b4210040f45c2f11400a3c108a45e24000b4e211241c5701038005e8178e05a30f8b04301c0ac58200f98763a1089449070f8bc562d1c80183017c80401f28cc5e20e8ac5e3820cc5d0101400c071c0b462f17004602916183e2c10405900000b4b04160b6020280182a2c800005a590884002d17946e050207c5851a0a6002d160a0562740d0582e15c06000013a06824140044a27838cc641f002c6230018bc5c2d1584502c158861200247c826120943e111508e442b17aa2c1c0d8904a1f8a8bc560051248420138b400451781d226128c854011207e442b17aa3d1d018040e00200a4662c50024e28160aca2a03)
def x191l9 : Packing := (122,2,7,0,0,13,0,x191d9)
def x191h9 (i : Nat) : Nat := (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def x191d8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xd855c830fdd314c140dfd7254830dfd7650020bfd855d110f7d5250553ff9614c140fdd3050553dfd754c420dfd7348020dfd745c910dfd7550020dfd511c940dfd635c910bfd821c153dfd8748063ff5514c910ff98448110dfd735c910dfd205c453bfd855cd10bfd8258031efd6058430dfd7244153ff92058030dfd405c910dfd7254140ff48148143dfd7250553dfd825c053bfd864c140dfd515c143fdd304c510dfd7158940ff93048110dfd855c831dfd405c553ff9204c140ff48148153fdd3044153dfd605d110bfd831c910ff48148140bfd865cd10fdd6350553dfd764c510bfd8348110dfd7248030dfd714c020fdd534c140dfd205d440fbd5450110dfd615c143bfd8550510dfd7258030fbd4050553ff98348110ff92058040fdd3059153dfd855c8409fd825c0539fc87589409fd8758c209fd87589409fd861c940d7d525d4409fc8754940f3d54541409fc87545409fd825d4309fd831c910ddd7358c209fc8759153f5d524c153ded615c840ddd205cc40fb9544c1409fd805c5539fd8758d10f9c844c153cfd615d830ddd7354c20bdd8358153ddc835c9409fd825d5439fd835c910df5615c440dbd425d543fb541585409fd815d840df9205c0639fd825d540d7d525d5439fd8754c20cfd815d830cfd615d8409fd841c910cfd605d8319fd851c940ddd305c543bf581551109fd805d831fd9534c140df5205c453ded805c8409fd825d440d7d825d440d7d525d4309fc874c540df9724c140ded855c840cfd605d830ddd305c5539fc8744153ded605c8409fd815d440ddd515cc40ded7254840df97348110fb9414c1409fd874c940df4815c940d7d615d440ddd525cc409fd821c153cfd525d840cfd605d8409fd811c940df5411c910f9d424c143d7d521c1539fc8748153dbd425d8409fd841c153afd861c1539fc8758d10dbd425c440edd6358153f3d52551409fd805c863fe94248110dbd425d440fd9634c140f5d5258d53fb54150110cfd515d840df5515cd10d7d205d440fd93048153df57154440ded7254830fb5414c540ddd635c1539fd855c543df5605c4409fd811c1539fd874c420f5d5458d53d7d515d430cfd205d830ddd615cc409fd815d540dbd7255140ddd605cc40df5714c4209fc8750153df5205c440ddd305d5439fc874c910df5865c440df5525c440edd6359153fb54250510f3d5450153ff141481109fd815d830cfd815d8409fd825d4319fd8750940dbd7250540fad4248040df5855c4409fc8750910cfd515d830fd9204c1439fc8758540d7d515d440bbd81551409fc8755110cfd205d840cfd525d830fd9314c140df57154430d7d815d440ddd734c420d7d605d440ded515c840d7d525d431df9205c0539fd815d430d9d425cc40cbd425d8408fd861c153d3d425d440db5425c440 else 0x4a2c4cae62b34ab42a44a6e288ca0a279c9ce265c96a251c91a23b48d4229c87a20e47f81f7c7b21e147621d246fe1b946b819dc64a18c460e17d45c8166c56e152c51e13c44d812ac488119444210543f20f143980d5c33e0c6c2ee0b0429e09c424e08ac1fe079417c049c0d201a4000bfd8148143dfd7254940ff56150540fbd4254543dfd7158c20ff92058d10dfd8748053bfd8255110efd6058d40dfd8748153dfd7154c20dfd205d540dfd755d110dfd7159153dfd205c543fbd4250510dfd205d430dfd865c440fbd4254440ff92058153dfd825c063ff9205d110dfd205c053ff92055110fdd3048153ff55150510bfd861c940bfd8058940dfc825d540bfd811c153bfd864c510fbd4248040fdd2058d53dfd7254440bfd8258430dfd205c143fdd204c143dfd205d840ff48148063efd6158140ff92044153dfd215d540dfd764c420ff94248110ff48148053bfd835c910dfd7148020dfd835c910bfd8158040fbd5250540ff5514c553dfd764c910dfd7154830dfd7348110bfd8448110fbd4158940ff5514c110bfd8148063dfd615d440dfd305c910f7d5255140fdd3054543dfd7258140fbd4254840dfd605c840bfd8148053dfd605c031ff53148510fbd4255110ff48148030fbd4158d40dfd525c143dfd7248140dfd755cd10bfd851c940ff55250510fbd2050540fbd544c540dfd7650110bfd8058430ff92058143f7d5254543dfd754c020ff55150110ff92058140bfd8258440dfd7158030dfd205c153dfd7148030dfd7258d40dfd535c910f7d5244153ff5514c420ff5415c910fdd3258d10bfd804c940dfd865c031fdd314c940ff9514c140dfd7044153bfd8254543bfd8058d10ff9204c910dfd7650510dfd7258430dfd525c831efd6158040fdd604c143bfd8054543dfd7348510bfd854c940ff5515d110dfd7254840dfc725d540dfd865c430dfd205d830dfd605c543dfd764c020fbd2055140fed2054940bfd8158d40dfd525cd10ff48148020ff5515cd10dfd7154840dfd765cd10dfd205d543ff54148110dfd7154140bfd8258143ff94048110dfd805c863dfd7344020dfd605c440fbc8255140bfd8258153dfd525d110dfd7254430dfd205c840dfd605c831fbd4250553dfd105d540fed4248110fdd3058d10fdd634c940dfd8748143f7d5254540dfd205c863fdd524c143f7d5250153dfd7258540dfd765cc20dfd205c440dfd755cc20dfd764c110efd6058d53ff5514c510bfd845c910ff5514c540dfd541c910ff9524c140fbd4258040dfd205d110fbd4158140fbd4154140dfd205c063dfd724c540ff9205cd10dfc8748153dfd205c553dfd615c840dfd7254540dfd525c031fdd634c140ff48148040dfd205c463ff9604c140dfd605c143ff56150553fbd4258440fbd541c940bfd8054831df) else (if i<3 then 0xe31382b14371285e1485b0019158003d0b48170621485e1585a60b82d12821685c30b42e0b03320021605e30742b0002f200e1688110a82e0e080042a170c2c0ac41c05a21142c105c0f84a0042c501d000b42e24001385a3006070a42d800b0223e20902b07000904a15a4e0005e40bc2d1058158a000a42d185d0fa4030fd1687c310a42d800e1685e2400290b460005a28d033004000aca038001685e40442d0bc61fa830005a40bc318402c20661788070002d0bc814c000005a487d120c42e0b60034371285e1485b0018330b451380e0005640fd418002d20561505e30b045107e0b43e1885216c0070442f105c1985216121b8942f0a42d800c8ac001e85a40b82f105e0f85630ac2d1008158028f902d800320b8816c001905c401c3d0b46008002705648a0010002b223e158811800290b4817052178e000a42d1c4b0005e30b42f1002c24001485a34a0110b42b2022170581c121f0c5160b42e800c1705a24a0000bc614a000005a4046000a42d20021585e30fc418002d24001485a3008000b4712c3f03c0040a42d10380de2c1204a0fe2a0005e15ab160902507c2f0002e0ad01882008c88160561705a80731506c240941fc58000bc2b56820e0361204a0fe2a0005e15ab1c4c65f17ec59714cc4cf124c3df0dec2ef0a2c1ff066c13702abff6fe4bf7efc6beb6f9ebe3ef76bd9ef44bcaef12bbbeeeabb46eaeba56e68b93ee36b84ede6b70edb4b646d82b5a6d50b4ded28b466d00b3c6cd8b2d6ca6b20ec60b0cec10afdebdeaf3ebb6ae76b7aad86b34ac46ae4ab56abcaa66a76a9c6a4ea8aea08a7e69e0a6f699aa5de954a4ee922a4268e6a35e8b4a26e882a156832a0167ec9f767ce9ed67a69e3677e9d967389c7e7069b8e6d49ac668e99d665298be61697a65c696de594963e58a959e54494864f4934649a91b6468911642290263c88e9638c8da63508d063288c162e28ad629289e626a88f621a88061d486ee1988626166853612a84460ee83560b28266080819e04480d60127f95fb87e55f7c7d8df547cc5f0e7badee67b0de9679cde4678b5e287815de2774ddb07635d74756dd4c74a5d1a7405cfc738dcca72edca27225c70715dc3e7095c0c6ff5be46f05bb26e3db806d9db4e6cadb126be5ad66b1daa46a55a726965a4a68c5a0467d59dc66e59b4669599665f596e652d92864158ec63758c462d589261e5860611d824602d7e85eed7a25e4d7665d0d72a5bcd6da5a8d680599d644588560857955cc567d55e544d4f05335496521d45a510542850153e24efd37e4d6d3244bdd2c04a4d270493522047cd1da46dd19e461516244fd12643bd0a4420505440ed00e3facfc83e94f8c3dccf463c64eec3afce9c39e4e5638f4dfc373cd8e35d4d523494d023354cbc323cc6c314cc3a3084bea2ef4b9a2d8cb else (if i<4 then 0xb440005c248e000006918570000044582d0b878004274042b185e10cc2d105a17891f0bc580041f085802091f08521709270b02d18001108330bc708058168c2a8042f40080f858158c400b0415c3e200021485a247c00104e0380030ac2d12028044e1692150b900187ea085c1690000c0014880407c3318520f856302021600034882d0b8714008800e1f08581689200b02d182216056341c2b000613856000c2e0a441705e20882f143a1585a30ac213c00800c000b841705224842a0b600224a0205834042b1142f207016881f0856147c2c104018002c105210cc2c10641585f00102d0b041689620a42f0b061785070ac001a4a1985c380040105c1485a34882b8006168002810250a82f204e1605a30b030aa00000c004482d0b8691056168e1d0b42f1a51038561692070ac2d1868808590005e54802d8002e201200a61f1c2a1605a34821f12461c0221585e1699000b02b185816883d0bc381a0016083308561788290b82d185c1580030842e0e02d22401685c30a42d122c140a040b82d20740005e30b02d123e1605680101f0b040e84e170c04084e1605a38003312440005a30bc0010568008030b42f143e1606230ac2f120f0f882d0e0483c3e148c1f08650005638042b0bc2d224e17c000012410b9001856160a270b441685088000018561786630c21f0bc600842d0bc70dc4a1705e4400290ac6814081685c40ac001022587c331a4f000003488283c00000c2f4002e185816882d10048805010ac2c1c2010ac2d1002f000417c0020ac21485e240033105616082c0b441785a21142f10701688040884148a0447c041a3e18961f0a4616042e0a441705220802c0bc61705a20ac001048148563c0028385e160c29084f0000030a42f105810ac2c123e0fa001790400858178928800001802c0a4010b02f105810c0290b0622a0e000d070bc00185e160833085817882b08221485a30b02d105e20082d0b050805c168c2c0b448f85e020e414582e0bc817856245420085a1740040bc4f0b061485e200407000290aca2005c24542c800000b4a1785c160c2b0b4408864270c070f42d18661788070b82f185c1c08070002f0b490dc4a178530005a60fd1687c310a42d800e0024e158c2d0002f1854038001705e50bc30005a0005c401c2f100e1788331142b180e1605a3000070bc70dc4a1785216c0060a82f0ac71a0508000313942d800320b8912c3e8440f001407004000b4817800168c2c0bc2d185b000641712000b4000b88178562008000b861705a20442f10221585a301c3d0b861685e28942987e07800a1fa2d0f8621485b001c070f42d1a2b0007a1690000b441705a1985840002f0ac68a87a168c100b42e18221788450b041fa830005a4046000a42d2023000521692150b0000b4902054178c004a02b18022705 else 0x5e000901402270b880080020bd0010581788300bc402042007c2c0b4813c0020110740061605a24a02a0b461605a212c2d10561e85e38101f0b00020521688015a0020b42e121010b03000522404310a0e168c2c0b4416056209c2b0b0600b02d10601605e38590012430385a171029)))
def x191l8 : Packing := (387,3,7,0,0,14,0,x191d8)
def x191h8 (i : Nat) : Nat := 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def x191d7 (i : Nat) : Nat := (if i<1 then 0x9b9c399b91b8f38cb84b71b5eb5c359b4c349b3c32eb26b2431c319b11b04301aff2f1aef2e72e4ae22dfad7acfacd2bfab22afaa229a28ca7f271a69a61a5424c23ea31229226a1920ba039fb9f39f11e39d61ce1c61c39ab1a899b18817a97817596816015294514293513292512291510d0ff8fd0ef8e20df8cc8ca0bc8a989688e88687e87686906105384603e03081d81580d80047f661205c4538fec910eb1a21fb14161120443f2a8298a64a07ad5854158940afac8aa839221d3d525c954503b5a84902ea2047f661205c4638fec810eb22a7fa92050960103be122902e031efc4818155110f5aa0ac2b02819f92021d54443af240b02ea20779245805c840e9ea12c0ba881f993055131503db2c6b0260a067d261205c440df490304aa2215f5914817114ebbb22b02e62067d2058748143ecea12a2b988157d9158175103f3260a0282a9e5f549841c153cfa4090e902a75f5984817114e3fb2243ac8a9ff2481524c143cfa48b04b80a757d9258575103f6282b0a60a0767509525cc40edaa130cb88819f48161d2018ff6282a02408865f21d5244153cee43a60902a75f5972052014fbe2c0902e22047f261205c553eba48a40ba881fd1302052054fa7a84a92ea2065f549811c153e7ab030cb8881cf56158171103b5a84902e22047f6448748153edaa12e2a88819f4916017218ebeb2ab8a621076d509855c440fd2a11029008197c875494054fa7a84c12ea2073d245205d8408fec910ea8a811fd9221d1054f3e930902e229c7f6488755110ed690284bb081df0914817014fbaaa2b9a621076d5c54258040ecea1240b9881db5415d9404432f90ea92a2a072f509205d840e9ea1302ba881d9d42581731038fac2b02ea2067d5c58258440ef8a8ae690221d3d7550961102bdb22b02e42077a481605c840ebaa8aa4b9a21de92054973442beb24c32e22076d5857250540fd8a0a84902211fd9221d4054fa7a84a8aea2057b649615c840cfaa8b06392219bd4260575103b3ae6a12c2207ea4814255110afac8ac0b88815dd925857310376a82c0ac6a0775245205cc40e9ea1240ba881fd13054531503b6ae2a12c22057b661615c840e7a48a40bb061f994158d30503fc240a928288737585605cc40e76b0ac0b90819f48161d2014f3790ea12a88872f509515d840cfa40b0e902a7dd93021d2054fe72a8a9260a067d61c8148140edaa12a4b88819bd5421d31503b6a84902e2205fc2614148110fe89810290287dd92058173103ed2a490220a9f875915458d53fd090284a0a21cad4248176103f1240a1260a1c3f261525d8308fa4c240b88a787d526187054fe9240a9260a9c3f261525d840c6e43ac6b22a7d2d42481751033a90640ae4a0763509205cc40fc8a0a629828199c872113054fe3260aa280a9f69509205c440 else 0x10200423e30660b04100160900851382e80030561002b05a2c820b8580020448082b05a484e0b4404431058b02d18220a00102b000224e800400000082908015a0010290800000016840005e8005455000817a001001604006001683058168c1602f05a30028aa001001482d102905a243e10100080000415a001001455000800ac20000170700041904800a8b2001002702d1516082b4002a8280040a41688000417041790010290b1605a22400b840b820003000447c178800050004000400ad000817900102b08290821a10105e80080a2c80040c815a00182f200200017800102d082905a20520b44083e0ac40a0f4004024e8004c0034550008105900080202c102a0b1605a3002e05a240907c158c1721f056305e105a1052105a105e0b440b420b417890f82b102b0a1f05620000bc158c178417850f82b14f04edcdaccd4bfcb7ca4c9cc9a48cc7f47745ec51449436433c26418c0b408c063fe3f63f3be63de3dbbd93d6bd43d1bc9bc73c4bb73a)
def x191l7 : Packing := (137,4,7,0,0,12,0,x191d7)
def x191h7 (i : Nat) : Nat := 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def x191d6 (i : Nat) : Nat := 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def x191l6 : Packing := (19,5,7,0,0,8,0,x191d6)
def x191h6 (i : Nat) : Nat := 0x81900
def x191d5 (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def x191l5 : Packing := (2,6,7,0,0,3,0,x191d5)
def x191samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc402ee4723402700821075b301c73e21f673,0x516b7a00004108082102532000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9401c100011c87330c6249c366a4c8c6487f,0x38c8481ffffae3330c6248c164a488c44829),(0x133511089c9ec04010038e7c8738f1078f9c,0x4321b34000011cc010010028831071038514),(0x235800308c800883e07c0f80f83f01f80fe0,0x24960cb3b52cc103e0580f80502f00b00ae0),(0x604a2032204028fc007ff000ffc001fff000,0x5a69404c4ad32e7c0027d000afc0014ed000),(0x8800ec54221107fff800000fffffe000000,0x52a908506683ef6a59000000fffdda000000),(0,0),(0x8a410885023507fffffffff000000000000,0x2c5644af997c0015a6feffd7000000000000),(0,0)]
def x191columns : List ColumnInfo := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | 6 => x191l6
  | 5 => x191l5
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 177 223 4 13 7 2 x191h10
  | 9 => lookupWord 185 697 7 15 9 2 x191h9
  | 8 => lookupWord 39 199 6 14 8 2 x191h8
  | 7 => lookupWord 11 35 3 11 5 2 x191h7
  | 6 => lookupWord 1 3 1 7 1 2 x191h6
  | _ => fun _ => none
def x191 : Forest := ⟨1215,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore known42623) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 10=true := sx191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_7 : block x191 9 7 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_43 : block x191 9 43 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_48 : block x191 9 48 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_84 : block x191 9 84 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_120 : block x191 9 120 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_9 : block x191 9 0 122=true := (@block_merge x191 9 0 120 2 (@block_merge x191 9 0 84 36 (@block_merge x191 9 0 48 36 (@block_merge x191 9 0 43 5 (@block_merge x191 9 0 7 36 sx191_9_0 sx191_9_7) sx191_9_43) sx191_9_48) sx191_9_84) sx191_9_120)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_5 : block x191 8 5 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_41 : block x191 8 41 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_77 : block x191 8 77 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_113 : block x191 8 113 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_145 : block x191 8 145 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_181 : block x191 8 181 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_217 : block x191 8 217 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_253 : block x191 8 253 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_289 : block x191 8 289 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_325 : block x191 8 325 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_361 : block x191 8 361 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 387=true := (@block_merge x191 8 0 361 26 (@block_merge x191 8 0 325 36 (@block_merge x191 8 0 289 36 (@block_merge x191 8 0 253 36 (@block_merge x191 8 0 217 36 (@block_merge x191 8 0 181 36 (@block_merge x191 8 0 145 36 (@block_merge x191 8 0 113 32 (@block_merge x191 8 0 77 36 (@block_merge x191 8 0 41 36 (@block_merge x191 8 0 5 36 sx191_8_0 sx191_8_5) sx191_8_41) sx191_8_77) sx191_8_113) sx191_8_145) sx191_8_181) sx191_8_217) sx191_8_253) sx191_8_289) sx191_8_325) sx191_8_361)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_17 : block x191 7 17 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_53 : block x191 7 53 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_89 : block x191 7 89 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_125 : block x191 7 125 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 137=true := (@block_merge x191 7 0 125 12 (@block_merge x191 7 0 89 36 (@block_merge x191 7 0 53 36 (@block_merge x191 7 0 17 36 sx191_7_0 sx191_7_17) sx191_7_53) sx191_7_89) sx191_7_125)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_0 : block x191 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_2 : block x191 6 2 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_6 : block x191 6 0 19=true := (@block_merge x191 6 0 2 17 sx191_6_0 sx191_6_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_5_0 : block x191 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_5 : block x191 5 0 2=true := sx191_5_0
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact allx191_5
  · exact allx191_6
  · exact allx191_7
  · exact allx191_8
  · exact allx191_9
  · exact allx191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl191 : Impossible false (graphGoal 1215) 10 (vars 1215).toFinset := plainA (q:=191) (prior:=boundsBefore known42623) (before_sound known42623 valid42623) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6847 : Lower false (varsX 6847) (graphGoal 6847) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=0) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known6847 := extendKnown known42623 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6847 : Known false known6847 := extendKnown_ok (m:=6847) valid42623 low6847 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low18111 : Lower false (varsX 18111) (graphGoal 18111) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=1) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known18111 := extendKnown known6847 11 [(14143,[135,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid18111 : Known false known18111 := extendKnown_ok (m:=18111) valid6847 low18111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17087 : Lower false (varsX 17087) (graphGoal 17087) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=2) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known17087 := extendKnown known18111 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17087 : Known false known17087 := extendKnown_ok (m:=17087) valid18111 low17087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2239 : Lower false (varsX 2239) (graphGoal 2239) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=3) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2239 := extendKnown known17087 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known false known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower false (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=4) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2751 := extendKnown known2239 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2751 : Known false known2751 := extendKnown_ok (m:=2751) valid2239 low2751 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1727 : Lower false (varsX 1727) (graphGoal 1727) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=5) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known1727 := extendKnown known2751 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1727 : Known false known1727 := extendKnown_ok (m:=1727) valid2751 low1727 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42687 : Lower false (varsX 42687) (graphGoal 42687) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=6) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known42687 := extendKnown known1727 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42687 : Known false known42687 := extendKnown_ok (m:=42687) valid1727 low42687 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58559 : Lower false (varsX 58559) (graphGoal 58559) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=7) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58559 := extendKnown known42687 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58559 : Known false known58559 := extendKnown_ok (m:=58559) valid42687 low58559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58047 : Lower false (varsX 58047) (graphGoal 58047) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=8) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58047 := extendKnown known58559 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58047 : Known false known58047 := extendKnown_ok (m:=58047) valid58559 low58047 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44223 : Lower false (varsX 44223) (graphGoal 44223) 11 :=
  strong_full (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=9) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known44223 := extendKnown known58047 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44223 : Known false known44223 := extendKnown_ok (m:=44223) valid58047 low44223 (by decide +kernel)
def x255d11 (i : Nat) : Nat := 0x4c88f1a284060808057fc10
def x255l11 : Packing := (1,1,6,0,0,0,0,x255d11)
def x255h11 (i : Nat) : Nat := 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def x255d10 (i : Nat) : Nat := 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def x255l10 : Packing := (11,2,6,0,0,10,0,x255d10)
def x255h10 (i : Nat) : Nat := 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def x255d9 (i : Nat) : Nat := 0x200005068b4c0503680286a12040a400206080504120c88021b072002050c8041c30dc0041b80081c018005c205070060017081507000e8709188586c321207400e040807861f848043300071805000004420507006001708140019090788000c8483c4414002210207e12010cc001c607006001708143509020640300081d050008800205a342c36190903a007014002210206a12040c80600103f1a161b0c8481d00385a0011081202000c8043c50a0404838007438407400001708141d000b84081a84810320180040e8280044204cc38befa5ddb8d652ba55da8d452714b98eb1560d3e876ce35b233b600b39452584287acd3963274420788c812c1b414800bfec92e6086ff609730437fa60c1021bfd5260c10dfeb8306086ff60954043ff2e098021bfd9460810dfea1304086bf551860427fb2ac2021bdd5260c10df6b9b04086f74c18304377ae0c2021bbd4261010df6aa304086f765d830427fb2ec1821afd4261810deeb8306086ef655840435fa60c3021bed4260810d7eb9b0c086ef649840437da60c1021bbd73610109fec9308086f75cd830437ba84c1821bbd5261010ddeaa308086f75518304377a60c2021bed9460810
def x255l9 : Packing := (36,3,6,0,0,11,0,x255d9)
def x255h9 (i : Nat) : Nat := 0x4200118060050390014553e041769a0
def x255d8 (i : Nat) : Nat := 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def x255l8 : Packing := (8,4,6,0,0,8,0,x255d8)
def x255samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff981017018004f68c0077c4481d3200821075b3090d9a33c9401c73e21f673,0x7892404800340000422904481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff848d107200410000f6f7c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x30db990d14ace6f3090c0004081330c6248c10420400804264a488c44829),(0x6401400c52820973fe802081863c4010038e7c98c38470f188738f1078f9c,0x2c32446006102010020520810028401001002898838470a18831071038514),(0x260480809b801730000070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x50c43b9c31a55a2554aa470c07c003e0580f80407c03005e0502f00b00ae0),(0x1a6008010938f6000000380ff8007c007ff000ff0007ff000ffc001fff000,0x7298423ce4aa5daa954b803e8007c0027d000bf0004dd000afc0014ed000),(0x112a780a404008c01083ff000007fff800000fffff800000fffffe000000,0x469af34f68936130486f2a000006a59000000fff6e800000fffdda000000),(0x8c00720041000000003fffffff8000000000fffffffffff000000000000,0x7cf2466f2eb53190cf6f3fffbf7e8000000000fbdfbff7fbd000000000000),(0x6102a0847602080009083fffffffffffffffff00000000000000000000000,0x5384108b0966c9ecf9780d5effd795a6feffd700000000000000000000000),(0,0)]
def x255columns : List ColumnInfo := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def x255autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x255levels : Nat → Packing
  | 11 => x255l11
  | 10 => x255l10
  | 9 => x255l9
  | 8 => x255l8
  | _ => emptyPacking
def x255index : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 5 23 3 10 4 2 x255h11
  | 10 => lookupWord 27 69 6 12 6 2 x255h10
  | 9 => lookupWord 2 13 4 9 3 2 x255h9
  | _ => fun _ => none
def x255 : Forest := ⟨1279,11,fun j => x255samples[j]?.getD (0,0),x255columns,x255autos,x255levels,x255index⟩
set_option maxHeartbeats 0 in
theorem geomx255 : graphValid x255 (boundsBefore known44223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_11_0 : block x255 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_11 : block x255 11 0 1=true := sx255_11_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_0 : block x255 10 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_4 : block x255 10 4 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_7 : block x255 10 7 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_10 : block x255 10 0 11=true := (@block_merge x255 10 0 7 4 (@block_merge x255 10 0 4 3 sx255_10_0 sx255_10_4) sx255_10_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_9_0 : block x255 9 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_9_27 : block x255 9 27 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_9 : block x255 9 0 36=true := (@block_merge x255 9 0 27 9 sx255_9_0 sx255_9_27)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_8_0 : block x255 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_8_1 : block x255 8 1 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_8 : block x255 8 0 8=true := (@block_merge x255 8 0 1 7 sx255_8_0 sx255_8_1)
theorem tablesx255 : checkedTables x255 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x255 0 0 0 = true)
  · exact (rfl : block x255 1 0 0 = true)
  · exact (rfl : block x255 2 0 0 = true)
  · exact (rfl : block x255 3 0 0 = true)
  · exact (rfl : block x255 4 0 0 = true)
  · exact (rfl : block x255 5 0 0 = true)
  · exact (rfl : block x255 6 0 0 = true)
  · exact (rfl : block x255 7 0 0 = true)
  · exact allx255_8
  · exact allx255_9
  · exact allx255_10
  · exact allx255_11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl255 : Impossible false (graphGoal 1279) 11 (vars 1279).toFinset := plainA (q:=255) (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2303 : Lower false (varsX 2303) (graphGoal 2303) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def known2303 := extendKnown known44223 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2303 : Known false known2303 := extendKnown_ok (m:=2303) valid44223 low2303 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17151 : Lower false (varsX 17151) (graphGoal 17151) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def known17151 := extendKnown known2303 12 [(17151,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17151 : Known false known17151 := extendKnown_ok (m:=17151) valid2303 low17151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2815 : Lower false (varsX 2815) (graphGoal 2815) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def known2815 := extendKnown known17151 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2815 : Known false known2815 := extendKnown_ok (m:=2815) valid17151 low2815 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6911 : Lower false (varsX 6911) (graphGoal 6911) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def known6911 := extendKnown known2815 12 [(17403,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6911 : Known false known6911 := extendKnown_ok (m:=6911) valid2815 low6911 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1791 : Lower false (varsX 1791) (graphGoal 1791) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def known1791 := extendKnown known6911 12 [(17405,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1791 : Known false known1791 := extendKnown_ok (m:=1791) valid6911 low1791 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1279 : Lower false (varsX 1279) (graphGoal 1279) 12 :=
  strong_full (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (index_root (g:=x255) (i:=0) rfl rfl (before_sound known44223 valid44223) geomx255 tablesx255 (by decide +kernel))
def known1279 := extendKnown known1791 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1279 : Known false known1279 := extendKnown_ok (m:=1279) valid1791 low1279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58623 : Lower false (varsX 58623) (graphGoal 58623) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def known58623 := extendKnown known1279 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58623 : Known false known58623 := extendKnown_ok (m:=58623) valid1279 low58623 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58111 : Lower false (varsX 58111) (graphGoal 58111) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def known58111 := extendKnown known58623 12 [(68863,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58111 : Known false known58111 := extendKnown_ok (m:=58111) valid58623 low58111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44287 : Lower false (varsX 44287) (graphGoal 44287) 12 :=
  strong_full (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def known44287 := extendKnown known58111 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44287 : Known false known44287 := extendKnown_ok (m:=44287) valid58111 low44287 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42751 : Lower false (varsX 42751) (graphGoal 42751) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def known42751 := extendKnown known44287 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42751 : Known false known42751 := extendKnown_ok (m:=42751) valid44287 low42751 (by decide +kernel)
def x383d12 (i : Nat) : Nat := 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def x383l12 : Packing := (6,1,8,0,0,9,0,x383d12)
def x383h12 (i : Nat) : Nat := 0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def x383d11 (i : Nat) : Nat := 0x470d8350e0370d05b0b8070194240001b8921a62187a8312246301c3c0d9324a9574743b48c41a09424e57882391205c90d4680ec6338cc2f0ba411c350dc380bc6512a0200006544a000bf120c1114421780c90dc38408060eca3044a2fc482f4b2174451080ca55d56555584f54050449434340fb0f000074b006c405c8912b0baa1e0920380c1dc36924591685ca56140125414343440b10c3c000192b8904c0b9f13c55018000380c2d44b124b311c44a0c0ce8b21b16c3b206c1a80e0310494cd310d1144832b4af0f0184c442240bc2e78b5134551400e0344a004492cc4710a410338371283880a041340638930ec301a45a1f01803c2508c270e429104180041e924210680d512434c3c060ed10cae240b84c508c1bc08a0c07008901d20470e0461148a223a892388d2301f0008423621a8488e578800c87c48174d415013f4c83444d304512d0f8070193d4cd31435200030f4ad1089107b87912c5b164361d874172039c3d0701e240d02f0b901c06f010000314360d43482a0b81c063a66992628a00f87a609022696a16006560344817a201748360d40701883287c1a45b12c590d8768190631885d8906101ce2e8401207d04c11054160380ca00007018713c5512800038b5124b311c451080cc5615755955551535493d501414b10a435020f807c430f4ae24a08e1005a1f00100c0701408032851140370e04f00006389c2409423c590d800752d334c93144d304510b4b520caf0f89110001e2509395e208e44860a82900c2809c09092230962288406606c1a80e03101f0c004876128721a862170800b844140b40c83a0f83406980501c020040803180b82a0982007018d04c11054160380c698acada4af1f88eac6a227f0e0854c101ed2f00732b751b4ed7a66fb139806b2c561a9b948297e449a0f8fd27b23b39ab8d0262c2f095e0aaa4d82058e886ae30c13888c03661860618208082000ffc10443ff5c530ffd73443ff5c130ffc73443ff1cc10ffd300c3ff61d40ffc30443ff5c140ffd604c3ff4c110ffd864c3ff5c540ffc83443ff60c10ffd824c3ff4c540ffd700c3ff4c152ffd814c3ff5c430ffc710c3ff54530ffd624c3ff60d10ffc814c3ff60430ffd30043ff48130fdd83042ff60d10bfc814c2ff60c10bfc810c2ff61d40bfd864c2ff60430efd860c2ff20d10ff9204c3fe5c130fbd41503fb60810fed2054abf61830bed82042f760c10
def x383l11 : Packing := (48,2,8,0,0,13,0,x383d11)
def x383h11 (i : Nat) : Nat := (if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def x383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe98a82a06ff60d300437fa62c3a817fd981cd10ffcb12e0986ff61d810c2ffb2ec1a217fd9720530ffcb8260886ff545864c3ff2e0980217fd915c140dfec0ac0986ff61d83442ff930b1261ff96048130bfec9820886ff25d83042ffb2098a81ff98748130feea9ac0986ff25d810c3fda60902a5efd6358130feec9aa2987fe261704c37f926c3a81bfc8760d10ff6c9a40a97ef65d415037fb30b1261bfd8148130dfe4c2e2a05ff65d31503fdae490261ff92061930dfec930c986ff645875037fb2ec1a21bfd814c030feea9b04987fe64d704c37fb04a8a61ff8815c130dfeb8306885ff65d824c3ff302b8261ff9725c130bfecb860887ef5c541502ffb2c90261ff97061930dfecc2e2187fe481714c2ffb2a40a61ff9315c130ffcb8304986ff61d514c2ff930a8a61bfc9760d10bfecb906886ff205864c37fb2ec0861bfd8758930ffcb8240985ff649864c37f90ec0a61fdd314c110efeb8ae0a06ff261714c3fd924c0a617fd9620530dfec0b04987ef505705037fb0a90261bfd5320530ffccba40985ff645824c37fb0ec1261bfd8158930dfe4c260a96ff645864c37fa40c3261bfc8160930dfecc260a96ff261315037fb0ab0261bfd9361d40dfe98306885ff66131503ff242b8261bfd7161d40bfec8b0ea06ff21c814c3fbaa690261bfd815c430dfec0ae0186ff5c1864c3ff10e90261bfd8560930dfe48b0ea05ff6453054bf7b26a0a81bfd8161930dfe43b04987fb5c52054bff32c90261bfd874c010bfec8a60886ff609864c3fdae4b12617fd9161930bfec9102987ef505875037fb04b0261bfd8558930dfe48b0c986ff61d204c3fdae4c1261ff88148130ff6cba40a97fe545204c37fb30b8a617fd910c110dfec3ae0186ff661514c3ff2ca90261efd6558130dfec3b06087fe605204c27fb2ec1a213fd981cc109fe4c2e68867f61d830427fb30388617dd9304110df6cbb04084ff261714c27fb3039a217ed97481529fecb902185df654814c3fb262b82613fd9720d109fecc260886bf619700c35fb02c3061fd953481309fec9902986bf619300c27fb26c3a816fd960c110dfcc0a40986fd605710c35fb22c3061bdd9060c10deecbb06084ff654814c2ff32039a21fe97248130bfcc80e6086ef61d415037f2e0c3261bed824c010dee4bb06085fb648734437db0439821bed8260c109fe4c2a2984ff640834437db26c1021afd865c430fb6a8a40a95ef650710c3f6a62a0a81b7d8560c109fecb902987fa4c12054b77b0898021f6d53481529fec930c984ff661710c35f922c3061bdd7060c10dbec2a60084ff645875027fb30982a5afd864c010bf6c90208847f65c810c36bb0ac1821bad8460810ceec3b06084df654814c26fb2a40861b6d85608109eec9902986bb6198204379b04c18213ed9220430 else 0xd403806206406c00031461c4813403a21861dc2305306c200200020660f6481a817341b035c1582c1a20700c74230510ec2d0d204007e0e0f81a94c801f07e00f89035006a56130172824447001806a083707d8130183a09ab00580c27882102506c0d705862c1501c031c1b035c1582c1a20700c7c45884006230740f81702f09a907d8340382e0d21b8c1450503606b82c1a20700c808e0d81c03706a0d02d82e00e019400003806183606a01c03101b03500e01880d81a80700c412418c320620c317421e2400e900001c030c1b03500e01880d81a80700c406c0d403806203606a01c03100000700c38e151b0e34ec6408c1f177a2d145878ac3143e25ec481888b107e1fcc3b286d70c92179c2d8853909ae11d41dd836f061a0aac10e818f0286027c0137f82fde9fa4bf187db8fa29f323e337bc2f6c1ebfbd597a50f359e5dbcb6790af151e11bbbb772aed65d99bb027576ea55d00b9ba7328e42dc6d38466ffedf0dbb3371f6d84d9c1b1a35ed6b20d57da8c34bb68e8d0e19f333b56708cd2196ab2a464bac8b18ed31a962f0c4f188030cf60b8bec97c0af505e28bb0972d2e1e5baeb6156a4acf75960b1796112be65728acb1572aaa95456a7e94df29775234a37944628244fe69edd391a6c64cfe990d30925ec4b4a95d1296a4f1496a91b9213a3e047488d1d18022b944fa88d90fd21be4330857109020d94150812d0021fde3f447d40f7f1e963c5c7820ee09d903a6673b0e529c7437aa6e90d9e1b00358868c0cfa19c3333a6584c6c18a730d66090bff17c22f0c5cd0b8c96f32d8458e4af395b62af45474a6b1458284e50049c71331257c4a609231220238645f088490b720b43ff47c50f4e1d7439a070b0dcf1ace34d866c8cb318d831185e98b9716482af052f8a2313fa27044c809491230239c43f88170fcc1da039b86da0c8c17d02c0850e0920115020103b006900c041520231041607680d48178022003a805c808800ae00980007ff4c173443ffae2982a5ffd715c140ffecc2e2987ff25d30443ff92ec1a21ffd315c140ffecc2e6887ff4c530443ffae4b0261ffd7148130ffec8a60a97ff65d31503ffb20b1261ffd7220530ffec3ac4987ff595204c3ffae298221ffc8758930ffe4c2e2987ff64131503ffb26b8a81ffd7161d40ffe98ac0987ff66171503ffaa690261ffc914c152ffeb8a62a07ff64d514c3ffae6c1a21ffd5158930ffeb92a2987ff4c5704c3ffb2ea8a61ffd984c540ffec0ac4987ff4c587503ffac4b8261ffd9858930ffec82e2a07ff5c5824c3ffb30982a5ffd6560930ffeb8106887ff21d604c3ffb20b8a61ffc8760d10ffe4c2e6887ff25d31503ffac690261ffc935c540dfec3b02986ff21c834437fae6c1a21bfd9760c10dfe4c2e6885ff64073442ffb30982a5efd6558930fd) else (if i<3 then 0xec48134260076e5961f0008393ea2000017201a62420e0182602e303a1140ec1f04c284c00c0e81711a0c0605c30900dea0e240d81f8d8902610705c42561303f02ec4841cc0ec1700020e130a9641d00000c0b8b4400323e27c224171a3204d63a01a038393410098c3c0006a05c6c480182610705c58494ae8830f20e1300002e4533a1a01c1f03b0746c398829260dc1e0bcd8911231005c130b0f90013e62000017183d06d05e1a817169206a0e61301716902060d43a560180386905c5c4601826a0005c50760010300640e130c1dc3c20605c4108c8000340706c442684c422181e8000380609a6101018178c2e83500e1f817968a03961e4fa8800605c706e0f80020600c1f41d1c1c6040f78083484a0d40dc032426b0f40101c0313e07c1301726880000983a5641c3d0060980b8c10d3c07705c4c281330680c05c1a41d03b44094450900327605e68494ad8807305c130c1d40002f098449105216c0b8401340060e0e903da083a0d20b9c1300386a05c40921370560b06881c1b03500c90781301d03b05c56200003984c05c52644c686d412410d00392b2e38903604d098dc4841c0002e0985c480008382f207000c0bc60fa958060de0b8b4c699b1c0720e987d400d81a4170070dcc0da1303602e251000c1ac0382e28498698938786a098600e1a8170d1f60f80c0183515a13110994401716a083a41e9642600709a70b60e840183484d180600e0b83491a153362348026b580980bd87d10c480b9856124b0f00e0f80302e383606a01c03108383b00013017170de2509b8b40362c0980b9019c3303e0bc1f82e9aabd2a07c0000380612d4ca8e8950b6b06c0d403806205b08a118611c1c03706c0d41a05b05c01c03282ec0bc1221f0407f80c01d15071206c07c0001c80700c1f817a8170680763c1d83c0304d05c1f0351c0000700c30860e4838070698901782e472ba38c831204c05c60ba1281b80700d86f1608b09a00140eb0d83e0998b01703b38504040dc25038c08134032028c0209e0dc1c03a00001914c699b11a29cad87e24a2013017281b03509801c0314280510ba0e01b8354040bc3284a09e000033426e2200e0bb1084c11a70a20dc810380740181d9e99d140980e81703b3446441806a0e0406f80c2683a48460fc24448101b035c1582c1a40709801901304708d1b1d07c1903f0070c2605c1a01d8c991302664808a70f2e38902606a505e0ba19817c672c2a84b09000007c4588f1082e05eaa821b02683ec48c729584c05c906a82c1b60a05e0d103806460b0bc19c17a662c350d00ec62182f06705f198a0d81a80700c4a3a01c3087e05e10cc2202506100e410e2180387a207e09180427e0406f80c1d04d4a1d0fe0e807e0d85a0b83e06a48470b611822921442a81388c0040684988590085074b06c0 else 0xc0ec170e0761c41b8820620c322109b0187504a0b0f6218911204c05c805f4902602e2625c5a13017111107ccb301817143403b102e00c0ec6dc43665925601c2602e3834cb2cae8802f0740b8e8329204c0000b8b4801d2060f0130a41c3f807184c05e1fc6c3e886240000b8839987d1005e01c0302e322c84a01c0303a05c6c480004784c2541c482a400e80004c40c5a828183c03a222105d01803101a05ccb2c402600000e0b91504a0a061b0f0980e403103f82f00c0b898900040640c1e01d1a840436200b80307c303c0760b86d098450d0fd9641703a3b71a119642602e2e5962143c2500000c0b8f4219582e00c1f83e180002e40c0bc98900002e20e40000ba0307705e5cb343c0000640e41c171c3f80020e3a8250426a062034c490919584c05e0b8e830170060f840f40bc17006204d05c1e478929584c05c4091504a0e59074c3c269c3905b1029006a00013094401782e00040b55041c84d203461e4fa8842444841c2602e480012a16c600103a0607c130a2384684c186306c2584a901d83e00001c1a82e30060f81a86d0a99b11639452900940980b98787ea21891a9680042400c1e01d180302f09830758900007cc4213711b2005e1303502e60680760e81711a03416400f817331656c400051c09b89026370104f0700dc00006304d0980180382e290706c0d03602f09a0bb12202503b0688fa0002e3311a1a10c2600700c1f817230560b06a1342600605c7cb20003c40605c5a560f8030070740b8c1a10dc254590b41d83a05c8c480e48382f232ba201300380005c606e1301b03508e0d00380640390d40182e84c05e60f99643c20605c561f44312107098000171d878060d20b880182da460fe48288f84480605c52ae4b124c34e1fc40039020fd89154200302e0f84a381271213e4000b8c24c3504d05e40ea2301d02e4d00f8261d1f60f00c1a890251080605e400041c0387f0fc547d4400003a05c5a821b10307e260905e0e817623c434802684c00ca26445096920868233878062e244d1f02fc48130353d8804c0000b898911204c05c4c460b83b02f09a545886f12e2d0769a0261c1a84ac040dd1f05d0ca00003249f30f05c01826148e0494484f90002e35420861300303e6200b8e17426e240980b8a86c1d80682081c1f02e3f2bc4841c2600605c60920ed1213e620130171c2531000013026968103806e0ec031601a218480001b806074706996595a3ea201300000705c9c490909f0490980b8d50403a0040c0e8ac2d9004d00c0e817b10a838902606a586100c0e417118851c27c12826171242427c1300002e3542a2210c2604d00e01817201a62400c0bc1714460750740b93403e098706e16c45e2cc360e82682e07698481303602e22028000012303a2d31a1a0d81d20fa814401707))
def x383l10 : Packing := (259,3,8,0,0,15,0,x383d10)
def x383h10 (i : Nat) : Nat := (if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def x383d9 (i : Nat) : Nat := (if i<1 then 0x8158930aff6a0974c540fdb5495348130dfb5c99648130aff69d8558930ebf68d864c010aff69c984c540bfe680935c540fed4c5415c140f9f5456558930cff261905c530cff2a1974c5409ff69c9858930f7e5c0985c530ddf6557220530aff68c985c5409ff2a5714c110bfe688815c130bfe698815c130bfe2a5215c130efb5c98548130bfb6857258930fed504974c540f7b5c97148130efb5c92061930bbf68d6558130ddf6899520530bfe69c8148130cff26172545309ff6a48758930aff6a0914c152cff4c0985cd10cff261914c152f7b5c57260930bfb688974c110aff684984c152cff65d8254530d7f65d7220530bfe2a1215c130ddf5949854530bfe6948748130ebf6056558930bfe69887481309ff6989854530eef61d7150540cff2618758930fdb2a55348152ffa5c96048130bfe6848748130bfb6888758130aff68c9161d40edf5458558930eef61d31505409ff69c9854530cff2a1914c152cff261974c540aff6848760930efb69d824c010fd754c914c152aff6948760530dfb6497220530bfe2a1625c1309ff6a57220530fbe5816348130efb5c98148130ef74c49361d40ffa5c97048130fde54565481308ff6a57060d108ff68898545308ff688985c5308ff2a19720d108ff6a48720530eed4c58750540abf6989361d40abf69c91618308ff6a55161930cdf68d9520530fda4c15148152bfc28596481308ff6a585589308ff68d9161d40cfd2859261930afd2859261930bf668c8148130cfb65d93608109fe2a551481308ff685984c152bfa6888748130aef6909161d40ded505904c540cfb689981cc10aef6909760430abf2a5865c430dde2819520530bde6948148130abf69d9161830cdf6555161930cef6a1941c430cdf6555320530afb6888720530af768c9161930dfa4c19748152cdf54c9854530afb6888760530afb6819760810ef54c49161930e7e5c1874c010f7c5c5315c130afb6889760c10bde694815c130cdf545984c152fd65455348130efa480984c152fd354953481308ff6a19648130afe2a17061930dd754c9854530adf6948161930bdb68d5148152eed504984c5408ff6989854530dd768d9520530ef64c57061930adf6949760c10ebe5c1864c010ebd5c59161830bfa6888148130b7e69c815c1308ff6a581589308ff6a570619308ff69c9854530bf66855348130adf6948160930cdf5949854530ede5c1854c010adf6949161930f7a5c57248130efa5498148130efa5c98148130afe6809361d408ff2a53161d40cdb655821cc10f745c5315c1308bf2a5865c4308fb689981cc10caf619941c430cfa609901cc10fd25495348130af66809760c10a9f6949161830af36889760c10aaf6909161830ad76949760c10abb6889161830a3f69c9161830ceb651821cc10cee611901cc10 else (if i<2 then 0x300b8600e09805c305d06a1026803017817102001304a200000d4098404307c02e19030030170c1761781f860b648c0fe307e03a10ce817f12003017141ab4400b86072074203e00707c183e0178801c1f0506a0fc05e3e2404c02e1826017094741340181f80bca11407c098300606a02e1817026080d40180b8609809a202f04c142ef120170c01c1f04623a2005c3d2402f02e180301703e0c1b41300b8784809805c300602f02e1e120360170c01c1a81f0640c074209407e102180301703e135041300b8605e098203500602e182781d081a80b8405c107502e10038030170c0181f8134605c098206ac2402f02e271203f080d40180b87c480d805c3920e2406a180381703f8c01c1301fc61260f805c307c06a1433a3303f01790134132c81d074738900e80b9009a0d407540c09e586786607e02f201782d83f823101f01fe25c0b88622a282180d4a2061ee1c0d205c904c07f29702e202783e0408e26e19c13060fc09a10a102402f07c86704c2700f0182e0268409780780c170134204b0ce8cc0fc05e489785d02e1f71bb3bd80eb7f4eba53d00e71f2eb93bc8ce2bf0eb823be8debef1b73bb80dabeceb63baf4d65ea8b50ba50d19e85b3c39b8ccde5fb2c3944c8de3cb1ab8b8c4de1cb0c3838c07dfcaf937a0bc1dd0ae4b714b75db3ad6367cb35d93ac4b608af5d70ab4b588ab5d53aa4b4f0a69d2aa903458a17d04a7bb3b49c5cdba6a332897fcb5a55b290939c95a45b2048f9c72a35b19c8c5c5ba2a3134885c3ba18b09c83fc1ba08b028805bf89f8afb47cbbdb9e8af1c76dbaf9d2ae7872db8f9c42de06dbb639acad48695b4099b2cb0643b17986ac185f1af19722b6859fac595daad0547a999492a20501a79937a9944bba4d921a8e4463a27910286441da078fea7cc3d19de8ea272837f9b58d7269c33398f8c425f82ed96f8b5a5902b394f8a424ec26792988fa45421590087b23bc1c38c885c22ac13b89083a219c0b9852822a0e004f81780520009ff6a5714c152dfb5c9914c152cff660985cd10efe6056548130ddf6999520530cff261935c540ddf69d9520530aff6988760530ff65c55348130ffc5c55148130efb5c98258130cff5c5984c152cff261985c530efb5c98558930e7f5c0985c530f7d4c5715c140ff62a55348130aff69c8160930ffa481714c152bdf694914c152cff2a58758930aff6988760930efb5c98748130aff6849361d40edf2958758930ebf58d8558130bfb68887589309ff6a5714c5409ff6a55158930ff35c95348130aff6a0935c540efb6097254530ffa5c96548130aff69487609309ff2a5315c130efd5c58254530fdb54d7148152cff548985c530bef690935c540f7d5c5315c130bef690974c540aff2a17360d10ffa4817254530bdf694935c540cff661625c130efb5c9 else 0x1f0250500c05c12a309505b1003846778901f80bc813c102e02f07c184b03609cac1300b8607405c207e083e40303f035102780e440d80000983d4102f02e181704430205f8480d4362006a101783e0170c253890405c12c204c00780618498350178c8180b8250700c00c2000e2408f04c202d817881f00bc407361f00c0f84d4107e02e183503f095c4130405c80c207c02e103f01703e0c0f80e81a860d405e2d41206172c81d081a80bc1306138137106a04c1ea083f0178c1fc250400020e11e302e06a02f1817803095c60d01b3964130a05c13428060e900260350f504818405c10a2308e5902e094204c841d016c5c4805c05e3d41e24101783f8b5041f8130605e05c2e2406a171203f0ac441f0407300c098306ce5903a04f23120178a0d00e81fc611900c0983249b0f806181701783e0c01c1a8409a80c05c0d44d1007f02f181701783e0c0b816c405d000243404ce2418178266920f4900bc0b8605f00c0d4302e07f15c1c000b89001840d5a2009838062060941e88078900b80bc744200e20390817855c401c40d40742e24d2b10218350170c01c0b8405e05c0d43e2402f02e183a01708260384805e098302f07f101703e0b440819018605c0fe202f081783f8b44001c018611880c000309302e02f192572cd878000031401c0b8400c00e05c302f06a10178350825416c40fc05e2e2106a000c2402f284983e0178c13c1f8134607c000098300707c10260170801c1a80b8600e0ea0fc300703e03a1f120260170f8901))
def x383l9 : Packing := (203,4,8,0,0,13,0,x383d9)
def x383h9 (i : Nat) : Nat := 0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def x383d8 (i : Nat) : Nat := 0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def x383l8 : Packing := (28,5,8,0,0,10,0,x383d8)
def x383h8 (i : Nat) : Nat := 0x2022120a00481835bb4200000707b100030
def x383d7 (i : Nat) : Nat := 0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def x383l7 : Packing := (7,6,8,0,0,6,0,x383d7)
def x383h7 (i : Nat) : Nat := 0x78001b2d178400008
def x383d6 (i : Nat) : Nat := 0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def x383l6 : Packing := (3,7,8,0,0,5,0,x383d6)
def x383h6 (i : Nat) : Nat := 0x1e0
def x383d5 (i : Nat) : Nat := 0xd41d1505c4da54cb94817254530
def x383l5 : Packing := (1,8,8,0,0,0,0,x383d5)
def x383samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff081210205f8a00b8028136002c6004203f193090d9a33c9401c73e21f673,0x1a6b048b813a54161041804002c6004202519200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc48c8065583220a4000393601008190c2c861f1632604c0ff66a4c8c6487f,0x5909b044884ab21e4880c201008190c2886090420400804264a488c44829),(0xc240015520000003083a40960f060704f181c98c38470f188738f1078f9c,0x2a0760dbb36254861b3092d960f0607047181498838470a18831071038514),(0x8601e9022015e0030942c9203000180701fe0e0fc0780fe0f83f01f80fe0,0x10e894240419815884476d0203000180000540407c03005e0502f00b00ae0),(0x137002048460b8004001c7c007e007fe000ff0007ff000ffc001fff000,0x25146b507ac42aa16bb812bc7c007e007da000bf0004dd000afc0014ed000),(0x3110400a858081500828000f80007fff800000fffff800000fffffe000000,0x2094b2646e818949ce866faf800055a9000000fff6e800000fffdda000000),(0x20a8060080600a44740400fffff8000000000fffffffffff000000000000,0x3a6c2460a71b145a0a47e3cfcba50000000000fbdfbff7fbd000000000000),(0,0),(0x3524888800519504f50488fffffffffffffff00000000000000000000000,0x503499b106462a431381010345aaa56fffabf00000000000000000000000)]
def x383columns : List ColumnInfo := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def x383levels : Nat → Packing
  | 12 => x383l12
  | 11 => x383l11
  | 10 => x383l10
  | 9 => x383l9
  | 8 => x383l8
  | 7 => x383l7
  | 6 => x383l6
  | 5 => x383l5
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 35 135 6 13 6 3 x383h12
  | 11 => lookupWord 470 589 6 16 9 3 x383h11
  | 10 => lookupWord 338 423 6 15 8 3 x383h10
  | 9 => lookupWord 9 55 5 12 5 3 x383h9
  | 8 => lookupWord 3 13 3 10 3 3 x383h8
  | 7 => lookupWord 4 7 1 9 2 3 x383h7
  | 6 => lookupWord 1 3 1 8 1 3 x383h6
  | _ => fun _ => none
def x383 : Forest := ⟨1407,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore known42751) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_12_0 : block x383 12 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_12 : block x383 12 0 6=true := sx383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_0 : block x383 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_3 : block x383 11 3 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_18 : block x383 11 18 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_11 : block x383 11 0 48=true := (@block_merge x383 11 0 18 30 (@block_merge x383 11 0 3 15 sx383_11_0 sx383_11_3) sx383_11_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_0 : block x383 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_11 : block x383 10 11 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_47 : block x383 10 47 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_70 : block x383 10 70 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_106 : block x383 10 106 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_142 : block x383 10 142 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_178 : block x383 10 178 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_208 : block x383 10 208 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_244 : block x383 10 244 15=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_10 : block x383 10 0 259=true := (@block_merge x383 10 0 244 15 (@block_merge x383 10 0 208 36 (@block_merge x383 10 0 178 30 (@block_merge x383 10 0 142 36 (@block_merge x383 10 0 106 36 (@block_merge x383 10 0 70 36 (@block_merge x383 10 0 47 23 (@block_merge x383 10 0 11 36 sx383_10_0 sx383_10_11) sx383_10_47) sx383_10_70) sx383_10_106) sx383_10_142) sx383_10_178) sx383_10_208) sx383_10_244)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_0 : block x383 9 0 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_16 : block x383 9 16 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_52 : block x383 9 52 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_88 : block x383 9 88 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_90 : block x383 9 90 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_126 : block x383 9 126 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_162 : block x383 9 162 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_198 : block x383 9 198 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_9 : block x383 9 0 203=true := (@block_merge x383 9 0 198 5 (@block_merge x383 9 0 162 36 (@block_merge x383 9 0 126 36 (@block_merge x383 9 0 90 36 (@block_merge x383 9 0 88 2 (@block_merge x383 9 0 52 36 (@block_merge x383 9 0 16 36 sx383_9_0 sx383_9_16) sx383_9_52) sx383_9_88) sx383_9_90) sx383_9_126) sx383_9_162) sx383_9_198)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_0 : block x383 8 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_11 : block x383 8 11 17=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_8 : block x383 8 0 28=true := (@block_merge x383 8 0 11 17 sx383_8_0 sx383_8_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_0 : block x383 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_2 : block x383 7 2 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_7 : block x383 7 0 7=true := (@block_merge x383 7 0 2 5 sx383_7_0 sx383_7_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_0 : block x383 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_6 : block x383 6 0 3=true := sx383_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_5_0 : block x383 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_5 : block x383 5 0 1=true := sx383_5_0
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x383 0 0 0 = true)
  · exact (rfl : block x383 1 0 0 = true)
  · exact (rfl : block x383 2 0 0 = true)
  · exact (rfl : block x383 3 0 0 = true)
  · exact (rfl : block x383 4 0 0 = true)
  · exact allx383_5
  · exact allx383_6
  · exact allx383_7
  · exact allx383_8
  · exact allx383_9
  · exact allx383_10
  · exact allx383_11
  · exact allx383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl383 : Impossible false (graphGoal 1407) 12 (vars 1407).toFinset := plainA (q:=383) (prior:=boundsBefore known42751) (before_sound known42751 valid42751) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2431 : Lower false (varsX 2431) (graphGoal 2431) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=0) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known2431 := extendKnown known42751 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2431 : Known false known2431 := extendKnown_ok (m:=2431) valid42751 low2431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1407 : Lower false (varsX 1407) (graphGoal 1407) 13 :=
  strong_full (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=1) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known1407 := extendKnown known2431 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1407 : Known false known1407 := extendKnown_ok (m:=1407) valid2431 low1407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54143 : Lower false (varsX 54143) (graphGoal 54143) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=2) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known54143 := extendKnown known1407 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid54143 : Known false known54143 := extendKnown_ok (m:=54143) valid1407 low54143 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44415 : Lower false (varsX 44415) (graphGoal 44415) 13 :=
  strong_full (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=3) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known44415 := extendKnown known54143 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44415 : Known false known44415 := extendKnown_ok (m:=44415) valid54143 low44415 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43903 : Lower false (varsX 43903) (graphGoal 43903) 13 :=
  strong_full (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=4) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known43903 := extendKnown known44415 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43903 : Known false known43903 := extendKnown_ok (m:=43903) valid44415 low43903 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42879 : Lower false (varsX 42879) (graphGoal 42879) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=5) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known42879 := extendKnown known43903 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42879 : Known false known42879 := extendKnown_ok (m:=42879) valid43903 low42879 (by decide +kernel)
def xdd14 (i : Nat) : Nat := 0x16ad2728c1ee6b16a4a0e629062082fff
def xdl14 : Packing := (1,0,5,0,0,0,0,xdd14)
def xdsamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc020000000003000003fbc001bfc000003ffc4c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x1c8e5425111515114115514111115115115104c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd000200000000003cfc000000000003fffffe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x200109c08e0a688e08e08e0ae48e08e08e08e10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x800010000007fc000000002003fffffc0000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x360c43c50c51450c50c50c50850c50c50c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0xa000fdc008000100003edc403ffc000000600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x18091ac1a418c1a41a41a41841a41a41a41a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0x800000000b000000003eddbfc00000000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x2370a11a4ae22a4aa4aa0aa6ae4aa4aa4aa4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x520da4003ff4800203ffc12000000000000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x16003c06c42c06c16c02c16c06c06c06c06c000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x3a5525a020000003cfc000000000000000003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x19783603707583703703303503703703703716a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x180005003b907fc000040122000000000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3c9f380383382b83283383283783383383383ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x2e57dfaffc464800300000000400000000003fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x2686c03c03803c03c03c43c03c03c03c03c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xdcolumns : List ColumnInfo := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(42624,0,42879,0,13),(43648,0,43903,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(60032,0,60287,0,13),(69248,0,69503,0,13),(49168,0,49647,0,13),(55312,0,55791,0,13),(43072,0,43455,0,13),(58432,0,58815,0,13)]
def xdautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xdlevels : Nat → Packing
  | 14 => xdl14
  | _ => emptyPacking
def xdindex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => xdsamples[j]?.getD (0,0),xdcolumns,xdautos,xdlevels,xdindex⟩
set_option maxHeartbeats 0 in
theorem geomxd : graphValid xd (boundsBefore known42879) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_14_0 : block xd 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_14 : block xd 14 0 1=true := sxd_14_0
theorem tablesxd : checkedTables xd 14 := by
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
  · exact allxd_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 511) 14 (vars 511).toFinset := by
  have h : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
    index_root (g:=xd) (i:=0) rfl rfl (before_sound known42879 valid42879) geomxd tablesxd (by decide +kernel)
  have e1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower false (vars 511) (graphGoal 511) 15 := plain_low (hints:=13438558465) (by decide +kernel) caseFA
def known511 := extendKnown known42879 15 [(511,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known false known511 := extendKnown_ok (m:=511) valid42879 low511 (by decide +kernel)
def xmd14 (i : Nat) : Nat := 0xc0280801804008007ffd20
def xml14 : Packing := (1,1,9,0,0,0,0,xmd14)
def xmh14 (i : Nat) : Nat := 0x100b543d23a41ec13f0a800211940df4a8000000000e080003010000f49000151a000147d06440200010a42441136050004a2c11000060c402a42e81110610000000007018000009e0e10e320400120940d9a6142c000441000202400000000005344066427203d2f602349c219c35c070103348010000000010000000200001051021001621000000
def xmd13 (i : Nat) : Nat := 0x24a80696200c02426974e8150221305607c088393a0540884e01c02800048e9702e23045e9242d85a4b296109a902a1305a95d2b2550a80f101491401644e8841d83c07a0450222504808d0f0128060800f85103b00000802ba504848a910a3746c84107a0b41c8342302000e0280901103a0040100849e93ae0581e2054260b00900a49a0ec0883d4980041004b7a4a49286d0d04808e0b41582401485169092023641884107a0d41683902a1340811820a37012028090118040041c80808b80880ec1ea054080f00480a0040460181201090d0f001824246c83505a130829011b8094208390620f0240460180a80402200001ac13427011024028020fd13a0e072a45e0ec1e02c01284d0221a0240f41581f0020e5c8dd1b20c42083d0720d41684c0480a02500c0880107d00004007983d078058160120760451d403014896000016c0540b011022138020e41c211ba3642083d0720d4168d40900a46804400a3306484e08190220580700a00c003a314608bd1740305a0b20002b04684d68a914a2844e89912a0540809011a2244201e0182080207d0f0028000740e590da1a4330610b81602a85109a529a2f4348d80f839300402681601c02803000e00809c0242690e1ca1e41a800a0100981f072044c0140221380700a0001238154548a51122844e8851321e00e0800f82404700c0081d80000a604808a1041e83906a0c416018050098060060000800f0812bf4df02f0e758b6bd95ac035c2a9e13868d74321f14dde65b2ff15249ee4791c10c685a628111207743160b50007ff54d20ffec8a41ffd93483ff8a6907ff60d20ffeb8241ffd74483ffaa0907ff26120ffea0a41ffd30483ffb08907ff60520ffe88241ffd94483ffb00907ff4c520ffea1a41ffd98483ff926907ff5cd20ffe41a41ff910482ffb30907fe4c120bfec8a417fd93483ff2e0905ff65120
def xml13 : Packing := (29,2,9,0,0,13,0,xmd13)
def xmh13 (i : Nat) : Nat := (if i<1 then 0x8142e90b40b5d47d30255c04b60fe5062800f2c1f4aed5600bda1e7d12da281802dca1cf99b6e0b61007f2342c15768adc4730000225cdaeef000010bcec19d20a4948280280809ac858e03b9da1800000060645b0830f00b3202f207e7a19000014af3c021824280001208a00002008f815aa0041015120b1a205610600001a278415fa816901c0000381080000375f14af9c0f0000000005008500b80000c024681f0c16f008000005019741580000142d2a02fc4440000c43c32379d1cf4887d061381a440fb2033e02e9015ac50b88db00000000040c2c814b4178828559d7c2410446881ee5067000a000060328501200000000000039d3e0000e02bca11f1136201a652098a2341360000507db819951ba48830000000000000c0c0f029c232540260000a64440118000000001036f8079910ac10700007a15d41d6c01800005024f11100000893c0000340ffa806b0374a2ec80e3acf3973c48374c17aa0f600007807400000000607300000001a92e9901ae84240000e0050000000000000000000006227501d26063c05c60150000028c800007a80641c60000a03a9a38400006073507ab01ab10a980aa8080683bbc40301026073b21980001e81c13808000350526e5a146ac800841c30008f856000019dcc000000000000210600000e948800000000e8b21068fa2de9108a85ee41ecb15580a24103106a800eac1c0e8f8d0822811665d52031700c903c2518b022a9627800000146000034608000000012089000000000404e0000094f80000000000409418b03180001205ea086800000001c84f548200000000000000000002a1e90de82e143f00000ad320000844ff02cc000042d7d459f00d3805b6ad7274880001d123201f00007832741740000b02200003405c60520000183a80000000010386210c8153802900000025e8092806c0000000018172a83500007033f5100cc32f05e382580000c0b100001832dc123007900005bba441f00000944cea21a0057ea85301210353808e62490000183d381ae487d801c80002c17ce014b0413a05c008200009477203c4c138e0e8447600000015d4037107ee837d18f78064007bda924418f40a240529a29ac1a00000045f1b2b0c1f3a0ef506642104c0d680a60463c0a890c59a0f386814a3dac1ada009f47130001407b409a0000784298124004a4005d22d30129a0f270344042f0058e08115516b2f1013fa8d854355c9682850e242a3052c10207086c104044001000802000c180007070000609861a1c30704009840805c21020c11100059800210480021c80202742002a24980041c400002408718085040014000002c100042498d081808d00906b9021400002480000e000800028309142400a045410f00143860a04c0000280000000005040400b0a0c0801a1818a0008507 else 0x6819d51d36c0ee4787806d90746a8160216036ec1b0205a2045c009ae1e688f2445a8b2c09117a0edb4729837885e4e06fc47698073d17540280060b0260c0be0000345c480f8909b60e5d65d8000611570819a41c282392d0a00006043fba2615e4c0a7903163aa05081ce38a04680364901ec0863001b0422421828d278278834cd1b2a09e302af48e151a9c85260622a0da8168c036d0447003a404540bb0408783684099207a006978233400caa221066a0215c00e2016041e6d1d0000048778082ca345d19e66156008381c9810640ff0000220ac802b603f003f121c4d84e2074a0061a1d2c17f08dfe076000024d57a471d0642a1ac5098c099b4510cb56518c000000088000000000000301dc82740001ce39241d800000001e012e47d800005dd5809050106a2b941c4e8946475019c400000000f0808000080b08c46c01900001d12bec949a4c9023e509c40b23025da1bc0001807600003013a50940000377458390000020dc0000582c3c09e0000c0183)
def xmd12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x3ffda764d20fff66173483ffd7361120fff69583483ffda054d20fff2a553483ffda04c520fff4c498483ffd9850d20fff2a583483ffd9850520fff68d91483ffd9364520fff65583483ffc8364520fff64d98483ffd9561120fff68d10483ffd3165120fff60453483ffca366120fff68d81483ffd3161120fff54493483ffda160d20fff68598482ffda560d20dff661744837fd9366120bff6a191482ffda126120ffe4c110482ffda844120dff60d93483ff9a14c120ffe54d704837fca366120dff655104837fca864520dff64d91483ff91054120dff5cd98483ff93054120bff2a5814837fd9550520dff65594482ffda364520bff69493482ffda824d20dff54d94483ff8a84c120ffe505704837fda164d20dff61593482ffda124d20ffe4c191483ff9a84c120dff2a5534837fd3166120ffb549504837fd985c120dff66110483fed5224d20dff28d91483bfd9860520dff685984837fd9561120ffe6a110483fbd5465120ffe65510482ffda120d20dff4c594482ffda114d20bff6a194482ffda354120ffe661704837fd935cd20dff644984837fd3066120ffe615104837fda960520dff545934837fc5364520dff65543482ffda814d20dff6a583483ff9845c120dff66143483dfd735d120dff66191483ff9834c120bff69483482ffda326120bff2a5834837fda466120dff69d934837fda864d20dff6a191482ffda914d20dff25493483dfd715c120ffe4c180483ff9935c120dff69593483ff95344120fef61143483fbd5461120ffe65530483ff99344120ff74c530483ff93026120ffe689304837fd9824d20f7f5cd70483ff8a54c120ffd4c5814837fd954c120ffb548834837fd9865120ffe68d10482ffda960d20bff68980483ff8a94c120bff695944837fca94c520bff6a1744837fca864d20ffe66110483ff9a54c120eff60580483fed5244120fef50584483fbd4165120dff60d914837fc8364520dff60593483ff9854c120dff6a553483fdd534c120ffe60d104837fd9326120dff68d91482ffda15d120ffe66130483ff9a04c520ffe4c1814837fd9124d20ffe55170483fed524c120dff29593483ff9515c120dff65493483ff91060120dff65483482ffda920d20bff68d104837fd9564d20dff66053483ff9a5441209ff6a5534827fda8645209ff2a5314827fca954d20ffa50970482efda620d20b7f69c934827fda5651209ff6a580483fd9304c520bfe680534827fda914d20def551944827fda364520ffc54510483fd93054d20bfd684834837bd41651209ff6a483483df9715c120feb50943482ff9a3441209ff2a583483fe9524c120f7e5c174482efda624d209ff6a194482dfda720d20bfb68883483fe95244120bfe68083482f7da520d20f7e5cd70482fbda420d20cff605984827fca960520 else (if i<2 then 0xc94518a1486e85c86b0e605485084d043643408f87302d02a428426808422622202402300722122701f002c03c0061301d750b90d90d023e1cc0b40a90a109a40ff00b00589d8390e4c0ee0ec0ea0e803000400344f41c0a2090b80057fb87f477f127e957d947cb77c827c297bf47b2f7aee7a657a2479cb790678b9788478137766771976d876a375ea75a9756874a373ea73a9737472df72aa722171a470d36ff66f556ecc6e8b6dba6d856d086cbb6c266b616b386ad36a92696d693868eb68aa682d67e0676f66f26615658c653f650a648163bc6387630a62c9622861cf612e60ed60405fff5fd65f7d5f245e235dee5da15cc45c535b825b295ad05a8f5a2a59f5599c5973593258c1589858575762572d56c8563f55f255b154e05493541653e1537c53235282521d51c4512f50b250294fb84ec34e5e4dc94d7c4cff4c6a4bd54b584aff4a46495d48f8485747aa470946a445a3453244c1445c43eb436e42f1428041f7415640f1407440333fda3f693ebc3e633dc23d513ce03c273b923acd3a5039bb390238b5382037bb375636cd368035f7356234fd3408337332ea326d31d8314330a230312f9c2f072e7e2e012d842d2b2c8a2bd12b002a832a36299528d0286b28122795273c26a7264e2595251824a723fa23a122f4229b2212217120ac1fe71f5e1f051eac1e471de21d411cb81c171b8e1b1d1ad01a5319ee196518b8186b181217ad175416bf167215f515a814fb144e13f5132412b3121e11d1116010ef106610250fb40f430ef60ea90e140d1f0cae0c190ba80b2b0b020a910a2c09bb097a092d08bc084b07fe078d06f8064b060a05d5057004db045e03e10370030b02be025901f4014700d600890000fff60980483ffda94c520fff66181483ffd9844120fff54d81483ffd8761120fff54d74483ffda864520fff68181483ffda260120fff6a553483ffda54c520fff54483483ffca564d20fff69593483ffd9360d20fff66174483ffca94c520fff60d81483ffd814c120fff68530483ffd985c120fff68593483ffd8154120fff2a193483ffda354120fff4c580483ffd8160120fff6a193483ffd9524d20fff68553483ffd9824d20fff64d81483ffd854c520fff4c550483ffd5361120fff54d10483ffd5364520fff65483483ffd535c120fff66194483ffd314c120fff69530483ffd9860d20fff54d30483ffd9114d20fff60493483ffd9544120fff5c584483ffd9864520fff65531483ffda844120fff65530483ffd984c120fff68580483ffd545cd20fff54d94483ffd9550d20fff6a581483ffd9565120fff65541483ffd5354120fff68d98483ffda960d20fff66053483ffd7350520fff65593483ffd8560d20fff60d91483ffd9861120fff64c98483ffda466120fff66150483ffd935cd20fff5493048 else 0xa83926c81f05f3d2ad3052b10250985282f50a41e42a02fac92a02508107e0481780fe04412c1bc85100817da94453046046287045e0df80642684884083f4860be804011006fa36a0e83bc0365805f03f80a811002801c0008205e008805085004f83200c01c51084f04e83584e2e07e1180ae044a6c074020ed3409013212f0240dac28725322fa3609580327a81f05f4201b02d21a0150f14c04b82fa00fe05a0260f412001704e04989e0050e41ac17db07b43507803b40b4260cd0730025140beb04124223603ba05805046237c5806f081439008683780491b91b01d80502fc03a1c82f0042d95811c0b40ad8102591509810f1208e0da0bd02207e10c6048c02402804604a1343f627812439504a004302b02349b49248948229280b407402113b0069741e70e423c2256c9507901502583080907601102211acbb43d0020bee65606321a45426c2603015b02044a09412036d0a1d81181584e0460e41b607c17d005640a0df01451603a0107c03403604a4380206f213a1e614a0d05e05f603693641cc1c04482f1802281100b00904d84e0fd8798360e5546203e0cd80005610c6283a2163703b03c03d60e011082c0008105f01d04b741dc1ec05409401801502c1e00eb4040431440082fb99581a811c17f0001b41fce0fc0fb44545102b44e0a2c0ac264f904100407a0d68720be03b1a3182c05e02b605020c00066079492981e00900b01d81ea0181580093d20f82fb106085e05817a8501e4d42e43643440807e42842702a0be983b809204801a1a83926c81f05f4c01a01d02b0290260010982f40921002fac1a817c9a41a019ca45f4344344a607a0cc4cb03e0be9a4a01d00800504ec3907fa5d0794802009b02c0fc08c1c980100b40f81c60e20e4c16c00200819a0900040261461494ba14e056c642a2aa21a1e63702060e03d03b01f03c01200a04b011c0001d008c3924ea50b90d90d023a1cc0b40a90a109a48c08c48bc0700b70e60b008f0000740ac84d941d07b07600ac0980187300e010908443824a83d00406fc392148014025306c1c41c8c8e88c29248be97216e96496084d34934b80910b50b74b24b0426803d20e03b604004c00c398070084823b09c0fc1cc08968be86894c0e40f607cc002027805409494c87872c3cc1a9a1721b21a04703f816815214213490601dc03a1c85f8041a85c86c8680130e605a05485084d216844c45410802a04804600e0a900287203ac04623620d03d06f03b20e011213ab1a83a33a2a0087529d0d41c93640f960f00ae1500b48004002c09426d01872c50c6e808422100aa0e03c012a8b011a13a4f24e01d6155118118917816c16015854c11909aa0f683a0ef00001004f0e585201c021443587383043702c03803a428426921aa1721bc39816015214213403ed17d0d31bc1)) else (if i<4 then 0x807ec268708720de0bc927c25383c23a68083d06620408f05f04b5d10d0f41e20c509d1381fc01025e0003782f842368120f412c8681be0e607c17d146345f8730580bc802046d000cd426a63106683902b086281fd0751384ac1c83582f9c1bc21300584f0082382550e4185307b07601040942741d87307805b01100380084018ae253839a2fa3627a81f05f391b11b83790701de1c804805008e0040382f804348bc86817894e8d819a0e508017d302c08e0bc4360da43502a42607e9072a0ca0da0e83b09e80460480560507343943805e008783501690281591803590211793d909c6102fb20268da8de83a0ef0030e40ac81084e04417d85201c178022149908d0770081530235825310400beaa268540b3095a27c0061361405e80205f084604315703c918d13c2a20c060510c0ec0160020902f00e3e9281b507d0468500acc87687882482303080300940ac86c3c0be0dec63122f49121a0b503b28a2be441ce01202209d0751383081fa01aa01581684c84c2380770090e50f417d60da05a1784f60be10c6ab183da0e83c0080bb283095801a330795d2e42e118117816815c2d42d93490992c116b295811c2269569820f21501851454c8544343cc6e07b03ec27040076c1c0220a2d7407900503b80049c1034a37a0d83da0e04509504b2b1a1383206106f642350700f81680440884252783680e80e2e81181284d84c0fc17a0460e607c17d446045e07845a002462caccaacc04268a8112c21b21ac39047c1881602b8150b22142132ab610d90d02402390201590981692540541210a036b42d423481484e9540f81448b40ad2c6ec1d801806806c080bed718041600bc0dec629627621c03403605658c0040281209705f6601a01847601302b2c02f60040904b82fae0e40e581184d85017a0442a607c17d54b34b846045e1530b74d24b04260beac0001d008658a130a702b385a40b10f41e408e02e09c09042015a1cc0080eb402600f0628110088140ec0f004404990c02987802017df45344d4510a944f04103f806166c08c0b4438000241030040bf1c0340340260505e658c0081209705f5015b25129c1c93640f981180248dc8d88340f484c04c0441b60c8ac4021a46c07a41c07783100a40801246e0220820de0978000da0110403a4361421305ea0d42005f412990d036c1c93640f82f9e0ee0470170101ac1b50e60050e017d54954360150480db4281127230231438a4322f40360461408921340205f630260004f41185802f0379c88489c87a0f007e04b0142bc21008e044207002004075e0dd41a0024260df4860da0becb0010ac0461303902d2130a9438a0e06b4c1ec1dc01a0c502a0290241e404009d21c00a1002fba05a86817a850aac23e84cf46f07780100608b408c0941cc2900e4280be0bc0deea53253a1 else (if i<5 then 0x7ca55d08c8a8c3c83f07280442615803801012a102d402801a0560521305e05f392510d90d02405a830a4883191885390a21d943b417d1502a50f018cb08346f41d014435409022160cb04280a300207e0dee08d68c081a1406d2d0282f02f8c2c88160801bc96200817ce55d0a80380bd00410212a749143883d83c41fc18c05a0560540481342081181201d05e00805f680402801ac0910984082f9208c072009850210254c55c8a8c42c3d46e84083e15a05a8054081590238000bc0100381032a608600632560892a80a785483c4a20d2512521da1e201e0c00e846a0884484752e853201047a00c41841ae97429028c2341e0e8228250068030700da0e67a1ba0502b06d06b2d06825830d0990991683784aa022288818c8b4908d46c08ac0a11c0de0be768c06d05f1c01b4610983682f969800fc2201988b695417a0f0a1d20560da0bc3a0540120505e05f2d1b41dd06c1ed07409601836b0241e408833116c0400440560021002f400d000607c1b417c84d941b0240dc07c0100e60bc885a24906b06107485b06605fa5827ba13583c030d0290283782f189818101cc0fc1aca0e40e24e00de4d946f41d41b0254084260dc05ac438000100db1a2f02b802a1306606b352b12b032031831016830c2a41e1302885281417c178814f4c00570a846255107850e8a0e045a4e09529b08406f384204741ca1ce0052c32c109d0a10a20902f02fb481084c1798160460e607c17d04940da873049014428056725321a03b03ca05a0403d06d83981f26c05f6429c1ec09102517c1cc0093d40f82fa99801200150e59588c59543491510f02257804c0ac0943c8048724d812e0be9283891a26a28084807a2781f051605c3943961328707e8020d165d0d001da042053e1ce0160005802f037a286a0f60f281684c33894c19a0060e508017d8c940db03f022c280566a05605a0460421341206d83981f05f5117b0d10d01e81d81e129833000932a0f82fb189d87907c0730020600fc2c184c1bc1782118c8607802307207a0775825310400bea08d03903e05108103f02b3c1ec1dc1e502a02902509d07022804400c1ca1002f84abe83683a0ee0f204a0460e50e681581481284c84e0f508300033200417a640a408c260db02307303e0be882c23022fc392050200a702b231823c002130666918117853816e1c902102c16118e00015909c11916ba83683a0f20610e5814a401c829d97432e01c021a0e4c36c9442743c0dac280108642807a21a1e63782060e03d03b03c04b60561301106b04601d43900880205fa84702f601302b2c40921c84b82fa5af812011d0e43288c5a492450ed246046203e0cd046872426056802ba05a0421301106d83981f05f4a1cb02509c09a01521d0f01e04b82fa832431100700900832031e97429829d413d008c else 0x124486d15306281184d08086a0ee0f018604a04417817c85200500a50710724260da0e60bc660461306105e05f839a27a0e03f484341c81582f901dc1e02349280fe89e8381ac1860e55484c54c4e83f830c0942741c1ac18b0225aa5a900280412e0c21a60da42849d52ab072846a37a0d06f83b81f28765d04581102d0a407901d00804b901cb0282f02f910498120e584d0040fc1ace40a0de8040be4a4a24a01d008402c3943921307808d08f05e08905fa5d0798302b020448398359485e8681ac1b417c33c17823e0541c80fd6096c084261020be581208940260521305e05f3d3011852b12b11891781f84490282f836d2ac2a11682f109c01be93812ca6c210254c0700720e60bc402b60424a06102d26045443c03f4c1ec1e035e0250222401fb1382fc16409040a1cc00b81b90089b030c1b417cc108c270040a20be581221306d05f244c40903581580450983ac1e94281f85902fc00c10132be04884c2058501b4b04016416c0960be50a180983c81106b02ba0483b8120b202d05e05f439801438814290dc1ec0921cc01502509c1dc1e03082fb13c0081fbe04884d81417817ca0400381720bc408da4a24a0a7a1308f04b06b07e072097439640130201f02f101ad81017d84e0fc0fc1b689d0482560e5614016a0d60bc48e46214e57c922876a09f80a83b8120b281106b02b05e804a0504b29805f2658014388839157420d1b506c1e60c41c83696351bc08c05062852025954004481e092886a0ee0f031017c8bc0ac94e0e607e005ac94494c08c0ac260be0f005703f023072b05f2ab247a1305e2d1441dc0f847835e0c30282f94384250f408b2e85183f80e825c41780200f817c80e20e40de0dc5310784268708720daa6052980974020c305f312b10d90d015909925030c1e054c2a02f916b01c81bf061814a608c48be0f204417c22429197687a04802200560cc0be30a906102b802604439a1306b441e80fc1c83302f958a989d8850828de8360f60ee04a0440761060f017a0212d012c020af602907d0090e600710060bc0560be422160460505f09505e302280440f81582f9408202a04900a81581484e0041e417d5025002c0a11c0de0be681621a214c1361380ac0240205f4837c0fe0040120880e00402580e840aa8da8341be0f00f81cd814a401e211a8de02a04597417c29201c022501507902401142642746645a50741a12ab60461383907303f06b340092705c82f1211a8da83a02811402100981604425417d60fe4744a616e1644ad07b07702216ccba11e0be5310400970401a0505e05f253012b02f830844831916d2ac2a41e2a84c84c9241781)))
def xml12 : Packing := (270,3,9,0,0,16,0,xmd12)
def xmh12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x2303061040c87050542cea41e4c16f50b9ed15070b0b00d8c525682543493a41bd000018172308a701b0802e40000809f8814f7003fc14bb06b98135c092c00000000341811019b85da47a280000a0b5c8078262298d8594a549a63a07e6002f802d282bd60b6442a6f03a40000301b801950000282b93074000000000248a0446b00000f0bf6c14d0000064b1e028c403d108fb42020094a161b0000100a9a5462129074ba91e92409e15e7c120a00000e7303423d4015a81b990bcad03e40ae141a8437f39cdf5022e805ec4412c67fd089591e3e007e52338034681ce104ad9109e49d641755012e12a2a408d400ac08529e280000000006091011fd000039e1f00002a69097b91c2f8605c350e974a100000707dc44951544aa6f0c029d800750206cc04641ed026c50b69c1a030afc0000ea5a202dc60b41800b2076242e4c0284811e304d8d1d1b01f940fd5002251bb0000281330000028fb80a50c01a2088e511c52756c1d9007b8000000000000000003c031506680000b0a38000000003de46c0b56056ec600a42011466c00009082105fda023a805a4028300bf449218243043a352f3d00ee02e56051ad118a79c1026f04453c08d3025c9993e046f46ef0048d8436b7bd08493400cbd049f01ab66d99080f41791001681483012bcc289217e9091c0a1941310000312350000000002033681ad509ef817db7a17818d0034dc1e8f560c0000d04128298b47a400000000140c2a7aee11574699b01ff0000352e355156c0eab7bb5256a0017f02c860399417a5092ad29de0938c16484a2c004400002408a40b270143815a0010c40b3400007071c000000000c2640086ad06000002c12854594000000000c2aa44b9f806f000000000000000000d062991cab40d85000c0410202004880c0c58612281811420482206000b560c3040c00000044cf0a1878406025c3811a188420a382820014285002c798020140038413220c041810e7400000981140c2020e020000a10c4087301df9a0a000915c080001000480021408e001c00a120d1020800b0b0e04180061c4801008018280800406c0203047c4850c00506041030202002020a508372601c9b0004003080c000002420100082821a010020838187000c0913c00082008c088003c0000408103202822706080933c0949b060000c046000c00000041a08298062800c1820d9e113c005281408600000010a00380280c080001400510713881a00210100100100041800014000004c900062100c0400081062400018000000000701040c180180430202000002a601814000f800804880000038b026c08410002000610181060038b0e6418406185031c501010a1840300041060a1800018185010000588000c019044400300081010230181001c413020c015020000508201000e3c010 else 0x1017480e7609f00000a05b3048c000001258d1462c2d2a058c116c30467014a163a21dff000009223b453c000000001d0936489e958dc01ce1ed8e1a3c0290707fb11cb70755c1bf448b351e569b90000050b8ede56709358070000021199548f8000025453421eb0b87812d000019d8c000000000000018603a0164000080050000000002c1a1509a80000b04560076209cc001200002c10e00002812ac0394827160440000000000000000000000030ad6c2d400000000000000599c794880000b80a602f32084780542497d00580000181dc27b7420e3548b8000000001d2e0000000000a06300000949e841f2f160e004ed4b0d80352431d445500000000000003dc11c01ad1e19f742c00007039001e21789110a8b0723c2b23076fc45ee64eec299302b5126784755803c80aef10f604a080000c071901b2c6a23529f14a8c0000b4b54292a300399136668581190b03ee01b10000046d23094c00002069d817eb0bc0286430614c2ec507698272608d44045f0295d1ba9010c2ed7204981177b798641c400003024830463a087e066702458082a806d000021dd0602480000f025a01d7605991263304680000a00cf901d00001418019382817800002d8e4000009429c0ad2668f8610c000000003c594b058b12607895c0000000000000000000000e5a3ad2660000000000000191df00181110500003824900000c11dd03880000502f9427900000916300001c0cb80482c0f133819413b50aa58144000000000765f5015000002c15dd05a4429b006da50b20000000008062342b600002c1fb3096c0000000000000000000000f0a82817c90bf000000000140fc841a00000904480000a03d001e70000000002721800000000000008064b409a0000301a22095952c800002812938a700000f00640000c0400009b306e8168fd014ad2bd00002d8e30000196b500000000000002924610202118c0033b00bb0937c000000000c0c4744c7822c2099440b67095511abe038c000040bdc00000000000004766bd12e94a0580a4709d20022b0578c156000000000000000000a4b89dcf0000000000d49534d91803640000000020d6430303813a208dcc1fd2068f41062428981c9e7bc6019d37992109d002be1acf5b3eec00d8055451c291ad64153b03b64050703d90020506b2017bd0375424254b08822ab09a3003470a21d1ebc0b05929cd00b3925beb4a85e1aa0700c1d24090180a6078cfc0ffe4366c03e14547d21a4040edeebc143a147d50041028faa43be68a0085e8160503cbc194d073351870000000004633e00b0b6b27a829746d2409047842c22d0000202ea674370101006d2822e30793c228009f5c15806beac1f5a082ed2cd700ea41eb301cb05420000381eca021ce6aa50827aa76244a30224e42e112ced476090d07654b) else (if i<3 then 0x9041d90b1292a0200a4000070a7502f100000c152e02e99c6ff73fe42dd7075880abd089fd835c43e45123b08145261c40caec7524aed400410b1a800000002507d00000000094a869213643e3415f00002c200207a80000f07d0004900003418200001c2a8f4a9a42a26037a828c0078052acb004c8002404d3c2cb00000405c504c980417006cd2aeb0abe107aa0ac6429a861c96e00d072c00000000098fa000038293889aba56c40b4e408400001019640982c600346cd4116a055fa808b02a800003087e02ee00001c01590245c0062020e0147000000000641be8046000009e4bf0af2cca0e07bf4109903e4a2b6605a800ef00002d23fa7936c0e0000029ee70000100110479c000090867401e301ec1221508e3e6eb8356b802e70ba500dfd0813d22a58257c18eb0314d0d4e079ad1bd640dc112d57bc2014ebb24c0000985d80000c6078c41cf044d8261201a3dd638497342ab505000000f098fa63357a41c1f6375b299c5e7aa2129a7362982c3c05311c9ce434ac284c01c64099708d8829590a0b186c6016c00239a637c2a730ae9403fa0a8c8221c0b7f01e9360ce1ce95031ec06c709ad829f04ad6c08cc0a1cd236d0931410817aac804c707b44176e0356d871d4b5a009c342d242e8744fa416db03a284dd27b388173901a4011f1058492f1511902d336035a88d0209640000000000000b49e741d3909ff422b314f34911f423c000080351007900000000010734000000000028d000000000d07e082dbb445a120b000000000803300000000035d9400000d28090775c2b7409d80000a04bc8258c020a81459024c1947908e81a57c0b32410fa019f122540a8400000000342c7103e1129e00001c232a02a3c2cfe060f0db4740ed9d8540155959a50644c127043b401225061910960420c810dd0bb5c1f0200594048d9b5c0251000008074644ac0000506615da9004f740da102cc00007122c12710000051a70000000008054400000000000000000259c351a9e92a70009f408500002810b1063c0000b65e00000746d40e27a0ab4825e9030400001b3058266a08889103602b35d41343cb0130c48a0000000000c210103c010630998400003042a8098990ec000000002813750324013cb08fc0000706f10061b2a1ece8789b0a80ee16396c2fe862a6c213103480000a08ec00003067bc2eba0092002d36697d171d02d7598b06257826d8000e40c6a041410e3a13e7da32505640000504840000062f690a7c01352a03251e600ec7084ac2ca060de807ff027b6460f7a3ec13f802f00247a4a1dc0f340227c59227aa8c25ca42f89276741a90241000770262468b60285e4a66503c10193c27000000000077b080000a25680000d0b464095a0450417170a2fdc94000000000c6bbc510f04769a4f0f34ac59efea1e7415c else 0x246be801c701de52500000080390000292c7979940000626fcc0887a7ee455c00001c1b7275aa50652432a9143c018bd2d3f04b3c030e451c000090b980000509de827a000020257a19240000000000000000000000000000000000000000209b94239000000000466880000000000000000000000a734a829246ad8428130250000020b89c0db402b882be1087101c110640c289f4838de4164b90c1fa9062c90080085b81a9108c55873200325195404e2426930697516bf245fc234b7134c0b10000118f600002423ce0a28000000002c2f6000000000f7702a6c9d070ec1c5619a80000000022169f010bc197c06ac109700001804f50819c1420000281f1002f50e239077810d3f43c0420f6015d40eb21be4825a2717b822fa05d19286406ce65da00002c11c00000000080bbe1a50908cc0000569cc000000003d08dcb7ee80b200003c037e64a50154000002a0040b5a00d000002c1bb4b5cac1d410524c187c649c0000f030e2244501d5d9c2a0854925ec093d8065128071ce0b79b802a594acf41e3c01f18226f45ffc2de740a5c16b063a8017700000000080408987794304e0ea30bd012d0b79c5c0d7f008680dcb091bc07dd08804028308378124072100000f02e068b560bee9164f0691809f96224d2248018d815a0a9ab9836e6b780000706700000409d400000000114870000080e1e03d4000000003803800003012e40941c1fc000000000f48be421df081e92323148642fab06e0000000001916e44395c1cfa0708000000000c26734a4c0000f4934c051748f0000000000000067470000000000c2ac200ac00260000262a9000000000a01e800000000091c100002a87d006d4925724a4801890000302ff44a0f801800001662450328c2a4f6ac090ce00001428020796c2e00000258a500000c0099083911f6c005c0000d000702f50000145120000001f3f033c425f8066d402a00001c29e00000507f90276c1939014d86d77086fc111000000000305b80000248a52563c406a829c5680f5df10000219ec0000212bcf077c41e140a46528ff236d41af545e7c25d50b15428391501c0faf045c9189145a320433028ae44d8021a429661987d24c20597ca233072b82f940ab8621ca44a8000000002403680494e58c000000000f7b120047645d8459a081c4c1aa90b01d28e604e51e3a444238107b41349288306f91dda102dc19ba67bf0020c50861408f30ac16d12a009641d11056e817f03a6126ceb693650ae3898f9144103dcd9e40000382d8904f9c16740acf819ff0a5e81a6d0101de55305a3c0fe88bd))
def xmd11 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0x2a5834837fcd4342982419ff645a914d20dff260d09309067fda828d914827fedc34688241bfe68d1054120dff260d1300907fe93054950482bfed9b30c8a41bfd545a124d20cffb46d4b02905fedb154893483fb6a92a6982415ff6c59850d20eff32a883009077ed522a531483fec9832a98a419ff685a764d20f7ea62c0b009057fdb564d91483efcb82e6a0a419ff6c5a954d20dff26054b02905ff9b864d10482bfed8b30ca2419ff6a19524d20ffcaa498b029067fd916a4834839fecc346c0a417fe6c53026120cff966d4322906ff9306a1914839fecc340c0a419ff6e99814d20cffb6ad1b229057fdb829593482bfed8b30b82419ff6a57161120efba62c99309067fcb568d91483feac0a62982417fe6e1a544120bff366c2a20906fed91688834833fed414ac9a41ff3549314c120affb6252b269057fdb3644984837f6d42a449a41bfe6953026120dfdaa4d4906906f7d5169493483bde5a352a9a41df74c53066120cffb74caa86906efda665493482bfed8b30ba241fdb54d5244120dfdaa2d1106904ffdb868d504827fe5d32ac2241bef655a420d20cffb46b9b309073fd81660534837fcd1a604c241b7f69d9524d20cffb72d29069047fdba655934823fed8b52c02411ff2e5a15d120cdfb6c54aa69057f9b028d984823fedd0a6c8a411ff6d5a920d20efb26051b309047fdba25493483fe4a9260a9a415f72cda4661208ffb6254b069063fda8660534833fccc34029a41beb549a420d20cbfb4ec89269057f5b114d9148337ed332249a41bf9549a120d20ffa302982629065fd9569c9348337ecc34c49a411ff2e5a85d120cdfb22d31069066fda6254934823fe5d262cc2419ef2d1a954d20fed2a6a9220906fe952680834833fadcb4241a419fe655a020d20dfd2a4d1a209047fdb36a19148337edb15298a4197f645a720d208ffb6a54a629047fdb32a581482b7edb15298a411ff2e5a560d208ffb70d48a69067ed916888348337ecab4c49a419ef655a420d208ff974a8b269067ed95688834839fa98b02cc241fdc5459544120cfeb22d0906906eed52698934823fe5d2a6ca2413fb6d5a220d20ff5284aa2e0906ded5269c934823fe5cb4229a41bdb6c9a520d20cbfb30d39269067f5812a5314839fc98302cc24157f6dca366120cff322d0106907de9425c5704837b6d2aa449a419df6959520d20cdfb2ad3106904ff8ba551704833bec8b4a41a4157f6dca94c520dbdaa4d39069047fdb16a4834823fed8952a9a417fa6c8a54c120dedb4aa91069065fd9569c83482b7edb152a9a419df6e5a520d20cfdaa4d4906906eed52698834823feda952c1a419fe4c1a960120cf7b22d21069067f595684834823fe5d262ca241fd85495144120fe92a4982a69046fdb62a531483ed4a12e0ba2411bf6d8a954d20 else (if i<2 then 0x419ff6e1a914d20efdb30a92a09067fda569d934833fed9b50c8a417fe6e1a344120df7b22d21069057fdb869d93482bfed9b50c8a415ff6e0a94c520dff34a983229073fda3605984837fccc346882419ff6a19544120bdfb6c54a62906ff5b5684834833fe5d32ac22419ff64ca960d20affb62d3b26906feda3549504837fcd4260882413ff6c5a914d209ff974caa629077dd312a1934837bed2b2a41a41ff66853054d20fef2a6c2a20906ff99568083482bfedab50c9a41bfb549a844120ffe2a2d1a20907fe5216a531483efcc9ae6b82419ff6a5a060520dfdaa4d09269077ed5266110482ff6d92a241a419ff2a1a564d20ffd2a454a609077f9984c110483feca9b42982419ff655a120d209ffb72d2b069067fda7691984833fed1b50c8a41bfb548a960d20dff350d2a209067fda568593483ff4a9330882415ff6cca864520dff302d00a69067fdb9684534837fcc8b4041a415ff6d5a164d20febaa6a9260907fcd5254d30482bfedd106c8a415ff6c5a960d20affb66cc220907fd9a54c1314833fe51b42cc2415ff6d5a960d20dfba62d1930907bf531661814833fec0b5229a415ff6e0a364520dfeb72d0906906ff9a0660534837fcd094a982415ff6cd9564d20dfeb02d0926905ff9b4661704827fed9b424c2413ff2e99560d20affb6acc3289057fdb84c594483fecd1260a9a41df74c59564d20affb64543269077f8b9685304833fed1b30c8a417fe6cd10541209ffb66d4322907df9845c570482ffcd8950982417fe6d59344120affb72a9b289057fdb52a531482ffcd9a20c0241fee611545c120cffaa2d49069067fdb16a4834833fed2b26c8a41bfd655a120d20dbfb2ad39069067fda869d934837fcd1b4a88241ffa549a84c120affb6ac8926907fd9534c191482f7edb146cc241dfd6055164d20ffb262982a0907fe5212a531483ff4dd2a4882415ff2e98164d20cffb2ad0926907fd93054d814833fecc34249a415ff6c59561120cffb4a51b22906f7db169483482bfeda906c8a415ff2e97366120affb62caa609067fdba654834827fedd326cc2419ff685a954d20dff32ad1a20906ff531684984837fcc2b46882415ff6e85364520bff37052a60906ff9a12a130482dfedab02c0241bfe645a014d20affb70a8b26906efd9569883483bfccc220a8241dfb5499824d20cffb46c99309067fda565493483fec982a6a8241bfb6c9a520d20aff974a8b26907fe952685304837fcd2b42982415ff2e98564d20cff952d0262906f7cb9694834833fea815298a41feb5099550520e7fb26cc3029067fda16a5834837fcd2b4098a41dfe2e5a54c120cffb50d0b269067fd956a1944833fed295298a41ffc5459844120ebf96ed2b26905dfdb728d984833fec9952c0a413ff6e9954c120affb62543269067fd95 else 0x2ac2286906efd9169883483ff45d2a4982419ff6a4a960d20ffd2a4542609057fdb368598483ff4a9346882415ff6c59565120dff350d2a60907fd9302a5314837fcdc34688241ff64c1854c520cffb06d1b229067fda365510483dfc98330c0a41ff654da24c120df7aa2d21069077f99864d104837f6a9352c1a41aff6a19814d20ffb26054aa69077dd954c5304833fed432249a41ffa5493026120affb6a543269077bd9550584482ff6d914ac9a41fdb5455224d20ffd370a9220907df9705cd844837f6a934241a41bdf645a520d20f7daa4c0b009077dcb94c530483bfac095298a41d7f61d935cd20bff370caa209067fda564493482ffcd82a6b8241df74c4a564d20ffd2a4d2a609057fcb9685834837fcd015298a419ff6a59814d20cffb2ad4906907fe95268131483fec98146cc2417f72cda466120eff326cc2e0906ff5a160453483ff4c0aa4982413ff6d5a344120cffb46c89309067fd536a191483bdecaaa8ca241ffa5493044120cffb5029b229067fca8685934833fe52b48cc241cff54d8166120ffb36a982629057fdb228d98483ff8c1aa2882419ff64da864520affb6e543269057fdb528d91482bfedcb06c0a417fe6d5a24c120cffb0054a629057fcb9544834833fecab52c1a413ff6d4a960d20e7f926cc302904ffdb8684934827fedab46c8a41aff605a260120cffb62d4b009057fcb9685534833fe5434ec9a41aff6a18124d20ffd2a4c1a609067fdb56a4834833feda95298a41bfb655a220d20cffb4acaa60906ff591684834833fe42b46c8a41bfe6d5a344120eff330caa609077f5316a5814833fed2b3049a417fe6d4a84c120dbfb4ecc1269067fda15cd984833fe98152c0a419ff2a5a94c520cffb4ad4b069073fd8128d98483feca9b06882415ff6e55361120cffb68d4aa6905ff9b954d70483ff8c0b4098a41cff6053066120dff26054b069057fdb366170482bfed9b52c0a419ff544a960d20affb66caa20905ff9b22a1304836fec0b4e49a417fe6c4a54c1209ffb6ad4906905ff9b868530482bfedc0a6c8a41ffa5491060120bff36051b30905ff9b8545704833fedcb5029a415ff6e1a164d20efba6054aa6906feda554893482bfe5cb46c0a413ff6c5a920d20ffd2a4cc260907fd931295304827fed9952c0a419ff6a58761120eff330caa20905ff9b229530482bfe5d262cc2413ff6e99814d20dfeb42c88a69077f8b96a130482bfed8b2aa1a41ffa6e9524c120bff362d1260905ff9b82a530482bfedc32a49a419ff68ca864520ffd306a9220907bf9814c180483feca995298241ff6601314c120cffb3054b069077f930661914833fed4306c9a415ff6c4a366120ffb26298130906ff9a82a530483fecc9b4098a417fe6c5935c120ef7b2aa0b289067fd8568d914837fcd4346882)) else (if i<4 then 0x1483bfedd306c8a41dff6058364d20ffdaa4c9b029077fd954c530482ffedc2a688241dff54d9564d20dffb42c2b06905ffdb52a193483dfea9b02c0241ffb549a960d20effb2ad0b06905ffdb3661814837fed432229a41dff60d9864520effb02ca926907ff9812a5304837fe5cb4ac1a41ffe4c19860520dffb46cc302907fdd536a583483ffca9b5088241bff545a326120fff30ad2a60905ffdb520d91483ffca8340c0a41ffd4c59860520bffb7052b269077fd83655934837fea9b46c8a41ffe6e58544120ffbaa6b9a829077fd8129593483ffca9a20c0241ffb549a060520effb0ad0b269077fd5364d91483bfecab52c1a417ff6e13154120bffb72d2b069077fd916a583483ffcd82a688241dff6617161120ffdb02a9260907fed522a5834837fed2b42c1a41dff544a366120effaa254326906ffd536a191483ffcc0b44982417ff6c59561120effb0ad2b26907fed5268d81483ff6a9326c1a417ff6d58154120dffb02d1aa0906ffd8568d91483ffcc0b5098241ffe5c19861120fff30ac9a20906ffda961583482ffeda95298a41bff6959326120dffb4acc126907fed2169583483bfec0b2a98241ff74c1a154d20fff2a298130907ff99560d30483ff6a9150c9a41ffe441a954d20effaa2d4b069077fd8169593483bfe98352c0a417ff6d5814c120f7faa6cc302906ffdb16a053483ffcca95098241ffd6053154120ffea62c0b00906ffda068553482ffed8952a9a41bff6a19524d20bffb6acc308907fed31549504837fe5434ac9a419ff645a560d20cffb4054aa69067fda12a553482bfedaa62cc2415ff6d5a364520ffd330a12e09067fda564c98483ff4a9260c8a415ff6d59326120cffb26d09309067fda166053482bfed8952a9a413ff6c5a260120cffb4ad4326907f6d5254483483fbca9aa8b82419ff614a94c520cffb30d1a209067fd816a5534837fca8b4041a415ff6e19544120febaa6aa2e6906f7db9694834833fed0b48cc241ddf5459524d20bff370d12609067fda568d914836fea8b4e49a41b7f545a720d20bff362cc2e0907fd9306a55348377ed333049a417bf6d8a954d209ffb6ad09269067fd812a553482ffcd9b4a882417fe6cd985c120bfbb6a98a60904ffdba60453482ffcd9a82b82419ff6a0a94c520affb72d2a60906efd5169893483ff4a934498241fee5c14161120cffb46d0b30906fedb568883483ff4d9aa488241bfb549a344120ffd2a4c9a209067fdb16a453483fec9835298a41b7f645a720d20affb6452b26905fedb154930482bfe5cb4a98a41ffa549a8441209ffb6ad42209067fd802a5534833fe5d32aa0a41feb6554250d20e7fb30c3b089067fda129593483ff8a8b26882417fe6e1a54c120dfdb74a91069067fda92a553482bfedc32249a41ff654d3044120ef7b else (if i<5 then 0x4f704b1045e040b03b80365031f02bf0286023301c60173012d00da00600000f7fb0ecc3089077fd8165593483bfe4c32ac9a41dff645a954d20effb06c9b22905ffdb54c580483bfecc34a98a41ffe6e98544120fff37498302905ffdb360580483bfe5cb42a9a417ff6c5a954d20fff2a4d0a60905ffdb268153483ffca9a60c8a41ffe54d9844120fff30098a60906ffdb969583483bfec8952a9a41bff605a914d20fff370a9a20907fedb8549104837fed4b4ac1a41ffe615a84c120bffb64a9a60906ffdb96a053483ffcdd30688241ffe4c15360520effb2acc308907fed5266183483bfec0b50c9a41f7f61d7350520dffb4ac0926907ff5814c530483bfea9b50c8a41ffe6e58344120effb06d1b22907ff99860d30483bfecaaa6ca241ff754ca960d20effaa6cc220907ff9854c191483bfea9150c9a41bff6e5a520d20effaa0d4b029077fd98549304837fed8b4a41a41ffb6cd5244120ffdaa4d02629077fdb954d94483bfecab40c0a41ffe6e9854c120fff302982a0906ffda854493482ffed8aa6a8241dff6159364520ffdb02a92a0906ffdb16a093482ffedab02c0241ffe64d535c120ffeb02caa62907ff9b954d70483bfecc326c1a41ffe4c1a360520effb0ad4326906ffda860493483ff6a9342c1a417ff6dd9861120dffb74a9a20907ff98129530483bfec8b0ac1a41dff6e98564d20effaa6d1b22907ff98568131483ff6a9302c0241fef6558450d20effb06d4322905ffdb1661844837fed4b42c1a41ffe541a04c520fff302d2a609077fd952a193483ffc8834ac1a41ffe4c1a960520effb72a9b02907fed5254d30482ffedc262c2241bff685a954d20fff300a9260907ff9522a130483bfec9b46c0a417ff6d4a960d20effb2acc3069077fd93661814837fec1b50c8a41dff655a360520dffb42a92609077fd954c584483bfec2b46c8a41bff6a1954c520bffb6ab8b08907dfd8764d73483fde5a352a9a41dff5459824d20fff30698322905ffdb968583483efec3ae6c22417ff6d4a366120f7fb06cc3029077fdb954d10483fdec232aa0a41ffe440a954d20dffaa6d42209077fd95605804837fec8b4ac1a41ffe60da544120ffdaa4c9930905ffdb954d844837fed433049a41dff655a04c520fff2a2c1a60907ff9526a130483bfea9b30c8a41ffb5498124d20fff2a4d2a609077fd9560d81483ff6a9306c0a41dff2e19550520fff300d0262907ff98365510483bfedd302c9a417ff6c95361120bffb70c9b069077fd936a581483fdec3a82c2241bff694a960d20fff30ad0a60907ff93060980483bfea8b264c241ffe615a344120dffb06d1b22907bfd9861583483feed92a698241ffe6c1535c120effb0452b26907fdd535cd84483ffc98340c0a41ffe605834c120effb22d2b069077fd986813 else 0x8fbf8f5f8f198ee08e9a8e618e018dd58d8f8d638d108cb08c778be38b9d8b648aea8ab18a858a4c8a2089da89878941890888dc88b08850880a87d18798875f873386e0869a8654861b85c88582852284e984b08477843183de83bf839383748348830f82c98290824a820481cb8185813f810680cd80a1805b7fc77f817f217edb7ebc7e427dfc7d9c7d707d107cbd7c777c4b7c057ba57b797b267ad37a9a7a2d7a0179d5799c792f78dc7889785077d677907764772b76f2769f7659763a75f475a1755b752274e974897450742473de73b27379734072fa72c172957269723071f77170712a70d7709170586feb6fb26f796f336eed6ea76e7b6e1b6dd56d9c6d3c6cf66cbd6c366bf06baa6b576b116abe6a856a596a2d69996960691a68a06867682167e867bc67906757671e66d8669f665965ec65c06587652764d46481643b63f563bc6390634a631e62e562ac6266622d620161bb618f613c60e960b0606a60315feb5fb25f5f5f335efa5ea75e6e5e285e095da95d635d1d5cca5c9e5c7f5c395c0d5be15bb55b555b1c5ae35a9d5a645a2b59d85978593f58df58995853582757e157b5577c574356fd56b7564a560455d855ac5580553a550154e254a95470541d53e4539e5372531252e652a05267522e51f551c951835164512b50f250b95066502d4fe74fae4f5b4f084edc4e894e504e0a4db74d8b4d524d264cd34c734c134bda4bae4b684b154ae94aa34a5d4a0a49aa498b495f49264878483f482047f447bb478f4749471046ca46ab463e45eb45cc45864540451444db44a2445c443043ea43a4435e432542f942c04287424e422241a84155410f40c9404f40093fd03f7d3f5e3f183edf3eb33e6d3e343de13d9b3d623d293ca23c5c3c233bf73bbe3b783ae43a913a3139f8398b3952392638d338a7386e382837ef37b63756373736ca36843658362c35a5356c353334fa34ce34a234693430340433b1336b332532df32a6324631e631a0315a312e30f530af304f2ffc2fd02fa42f6b2f182ed22e8c2e462e002dc72d812d482d022cbc2c762c4a2c042bcb2b922b4c2aab2a722a392a0d29d4299b2962290228bc2890284a281127cb277826f126c5268c2660262725ee25b52596255d250a24b72464243823ff23e023a72354232822ef22c3228a225e21bd2150211720d1208b204520191fed1fb41f3a1ecd1e941e681e2f1de91db01d841d581d1f1cd91c6c1c261bed1b801b2d1af41aae1a6819fb19741948190f18d61883184a17f717cb1778171816b81665161f15e61593152614c61473142013e713ae133412d41274124811db1161110110bb1075103c0fdc0f890f290ed60e760e160ddd0d630d100ca30c430bc90b690aef0a9c0a4909dc0989095008d60869081607c30749071006bd0677063e05b70557))) else (if i<9 then (if i<7 then 0xdd028e0f014e02b280ad4d206f042017ca05e06c80fc10c4c1648c40bc43985481980f2790d306011e05e90a01e4c0f206d80200db439a1e81a8f21a60c023c0bd21403c9840a05e43790e58700610359c0bc06b41ea0e40cd42002f9c0bc0d901f82189231917819b058823854c84c19805e481c801165d06400f814e6023c868003214555c84c18a05e4183b80008100e817c01004b3821245e02be1cba0305805e9098075209e00e80201bb25890980ace247023c86980281590a484c18a05e4f0000c2c3904201bc0bc6838a0e41bb83807681acc08ee0138350df43903081780be8030f0e78000840378178c04702f80fc10c491500f80e683c00e50e500205e00ea545e08f015e0b2046a1306281790a1aa0c023c0bca1403c9a434418047817a4280793039e079011b09f0000be01d035812d205e06c80fc10c4050827707207303f0270d21a069c85242601d280100be03f043100fc07206980740100c8036b0e414e02b501bb48606f03699600bc0083891d434a14155a84c18a05e381f58300d390a01e4bee0063832014c0df0539a434c18047817a4280793486a428aab90983140bc690d48515572130628178c04b00e829c0cc02d2d0e249520502f82c00bc068381781b203f04312434048047817a428079301cb41c064c1d8022c4203e04f200fba2fd0d40e607a81f36929d01c3971438dca0e406fe84e0e383806e9808ca0e0378938023a9bd2780740109866c28e16c0c885201441ba7c04fbffcbfddbfb1bf85bf32bef9bedabea1be68be2fbdf6bdbdbd84bd4bbd1fbcccbcbabc9bbc62bc50bc0abbdebb98bb6cbb4dbb2ebaf5baafba69ba23b9ddb997b951b925b906b8dab8bbb875b863b82ab80bb7d2b7b3b77ab727b6fbb6c2b689b643b60ab5deb58bb552b519b4edb4c1b495b45cb430b411b3e5b3c6b38db354b328b309b2ddb2a4b26bb232b206b1dab1aeb175b149b11db0f1b0c5b08cb039b000afeeafb5af6faf43af17aed1ae8bae5fae26ae14addbada2ad76ad3dacf7acbeac92ac66ac2dac01abd5ab8fab63ab37aafeaac5aa99aa60aa1aaa08a9cfa996a977a94ba92ca8f3a8e1a8b5a889a843a80aa7b7a78ba75fa733a6faa6a7a66ea635a5fca5eaa5b1a55ea53fa4f9a4cda4aea475a449a410a3d7a3aba372a32ca2e6a2baa29ba262a243a217a1d1a1a5a179a14da114a0e8a0a2a083a057a02ba00c9fe09f9a9f549f4f9f169ef79ed89eac9e739e479e289def9ddd9db19d6b9d329d139ccd9ca19c689c2f9bf69bca9b9e9b659b399b0d9ae19a9b9a559a439a0a99c499a5995f992698ed98c19888984f981697d097a49751973296f996cd96a196759649963795e495ab958c9560953494fb94c2946f942993f093aa937e9352931992e092a792959269923d920491d8915e910b90d2903e8ff8 else (if i<8 then 0x7c9439909838812e05f2a938010204302c84c0be05e3823dc0a0df03f02740d6602f42180be3c09025c0be3030807445a05e20235803039040c0fc0da6044881409605e02f9483a02d302b0e40da5028e9570780880331680443990982180be5909884c0da05f24928056e1e90a01b4a83902f81780c24c0f80e403806b02f960402e100082cc0be5902b04c42605e02f9553004b0470e40b83902281780be580f819a42606b220e405a06b030900cc401d09c0080bc583941bc11205e02fc8bf078e80047c84dc510c36012c05b06f0309207b039024017c809503f0178661eb0281780be4043022403805f230e30258010359003fa05302e0e408a05e02f9d08c40220e802012a503c81781123046c0e607e051036940bd839022817c980190281140bc05f2a8c780143904202200f2604781840bd20571b81ad80921321c40e5403f036817c604881c81ac0c24015825c0e63c1c817c0bc0612207e07201c02f91031039a010184805e02f8b02208672c02248089e1c81bf8000ca03f9a108414c0100700d605f301a80c200840982380bc603580ac0e63c0fe0440da05f250e00e62c0f81781b405f201b4d212be34382540d6601581b40bc302f284c16005f201af00208e1e04987206d04710c2606d0358d45e0a7e1cda00108a31030d0060460cc02f284d8a1b52501b7048a148050178112800448140be05e248bc0cc20490981aca04be0170e40be08f281ae82206d037817ca0790628178601c0330178640406c41bc12a403c60f003aa2f047817b07301fc00a64340cf04781b40bcaab01f81c9182005380700be410208b40cc300e025448e05e201be80404b02f0224a06a02f81780c2430981b4112300e01980bc360c007048e08f2700009008f02f81e4b80100230e405a05fa0101ac0c2803780765160080289407c05105380ac9c00053f00b8720b002f01bc0be830249ec1b204702f8218c02b90a017c0f24d0282c00bc06802f941ba658509829c056553e3a000f081d71b823d4b005f458dec1dc00053817f805c3905801780deac2a00b4056302f81a00ce061201840d006702f92435214555c84c18a05e301f687202b043104f602d03583640be086300ac1520861c86a428aab90983140bc6109a0fd07383870701ac112703eb815872084e0001980f27c11b9601600a90378178c0dd00e80201ac02b281781b203f043101ba008b2c284c14e02b3027c14001d036e81687343804ea34bae0e047f0e755005f03c9c0fae4a80fe0e54d805e3486a40aaab909823c0be602f036407e0862306242805f03c910fa81f001686b072a8a936017c0bc9030e07f02204bc1c825c0be705a81790728a9c1c0274056703e80fc10c303b807405b838838e0e41a608f401d744ee1300e80200ee01c040812120e406f81b707009d06e8270e else 0x449142624700e0178808d04781ad87208e04498c952be3485244801c90288140bc05f2e04811e01c02f9307a01d909a14c1e208e300f407e06b40083c00be620881b40bc3801017803901d0408254c81881cb0080c2400fb00687206604a9410983d902812c0bc08e3100418a05e1d0e41ac08f044924270080470d030008502c84e03805f36835003402302084c11c0893807243408f902812012a05e3822409605e02f90c9c05e02f8d02303930281780be5046c816426e8001f0198d01f03e817c743903f821812e05f2e0e607225302f0238a02b309992b03e614036980c205f036817a4b121353d9c0da06b100ac0da05f1e04803809702f9292208fa0fe0f00d605e02f8227022e5dc00d00811ad302023c09608e201b40be207702580c23c1c812c0c605f2017c0d6089182a687205f02f0184a04800e02200c2490d884c07e06d035940d605e101840bc048036817e4b121353da0c62605c1c825810c02b301b40bc2116a84c42605e02f96cb005e066c0040be504481fc0be303090e642606b260080bc01c0471010c02b90281b40d6510208b40cc3c00c81403805f02f1407c439025c0200e6504790040bec0204494870839b0a0254802d03681787439d0681b40be450988140bc05f2022403a08602f9008a06b02f8e45481101581b507880102f50e603a932510e40e5a1e30a01b4c03f000e0e416605f28224c0a07900e017ca0d3202828011e06b03f027813a09c4900840a613043017ca011c014074102490d01a80e5205c0a817cc06d02f8a022a0504780700be5909807048e05e200701a605e1d008c0b21300e017ca08940f82180be4044c0f083a6049758238c01cd0981f40cc05e281e00bc09702f900f00611168178808f04481840bee27035981487343d067ab00805e808825c0be501c00e40e605e2007c0cc0951e04810243f03692873039074819812a503c0234010401209b87a49405f706825f072b702017c15206121c8254c008201017b07802d61c8314e81fb0981980bc490d01b419e05e047e0540e403f4017b07208606c901080950580f003a0520281ac03805f301e418a05e1a81442605e02f9187344e20c023c1125044807410c05f2481405606d035914a606d55f32440d669002f1c0da05f101bb41a4a902f81b40de6580042045e09760102240da500081ac0be301581b40be3047822603a41d030817a87a6be0678205521300e091c0bc481ec0e416e05f2181010806102f10c2606d0448c0380660478f04083b025817c921a90982c811e4a1e82040be320e900ac0b26c02f8238d40270290e410c05f2d0eed2408106501b4a83840c484c0da06b282a40102e5036900c8c3b015839003aa980331d08ca36022900ac0a05f04a9d80203f02f40e40be541e29801c6097030960700970398c112c0200e01)) else (if i<11 then (if i<10 then 0x7c07e06d3029f07205fc0f8184b00802583300be481e819903b03fd02c9b00bc08e4018405a05e02f9012f213036822480a7004017816005f2d0e416005e02f8184a83841c884c11c0892829c83805e180ac0d665613020f18a805f3a04607203f02f017cbc3906b107412e40158184c08631c1c984c0cc7201498207e04503094c0b21300e017c80dd028823c0c2c3b033040c108102015a82020dd004033c0da5502aa1c09605e02f9446224a102695407c066302a58050390358184a02b030817c07f2130359840a01c035817c803f035817c6c3902f018460dfd2500740c20080478224198081a1c82356100909820411240308816872a130359645e41d030c0040bce8002f9a1e426900e091c0be05e260e016b83904e8198b21312380700bc404781e40be310981b40bc303700b412e05f2607d07e08602f91427402302c84c0be5a02281405a06b218100cc05e0420184a61b0396878c9406d02f18500108b0200f80bc384203fc1600952406180208d801020609006d3a0e00d683990981b40bc652b43f81d806304b8184c0a961c817c0bc0612c980cac6a881e5150a06d06b4020112404481e40bc3c0118140bc01c0471445f0380398e802818837817c808d04088b40da4037e0081fa01c02f9707202d0358184807305381ac6048c1c812c1f805f2802011209518184056e0461cc84c0d66038e83487205f0370238c002123817c0bc4d06c0bc87201c02f940bf27b0430364903d02f01f607208e2e814c2605e02f9207b80221c984e03a06b301a845a0611e048d7009702f900d74020468321c860fb31811426066047924c041302403b40d65036817c48014015814c0921302f8254e06eb2c40040da05f2884c11a05101f81b4a81840450090260fa0581907203f02f8c83a0951021012a06102f8178a22d02f017c6213036817c6402016817c68a900e60f00100f80168254ee0537b817c12a4909884c0da05f2484e80402d00e017ca01c04201840bc4c0fa0440da089201780be06653029b0d0e64243062003c0241cd04c0be7118884c11a05f20286870c0502f204412e05f382200cc05101588b4a05e309c81542605f2836c45a0611829c0c205f61c8254ba1b0358224740203180700be481c01ad07205f26008c0a05e00e0238a24e702c0e40be0952823c0c269055f32440da0e502fa203f00141c82180be511681780be304782c811c304481fc0be3408e0e507205e0309703e00106d017c806d02f0b02407f04b817c960502281780be4050901414183804e83d8d01f50280700be4600817a8724390309600405e02f8f07b00841ca84c1ea0f402f9d07206b02f0e43403f04781c80d6506b70000cc0c52023410222d0369302421304b817c804b0478238701f800a0e403805f281b40be2015807419805e2025f024c390 else 0xc0e60a70359221620505381bc11e061a1c822687006b02fac11260532701780be5037817c0960952281287382450a02268240ca3a81340b21302f8254a439327023c1124016c0e704903f0369413a06102f8254841120f823418e0c861c829ce03f02f017c6c0250981fc12e05f2e86818a05e1c0f202200800e00741026047837587601d03084281407909821821205f22928090e2770702c011e08902f80b412ac395c8680e5205c0a817cb83904302d40be472e81be822089c0f884c01001d040a642601c12381788c3902f82c07020d0980ac0d6490980700be3808b81411e08602f9410802b03ec84c0cc06b304040fa03f909834cb80202f036811c4384025c0be3b0200f80bc303081ad4bb0a385201e011a703e80ae426066035958720dd03081ac981f01f82180be4c01017803808e200040be073180ac0c2039502284c0d66b21014700400804a9607083906e83b40d65c00807012e05f248bc15202b90981980d66302581642605f04a9648404691bb0818054390409d80343902f017c981605900700bc401583c107e095248bc03b03fc008238a25381fc00607205e047180da05f1084c12e05f181b40bc2c0901b40bc303320ff00208e2037480809d03681aca05e03ec0e411c4c0f80e403806b02f941bac0204200ac0c2507301980be0952483403822d8040254a484437c9380380612823942606d02f9007a05e17a817c909800e017c7015023812c18a05e2c07601006160101e34ba106036a84c0d608d582a603e4390358184a07881de07c112253c01017cf03d03083b40f3008281b40bc223f5a02c50872b1ba1bc0be4f4461a4111854033018c45a5839017ac95614909b8a2186735c01780be343ee86a07e07d936017811c7c00e814c0a01c02f8178d402601181642605f2c0e40d60951e8db03e839043017ca06d02fcafa92206b21d8178e10504b02246089502a84c10c0f402f9a07ec02c1cc0e40bc05f3181042609702f9243406d067817811f81503900fd083901f817c683c0258178605e10988b40be403081ac0bee1e72181e1c1a08d4316302206d04bc0e40be6502a8c687209604300acda4a412402b42840801074c0805e06782278018120652408a80561050e6010506181b40be3d17c00812a06b212441e084504a91022402909e0e483a0813300411f21390d0178a06d02f0b07a83a04740e40be5050c0e487006b03681ccd038030837413a06b2a07420801c04b900bd839059817c806150218114634395098198e07921f807011c404730e40da3044900a427614047140900fd0768c05703902f01cc8a1310281780be400e481440a05f02f15070038c1c82549a0502f017c7a0502f8178680202f007011c4934a81142606b210740c2808800c0080bee277070255872ac0f881403806b02f954266135255) else (if i<12 then 0x46a13031817c6420208817c0da484c022680521321f817cd812509817c12e40448607206b309817c807892531380ee0892981253004b188b40da0611d0080bd213046817cb402c09a00483a05e2c02012e05e18226072048039914ac1909817c45a0b02300607e03f02f9045a02b02f8e4c103903201ac806d02fd008056095281b40bc0978041087606d02f8c0d606602f8c83a08e0368314880202f0070601c02f017c60a903301ac10805e2984c0be22d181ac0be22d180b480406100e100f002b02f017c805f01f80ac607840c012c112442328d808b40202f95872103c03e40c205f202c011e04802f900da05f1315012c05f183140da2201022445a05f21814321303681ac701302f8224703c044b00812a41d2817a07206102f9215202b40150e40d605e3025c12a41d1c9800c80b01c92a4c0061183580cc08f40412070411035c84c0be06d321500cc05f079900c2a1304490fc822d02582240bc41168607205f01f81cc9046837b07e01103906b1811006d112450760940368224a61340083486073036889220ef036817c8213036817c625611889280be4047e0040be04b2023c09701d181840da05e02f9058c60406290740105a0140e4c2605f039944260610448c14e0611484c0be06d035900c60e3110fc1da0891904a80260481f817cb801036825c7839036817c7402102284c60b512381ac0c24c0901b40be3a0c018607206b02f940c20ec148500c80971c0fcc27839181b40be201f80ac0be3454c08087e06b02f140d6c3990981b40be503008c2605f81f9005605f1017c1d8281c81dc0be390d01b40be06b2029c112094181b40bc207518100d605f200fc3812036817c6a05509817c45a0972817842606d02f901080e81034e83e09520e8020a061067817c703b81c81dc0be430240e40d605f230ec87606d02f900da61302f8e42622d04b8e871804033017c808802f8070721303088b4780241c8218648420e81781cc0612e0f7003404404017ca83c0c98007e061035901080a903081780be506281b44078015817a07205f2822487f21302f908040c5116817c80ca02f81fc7260030c0e40d64902817e4260082281100802b02f9304087501f81cc0be502581b40be3044c0f0873213016817cca4e0258807606d02f83788063025817c66040158178603e036817c602b3020178683c0e0f501180106e11200be604782340d605f201ac0562909825c45a3c09484c0da302f30e48720862036c0bf0130309302540261cc84c87e089300fc0d605f0168184b81203981b40be402f60e607206b02f9445a0640308e0112130408e87181200460109812309818600a404681cc11e05f230e4201c033017c60c52016004608f80201980be4702a84c1ae304781b54c1290053b07c0be061035a40d6a13d2e82341900fb3037 else 0xa4e0e00680521341f90fc0be6066025c407804330e4606d309817c7438059023c05606b02f9813a08902f01ac803f075098046eb02f81cc920580280ac0be406f823e872089201ac0bc01c02f9011206d6010254808d02f017c038402f184c0be078260e607205e181c502205e4008020112656a040d6c391297007206d02f930041248823f00205f0331507806302f8d076089016817c1285036817c0383116817c40860718842703f0308224822d601017c0960612c9280c321312b017ca08921f8186426c392834c83e41d883c020aa04033018687206b2c1c60de21304481cca06181c817c603c06908c2606d02f8c0be22d100f803900802fc84caa050831203006102f900be0b5140b40da05e04b905ca05e100fc08e06b02f900be06f20250090260953486819e08f1823f00205f0331007006b02fd004807800e40200bf2132c0e40be048035900760890538e04103d41fe00a42605f328bc05605f0359300408f015817c8690036817c608f059017c6c390158184602b90282c80be402f007203a30358178408f00e4074605f1168811206181c81ac80ca03081fc0be4a1c8184056390a018440513026004608f03580701124707400702605f2484e4940a70309019406103f8cc2606d02f8c92206b02f0d40808f030817c920d00e484c603f015817c606b21ce))))
def xml11 : Packing := (768,4,9,0,0,16,0,xmd11)
def xmh11 (i : Nat) : Nat := (if i<1 then 0xeef048c83850101831ff9623839c0000e0fa00000000380f7d498f633203e400018c7914494ba63823800008018ac05a583aa055641400c2f81df20962057383abc0654cf6a452b80880000a137448f7028ec07a00a9b4079035b4251c8ded23270053c05e40290000283900000ef2c2096e002a8235ccdd00007037d584c810600004a3180001044fe21780001a6779298207f902dac177448ad0003016b420a0936000068194dd784847b44e8810699d3e0786036c02ff00a1a473322428313424644540000101d80000c09a000040327c8f520742007e02788169c079d0614804f847c7439b070400d000000000607b8000000000000825f80000909773380000000011d8960bc500b223bb8282008a00000b3ce80080000375880003246048360000700640000000000000000000008117f02e00368000060ba900860210000000000000522e619c4404e0000083700000c033218b1246c8252c0c3506a8000200d260aa70685a3c480c80136904ca84f1c025a0ca00967a46041fbe8302095923531dbe667c9215000000574093b8069f91a00001e0ab0000000004277e0a772258000000000000b69a784c6802a0000908e8000000012474669d22b1f410a0000c097d0436010de075000000002404b211bf022d214c0001a6688662800031ca606ad0000000020103f255d035fc94f40128f211038c84ff4137a04b700fb236ac1e60133f7417822c000181120000000038c9e0000a017603b40000000000000000081b1004df746201f8c1e08929c13a0000000b6803cf0309b2d8d9060073a434581660037865dc04fb83306230e0e9e08c000020159c04200002849810c8acb7e08658bdf824e0000f099692ce80e4c03b000058248257380f1449c00002805bc0e230643a1fac03800c1a031480dc0000000000007013212080000046c201780001408c402c284566606a0a1a0693894a909380de508a0838d8212000004028000245e3e231a058f02e700d8ec1ac01b4124c00000000a065800000000e3010000583d45c6ca26100003a439d14d60b3000000003c0bec11ea98b00001c0e0ceea80158000291b8000000006b447408f812a9037a809a02744102b01080000419d76980000591c040710110181c8848940dcee94e0581804402018c56906db0491420200f86469bd19e401a810a000000003812800009483203ed4061a02300000b43682320000131a8000300020139f431a82a3411fa07f1840181d800110c1420002067410013960b3042184c4412105800b1c231909d38524416d05300040c00a0c721500508228121600d4d50410070060c00c63020630801090000001400ce1820000012594c00c62403c304714a2822d218000d1110020b014020208000030214d09d04200b24102228600100300a08120111100a004048 else 0x2fa406680001c20fa03a00003a4ae81a28eb9989d4814b4d666e2bf62808033c093e020504e091fdd9f2a07d804ec0500000ce03e600ef3c7e0268000060318000391a0b20f00004814f902aa25cc987000001168c138b07e1dc5800cc00e8742c3831d01b200001021d31574c9680b56101004fbc23fe0c5b048188dcc094605df015282554144a46d0000484840001d005907a0000148374d186033b91740000e02770590000081a8000000004a4200000c2c700001230c0000e8e00000413cb41d840b7000000002c20600000000000011dfe0000e785f833c420860892087b233e8091eefce96feb83c007e80a5802a0000381eda8db000c6b11b8007608d420c58283da004082c044782930126cd174a2859a78c06b60d7d00580093c004002c579da03c8001c045e804c0821c822328c700005b29881fc407c96168000281800057a05c23c26d8ae0000d963e82f9008dac08f075e0015402e485d206ec20c4000000009084000000000033b205680002417be410d0875020d8011260e24768a3cdd15b672900973842d015e8c5f301450146c40dc0073073701e980d5cec6609ec3ce0426ba116845ebca31012f0c02e03b8342802414e30b02b333aed1318258c00f0029b68d4ec58c089e00e7d10f406000002a0800000008e8092f0112d839252960633006b009fc040503478396c260c0)
def xmd10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xef6951549a020d20ded9b64c0a954d20af6dc16c9a520d20f77151661954412087fcca6e15164d20a7edc1549a920d20c6fdb86d8a94c520e775b5655a120d20cf6d526d5a124d20c7f5812e5a114d209fd9c36c4a54c120b3f5c154d8166120cf6db16955220d20d3f5816c4a366120d5dd306dca94c520c7f9a02e55120d20c6fdb66a4a954d2087fdcb615a3645208fedc16d5a220d20c6fdb56d8a94c520c77db16e5a520d20a7dcca4c53066120e3f5a16059814d20a7bdc5645a420d20d7d9302e93166120fbd1314c19860520e67d51655a624d20ff61525459344120c6fda06d8a954d20cef9b6680a94c520a3fcca54d8166120cf78ba54d545c120f3d53164d9860520e77951655a020d20a7f9c5645a020d20f3d9814c0a366120a77dcb645a520d20afe5cb549a120d20adedc2545a724d2087fdcb68da9605208ff8cb661a344120e76d52694a94c520df4d526d5314c120c7bda42e55120d20ff4953549a84c120d7d9b14c0a36612087fdc16d4a960d2087fccb661a344120ff6151549984412087fdc86c4a954d20d5f5816dca94c52087fdc82e5a114d20a7edc5645a220d20a6fdc6295a466120e3f998605a014d20e57d51655a720d20a7edc2295a466120e6ed526d8a94c520b7d8c9695304c520c7f5816d4a94c52093fccb661a360520c7f5812e95164d20e3f581600a94c520a3fdc16a19814d20a7f5c56e5a120d20d3f9816c0a366120c7f5516c4a960d20d3f5b8604a94c520aeedc1549a624d20a77cc96c5a520d20f3d5316053066120e6eda65499824d20a7f9c028da166120c7bcb46c5a954d20ff615160d524412087fdc82e93165120c5fda06dca94c520e1fd81661a724d20e3f9814c1a960120ff4953548a94c120e67d51655a620d20c5fda16dca366120e76d526d4a94c520d6dd306d8a94c520ff4953549984c120e76d51549a920d20e57d51655a724d20b7d8c96853054d20cf6d516d5a220d20ded9b64c0a94c520e76da55499824d20c5fda76e19124d20ff495254d8344120efd1a14c53026120c77d516d4a960d20d6dd306d8a954d20d7e4b95493160520b3f5c124d9860520dfd1316c4a84c120a6fdc62a5a94c520aeedc1549a620d20dee5b6484a94c520af6dc2545a524d20ff6152545a344120e7d5a14c59326120fbd181601314c120c7dcb369da466120a7f4c96d5a120d20ef6552545a124d20ee6d51549a624d2087fdcb614a94c520ee6d51549a620d20ff4953549a54c12087fdc56c5a920d20d1fd816dca366120cfb8ba611545c1208ff9c12e9545c12087fdc82e95164d20c6fdb56999124d20c77db5614a94c520cfe9b2684a54c120c7dcb3685a466120ffc1216d5304c52083fdc82e5a114d20c4fdb76d8a94c520f3d1314c18166120cfa8ba509545c1208deccb549a724d20 else 0xd6fdb6644a954d2097fccb661a54c520d7bd436c595611209ff8cb54da844120efe9524c1a126120d7f5b1544a366120ffd1314c19860520e3fd956a18124d20ff695354910601209ff4cb4c59860520e7f5816d4a94c520ebed526a18124d20ffc9524c53026120c7fcca6d53166120ff5953601524c120d7ecb9549a160d20dfe9816c8a54c120cff9b54c0a960520c7fd956cda126120cfedb16a15224d20c7fdb8540a94c520ff4d5254da960d20ffe152605a04c520d7dd306e0a94c520dfe9526d4a84c120c7fda06d4a94c520c7fcb9695a160d20c7fdb92e5a560d20e5fd81655a724d20f7e552604a94c520c7fdb8684a564d20a7fcca544a366120ff4d535499360d20c7fda56cca864520e7ed526a0a94c520efe95268d3026120e5fd876a57161120e7dda54c59326120c7fdb56a19124d20efd9a54c53026120d7f5b1544a864d208ffdc82e9954c520c7fda16d59326120c7fd526cca960520c7fda56cd9126120e7f551661a124d20eded81549a724d20cff9a56c53026120e7dd954c5a326120a7fdc32e995611209ff9c16e0a54c120f7ccb9549314c120c7fdb56a0a94c520efe952684a84c120d77db5544a864d20cfed526e1a124d20ef6d53549a844120dfd9306c4a954d20ffd1814c4a54c1209ff8cb54d9844120eff1514c1a126120cff9b54c0a960d20cff5812e9954c52097fdc52e98164d20f775516558360520c7fdb8694a94c520efcd524c5a326120c7fda96c4a954d2097fdc86c4a564d20f75d53661524c120def9b6440a954d2097fdcb544a864d20dfd9b54c0a94c520ffd1814c53054120cff9b5684a84c120ffd1814c1954c520ff715160d9544120a7fdc82d5a364520ff695254da844120ef6d516a15224d20c7fda96d4a960d2097fdcb544a366120b7f8c9545834c120d7f5816c4a564d2097fdc82e95164d20dfe9526c4a84c120f7d5814c4a564d20e7eca95499860d20d7ed526e0a94c520f7d5814c59564d20c7fdb564ca960520d7ecb9549a360520d7dd306d4a94c520c7fdb5660a960d20e77d516a19524d2087fcca6d53166120f3e9524c18166120ff61516e95244120ffc12164da04c520ff49534c1525412087fdca2e55120d20c6fda66e19524d20ef65b5549a120d20f3d93054d8166120ed6d51549a720d20c7f5a86c45364520c6fda06d8a94c520c7f5816c4a954d20afe9c1549a020d20ffc1305493160520e77551655a124d2087fdc52e93166120d7d5b14c4a864d20ff49532e9524c120ff49524c15360520ff49535493044120cf6db16c9a520d20c7eda22e55120d20ff49524c0a954d20c5fdb76a0a94c520ffc130484a94c52087fdcb605a914d20e6f5816d8a94c520ed6d52545a724d20cdf9b7680a94c520ff49535493064520afe5c2545a124d20ff49536e9524c120) else (if i<3 then 0xdec56b0d6c14b03ebfcafa6bbaae66b78ad96b36ac8eb10abf6adcaa7ea8caa1ea66a916a24a7d69e2a7769bca5fe95ea4f690ea3b68cca2e6898a216864a10e822a0067d29efe7909dbe76a9d5e7369c567029b866ce9a7e670997663c986e608976659c95ee522943e4ee93364ba922e478915e43690563f48f4e3b28e4637e8d0632e8c362ec8af628e89b624c88ae1fc87361ba866616a852613684560f483860c0827e07e813e02e806dffa7f65fb87e95f847dfdf5e7d2df1c7bedecc7aade7c796de2c7865e067795dc4768dd74754dd327445c8e71b5c3e7075bfc6efdb9e6dbdb406c45af06b05aa069fda1868159e4670d94e62f5872610d8065e0d7465c5d6f65aad67c593561057f55ce567d538545d504538d4c2524d47251454224fcd3d24ec53904d4d3084a85280497d22248051e047351ac45f515c44ed0fe429507640e4fe03ec4f903dbcf4e3cb4f0c3baceca3aa4e7a3964e1c3744da23604d6034fcd103384cc0327cc7e31acc4a30a4c082f9cbb82e5cb682cacb0a2ba4ac82a9ca862994a28281c9e627149a4252c91c237c8be227486e213482c202c7ce1e0c7541ccc7041b546b41a84680194463e18745e016fc5ac166456a152452814544d812dc488116441c0fb43be0e7436e0cfc31e0bf42ce0a44270090422007fc1d00684172049c0c0019c000bfe9c82e9524c12097fdc52e93166120a7fccb605a954d20d7f5812e95164d2097fccb54da864520c7fdba605954c120fb6d5254d8160120ffc531605524c120a7fdc12a1a764d20ff69524c15360520d7f5816d4a94c520dfe9526c53026120d7ddb84c4a564d20a7fdc52a5a94c520e77d98545a524d20b7bdc86554161120c7fd986d5a124d20c7fdb564ca960d20e7eca9549a04c520d7bccb6554161120a7fdc82e995505209bfccb54d9860520d7ddb14c0a954d2097fdc52e5a160d20ff65515498360520efe930548a960d20e7f581655a124d20b7f4c94c5816012097fdc52e5a360520a7fdc82a5a04c520bfe9c1548a84c120dff1816c4a54c12097fccb54d986452097fdc82e5a54c520abfcca54d8160120cfed526cda126120c7fd956e1a124d20e7f581540a94c520c7fda06c4a954d20c7fdb8694a364520a7fdc52a1a164d20f7d581655314c120dfe5b5484a94c520f76d535499844120cff9b8684a54c120bfe9c12e9524c120a7fdc12a1a564d20c7fdb86d4a94c520f7d53164d9860520efe552605a124d20a7fcca605a564d20ff6952440a954d20cff9b8680a94c520ef6d526958124d20ff6980549534c120e7ed52694a94c520ff4d53548a960d20efe8ca549a14c120cff9b5680a94c520e7f5a15459326120efe9524c0a960520e7bca92d1a954d20ff59536153064520d7ddb54c4a864d20aff8ca54d1060120dfd9316e0a54c120 else (if i<4 then 0x359072201b40c5164c003080d6360e406b100cc02f8943901ac400e80dba1c811e030811202f00d602fa405e017c500f80cc02f0c839017c4047811c20374008033c06d2003802f0b21a01ac05e180c202f00be3c86808f0178601680be2684c06d01ac600280d62100405e1011e030c87003580bd81cbc1a701ac2088011e230e408913cba4396c6e437c80402fec50461a0078023501d802324a78a1e370224095e0e5403c103b80081120471721a023c05e181ba004019e03693a4a018406b017805f78a1e8078dc08d4a0fd41c81da03592039017806d181fe0308809ee0e083903b406b2e45e03580bc300ac05e01cc603c011202f812a40178337b811204a8f21a023c05e180f0046dc1a06980c2035c1487300405e100be1033c06d1001002f080b501440ed180900478806b0178404f01ba0358c06e017c089180c2035894010178402f80c22028607e02740732342606e819e00400be5034c061b00806da84c06b03b4e06c00be2000405e1507205a813a03310c18023c403680be20184206b00bc2018405e017c603580be200ac06b1407b01f80bc0471008d034c0dd01ada1303ecc01580bc0398c0dd017805f0184981e60220044c2600e8102640e48390178660c011e2007008f100be030880d60178460080bc2014405e101b002f88002017c402f00fc0358c05f0314406e801006780da4c0f041dcbac6040238a03080bc02f8c02d01ac403680be2017808e1005a03080d6381f9a1301ac603300c22035805e1019002f8806109830047880c8017c4c1c012a201b408917070024011e300ac061101e404481d4381c408f037406b20056030880d601784e1c80c22001006b100c203588c010178406e801006780da4017c07314c0802f080ff01845601011e222a583d023e454019805f3002603200c2381f9a1301b406b218720308b438017c4909a0100470c418023c407f80c2260e005e141ba035b802039900780224061017c0952e43404780bc300ac06b1011a04781123c86808f01786035812a20178207f80c229929454c0f060448402b023c4035811a06401f6490e3039100c210224390980da0358cc010178403580bc20178301f80fb01e80d6410e40891687003580be3029c05e017c606e801006780da4407c06b0178791780d602f0c0660184590d011e02f0d213023c08e181ac02f09c3901845008a03a0408f01100ac05f01cc803300c22007002d01786002811e2300805f100bd61c80c233c3006d0224602f019f0388c0b502780cc03b402b2dc1a047207ea1c812a03580be7f00001d01ac05f002004b3010c02f5d01e1c821a03580387c53f120c3ff0ecc32f09cc1b704cc0af00abfa6fd6bf0efa2be3ef6ebcfef1ebbf6eeabb26e8cb9aee4ab8dee24b80edf0b73edaeb636d5eb4f6d0eb3b6cdab2aec98b1 else 0x3628d8dc078180c202f00be303b40cf1687a101b405f1202602f819e301ac05f0178603580be2017c0ed100bc0448809d023c401586c39080da06288061080be0730806601ac05e180da0628b21321f840730480802c0405480bdc1c80be4100406b1005a030880610811a101ac02b101ba1012008f12c0a0308806d017c503880e602f8c06d02a4404480bc0358f41802a440158443f017c06b181d4130e407311c0a0580806d0314403580be2000be183342438811c04a8c073033c4702816a220e4321c80d602f0c0d70d872100ac203580bc201e3213017c05e200fc10011c0660802b0178481680da2023405f00ac700e040016d8722034c0a9d00805f200dc02f8806b30e4404480d602f0da1300705c0f80be2c928202f00be2c814201580d62c0e405f1640b41c8b83860e45a1c80d602f8c06b0811e04480d63017c08910005f0811a0158806d01ac4a0084066017c40760503801ac05e180d6c1c80be3023c2036818a2018406d10172170e4c3f01ac603080d7509a0fc43814061101a705480c203680bc02f980c509c2604b8a83941f84044840cfa04c05f1c872118140b0134360358902d01b4403680be201cc0661003a04b8806d0314402f0402b0179c3901ac80158406b017c408780be201b4073017c6035e07223f0ce04023c460100be240b405f1005602f80d6301e3039017c60448406b017c4054f07202f0c06b00ac55098406b01784036818a20120270280d62017c06b1021c0358806101b405f1e80402f88c39080da0398805e01ac5c0200be2b008203580be2000da0308b0390d45e02f80d6301980c5100d602f00be30184008100c261c80be301b4061140e532500be330e420330406101784)))
def xml10 : Packing := (322,5,9,0,0,14,0,xmd10)
def xmh10 (i : Nat) : Nat := 0x38594308d7102fb100948d60002b01490000517802bc1ba68d059838023401c9d22681b34ede0cbb568ca4174099054000000a000002514e1ba01387a1a1806471800000021ab159b754072145760003c192d10000000929a08e078002138210b614877c1201c1094bc8001e380000000000000c7c201d9d06040c000001060040000000002020001010000200450000000110200000000
def xmd9 (i : Nat) : Nat := 0x35805e00be30006b0e01100da2000190e0390e002f080358700e0403584044841e0e42034c2027820234047009518002f84044805f1005e00be2011201ac40184035be287c6e400d6100d6017c401b42023404b8804f006b1005f0806b0d835e55142d013dced3147f15c2f01bdef53ace135cbe2eeb1a808e9f45c94a410dc258500a00107fcda72d5128d98483bf8242daa6054a62907bf0549a14c53026120a7dce8974c22a8b8241de69526d9102a5534838ddaa4dc36c54a62906adb548ca54d8160120ebb2ea972a9262c0a41d6e5d62e5524c581483bf8262a9362542609059af758a92d1a954d20e3b6d2aa4dc15298a41df49524c1b12a55348387eb02dc36a54a62906df2548c9695304c520b7b46d2a6a9220c0241c6f5816d5b62a5314837e92a6e0974a92609067da32d5254da8441209bae6e2a6cc2a49824187d930329b54c598483a7a3029817498b309077d06c5524c15360520ef24a936c98152a9a414fa9d12e9425517048367a260e0aa6c0b309077b04c1b6484a94c520dba4a9192d0a60a9a41c4f5816ddb62a531483a7a302d8a6051b309070bd605b86d8a94c520
def xml9 : Packing := (31,6,9,0,0,10,0,xmd9)
def xmh9 (i : Nat) : Nat := 0x282e060000020800000199f84e02
def xmd8 (i : Nat) : Nat := 0x1ac01784000035802f880178017c5527ca4a03c4e552605b76d8a94c520f0b9549816e1b62a531483c36552605b86d4a94c520f4d0661b15493054d8148383d1814c0ca6d53166120
def xml8 : Packing := (5,7,9,0,0,7,0,xmd8)
def xmh8 (i : Nat) : Nat := 0
def xmd7 (i : Nat) : Nat := 0x2f0017c5e0d0549814c0ca6d53166120
def xml7 : Packing := (1,8,9,0,0,0,0,xmd7)
def xmsamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc93c600104800f00033a821010a4040000e784c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x2a2c892948494384049443e911490019504944c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03000c538c42003890004200000001bf8e7a10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x1092049602b0045b1b60a410c4864fe48810a10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x26010014d0082046000004200913f9d3b00800001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0xd485220dd0e2184e48942ed2940800050c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0x30030208803b402c44c001474203e88004100600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x20332dc802e0524012408c02d4a45a41ad0a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0xe420804100c080000035552a400000400380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x15c05216b516ac3be92b30142a12a5a602b4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x9803c2203009310323fc888000806200200400f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x58336c48484301962402c12a02457c025168000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x4081c02844008188003000a440000c49003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x2d293b48ac4cfaa06402188b33303003372f56a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x6000c1040009050300540080910116000083ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3234891b2271ce6219369100569b283f8a287ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x10c09122032340a044c03882a448020403107fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1244c0335113050689bd4364084b803c40c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xmcolumns : List ColumnInfo := [(43072,0,43455,0,13),(17,0,494,0,11),(132,0,379,0,11),(43010,0,43517,0,12),(32,0,479,0,12),(256,0,255,0,12),(8,0,503,0,12),(44164,0,44411,0,11),(9,16,486,0,8),(12305,0,12782,0,11),(13841,0,14318,0,11),(49168,0,49647,0,13),(27664,0,28143,0,13),(43536,0,44015,0,13),(50704,0,51183,0,13),(59920,0,60399,0,13),(69136,0,69615,0,13),(47633,0,48110,0,11),(52753,0,53230,0,11),(24,0,487,0,11),(320,0,191,0,11),(18564,0,18811,0,11),(18433,0,18942,0,12),(18464,0,18911,0,12),(66,0,445,0,11),(18434,0,18941,0,12),(42752,0,42751,0,12),(47872,0,47871,0,12),(156,0,355,0,7),(36,128,347,0,8),(43648,0,43903,0,13),(42628,0,42875,0,11),(44676,0,44923,0,11),(48256,0,48511,0,13),(60032,0,60287,0,13),(2180,0,2427,0,11),(4740,0,4987,0,11),(46208,0,46463,0,13),(47744,0,47999,0,13),(50816,0,51071,0,13),(53888,0,54143,0,13),(69248,0,69503,0,13),(57984,0,58239,0,13),(7,0,504,0,7),(11265,0,11774,0,12),(344,0,167,0,7),(27656,0,28151,0,12),(42504,0,42999,0,12),(47624,0,48119,0,12),(69128,0,69623,0,12),(57988,0,58235,0,11),(57920,0,58303,0,13),(57888,0,58335,0,12),(57858,0,58365,0,12),(42512,0,42991,0,13),(53776,0,54255,0,13),(48260,0,48507,0,11),(43074,0,43453,0,11),(46112,0,46559,0,12),(69137,0,69614,0,11),(59921,0,60398,0,11),(49169,0,49646,0,11),(21,0,490,0,7),(43330,0,43197,0,8),(55312,0,55791,0,13),(54801,0,55278,0,11),(68624,0,69103,0,13),(43584,0,43967,0,13),(27665,0,28142,0,11),(83,0,428,0,7),(6161,0,6638,0,11),(352,0,159,0,8),(322,0,189,0,8),(17152,0,17151,0,12),(58624,0,58623,0,12),(177,0,334,0,7),(44608,0,44991,0,13),(44546,0,45053,0,12),(144,0,367,0,11),(64064,0,64447,0,13),(9344,0,9599,0,13),(133,0,378,0,7),(68625,0,69102,0,11),(42528,0,42975,0,12),(60036,0,60283,0,11),(59968,0,60351,0,13),(59936,0,60383,0,12),(59906,0,60413,0,12),(160,0,351,0,11),(16960,0,17343,0,13),(16913,0,17390,0,11),(16900,0,17403,0,12),(16898,0,17405,0,12),(58432,0,58815,0,13),(202,4,305,0,4),(114,1,396,0,4),(59970,0,60349,0,11),(120,256,135,0,4),(4,8,227,272,7),(59911,0,60408,0,7),(266,64,181,0,5),(44610,0,44989,0,11),(167,0,344,0,4),(46244,0,46427,0,8),(55321,0,55782,0,8),(17216,0,17087,0,11),(162,0,349,0,7),(197,2,312,0,4),(42520,0,42983,0,11),(15,16,480,0,4),(47625,16,48102,0,8),(55305,16,55782,0,8),(9240,0,9703,0,11),(6153,16,6630,0,8),(49161,16,49638,0,8),(85,2,424,0,4),(17218,0,17085,0,8),(44866,0,44733,0,8),(53058,0,52925,0,8),(58690,0,58557,0,8),(43048,0,43479,0,8),(44700,0,44899,0,7),(42816,0,42687,0,11),(16962,0,17341,0,11),(47776,0,47967,0,11),(42532,128,42843,0,8),(48164,128,48475,0,8),(52913,0,53070,0,7),(53824,0,54207,0,13),(141,16,354,0,4),(44068,128,44379,0,8),(58016,0,58207,0,11),(46116,128,46427,0,8),(44800,0,44799,0,12),(42652,0,42851,0,7),(60064,0,60255,0,11),(44812,0,44787,0,7),(340,8,163,0,4),(42656,0,42847,0,11),(64066,0,64445,0,11),(16,0,495,0,13),(58373,0,58874,0,8),(178,1,332,0,4),(449,32,30,0,4),(69144,0,69607,0,11),(69252,0,69499,0,11),(69184,0,69567,0,13),(69122,0,69629,0,12),(69145,0,69606,0,8),(154,4,353,0,4),(42764,0,42739,0,7),(404,8,99,0,4),(44568,0,45031,0,11),(416,0,95,0,8),(68864,0,68863,0,12),(64320,0,64191,0,11),(14,0,497,0,7),(26,0,485,0,7),(74,0,437,0,7),(44618,0,44981,0,7),(69194,0,69557,0,7),(46090,0,46581,0,8),(3076,0,3579,0,12),(2084,128,2395,0,8),(12297,16,12774,0,8),(43010,64,43197,256,9),(185,0,326,0,4),(296,0,215,0,7),(58688,0,58559,0,11),(43266,64,43197,0,8),(26632,0,27127,0,12),(18592,0,18783,0,11),(54793,16,55270,0,8),(200,256,23,32,5),(68632,0,69095,0,11),(59395,0,59900,0,9),(232,256,23,0,4),(58176,0,58047,0,11),(289,0,222,0,7),(134,0,377,0,8),(1156,0,1403,0,11),(69127,0,69624,0,7),(11297,0,11742,0,9),(35,0,476,0,7),(80,0,431,0,11),(181,0,330,0,4),(9232,0,9711,0,13),(58178,0,58045,0,8),(47649,0,48094,0,9),(9360,0,9583,0,11),(69186,0,69565,0,11),(44230,0,44345,0,7),(4764,0,4963,0,7),(44864,0,44735,0,11),(17028,0,17275,0,11),(25,0,486,0,8),(42792,0,42711,0,7),(401,32,78,0,4),(27672,0,28135,0,11),(56,0,455,0,7),(168,0,343,0,7),(47672,0,48071,0,7),(53025,0,52958,0,7),(296,16,198,1,5),(53,128,330,0,4),(3100,0,3555,0,8),(42840,0,42663,0,7),(482,0,29,0,4),(60,128,323,0,4),(43304,128,83,4,5),(268,0,243,0,7),(39,128,344,0,4),(60048,0,60271,0,11),(69264,0,69487,0,11),(400,0,111,0,7),(157,0,354,0,4),(208,0,303,0,8),(47905,0,47838,0,7),(198,0,313,0,7),(60066,0,60253,0,7),(50824,0,51063,0,9),(258,64,189,0,8),(69148,0,69603,0,8),(58370,64,58557,256,9),(0,0,511,0,15),(42752,64,189,2,9),(52819,0,53164,0,7),(59987,0,60332,0,7),(44546,64,44733,256,9),(480,0,31,0,7),(146,0,365,0,7),(57892,128,58203,0,8),(69254,0,69497,0,8),(2182,0,2425,0,8),(291,64,156,0,4),(43600,0,43951,0,11),(59953,0,60366,0,8),(282,64,165,0,4),(60112,0,60207,0,8),(69203,0,69548,0,7),(42660,0,42843,0,8),(43104,0,43423,0,9),(55330,0,55773,0,8),(60038,0,60281,0,8),(164,0,347,0,8),(42912,0,42591,0,8),(270,64,177,0,4),(53904,0,54127,0,11),(47665,0,48078,0,8),(58436,0,58811,0,9),(44420,0,44155,0,7),(297,16,198,0,4),(52771,0,53212,0,7),(60037,0,60282,0,7),(59906,64,189,256,9),(200,0,311,0,7),(288,128,91,4,6),(1060,128,1371,0,8),(6169,0,6630,0,8),(11331,0,11708,0,8),(102,128,281,0,4),(60080,0,60239,0,8),(296,128,83,4,5),(13321,16,13798,0,8),(43664,0,43887,0,11),(388,0,123,0,7),(69253,0,69498,0,7),(48129,16,486,8,9),(47760,0,47983,0,11),(11425,0,11614,0,8),(87,0,424,0,4),(472,0,39,0,4),(31,0,480,0,4)]
def xmautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xmlevels : Nat → Packing
  | 14 => xml14
  | 13 => xml13
  | 12 => xml12
  | 11 => xml11
  | 10 => xml10
  | 9 => xml9
  | 8 => xml8
  | 7 => xml7
  | _ => emptyPacking
def xmindex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 49 69 4 13 5 4 xmh14
  | 13 => lookupWord 158 593 7 17 9 4 xmh13
  | 12 => lookupWord 430 1617 7 18 10 4 xmh12
  | 11 => lookupWord 174 657 6 17 9 4 xmh11
  | 10 => lookupWord 59 75 4 13 5 4 xmh10
  | 9 => lookupWord 1 11 1 11 3 4 xmh9
  | 8 => lookupWord 1 3 1 9 1 4 xmh8
  | _ => fun _ => none
def xm : Forest := ⟨1535,14,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem geomxm : graphValid xm (boundsBefore known511) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_14_0 : block xm 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_14 : block xm 14 0 1=true := sxm_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_0 : block xm 13 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_7 : block xm 13 7 22=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_13 : block xm 13 0 29=true := (@block_merge xm 13 0 7 22 sxm_13_0 sxm_13_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_0 : block xm 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_36 : block xm 12 36 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_72 : block xm 12 72 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_108 : block xm 12 108 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_144 : block xm 12 144 25=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_169 : block xm 12 169 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_205 : block xm 12 205 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_241 : block xm 12 241 29=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_12 : block xm 12 0 270=true := (@block_merge xm 12 0 241 29 (@block_merge xm 12 0 205 36 (@block_merge xm 12 0 169 36 (@block_merge xm 12 0 144 25 (@block_merge xm 12 0 108 36 (@block_merge xm 12 0 72 36 (@block_merge xm 12 0 36 36 sxm_12_0 sxm_12_36) sxm_12_72) sxm_12_108) sxm_12_144) sxm_12_169) sxm_12_205) sxm_12_241)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_0 : block xm 11 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_5 : block xm 11 5 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_41 : block xm 11 41 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_77 : block xm 11 77 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_87 : block xm 11 87 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_123 : block xm 11 123 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_159 : block xm 11 159 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_195 : block xm 11 195 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_231 : block xm 11 231 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_267 : block xm 11 267 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_303 : block xm 11 303 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_339 : block xm 11 339 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_375 : block xm 11 375 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_411 : block xm 11 411 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_447 : block xm 11 447 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_483 : block xm 11 483 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_519 : block xm 11 519 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_533 : block xm 11 533 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_569 : block xm 11 569 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_605 : block xm 11 605 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_641 : block xm 11 641 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_677 : block xm 11 677 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_713 : block xm 11 713 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_749 : block xm 11 749 19=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_11 : block xm 11 0 768=true := (@block_merge xm 11 0 749 19 (@block_merge xm 11 0 713 36 (@block_merge xm 11 0 677 36 (@block_merge xm 11 0 641 36 (@block_merge xm 11 0 605 36 (@block_merge xm 11 0 569 36 (@block_merge xm 11 0 533 36 (@block_merge xm 11 0 519 14 (@block_merge xm 11 0 483 36 (@block_merge xm 11 0 447 36 (@block_merge xm 11 0 411 36 (@block_merge xm 11 0 375 36 (@block_merge xm 11 0 339 36 (@block_merge xm 11 0 303 36 (@block_merge xm 11 0 267 36 (@block_merge xm 11 0 231 36 (@block_merge xm 11 0 195 36 (@block_merge xm 11 0 159 36 (@block_merge xm 11 0 123 36 (@block_merge xm 11 0 87 36 (@block_merge xm 11 0 77 10 (@block_merge xm 11 0 41 36 (@block_merge xm 11 0 5 36 sxm_11_0 sxm_11_5) sxm_11_41) sxm_11_77) sxm_11_87) sxm_11_123) sxm_11_159) sxm_11_195) sxm_11_231) sxm_11_267) sxm_11_303) sxm_11_339) sxm_11_375) sxm_11_411) sxm_11_447) sxm_11_483) sxm_11_519) sxm_11_533) sxm_11_569) sxm_11_605) sxm_11_641) sxm_11_677) sxm_11_713) sxm_11_749)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_0 : block xm 10 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_5 : block xm 10 5 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_41 : block xm 10 41 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_77 : block xm 10 77 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_113 : block xm 10 113 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_149 : block xm 10 149 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_161 : block xm 10 161 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_197 : block xm 10 197 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_233 : block xm 10 233 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_269 : block xm 10 269 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_305 : block xm 10 305 17=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_10 : block xm 10 0 322=true := (@block_merge xm 10 0 305 17 (@block_merge xm 10 0 269 36 (@block_merge xm 10 0 233 36 (@block_merge xm 10 0 197 36 (@block_merge xm 10 0 161 36 (@block_merge xm 10 0 149 12 (@block_merge xm 10 0 113 36 (@block_merge xm 10 0 77 36 (@block_merge xm 10 0 41 36 (@block_merge xm 10 0 5 36 sxm_10_0 sxm_10_5) sxm_10_41) sxm_10_77) sxm_10_113) sxm_10_149) sxm_10_161) sxm_10_197) sxm_10_233) sxm_10_269) sxm_10_305)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_0 : block xm 9 0 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_11 : block xm 9 11 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_9 : block xm 9 0 31=true := (@block_merge xm 9 0 11 20 sxm_9_0 sxm_9_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_0 : block xm 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_2 : block xm 8 2 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_8 : block xm 8 0 5=true := (@block_merge xm 8 0 2 3 sxm_8_0 sxm_8_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_7_0 : block xm 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_7 : block xm 7 0 1=true := sxm_7_0
theorem tablesxm : checkedTables xm 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xm 0 0 0 = true)
  · exact (rfl : block xm 1 0 0 = true)
  · exact (rfl : block xm 2 0 0 = true)
  · exact (rfl : block xm 3 0 0 = true)
  · exact (rfl : block xm 4 0 0 = true)
  · exact (rfl : block xm 5 0 0 = true)
  · exact (rfl : block xm 6 0 0 = true)
  · exact allxm_7
  · exact allxm_8
  · exact allxm_9
  · exact allxm_10
  · exact allxm_11
  · exact allxm_12
  · exact allxm_13
  · exact allxm_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFB : Impossible false (graphGoal 1535) 14 (varsX 43519).toFinset :=
  index_root (g:=xm) (i:=0) rfl rfl (before_sound known511 valid511) geomxm tablesxm (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨u,k,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 43519 := by decide +kernel
  have er : inputs++[seed]=varsX 43519 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : fullOK 43519 [20, 1, 9, 4, 1, 1, 2, 4, 8] = true := by decide +kernel
  have g1 : graphGoal 43519=graphGoal 511 := by decide +kernel
  have g2 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have v1 : vars 43519=vars 511 := by decide +kernel
  have hb := caseFB
  rw [g2] at hb
  have sp := full_split ok run sub
  rw [g1] at run
  rw [v1] at sp
  cases u
  · rcases sp with e | e
    · exact caseFA k hk (e ▸ run)
    · exact hb k hk (e ▸ run)
  · rcases sp with e | e
    · exact caseUA k hk (e ▸ run)
    · exact caseUB k hk (e ▸ run)

def orHead : Gate := ⟨.or,[0,2]⟩
def andHead (j : Fin 9) : Gate := ⟨.and,[j.val,9]⟩

def withHeads (j : Fin 9) (D : Circuit) : Circuit :=
  ⟨orHead :: andHead j :: D.gates, D.output⟩

def supplied (j : Fin 9) (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 2]) ++ [x j && (x 0 || x 2)]

lemma headWires (j : Fin 9) (D : Circuit) (x : Fin 9 → Bool) :
    (withHeads j D).wires (List.ofFn x) = D.wires (supplied j x) := by
  let w := List.ofFn x
  let z := x 0 || x 2
  have first : orHead.op.eval (orHead.inputs.map fun i => w.getD i false) = z := by
    simp [orHead,GateOp.eval,w,z,List.getD_eq_getElem?_getD]
  have raw : (w ++ [z]).getD j.val false = x j := by
    rw [List.getD_append _ _ _ _ (by simp [w]), List.getD_eq_getElem _ _ (by simp [w])]
    exact List.getElem_ofFn ..
  have added : (w ++ [z]).getD 9 false = z := by simp [w,List.getD_eq_getElem?_getD]
  have second : (andHead j).op.eval ((andHead j).inputs.map fun i => (w ++ [z]).getD i false) =
      (x j && z) := by
    change ((w ++ [z]).getD j.val false && ((w ++ [z]).getD 9 false && true)) = _
    rw [raw,added,Bool.and_true]
  change D.gates.foldl _ ((w ++ [orHead.op.eval (orHead.inputs.map fun i => w.getD i false)]) ++
    [(andHead j).op.eval ((andHead j).inputs.map fun i =>
      (w ++ [orHead.op.eval (orHead.inputs.map fun t => w.getD t false)]).getD i false)]) = _
  rw [first, second]
  rfl

lemma extendsInput (gs : List Gate) (out : Nat) (w : List Bool) :
    ∃ l, (Circuit.mk gs out).wires w = w ++ l := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_,hl.trans (List.append_assoc _ _ _)⟩

lemma headFirst (j : Fin 9) (D : Circuit) (x : Fin 9 → Bool) :
    ((withHeads j D).wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
  rw [headWires]
  obtain ⟨l, hl⟩ := extendsInput D.gates D.output (supplied j x)
  change D.wires (supplied j x) = supplied j x ++ l at hl
  rw [hl]
  simp [supplied,List.getD_eq_getElem?_getD]

lemma headLegal (j : Fin 9) (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) :
    PEqualNP.MetaComplexity.FanInTwo (withHeads j D) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp [orHead]
  rcases List.mem_cons.mp hg with rfl | hg
  · simp [andHead]
  exact legal g hg

lemma suffixBound (j : Fin 9) (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D)
    (small : D.size ≤ 13) : ∃ x : Fin 9 → Bool, D.eval (supplied j x) ≠ edge x := by
  by_contra! agrees
  have h := bound (withHeads j D) (headLegal j D legal) (headFirst j D) (by
    funext x
    change ((withHeads j D).wires (List.ofFn x)).getD D.output false = _
    rw [headWires]
    exact agrees x)
  have sz : (withHeads j D).size = D.size + 2 := rfl
  omega

end PEqualNP.Outside.L_meta_5146

theorem PEqualNP.Outside.L_meta_5146 : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       ∃ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ))];         x2.eval (x6 ++ [x5 x1 && (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_5146.suffixBound
