import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_40411, which copies L_meta_10856 (same repository, Apache-2.0),
-- which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_43706.Model
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
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
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

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
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

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
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


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_43706.Model

namespace PEqualNP.Outside.L_meta_43706
open PEqualNP.Outside.L_meta_43706.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [7,5,5,5,5,3,7,5,7,5].getD j 0
def sliceDomain (raw : List Sig) (j : Nat) : Sig := if j<5 then neg (raw.getD (j%5) zero) else raw.getD (j%5) zero

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 16)-1) 9
  let d := sliceDomain raw j
  let cs := tips raw (hint >>> 7) (hint/16 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps (code : Nat) : List Move := (if code % 2 = 1 then [swapRows 49] else []) ++ (if code / 2 % 2 = 1 then [swapRows 66] else [])

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 4 != 0 && autoOK (target g) (mirrorSteps code) then ws.map (movedWord (mirrorSteps code).reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 4
  if row < count g k then [variant g code (vals g k row)] else []

noncomputable def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (sliceDomain (roots g) (min ((tip g k i % 16)-1) 9)) (SBf (min ((tip g k i % 16)-1) 9))

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

noncomputable def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

def b0K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b0K5 : Nat → Nat
  | 0 => 0x5a800412338c05f861f8c3e98fd30fc41fcc7e907d10fa43fc83f197f21fc43f0cbf997c20fc63fcc3f887c10f843f0c7e997e10
  | _ => 0
def b0K4 : Nat → Nat
  | 0 => 0x3a000b80000010680400600001c00090206dd804000556aa8029d8020c2e27004220181c0a087601c0202d9300c2fcd031be34443bc9021bf04882f4d321de34483d10532bc34842f90021bf24cc7dc8410dd320caf45220bf14042fc9030bf04842f09210de304c2f0d021bf24083b0ca20e521086fd05309c34443dc5031bf34043b0c821bf04ccafc9021f731087dcc610bd348cafd0520bf34442f89310bf048c6fcd210bf24442f0d320de320c7bc8220ed320cafcd221f9300c370c831be410caf10530bf14ccafc9010f8404cafc9232dd300c2f49310bf04c86f49231fb40486fc5221bc24c43e0c020fb30083b88521fb20c42fc1010ef24082fc52329e34442f4d220bf24c42ed0121bf1488378ca31bc424c778c630bd140c370d110bd148caf09110bc34082b89110fb10843dc8610bf414caf8d221de328c2fd0931bd34042f8d310bf248c2fcd120df340c2fc5320bf34c82f10131f9100437cca32bd34483bd0930f431042dd0530f431c87b08420bf14cc3ec1020bd04886bd0930bf24843e48020de34442f4d210bc404cbd08610fb040c374c431ec424c2fc5231f7414c2fcd321bf248c7e08010ac424c2b09110de310c37cc631f7314c6f49230be34882f10532f43108734c832ee24442f49330bf34086fc1232bc40486fc5030bc34443bcca32fb30c43dc4210ee21082f0d121ef32886f4d020ef424c7b10931be34c82f4d121fb404cbe0c310bd348c6b10931bd14083b09110b441483b48421bf148c2f4d320bd048cafcd121f8404c6fc5020ee20483e0c010f840487d0c610b8404cbb88620fb10442f50032f721487bcca20bf240c770ca31bc34882fc1221ed20083d48421b840486f4d230de324cafc1030bd240c2e10131bd34c42f49221dc328c2f8d121ef32083d10530df340cafd0131de34487e08310be34482f09010be34c86dd0520fb30c82f49331bd24042bd0931fb404c670d121bc34042f8d210b4414c270d120be24842fcd030ef2188778c830ec32886fd0132bf34083dcc631fb308c2f50432bf34c43dc8621f441483d08410bd14cc2f0d3109e34482f41321f7414cba48020dc320c2f89010bf34882f4d221f510042ed0131bd148c3d4c431df308c2fc5031bd24842f4d021ef3208770c630fb20482f8d010fb04043ecc130bd14842f49110b7414caf50021be400c6fc9032bf24cc2f90032bd24883dd0520bc34482f8d020bf1408678d121bd04cc6ed0132ec21882fd0121ec3208370d120bf340caf0d321be34087bcc932de314c6f41231fb20883dc5010bf048c2f89110bf04082fc1331f110043ecc010bd14c82fd0930bc34886f45332bd400c7dcc410f714086f49031fb20043d84110ef240caf41332d5310c6f10520f731c86f4d110dc344877cd031dc310c2f10930b4414cbe0c320
  | 1 => 0xcf0ee303c474cd00020047d10849d003343cc64040002d9c474d098b8000284c1c01070001c0003814162e000349a095a088561c240001a34092b0001e7280000001700c000b2e83004043c91c00001b000
  | _ => 0
def b0K3 : Nat → Nat
  | 0 => 0x80212c524d110b828a4010660d3404863e8a1a221e05048421b88a8400871d49310c6aea898863ab5448020a7aa264196a108404c734642026568504c832cc1846990530d520082e04a8802158504c832a69ae48194e1413404334622026337544c431b228a40105a149300c3306990241643548421e5a8264195949431086386a8a0415935c1030b3aa24210c7d51310c7c6a290041673548421ca18c690859149310c698a4988632d258d310c61924818c7d16344863e6b92221cb524c030e21aa4210cd4573448330609a0211c3549010a61aa4210cbd493404276a0922216425440108f9ac4908720c83008298a0990659b544c030a429260185acd520082760b1a6432c2550031cb1a6829056540310c2386aa0043ab42d0131f012a20085c5402104288a49886350514c0309a28a80194ed4134487c6a0908433945c1010e9a826218dc141310c6e2a0188212d250d0109a28a68104dd45240c2886a908433b504d120ac1aa401063d51320cae0a2980611f458d120c6214609865106304c2c0a0908438c3409110ac2826218e30c9240c2aa6b8a06358514c03097a9268884bd49344832869a0a418e3409110cd1a68090e910b314c6584a8a0618c328d221e228a6419630ca34883a6a298061a42149010d221082984dd4524442ca4b8a04337158d3209792c69884d1453408676a888021733544010a82826218cb895140c25c4aa0063543544010b22824210ec107404cb568420263aa2110121a628a64195ad5120082caa2190431e3549110e3a8a64196cc8440486e0a09084339058d321e81aa200872141320cb34682024358524c030aca8064184d14534482720b9a2433b54480209ba8a6888474d7244432ea898863ca354802097aa264194dd51210863c6aa004337514d121d42166098478d52404270a09a043e051480209ba8a6810748d510043c44a88021b341d0132d99888098da0d5200823a6a1202154524c4319a28a480859145320cb4e85a0a6137150d0208faa2601872149300c3186910a4354514c8328f1aa281071149310c6d0a2900418c3489110d21242088550d5210865ea8900414c524c0309a8a86810474d624c4276a09a0439634105209ba8a80194dc563488270a0a0865d0504c4319ba8a6890470d5244426e2b9a241a842d0131b028a4010691062048318649a041b341101329a28a4818650d32148688a2990652f4509110b412a20084bd493448748431242139500d021d41262088638d2244434ea89084369500c8208f9ac49884bd51210865e4a1a0212f45891109c2826890cbc9634842e64a8802135158d2209d82e6890ec107304c258a49a0412c524d0108fa286890f10c831087a0a29806194314d010b012a200852141320ca906a9004155510c8319c2826810660d0404876083902412d25cd110
  | 1 => 0x1e030883c00160992cb6007b0ec122431021580006800023a081da200c0a000540204978fafa6438506791a8005e0b0d058b01e748056a380081002000882c00000d00804000000216531080423124c80814060e8340e000900000007f0040000060dc0400050183401086910b414c23a6b1242154504c431aa28a6018660c234c4330609a041375444010f01084008650d210443906a90041a73210532b492e08105a54021082e6a8880217115c1010962926810d6d51300c35664202653b5049031e31aa4210e50c53408676a09a2213b058d221d3a1082985c0d51004318649a043943410520d410449884d45634c8276a0a08652d258d210c62146298d60d510042d24a1804194318d3218faa26419660d31044366a888021a820490109d2806810c7d143448360822026534514d0108fa2c688869085140831869102413b544c030ca18a28184e141240c6720b1a443963210532e818860084bc973444270a0920211f3509010b42824210d40d510042e22a1
  | _ => 0
def b0K2 : Nat → Nat
  | 0 => 0x10700801146a05895040120000240906855b11061c200064400194cdb2544010c2148304d020c20d42049010c20c3258d310d0d48504c431d0148504c431c10d42145020d0147504c832920d925c1020d00d45048421c20cb058d22198185500c820c2083358931098099150c010d00d4514802098c1b3548421d00d62544010d08d45048421c81442049010c10d42149010c10943145030c2148304d01098185250c020c40c4504d010910d925c5021d00d42544010920d95008420940d915c1010d00d75048421c1148314d010940d95008410c20c8504d020c10873589210940d91508010d0148514c0309809915c1010c20c8504d021c10c7258d210c10cb158d220d014b514c030d0d44504c83298181250c42194185500c830d08d4514802098099500c41098c9b3544010c20c85049031c4144304d020c40c3158d320c40c7058d321d014b504c431c4144304d010d0d48514c03094181510c831c40c4504d02192099500c43098181510c821c1148314d021c10c8514d021c80845049010d00d7514802098c5b3548020c10c8514d020d08d42544010d0144504c832c10c85149030
  | _ => 0
def b0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def b0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt b0K6 (i*4) 4
  | 5 => packedAt b0K5 (i*15) 15
  | 4 => packedAt b0K4 (i*26) 26
  | 3 => packedAt b0K3 (i*37) 37
  | 2 => packedAt b0K2 (i*48) 48
  | _ => 0
def b0I (k h : Nat) : Nat :=
  match k with
  | 6 => 4*((h/1+packedAt b0K6 (4+(h % 1)*1) 1) % 1)
  | 5 => 4*((h/13+packedAt b0K5 (360+(h % 13)*5) 5) % 24)
  | 4 => 4*((h/111+packedAt b0K4 (7852+(h % 111)*9) 9) % 302)
  | 3 => 4*((h/95+packedAt b0K3 (10323+(h % 95)*9) 9) % 279)
  | 2 => 4*((h/32+packedAt b0K2 (3168+(h % 32)*7) 7) % 66)
  | _ => 0
def b0Pos : Nat → Bits
  | 1 => 0xffffc7fc7fefe1ffff8ff8ffdfc3ffff1ff1ff
  | 2 => 0xffff8ff8ff7fe1ffff1ff1feffc3fffe3fe3f
  | 3 => 0xf0ffff1ff1fbffe1fffe3fe3f7ffc3fffc7fc7
  | 4 => 0xff0fffe3fe3dfffe1fffc7fc7bfffc3fff8ff8
  | _ => 0
def b0Neg : Nat → Bits
  | 1 => 0x2222c12436d03c444582486da078888b0490db
  | 2 => 0xe44548498b4845c88a909316908b911521262d
  | 3 => 0x4e899212d184889d132425a309113a26484b46
  | 4 => 0x88ee24836c031111dc4906d8062223b8920db0
  | _ => 0
def b0Atlas : Atlas := ⟨6,rawDecor 30 b0Pos b0Neg, 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000, b0N, b0R, (fun _ _ => 0), b0I⟩
def b1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b1K3 : Nat → Nat
  | 0 => 0x1870000003710ec21de65b0cb6906f20
  | _ => 0
def b1K2 : Nat → Nat
  | 0 => 0x388c344823cd221a4414829c5332
  | _ => 0
def b1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def b1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b1K4 (i*4) 4
  | 3 => packedAt b1K3 (i*15) 15
  | 2 => packedAt b1K2 (i*26) 26
  | _ => 0
def b1I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b1K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/12+packedAt b1K3 (90+(h % 12)*3) 3) % 6)
  | 2 => 4*((h/3+packedAt b1K2 (104+(h % 3)*2) 2) % 4)
  | _ => 0
def b1Pos : Nat → Bits
  | 0 => 0xfffc7feff9ffff8ffff8ffdff3ffff1ffff1ff
  | 2 => 0xe1ff93f5fe3cfff1c3ff27ebfc79ffe387fe4f
  | 3 => 0x1c3e3397fc0e7fe0387c672ff81cffc070f8c
  | 4 => 0xfe03fc3e7fff07fffc07f87cfffe0ffff80ff0
  | _ => 0
def b1Neg : Nat → Bits
  | 0 => 0x244825500c08008248904aa018100104912095
  | 2 => 0x48b1928a11914310916325142322862122c64a
  | 3 => 0x151ae306a4ba8da42a35c60d49751b48546b8c
  | 4 => 0x98235801c120d6493046b0038241ac92608d60
  | _ => 0
def b1Atlas : Atlas := ⟨4,rawDecor 29 b1Pos b1Neg, 0xfaaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0, b1N, b1R, (fun _ _ => 0), b1I⟩
def b2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b2K3 : Nat → Nat
  | 0 => 0x627421d8439087710f721
  | _ => 0
def b2K2 : Nat → Nat
  | 0 => 0x29c5221
  | _ => 0
def b2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def b2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b2K4 (i*4) 4
  | 3 => packedAt b2K3 (i*15) 15
  | 2 => packedAt b2K2 (i*26) 26
  | _ => 0
def b2I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b2K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/3+packedAt b2K3 (75+(h % 3)*3) 3) % 5)
  | 2 => 4*((h/1+packedAt b2K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def b2Pos : Nat → Bits
  | 0 => 0xe3fff1ffbfc7fffe3fff1ffbfc7fffe3fff1ff
  | 1 => 0xfc707e67d7f879ffc707e67d7f879ffc707e67
  | 3 => 0xff807f87e7ff81fff807f87e7ff81fff807f87
  | 4 => 0xffff8ff8fbfffe3ffff8ff8fbfffe3ffff8ff8
  | _ => 0
def b2Neg : Nat → Bits
  | 0 => 0x609310ab4071100609310ab4071100609310ab
  | 1 => 0xa42526652897229a42526652897229a4252665
  | 3 => 0xc90a4b861922752c90a4b861922752c90a4b86
  | 4 => 0x124c0d50060441b124c0d50060441b124c0d50
  | _ => 0
def b2Atlas : Atlas := ⟨4,rawDecor 27 b2Pos b2Neg, 0xeeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800eeaa8800, b2N, b2R, (fun _ _ => 0), b2I⟩
def b3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b3K3 : Nat → Nat
  | 0 => 0x8283a10f510e863dcc7b887721
  | _ => 0
def b3K2 : Nat → Nat
  | 0 => 0xca724cc650d1109734c86909110
  | _ => 0
def b3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def b3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b3K4 (i*4) 4
  | 3 => packedAt b3K3 (i*15) 15
  | 2 => packedAt b3K2 (i*26) 26
  | _ => 0
def b3I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b3K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/5+packedAt b3K3 (90+(h % 5)*3) 3) % 6)
  | 2 => 4*((h/4+packedAt b3K2 (104+(h % 4)*2) 2) % 4)
  | _ => 0
def b3Pos : Nat → Bits
  | 0 => 0xfffc7feff9ffff8ffff8ffdff3ffff1ffff1ff
  | 1 => 0xe1c3b3357e1ce7f1c387666afc39cfe3870ecc
  | 2 => 0x1ffc3f9ffe0fffe03ff87f3ffc1fffc07ff0f
  | 4 => 0xfe03fc3e7fff07fffc07f87cfffe0ffff80ff0
  | _ => 0
def b3Neg : Nat → Bits
  | 0 => 0x244815500c40008248902aa018800104912055
  | 1 => 0x4c99b30a95c94b90993366152b9297213266cc
  | 2 => 0x1132c286209a85242265850c41350a4844cb0a
  | 4 => 0x98236801c110d6493046d0038221ac92608da0
  | _ => 0
def b3Atlas : Atlas := ⟨4,rawDecor 23 b3Pos b3Neg, 0xeaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0eaeaa0a0, b3N, b3R, (fun _ _ => 0), b3I⟩
def b4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b4K3 : Nat → Nat
  | 0 => 0x685c31a86378c7b98f431
  | _ => 0
def b4K2 : Nat → Nat
  | 0 => 0x25c5231
  | _ => 0
def b4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def b4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b4K4 (i*4) 4
  | 3 => packedAt b4K3 (i*15) 15
  | 2 => packedAt b4K2 (i*26) 26
  | _ => 0
def b4I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b4K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/3+packedAt b4K3 (75+(h % 3)*3) 3) % 5)
  | 2 => 4*((h/1+packedAt b4K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def b4Pos : Nat → Bits
  | 0 => 0xe3fff1ffbfc7fffe3fff1ffbfc7fffe3fff1ff
  | 1 => 0xfc7e0e7cdbf87f3fc7e0e7cdbf87f3fc7e0e7c
  | 2 => 0xff8fff8fefff8ffff8fff8fefff8ffff8fff8f
  | 3 => 0xfff00ff0f3fff03fff00ff0f3fff03fff00ff0
  | _ => 0
def b4Neg : Nat → Bits
  | 0 => 0xa092a0b54071020a092a0b54071020a092a0b5
  | 1 => 0x6424665c24972456424665c24972456424665c
  | 2 => 0x49094b0a110268249094b0a110268249094b0a
  | 3 => 0x92418de00e244eb92418de00e244eb92418de0
  | _ => 0
def b4Atlas : Atlas := ⟨4,rawDecor 15 b4Pos b4Neg, 0xe8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0, b4N, b4R, (fun _ _ => 0), b4I⟩
def b5K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b5N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def b5R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt b5K2 (i*4) 4
  | _ => 0
def b5I (k h : Nat) : Nat :=
  match k with
  | 2 => 4*((h/1+packedAt b5K2 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def b5Pos : Nat → Bits
  | 1 => 0xa9ad4d89d7535a9b13aea6b536275d4d6a6c4e
  | 2 => 0xcef18ee27f9de31dc4ff3bc63b89fe778c7713
  | 3 => 0xf0de0f139be1bc1e2737c3783c4e6f86f0789c
  | 4 => 0xff1ff01c1ffe3fe0383ffc7fc0707ff8ff80e0
  | _ => 0
def b5Neg : Nat → Bits
  | 1 => 0x92451428c9248a285192491450a3249228a146
  | 3 => 0x5382853060a7050a60c14e0a14c1829c14298
  | _ => 0
def b5Atlas : Atlas := ⟨2,rawDecor 30 b5Pos b5Neg, 0xfffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0fffffcf0, b5N, b5R, (fun _ _ => 0), b5I⟩
def b6K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b6K5 : Nat → Nat
  | 0 => 0x93910000aa1fa21fcc7e107f20f821f483f887c21fe43f8c3f197f32f865f8c7e187e21fc21f883e997d21f863f4c3e98ff30
  | _ => 0
def b6K4 : Nat → Nat
  | 0 => 0x10c0103420150a81c041202040030c04028121b370b004020083c0c006381400cc008340e000300c0009f510042fc5020bc34486fc9230bc424c2f10132bd248c3bc9010bf340cbbc9032bc34886fc5330bd14842f45330ef21c82fc5030f7140c7ec8120ed24042fc9232bf40486f10931be34c87dc8621bf148c7ec1030b5410caf4d020bf140c6fc5232bc41483b49031bd24c437cd020fa30443b4cb21fa30843d4c521ee2148764c030fa400cbe90021af240c3ecc230bf34042f49330bf414cafd0930be34042e50032fa30882f90032f521442fcd210dd324c6e50031bf24442b49031bf34886fcd120ed240c2f4d320ef240c6fc9331bd240c3b8cb20be3448374c930be410cafc9310be24042fc9330ee32486f8d310bf41483bc8220bf04843d48421bf048c7e4c210fa3048374cb31bf24843e50021bd048cb7cd032f910042f50021cd320ca7cd020bc24042f0d220bc34483e48210bd34487d88510f5140c3bc86219d34086f45020bd04ccbd8c710bd04887c44010fa20442fc9020bd248867cd021f631487d4c710bf14043e4c030ed21087d84110fa400c6fcd020af24043b8cb21dd32cc3e4c220bd04c8674d010bd348cbd4c621ed21483bc9030be24842fc5220df308c2fc9030f714082b49010bf04882f45332af240c774d020f6410cbe48110ed32483dc5021f930442f41331bf34882f8d320bd240c7b48020bf14ccaf50432d5310c6fd0132be34486fcd121be400c6f8d020bc414caf09310b714082f45220bf424c7d8c621bd34887ecc130bd34c877cca32bf340c2fc5230f930482f4d110bf34c83bc9021dd34086fc9021bf0404374c832f714042f90021bf344437cd010bf04c86f09210bf14086fc1030ef324caf0d010bf0488774c730bf34c43bc8520fb04042d45030bf24042f49010bd34882f0d321ee3248374c530bc414c37cd0309d34082dc5030ba40087d50432df31cc3dcc531be34887d45020df324c2f10121f531442e90032be34442f89110bd400cb78c531dd300c3d4c431f631443e50032df32cc7b4c832bc24443ec1020bd34086f89310bf414c2fcd021bf404c7e50031bf240cb7cc530bd348c6fc1020fb20882fc5320bf34c86fc9231be34883e48020bc34442fc5221df324c77cc631ee20482f0d020fb10842fc1230bd24882fc1332dd310c6f49331f521c43a48020b514083dcc631b940087dc5030bc34c42f45030ed21c83dc4210bd34042f4d310bd14c837ccb30de324cad90432f621c42e90031bd348c2f0d320bd248c7b4cb20bf340c7b4c921bd400c778c130ef24082f0d210bf048cb7cd021bc404c7bcca32dd34042f4d210bd148caf49110bd24842f4d120ad240c2f412319f34043dc8521bd148c2fc9031df340c6f0d021fb10443e88210be34086fc1331be34843948421
  | 1 => 0x480ca2e20180800be081154e001ac2000010a81e2a161299c1a0f1d8c4022b7608c00070b0bd4d051a08c100000040ca760101a04540e04c040000000585f1084424003280a000105910000210808
  | _ => 0
def b6K3 : Nat → Nat
  | 0 => 0xa0619534c50109aa8868906c885400876221120218d34c90109c2826890e34c1240c276a8880213b050d010c621264984bc94404c71868992433454485108f9a848084e151304431a641a641a12150021d290a8010dc1452044362211a0213b058d021cc9026810654c5240c74a498a06337150d220d290a6810d6d51300c23e6a1262134544c51097aa24210cb1493444352408a041c53290432d41224088474d424842b26b820618932500329b288849866cd240086760a120212f250d110979286810cbd512008342408a041ab2490031ca9886910f14c5240c66ea89886339050d321c690268106c4c5400c7c2418a041a521093109792848085a49704083a2209a02185214d0219792c680863cc5240c74a498a021b14150032cb9928219664c5400c762608a061973445020d920a80194e4143488658a899241371510132cc98228184e540414cb4ea89084395104d0109b8ac6810634d3240838a64a0865c920cd020d498248186c44124042e0a298221675448421c79a24808644c5400c63e6a1a0211f544c431e8986281878441240425e4a1a041705048510962a26490e6cd14008722608a061c5324c521cc98069104bd49344425a4a1a4216525c5021c498248186a482340834a2092021a921500219b288689047cd434082e22b82021c5214d0219c82c6810e64c0348435648a00634f544c832d290c6810cd45434c826e2a1a641a52445030d3192821964441340425a4a20263c9324c120ca992821969493140c25e4a20a6137150d0218e1aa488863109324c74a6292063c932500329da826890e5d51310c63c6a922214d35c9032d4902681078481140823a6a120211d358d020cd9928019634c5240c65a4b1a021395010931ca9a628104b494414c23e6a20243b114c1020c79a6480869c93140c312409a04135150d020cdaa26018474d4404863ea89906537514d120d918a8018cd151314871a68920218d214d021979286808724c1240c3c242a0043a924900318e9ac6810e64d1400870a6292063355110930d49228018ce940340863a6b1a0219934c1020d39022810554d7140c78a439a04335158d020b9aa220084ec1434c8732209a0211f35091109d2808498c7cd4248423e6a20a419934900219692869884e540344872a688a04195214d021e498648184dd51210873264a006554514c931d89022810691052148274a01a2432d250d110d212242886cd511004268a29a241e12148110cc1a260904dd511004272a01a04364524c521cc9a6080856141324c34e488a061aa32500328e9a848885a14121483a262982211d358901096928680865105314c356a890041a910490109ca2e08084ed51300c25a4b12021e110c9010c69a64810e34c9400cad0a498241a11049010d290228104e151204434a64a086598344c110
  | 1 => 0x7c0fc0e0032a986c00040041243008241acc280002a9d0b90c02010027c28156913404002d10c1803010043c06018d8101407b38041402022180a0799c00060100c5e2c438180e05108242c010101000a40002000080281886c00180000006800812005a1540e060000c020c00820000417014161a05c000e030163d51320ca3e6a1a0431d35093109c2a26090744c1140c274a020a656b5448020ca9a62810da141324826e2a12021a924c1010b828262886ac85400875264a0065b24190032c69928219724ca400cb286898a212f250d3109792869084ec143488676a89004195310d310e898c8018cd454404cb92409a0411d3510520c61a264907848640087a262a0063853250432cc98248184ec14340836229820619730450309a8a869104dc5434082aea8988639b3150031d890a8010e3cc1240c31a641a64394344c521ca98a8018cbd51320cb52498206158504c530d8a0c801947cd62404362209a021a920092109b8a8680859145324872e698a041d110cd0108faa26018714c7240c72a608
  | _ => 0
def b6K2 : Nat → Nat
  | 0 => 0x2eb80050e2c18008040840000001404001334940830000001000002f6458300e04813445020e044134c9010924d85048520c8441258d010c44413589010a24d82448110c14853509310c44c5050d221a2498344c110e04c12445030e048134c5020e04c52450031e04853450021e04853490021c14c5250d310a2191324c120e04c32445030a2580344c921a4191314c110a1498414c53098498514c110944d85148110c8485058d02194580514c931a2580424c93192498504c530c44c1150d220c44d115c1010944d85048510e04c52490031a1498344c510e04c72450031a1584424c930c849115c1010a1584344c920a4584344c120c4151314c11098580524c521c24c1250d210c14d125c5021c24813509210e04433449010a14d82448510a4580344c521a14d8414852098498504c510e04c94190032c24c9050d321c14c9150d320a1191324c521c2151324c120c1151324c521c24d125c1020e04c124c5030e0487345002198584524c120e04ca415003298458504c920e04c94150032c8151214811098580514c921a8191214811094458504c930e04413449010c8481158d020e04833445020
  | _ => 0
def b6N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def b6R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt b6K6 (i*4) 4
  | 5 => packedAt b6K5 (i*15) 15
  | 4 => packedAt b6K4 (i*26) 26
  | 3 => packedAt b6K3 (i*37) 37
  | 2 => packedAt b6K2 (i*48) 48
  | _ => 0
def b6I (k h : Nat) : Nat :=
  match k with
  | 6 => 4*((h/1+packedAt b6K6 (4+(h % 1)*1) 1) % 1)
  | 5 => 4*((h/13+packedAt b6K5 (360+(h % 13)*5) 5) % 24)
  | 4 => 4*((h/108+packedAt b6K4 (7852+(h % 108)*9) 9) % 302)
  | 3 => 4*((h/109+packedAt b6K3 (10323+(h % 109)*9) 9) % 279)
  | 2 => 4*((h/37+packedAt b6K2 (3168+(h % 37)*7) 7) % 66)
  | _ => 0
def b6Pos : Nat → Bits
  | 0 => 0x9cf1ddec33efe939e3bbd867dfd273c777b0cf
  | 2 => 0xe73e1ef4ccf7f1ce7c3de999efe39cf87bd333
  | 3 => 0x7cfe0fb0f3bfe0f9fc1f61e77fc1f3f83ec3c
  | 4 => 0xf80fff03f03dfff01ffe07e07bffe03ffc0fc0
  | _ => 0
def b6Neg : Nat → Bits
  | 0 => 0x210044201150224200884022a0448401108045
  | 2 => 0x8420840448844108410808910882108210112
  | 3 => 0x501480810a0480a02901021409014052020428
  | 4 => 0x2a91002a00300055220054006000aa4400a80
  | _ => 0
def b6Atlas : Atlas := ⟨6,rawDecor 29 b6Pos b6Neg, 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0, b6N, b6R, (fun _ _ => 0), b6I⟩
def b7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b7K3 : Nat → Nat
  | 0 => 0x37907510ba617cc36907710
  | _ => 0
def b7K2 : Nat → Nat
  | 0 => 0xb24c120e12044344c110
  | _ => 0
def b7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def b7R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b7K4 (i*4) 4
  | 3 => packedAt b7K3 (i*15) 15
  | 2 => packedAt b7K2 (i*26) 26
  | _ => 0
def b7I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b7K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/5+packedAt b7K3 (90+(h % 5)*3) 3) % 6)
  | 2 => 4*((h/2+packedAt b7K2 (78+(h % 2)*2) 2) % 3)
  | _ => 0
def b7Pos : Nat → Bits
  | 0 => 0x27feaef1b77c27feaef1b77c27feaef1b77c27
  | 1 => 0xdabf333e3ba0dabf333e3ba0dabf333e3ba0da
  | 3 => 0x1cdfc3cfc3c31cdfc3cfc3c31cdfc3cfc3c31c
  | 4 => 0xe0effc0ffc03e0effc0ffc03e0effc0ffc03e0
  | _ => 0
def b7Neg : Nat → Bits
  | 1 => 0x4a42444211044a42444211044a42444211044a
  | 3 => 0x14241814820914241814820914241814820914
  | 4 => 0xa01801a92012a01801a92012a01801a92012a0
  | _ => 0
def b7Atlas : Atlas := ⟨4,rawDecor 27 b7Pos b7Neg, 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaa, b7N, b7R, (fun _ _ => 0), b7I⟩
def b8K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b8K5 : Nat → Nat
  | 0 => 0xae1aac5608800fa65f043e907c30fe43f883e197f32fa21f487e10ff20fc65f8c7e987f10fe63f083e18fe30fc43fcc3f087d31
  | _ => 0
def b8K4 : Nat → Nat
  | 0 => 0xe06048dc00030e804440077ac49706008000405033a45a11008341400020000008003051a00958340002ef21887dc5031bf414c2f0d220bf424c2f45232df340c3b48421bc40486f10532bd34443e8c120fb304c3dc5010df324c6f0d021bf340c378c130bf240c374c530fa3088334c832ee32486f0d020df34043ec1010bd14083b4cb20ed240c6f4d231f721886fcd220dd34042fc5031bf344437cd020df31cc2fc9032ad240c7b48720bd04c86fc1030bf34086f49310f631c42f8d010f110043dcc531dd324c6f90031ed24042d45030bc24042f493309f340837cca32ef21c83bc90109d34086fc9010f714086fcd310df318c6f10520bc424c6fc5220bd24886f8d220dd31cc2f45320bd248c3e88210bd24042bc9030df308c2f4d210dd34082f8d020fb20482f49231bd148c2f10930bf14887b48520bd048c6f8d021bd34c42fc1210bd04ccad50432fb040c378c932bd14cc3e8c110b940086fc9031bc414c2f0d210fa40087ec1020ee32c83d4c510bc34886f45030f7318c7e48020f6318877cd031bd3448274d020bf41483bcc932ed32482fcd121fb10842f10131f521443b49030f910043ecc230be34c43bc9021bf240827cd010ef21483d4c621df34086fd0121bf14ccafc9230de314c674d010bf24442fc9331bd34883b8cb21f510043bc9030bd34c83dc4210b9400caf8d321df314c2fcd031b6410caf49030ba40086fc5330ee21487d88510bd24cc6fc5231f621c42f0d310f5140c2f0d120f930883e48210ef24083b4c921bc34042f49110f9400c6f50021be24c4354c431bf04883dc8521bf048c3a48020bd34086fcd020bd14882b49010be2444364c030bf14043d4c521f930483d8c510bd34c86dc5030bf34887d45020bc404caf49210bc24843d50432bd410caf90432bf248c6fc5232df32cc6f4d230ed320caf41221bf04083d48421be34886fd0132ed32c877cd032b9400c6fc1332bc34442f8d121f930843ec4110fb20882fcd321bf04043e4c030be34842f49220bd34082e90032bc24442bc9010ef20882fc1231df324c2fc5021dd32cc6fd0532be24042fcd032bf140c3bc9031ef328cafc1321bd048cafcd120fa20442f4d010bf34042fc9330dd310c7d90432f920442fcd320bf424c6f50032bf04cc7e90031bf14c82fc1232ef240cbb48020f63148774c930f9400cb948421ee3248374c030dd34087dc5020bd34886bc9031bc24c43e90032bf140827cd021f610442fc9310bf0488774c832be24842fc5230f940086f45332bd34486d45020ad240c2f0d320ba400c6fcd210bf248cbe4c110bc344877ccb30bd400c6f8d320bf404c6f8d120be40087b88120bd240c6fc9210bf24086f4d232f5310c7d48710f531c43dc5030b714082f90032dd32cc2f8d110bd04cc6f45210bc34c87e8c210
  | 1 => 0x12c6120b6c220c09108c92a008000308170600016009b0060a002285e7d01ad8020355914000b2d88c460120830366a070441a0103c080a0a01805740041004000a0782cf2c06e0a43200020d40c040a9cc0c00000644480001f2340700000
  | _ => 0
def b8K3 : Nat → Nat
  | 0 => 0x12611f3509210d29928219650d131443a2219a021a75448421b22926290e3cd1240425e4a1202157544c431979286810ce940424c65a4a1a0216b5448020cc9824818691052148258a899243a12045020d290a6810cd151214431a409a0413b54440109ca8082996948540087286898a431f3510121c69a64810e54413404276a8980613a50105329b8a880994e540424c75649200632c544c920d890a8010cdc54340425e4a20a611f350d010d49248018d5145324c65a4a20a613a500d021d499280194dc54340835242a004399104d010d2122428866d51300c318689924335510d1209c2a26088664c1140c3c24320043e120450209a2a262884b149344423ea899065a72045020c898a8018ce141344874e498a061a521093108e1aa48884ed4134486b6a8980618f544c832d88a6081847cd4340826e2a1a641a12150021d319282196c441240432a621a443a924c1010cc9a48010dc141314425a4a1a221a72445030cc9a608106ac91400c74a6292063b114c1020e290a6810f24c9304826a2a1a44135150d020c61a26490474d63408792419a041b1108d010c69906990f44c53044270a8902211d3509310b42926090554d7140c75464a006558504c930d49004908664c034882760b1a0433b050d321cc1a2608865105314c31a641a641b22150021c8982281863109324c72a64a0865351510132e498648184d14534482720a1a44336510d120d898a8018e9441240438a439a043d13190031c6992821965d51310c74a431a0436754484219792c6808564d7040c362211202170514c1109daa240106c906400ca5a4b1a021953149031a7aa264194dc543408712409a0411f35090108f9ac48084b494348423c6a92221a824481109b8a8691047cd434087422092021893049030cc992801947d51300c366a888021a92450031d2926281865485340872a698a041993450021ca988698847cd441483188499261b24150032c69a64810714c7240c722209a0212d2510131c690a6810ec506400cba2209a0218f3049030d29222818614c9410cb4a498a0631d358d010e299482194bc9434042e22b820212f250d2108e9a8480878441240425ea49a22137514d120d590a8010e60d130482ca4b8a0431f3509110d492608186c481140826e2a120218d31490318e9a88090e5cc1140c352409a041a920450208e9ac4808474d424842e0a2902219b3490021d4904681069481140825e4a1a62164514c9219a2a26290cbc94344435260920618f34c9010cb9a228104e54034086760a1a04199204d020c69a248085c141214438a64a086537544c431c699280196c44134043522092021c930490309ca2e08084e54034487c2418a041b130450309692c4808744c5400c6d24b82041b14150032e4994801966cd1400866a2a1a6419534c5021
  | 1 => 0x2c8040ca96a948f8cc0c1706c790000c1c350c05c00a90084804cf0081416390080802032da7402001f81cd0004704808010a00dc4740041c00614d00026013208d8cff7406400050104c4024038081202010040c1a21af004160700008681182014020d3758c000300c001b0b009d0170080102f303820141c000040209018041000026c8c5400c69a6b9206558504c530b42824290654c5400c71e6292063973250432e29926290cbc94340833262a00633b050d010f090a4088744c3140c270a89824199300d2109a8ac68104dd51210872a608a0611d3509110cc9a608084e9403448792409a041e110c90109c82c6810f44c1140c2760a12021e1215002197aa24210cbd51320cad0a0992413651109309b8ac681047d51310c71a6092061ab544802097aa240104b49434c432a698a021c53149031cd98a8018e6cc9400ca720a1a6431f3509310b9aa22008624c9400ca3a6b1a041c93250032cb9a62810474d4414830a429a043a524c5010979288098e54d1140831a69920213b050d2219baa22008614c5240c66aa22
  | _ => 0
def b8K2 : Nat → Nat
  | 0 => 0x2800e0c01c0000e05000400006003b5102c1001a09e0166400000001d02c14853509310a1191324c521e04c124c5030c2151324c120c849115c1010a1584424c930c44413589010a2191324c120a2580424c931c14c9150d320c8481158d020924d85048520c81512148110a2498344c11098584524c120e04c52450031944d85048510e04853450021e048134c5020c24c1250d21098498504c510c44c5050d221e04c12445030c24813509210a1584344c920e04c32445030c44c1150d220a1498414c530a4580344c521c14d125c5021e04c94150032e0441344901094580514c93198580524c521c24d125c1020c24c9050d32198458504c92094458504c93098580514c921c4151314c110a2580344c921e0485349002198498514c110e04c72450031e04833445020a24d8244811092498504c530a1498344c510e04873450021a14d82448510e04c94190032c14c5250d310e04ca4150032e044134c9010c8485058d021944d85148110a4191314c110a81912148110a14d84148520c1151324c521a4584344c120c44d115c1010e04433449010e04c52490031c8441258d010e04813445020
  | _ => 0
def b8N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def b8R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt b8K6 (i*4) 4
  | 5 => packedAt b8K5 (i*15) 15
  | 4 => packedAt b8K4 (i*26) 26
  | 3 => packedAt b8K3 (i*37) 37
  | 2 => packedAt b8K2 (i*48) 48
  | _ => 0
def b8I (k h : Nat) : Nat :=
  match k with
  | 6 => 4*((h/1+packedAt b8K6 (4+(h % 1)*1) 1) % 1)
  | 5 => 4*((h/11+packedAt b8K5 (360+(h % 11)*5) 5) % 24)
  | 4 => 4*((h/122+packedAt b8K4 (7852+(h % 122)*9) 9) % 302)
  | 3 => 4*((h/117+packedAt b8K3 (10323+(h % 117)*9) 9) % 279)
  | 2 => 4*((h/34+packedAt b8K2 (3168+(h % 34)*7) 7) % 66)
  | _ => 0
def b8Pos : Nat → Bits
  | 0 => 0x9cf1ddec33efe939e3bbd867dfd273c777b0cf
  | 1 => 0xe73e1ef4ccf7f1ce7c3de999efe39cf87bd333
  | 2 => 0x7cfe0fb0f3bfe0f9fc1f61e77fc1f3f83ec3c
  | 4 => 0xf80fff03f03dfff01ffe07e07bffe03ffc0fc0
  | _ => 0
def b8Neg : Nat → Bits
  | 0 => 0x210044201150224200884022a0448401108045
  | 1 => 0x8420840448844108410808910882108210112
  | 2 => 0x501480810a0480a02901021409014052020428
  | 4 => 0x2a91002a00300055220054006000aa4400a80
  | _ => 0
def b8Atlas : Atlas := ⟨6,rawDecor 23 b8Pos b8Neg, 0xfefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8, b8N, b8R, (fun _ _ => 0), b8I⟩
def b9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def b9K3 : Nat → Nat
  | 0 => 0x5a3b885f30ea21bc836905d30
  | _ => 0
def b9K2 : Nat → Nat
  | 0 => 0x344c110c930483848110
  | _ => 0
def b9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def b9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt b9K4 (i*4) 4
  | 3 => packedAt b9K3 (i*15) 15
  | 2 => packedAt b9K2 (i*26) 26
  | _ => 0
def b9I (k h : Nat) : Nat :=
  match k with
  | 4 => 4*((h/1+packedAt b9K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 4*((h/5+packedAt b9K3 (90+(h % 5)*3) 3) % 6)
  | 2 => 4*((h/2+packedAt b9K2 (78+(h % 2)*2) 2) % 3)
  | _ => 0
def b9Pos : Nat → Bits
  | 0 => 0x27feaef1b77c27feaef1b77c27feaef1b77c27
  | 1 => 0xdabf333e3ba0dabf333e3ba0dabf333e3ba0da
  | 2 => 0x1cdfc3cfc3c31cdfc3cfc3c31cdfc3cfc3c31c
  | 3 => 0xe0effc0ffc03e0effc0ffc03e0effc0ffc03e0
  | _ => 0
def b9Neg : Nat → Bits
  | 1 => 0x4a42444211044a42444211044a42444211044a
  | 2 => 0x14241814820914241814820914241814820914
  | 3 => 0xa01801a92012a01801a92012a01801a92012a0
  | _ => 0
def b9Atlas : Atlas := ⟨4,rawDecor 15 b9Pos b9Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, b9N, b9R, (fun _ _ => 0), b9I⟩
def innerK9 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def innerJ9 : Nat → Nat
  | _ => 0
def innerK8 : Nat → Nat
  | 0 => 0xfe4200fd4200fc4208fe3106fd3100fc3106ff2100fe2106fd2100fc2100ff2001fe2000fd2001fc2000ff1001fe1006fd1001fc10
  | _ => 0
def innerJ8 : Nat → Nat
  | 0 => 0x1a1c501c28c08000039c2c53d19a4412e15214b0120c08980015cb582b4e14d2052e483c5088e232420b2c5e50c0d
  | _ => 0
def innerK7 : Nat → Nat
  | 0 => 0x403fe8b10805fd162102ff22c42017e4588403fa8b10805f5162102fe22c4201ff3588402fe6b10817f8d62108bf1ac426dfd3588422fa6b10817f0d62100be1ac420dfd258841afa4b10837b4962106bf8ac426bff0588406fe0b10817f8162100fe82c42017d05884d7f80b1080df016210fffa184201fe430843ffa8610807f10c2100ffa104207fe4208403fa841081ff1082100ff9904207fe320843ffa641081ff0c82106ffa084205fe410841bfa8210817f1042106ff988420df7310840bfc6210837f4c42102fe1884201f4310841bfa4210837d4842106f69084201ff4508402fe8a10817f9142100bf2284201fd4508402fa8a10817f1142100be2284201ff3508402fe6a10817f8d42108bf1a8421ffd3508422fa6a10817f0d42100be1a84207ff250841afe4a10837bc942102ff8a8420d7f1508403ee2a1086ff900210dfe200421bfe300843ffa601086ff0c0210dff100421bfc2008437fc2010837f440210dfe0804205ff5008437fca01080df9402100fea8042017d5008437f8a01080df1402100ffa164007fe42c8003dc8590007f50b2000f6a164007fc42c8123fe8390007f9072048fea0e4001fc41c8127fc6390247f4c72000fe18e4007ff21c8003fc4390247f4872003fe10e4003ff40c8007fc819000ff1032001ff1064003fa20c8007dc419000ff8432001fe8864003fc10c8003fe8b90005fd172003ff22e4001fd45c8002fa8b9001ff1172000be22e4003ff25c8006fe4b9000fbc972000ff8ae40017f15c800ffc2b90035f8572048fe8ae400d7d15c800ff82b9000df4172007ffa2a40017f4548003fc8a90005f9152007fea2a40017d4548003f88a90005f1152007ffa124001fe4248003dc849003ff5092000f6a124001fc4248006fea49010ffd052000ff20a4043fd4148003f88290117f8c52021fe98a4001fc3148087fea290035fd452007ff28a4043fd514801afaa290007f1452000be28a4043ff214801ffc429010ff4852000fe10a4003ff4048007fc809000ff5012001fe20240037f5048007fe4090007ec812001ff1024003ee2048007f8409000fe0812001f61024003fe1048007fa209000ff0412000ff2162001fd42c4003f88588007fccb1046ff196208dfd32c4003f86588037fcc71006fb98e2005fe31c401bfa6388017f0c71000fa18e200dff21c400bfc4388007d8871006fe90e200df521c400bf8438800ffcc31001ff1862003fd30c4007f8618800ffc831001ff1062003fd20c4007f8418800ff8431001fd0862003f610c4003fe6b88005fcd71002ff1ae20117e35c411bfa6b88045f4d71002fe1ae20017c35c4003fe4b88005fc971002ff12e20017e25c4003fa4b88005f4971002fe12e20017c25c4007fe2b8800dfc571001fb8ae2003fd05c4006fa0b88037e41710
  | 1 => 0x7fd0a4200dfa148481ff4190903fa832120ff8c64240fe98c8407ff2190903fa43211fff902423ffe204847ffe20908fff841211fff8424240fe884847ffc1090802fa8b21005fc964200ff8ac84017f159080ffc2b21035f8564240fe8ac840d7d159080ff82b211fffc164201bf82c8407fe0590803fa0b21005f416423ffe02c84037c0590827fc84a1006f909422fffa8a840d7f515081ffca2a117ff5454206bea8a8401fc5150802f8a2a1187f8c5422ffe98a845fff21508bffa42a1007fd414200bfa82845dfe5050806fca0a103ff541422efe28284037c50508bbfc40a1177f081422eff082845ffd10508bbf820a1007f5084200dea108401ad421080ffe4a21005fc944200f79288435fe3110867fa622101ffc844219fe9088407ff511081afea221007f9444200bf2888433fd511081afaa22101ff1444218ff1008431fc201080ffea0210c7f9404201bf2808401fd5010802faa0210c7f1404201be2808431fe1010867fa20210c7f0404200ff2106201fd420c403f88418837f4c43106ee988620dd5310c41bfe4218837dc843106fe9086201ff250c402fe4a18817f8943100fe92862017d250c40bf84a18817fc543106bf8a86211f7150c443fc4018887f0803110ff080620dfd100c41bea2018887f0403102ffa806221fe500c406fca018807f5403100bea806221fc500c406f8a0189b7fd0e2100ff21c426dfd438841ffe8510807f90a2107fea144201fc428841ffe65109b7f8ca2107fe994420dff418840bfc8310837f5062106ff98c4205fe318841bfa6310817f0c62106ff90c420df7218841bde43109aff9022135fe204426bfe30884dbfa61109aff0c22135ff104426bfc20884d7fc2110837f4422106fa884426bfc1088
  | _ => 0
def innerJ7 : Nat → Nat
  | 0 => 0x235c1666f4c0a2a01c54a5c20f0bc63517e49ad36f186750ce85631d882c411163b4652f7ab420877cdd88a2827ca7854b1bc801045fa2147dea3e4f2c58b33e5210736580b148bec5f4c81dbc817ab2855393e5011710c9b2bc92526a8be3b4c5824a50524e61ea1265d4b3ed596e480a996458c8ac899861e06be78c5b9ccb54f805a3b872ede6e00c090cddee7195a2a920ce4c878e8581a22464aa91b32aaa327fd2f2e13311e9e4dbb2780bc14ad5ab8f98b41de11f6480c84c61d1e0ee18a11c5c12c307b3f5e1892d78381aaecaae71d1da0188da9667e7696a0095a5be27a5ec1b5dfd8a5e05f2f0a465632700ad286509ac9123c59cb2c6da281208e90249081ab3160868552ae15b0603e94084b283b60035a2ad0510e9058b751222f19bd08b8904ed2ac42ac4d4f71328e8382d7a2abce37010dee5ac2c19ace12462105ea620a0d89115614e8589efc801e40daaabe734a28243bfc7f4b4a0b9727401d50522e4bac29ac41b753039d73cc64516130994712ae8d0ae7762ca86d2dd2c0bcae3340030dc5b0d1c9955251c0645bc9ba9a0f05728f98e3498255467e2da1a60baf328d10ee8830ab4000a6986bf99d8d92aa4c41ae925923b503a9a6805d2b5b532c32735b630a0ca12ae5111b42f905a38a4c3da9992e0102ab67f391de4fe9cad221e0d178c5e0bb07958175400bc20e1380970d55fe46d9cda49de51c4484d5a63792f912b9175e9015148acb9652676b406918131b3b2094224b55aa4ca7deb4e06c12d12c32d061918b90e56eae60cf8bab455e0c5805106d72f54f2306078bf8933c08691e72b1b037dd494009af51156d89de0e953170218cb9ae114275ce36a9794f1881d9b34cf2380e4860a65f4414750e05ee937a1c3a139545772b72da06622d78af61487b965c9b4f87d25323f2555d6cad5ebe111970da0b3b4212a42c3840a3199192ed4deeacd248dacaed9ad893bca0e1ba3c8088ecc493f530868866b1bb30094751d63406198214371e1b09d2b29d02946c146282abceea8cb7160256408b7c016521195426685619e6acc9808af3b2086e112c2256e1691596bb0d5c860bab94ad5849db760cbc4e308796a5df738c722b35c02643be8957e544100f3a8342c2703f8909a650ec60119c4899781f1028494a42671c86e482c19831b827f5aec85028816be1d2a48f413b3f83d176a861179e44a230bffbb6a784c243350bb13401bb46a24f219216d622d104854adf66a47d29b51c0818cb4087111c5073a1f054352514e4c6490a4c75c1b49c6b780f527b90060b9682468ba0c693e9ac68cfed274065415b1c155d60ae0d1038d1e868d011339e844da2548bbd191510f666345080180320ce959df07e2facd3b157fa6b520bcd6708258fc727c8be0d4d9b44e022b234e821476463ba3c4f8ca5b7f
  | 1 => 0x150a7c00050784104000210102580e2df08900c3f00b0020012080e000e7c5f23803a0022381e01a00c180140020080c830020170088340a8010032f401836c290282221881e0263a00000e008278020010000ee011cf24e0120f8000040800680915703219c090296ea0f96b8250d2000108d60be1b4a50030349c903012000234008235c20000b06a1be12c6701a094004030df0000005982800409000238000030a2829028061980470042a81a80c00f030560600261e816099000028068736200ec318030a63400381f0000004db9500c4041180402c0000501b00403c1200000600002b1c02c0180d80c000014008187500f40b0150680240400001200c1404b03c14c01c1b03404c140013e407c031c71422780013b000a28030000040040f831000010002d6028ce00000009e001698000620003f00f052004000010480940a812008018000004ba00000004024028088d503e01948059888190a780200004402001650004101036ca0c00001f0020140c0053920087e01900400c0034b0000003a966000030000090040080a01e00001019800000064003de0260140081501a120118260360040c00003e009cbc07000030063cf5100080788b09001cb48000040280080a00002c610030040080387100001c028013f603805beb0160080282b00a004000006fc0000080307600400801008010059260040e409001714a55e7a15bd07f08408b69954173438240819eb894a207299390e418db8620e677ab0ebb560834025ae0ce4da52a060a459209dc903256ed8d0b89b68e8692986e06ae8c97d7e7b0d66d61b874f6847e12706e511b992408299a2289a51c8398b8885366d2b6ad820c4a68c33e3041518a2e375a59088221bb859a6cb4298007145d2c0546214e2fe23a7c842b00560fc9cf89503e2b5e0d4a4f963aca1348690a1c5aee5a9005388597e62647c0ec0b8bf62934b74b345e937e39d499c38cc4a36798cae4758701eb343176548ea207694349cca8503c1ae6847c4ca9f9c41494b2d3d362d95f6a8df69d00d2ff81224433266d2db0b9607e22a3c5b52de1f54844030101102bab27a8ce8c35020309533448e3e83eb1e70cdeadfb51239295e22e86cb374a10d03e0eedaa3c00e86a9ec90f222eaa9c47f4eadad2937b6a70550c46e1535d0db4203cce58928b528af28ae2f743e5008fb9e9e6dc2981189b0d7850ce94b9101e9c0989b5611a18e558b1c2eb0f4f6801a80d95d2cb4ff483642a619831d67aebcdd5a74a88786b03c08b60a44360b38f443292d3d8561ca2f40809312b0c8b096f59b1748429e17140b260aa1aadb90ab182eb4ee6ce5504bcb4a8c876d30d45dee98ad4f1af4ec92b9f65769a8b6236950fc0774dc8496a1ed9ab385654a71af2bd121832606024693fa03786b7ea04
  | _ => 0
def innerK6 : Nat → Nat
  | 0 => 0x1bf98525c4006f6614971029bf58525c40a6f5614971001bf18525c400bf6214971002fb88525c400be6214971029fd48525c400bec214971029bfd8125c4006fe604971029bf58125c4006fc604971029fbc8125c40a7ed204971029fe84125c40a7f6104971000dfd1525c400b7e454971000df51525c400b7c454971000dfcd525c400b7e354971000df4d525c400b7c354971050bfd9525c40037f254971002fb89525c400b7c254971002fb09525c400b6c254971029fdc5525c400bf9054971000dfd0d25c40037e434971000df50d25c40037c434971007dfd1925c40167f464971007df91925c40267e464971007df51925c401e7d464971007df11925c40167c464971007dfcd925c40127f364971007df8d925c40227e364971007df4d925c401e7d364971007df0d925c40127c364971007dfd0925c401f7e424971007df50925c401f7c424971007dfcc925c401f7e324971007df4c925c401f7c324971002dfd8925c400b6f6249710359fd8925c40cf7f414971002df90525c40cf7d414971002df10525c40cf7f314971002df8c525c40cf7d314971002df0c525c41427f614971029df98525c40067e6149710299f58525c40a77c6149710019f18525c40cf7f214971002df88525c400b6e214971029df48525c400b7c214971002db08525c40a77f404971029df90125c40a77d404971029df10125c40a77f304971029df8c125c40a77d304971029df0c125c40a77f6049710299fd8125c40067e604971029df58125c40a67d6049710019f18125c40a77f204971029dbc8125c40a77e204971029df48125c40a76d204971029df08125c40a77f104971029df84125c40a77d104971029df04125c40037f430971000df90c25c40037d430971000df10c25c400f7f420971003df90825c400f7d420971003df10825c400f7f320971003df8c825c400f7d320971003df0c825c400b7f410971002df90425c400b7d410971002df10425c400b7f310971048ddcc425c400b7e310971002df4c425c400b7c310971002dd0c425c400b7f210971002df88425c400b76210971002df48425c400f7521097100ddf08425c40377f40097100ddf90025c40377d40097100ddf10025c40377f30097100ddf8c025c40377d30097100ddf0c025c40377f20097100ddf88025c40377d20097100ddf08025c40377f10097100ddf84025c40377d10097100ddf04025c400b7f4609710059fd1825c400b7e4609710029f91825c400b7d4609710099f51825c400b7c4609710029f11825c400b7f3609710049fcd825c400b7e3609710029f8d825c400b7d3609710089f4d825c400b7c3609710029f0d825c400b7f2609710509fc9825c400b6f260971002dfc5825c40d67f160971002ddc5825c40377d06097100d9f41825c400b790609710
  | 1 => 0x1000bf11b25c4002ff36c971046bf8db25c411afd36c971000bf0db25c4006ff16c971050fdc5b25c4006f716c97100afd45b25c4006fc16c971050fbc8325c4143ed20c971050fe84325c4143f610c971050bfd8325c4142fd60c971000dfd1725c400b7e45c971002df11725c40037f35c971002df8d725c40037d35c971002df0d725c400b7e25c971002fb89725c400b6e25c971002fb09725c4143f715c971002fe41725c40037f43c971000df90f25c40037d43c971000df10f25c400f7f42c971003df90b25c400f7d42c971003df10b25c400f7f32c971003df8cb25c400f7d32c971003df0cb25c402b7f41c971002df90725c402b7d41c971002df10725c402b7f31c97100addcc725c400b7e31c97100adf4c725c400b7c31c971000dd0c725c400b7e21c971003dd88725c400b6e21c971002df08725c400b6c21c971003dfd1b25c40167f46c971003df91b25c400f7d46c9710099f51b25c400f7c46c9710039f11b25c400f7f36c9710049fcdb25c400f7e36c9710039f8db25c400f7d36c9710089f4db25c400f7c36c9710039f0db25c40367f26c971050dfc5b25c40067f16c971050ddc5b25c40067716c971050df85b25c400f7d16c971003dd45b25c41437c16c9710019f05b25c41437f40c971050df90325c41437d40c971050df10325c41437f30c971050df8c325c41437d30c971050df0c325c41437f20c971050dbc8325c41437d20c971050db48325c41437e10c971050df44325c41437c10c971050dfd8325c41427f60c971050df98325c41437d60c9710509f58325c41437c60c971000dfd0e25c40037e438971000df50e25c40037c438971007dfd0a25c401f7e428971007df50a25c401f7c428971007dfcca25c401f7e328971007df4ca25c401f7c328971002dfd0625c400b7e418971002df50625c400b7c418971002dfcc625c400b7e318971002df4c625c400b7c318971002dfc8625c40d77e218971002df48625c400b7c218971035dfd0225c40d77e408971035df50225c40d77c408971035dfcc225c40d77e308971035df4c225c40d77c308971035dfc8225c40d77e208971035df48225c40d77c208971035df84225c40d77d108971035df04225c400b7f4689710059fd1a25c400b7e4689710029f91a25c400b7d4689710099f51a25c400b7c468971002dfcda25c40127f368971002df8da25c400a7e368971002df4da25c40227d368971002df0da25c400a7c3689710299f49a25c400b7f16897100d9fc5a25c400b77168971035df41a25c40d67d068971002de41a25c4002ff464971000bf91925c4002fd464971000bf11925c4002ff364971046bf8d925c411afd364971000bf0d925c40d6ff624971002fd90525c40cff5414971033fdcc525c400bf4314971050bfd8525c40a7f6614971
  | 2 => 0x71000fd10e21c4117f7428871000fd90a21c4117f5428871000fd10a21c4117f7328871092fd8ca21c4117f5328871000fd0ca21c40d7f7408871035fd90221c40d7f5408871035fd10221c40d7f7308871035fd8c221c40d7f5308871035fd0c221c40d7f7208871035fd88221c40d7f5208871035fd08221c400bf6458871002fd11621c400bf6358871002fd4d621c400bf4358871035fd41621c40d775058871002fc41621c400bf7468871002fd91a21c400af6468871002fd51a21c4002f5468871002fd11a21c400bf7368871000bdcda21c400bf6368871002fd4da21c400bf4368871002bd0da21c400bf5268871002f949a21c40d7f7068871001bdc1a21c40d7f3068871035fd41a21c400bf1068871002fdd5a21c40d7f6568871035fd55a21c40d775568871035fd15a21c400bde31cd71002fd0c735c400bdc31cd71002f50c735c400bf621cd7100bfd48735c4002ff26cd71000bf49b35c4006ff16cd71052bf85b35c414bf616cd71052bd85b35c40aafd16cd71001bf05b35c414bf416cd71001bd05b35c414bdf30cd71052f74c335c414bfa10cd71052fd84335c414aff60cd71001bf98335c414afd60cd71001bf18335c400b7e35cd71002f78d735c400b5e35cd71002f70d735c400b7e25cd71002df09735c414bf715cd71046df59735c40aafd65cd7102a9f59735c400bf905cd71000df90b35c40037d42cd71000df10b35c40137f32cd71004df8cb35c40137d32cd71004df0cb35c400b7e31cd71002d78c735c400b7c31cd71002d70c735c402f7f21cd71002df88735c402f7d21cd71002df08735c40427f36cd71004dfc9b35c400e7f26cd71004df89b35c40137d26cd710079f49b35c40137c26cd71052dfc5b35c40067f16cd71052df85b35c414a7e16cd71004df45b35c40aa7d16cd71052df05b35c40067c16cd71052dfcc335c414b5f30cd71052df4c335c414b5d30cd71052dfc8335c414b7e20cd71052df48335c414b7c20cd71052dfc4335c414b7e10cd71052df44335c414b7c10cd71052dfd8335c414a7f60cd71052df98335c40067e60cd71052df58335c414a7d60cd71052df18335c40067c60cd71000df90835c40037d420d71000df10835c400b7e310d71002df4c435c40437c310d71002dfc8435c400b7e210d71002df48435c400b7c210d71010dfc8035c40437e200d71010df48035c40437c200d71010dfc4035c40437e100d71010df44035c40437c100d71002dfc9835c400e7f260d71002df89835c400b7d260d710079f49835c400b7c260d71002dfc5835c40de7f160d71002ddc5835c40437d060d710109f41835c400b79060d71002fd90725c402bf541c97100afdcc725c400bf431c971002fd88725c400bee21c971002f988725c400bec21c971000bfd1b25c4002fd46c97
  | 3 => 0xb10029f19542c40c37e3550b1030df4d542c40bb7f1550b102efdc5542c40bb7d0550b102ffe41542c4003bd4210b1000eb50842c4002ff3610b1046bf8d842c411afd3610b103fbfc9842c4003ef2610b1019fdcc442c4067f52110b1006bfd8442c4003f66110b1002bf98442c400af66110b1019fd58442c401afd6110b1006bd58442c400afc6110b1018bfd8042c4006fe6010b1018bf58042c4006fc6010b1018fe84042c4063f61010b101adf8d442c406b7d3510b1003dfd9442c40037e6510b1002bf99442c400a7e6510b1000df59442c4002fd6510b10009f59442c400f7c6510b1002bf19442c40637f1510b1018fdc5442c40637d0510b1019fe41442c411bee32ccb1046f78cb32c4163f541ccb1044fdcc732c4163f521ccb1057f74c332c415ffa10ccb1057fd84332c40237e35ccb1008df4d732c415f7f15ccb1057fdc5732c415f7d05ccb1058fe41732c4002ff46ccb1000bf91b32c4002fd46ccb1015bfcdb32c40b2fd26ccb1046fb49b32c400aff16ccb1006bf85b32c4113f616ccb1006bd85b32c401afd16ccb1002bf05b32c4113f416ccb1001bfc1b32c415efd06ccb1001bf01b32c400aff56ccb1000dfd5b32c400a7f56ccb1004df95b32c4002fd56ccb1000df55b32c40027d56ccb1002bf15b32c40137c56ccb1046fb4c832c411bdd320cb1000bfd1832c4002fe460cb1000bf51832c4002fc460cb1057bfcd832c4003df360cb103cbfc9832c411bef260cb1017fd50432c4113f7310cb1016f78c432c405bdc310cb1017fd48432c401aff610cb1000fd98432c400afe610cb1002bd98432c405ff5610cb1006bf58432c401af5610cb1002bf18432c4006fe600cb1015bf58032c4006fc600cb1015fe84032c4057f6100cb1008df8d432c40237d350cb1003dfd9432c40037e650cb1002bf99432c400a7e650cb1000df59432c4002fd650cb10009f59432c400f7c650cb1002bf19432c40577f150cb1015fdc5432c40577d050cb1017fe41432c4003f6420c71000fd50831c4003f4420c71044fdcc831c411bf6320c71046f58c831c411bf5320c71044fd0c831c4003d4320c71002fdcd831c400bd7360c71002fdc9831c400bf6260c71002fd49831c4002f5260c71002fd09831c4043f7300c71010f5cc031c4043f6300c71010fd4c031c4043d5300c71010fd0c031c4043f7200c71010fd88031c4043f5200c71010fd08031c4043f6600c71010fc98031c4006f6600c71010fd58031c400bf1600c71002fd4d431c402375350c71002f54d431c402355350c71002fd89431c400bf4250c71010fdd9431c400bf6650c71002dd99431c4043f5650c71010dd59431c4006f5650c710019d59431c4043f4650c71010fd41431c404375050c71002fc41431c424bf7438871000fd90e21c424bf54388
  | 4 => 0x145200ddf49851480067d26145200d9f09851480377f40145200ddf90051480377d40145200ddf10051480377f30145200ddf8c051480377d30145200ddf0c051480377f20145200ddf88051480377d20145200ddf08051480377f10145200dddc4051480377d10145200ddd44051480377f60145200ddf98051480377d60145200ddf180514801f7f450852000df914214801f7d450852000df114214803f7e350852007df4d421480037c350852003fb908214801fed42085200ddfd482148087f7310852000fd0c4214801b7f510852006df54421480377c510852003fd4842148087ed210852000bfd18214800efe460852000bf518214800efc460852000bfcd8214800efe360852022bf4d8214800efc360852050bfd58214800f7f5608520509fd582148142ff260852003fbc9821480d6ff160852003fdc5821480377f50085200dfb8802148037f820085200dfb0802148006fe60085200dbf5802148006fc600852007fed17204801ffa45c812007fe517204801ff845c812003fed0b204800ffa42c812003fa90b204800ff942c812007fa50b204800ff842c812001fed4b2048007eb52c812001ded4b204824ffb41c812000fe907204824ff941c812000fe1072048253fa31c812093fe4c72048003f831c812093fed47204801ffa51c812093fe547204801ff851c812003fec87204800ffa21c812003fe487204800ff821c812003fed1b204800ffa46c812003fe51b204800ff846c812001fed5b2048006fb56c812001ded5b20480067b56c812001fec9b2048006fb26c812001fac9b204800ffb16c812003fe85b204800ff916c812003fe05b2048003bf4290b1040fd50642c4103f73190b1040fd48642c40ffef2090b103ffb48242c40fffa1090b103ffd84242c41077e3590b1041df4d642c40ff7f1590b103ffdc5642c40ff7d0590b1040fe41642c40bafd4690b1000bfcda42c411afe3690b1046bf4da42c4062ff2690b1002bfc5a42c4003f71690b1002bdc5a42c401afe1690b1006bf45a42c4103f51690b1006bd45a42c400afc1690b1001bfc1a42c40fefe0690b103fbf41a42c4006fc0690b1002bfd5a42c40037f5690b10029fd5a42c400f7e5690b1000bf55a42c40037d5690b10009f55a42c400afc5690b1003df15a42c411aff6350b1046bf58d42c4002fc6350b1000ef90942c401aff6150b1045fd98542c400afe6150b102ffd58542c401afd6150b1006bd58542c400afc6150b102ffdcc542c40bff52150b1000fed8142c40baff6050b1000bed8142c4006fe6050b102ebf58142c40bbf86050b1001bf18142c4006f86050b102efbc8142c40bbed2050b102efe84142c40bbf61050b1000dfd9542c4002ff6550b10009fd9542c401f7e6550b1002bf99542c401f7d6550b1000df19542c400afc655
  | 5 => 0x21052013dfd484148087f5411052021ef5044148087f7311052021fdd44414801b7f511052006ddd44414801b7d511052055bfd184148087bf461052000bfcd8414808afe361052022bf4d84148002ff561052000dfd5841480027f561052007bf958414800b7e561052007bf55841480037d5610520079f558414800b7c561052003bfc984148003ef261052000bbc98414801efe261052007bf4984148003ed261052007bb49841480eaff161052000fdc58414804f7f501052013fb880414804ff8201052013fb080414804ffa601052001bf9804148006fa601052000fe580414804efd601052000be5804148006fc601052000dfd1431480037e450c52000df51431480037c450c52000fb9083148003ed420c52010dfd483148087f7410c52000fd1043148087dd310c52021f54c43148087f7510c52006dfd44314801b77510c52006df5443148087f7210c52000bfd183148002fe460c52000bf5183148002fc460c52000bfd5831480037f560c520009fd58314801efe560c52002df958314801efd560c52000df558314801e7d560c52002df158314800eff260c52000fbc983148002ef260c52007bf898314801efd260c52000fb498314801eed260c52037bfc58314808bf7160c52010dfd403148043ee200c52010fe0803148043ec200c52010fd4403148043fa600c52001bf9803148006fa600c52000fe5803148042fd600c52000be5803148006fc600c52007dfd1451480037e451452007df51451480037c451452007dfcd451480037e351452007df4d451480037c351452000fb908514801fed421452021fdd045148003f4411452021fdcc45148003f4311452021fd54451480877d511452021dd544514801ff6211452021fd4845148002ff461452000bf9185148002fd461452000bf1185148002ff361452022bf8d8514808afd361452000bf0d85148142ff561452021dfd5851481427f561452001bf8985148006fd26145200dbf098514801ff716145200dfb8805148037f820145200dfb0805148037f710145200dfd4405148006fe601452001bf18051480037f431452000df90c51480037d431452000df10c514801f7f421452000df908514801f7d421452000df108514801f7f321452000df8c8514801f7d321452002dfd04514808777411452002df904514800b7d411452002df104514800b74411452002dfcc4514808777311452002df8c4514800b7d311452002df0c4514800b74311452002df884514800b76211452002df484514808775211452002dfd1851480167f461452002df918514800a7e461452002df51851480267d461452002df118514800a7c461452002dfcd851480127f361452002df8d8514800a7e361452002df4d851480227d361452002df0d8514800a7c361452002dfc9851480377e26
  | 6 => 0x20909202ebf51a424800fbd469092018bfd5a424800f7f5690920189fd5a4248062ff269092000bfc5a424800efe169092021bf45a4248006ff06909203fbf81a42480fefd069092001bf01a424801fef459092005dbd1642480ffee459092007fb5164248003ec459092005db116424820bef419092082fb506424820fee319092082fb4c6424820bef519092007fb946424820bed51909203ffbd0242480ffee40909203ffb50242480ffec40909203ffbd4242480ff6f50909203ffb84242480ffed10909203ffb04242480baed469092000fbd5a4248062ef569092000dbd5a4248003ef169092003fb85a424820bed169092003fb05a42480ffef069092001bbc1a42480ffee06909203ffb41a42480ffec069092001bb01a424801fef645092007ebd9142480bbec65509202edb1954248006ec6550920019b195424801fef455092005dbd15424801fee455092007eb915424801fec455092005db115424801fac455092000cb11542481ffef615092007fb98542481ffed615092007fb18542481ffef41509207ffb5054248203ee31509207ffb4c542481ffef515092007fb94542481ffed51509202efbd81424801feb60509202efb9814248006ee60509202efb58142480bbec60509202efa1814248006ec605092001ba18142480bbef40509202eebd0142480bbee40509202efb50142480bbad40509202efb10142480bbef50509202edbd4142480bbee10509202efb44142480bbec105092005dfd1442480277e451092007df51442480637c451092007fb508424800fbd421092007eb50842480637f521092059bfd18424800fbf46109203fbfd58424800f7f56109203f9fd5842480feff261092003fbc9842480feef261092019dfd4442480677d511092003bfd844248002fe611092021bf58442480637f501092018fb8804248063f8201092018fb0804248063e8201092018bfd804248006fe601092018bf5804248006fc601092005dfd1641480277e459052000ef91641480273e459052009df51641480177c459052000ef11641480033c45905203bdf8d641480ef7d359052023fb90a414808fed42905203adfd4a4148087f7419052021efd06414801b7f519052006df54641480eb7f50905203afb88241480ebf820905203afb08241480ebf510905202bbf51a4148087bd469052000bfcda414808afe369052022bf4da4148002ff569052000dfd5a41480027f569052007bf95a414800b7e569052007bf55a41480037d5690520079f55a414800b7c569052003bfc9a414801efe269052007bf49a414804eff169052001bfc1a41480eafd069052001bf01a41480177f451052009df9144148003be451052000cf91441480177c451052000ef11441480173c451052014df8d441480537d351052000fb9084148003ed4
  | 7 => 0xc16d152059df41b45480177906d152007dfd16454801fbf459152007cfd16454801fbf429152007ef50a45480037f519152007df946454801f7d51915203fefd0245480ffbd40915203ffb88245480fff820915203ffb082454801fbd4691520189fd5a4548006fe26915203ffb89a4548006fd269152000bfc5a4548086fe169152021bf45a454801f7f429152007cfd0a454801f7d429152007cf50a45480277f419152009df50645480037e319152000df4c645480037f219152007df886454801f7d21915203fdfd0245480ff3f40915203fdf50245480ff3d40915203fdfc8245480ff7e20915203fdf08245480ff7f10915203fdf84245480ff7d10915203fdf04245480ba7d46915203fdf89a45480067e26915203fdf49a45480067d269152009dfc5a454800a7f169152009df85a454801a7e169152009df45a454801a7d169152009df05a45480ff7f06915203fdf81a45480ff7d06915203f9f41a45480ff7c069152007dfd89454801f6f62515202edf509454801f7f615152007ddd85454801a7f6151520069dd85454801f7e615152007df585454801a7d615152007df185454801f746151520029f185454800274615152000df8c545480037d315152007dfc85454801f7d21515202edfd81454801f7b60515202e9fd8145480bb7f20515202edf88145480bb7d20515202edf08145480bb7e10515202edf44145480bb7c105152007df514454801fbd451152007cf5144548166ff461152007efd1845480feff561152000dfd5845480fe7f561152007efd08454801fbd421152001bfd884548063ed621152001bf58845480037f511152007df944454801f7d511152021bfd844548002fe611152021bf5844548063bf401152018ef5004548006fe601152001bf1804548063ee201152018fe0804548063ec201152005dfd1845481667f461152005cfd1845480177f421152005cfd0845480177d421152007cf50845480637f6211520019fd8845480fe7e621152018df58845480636d6211520019f58845480627c621152005dfd0445480177d411152000df8c445480037d311152005dfd8445480167f611152005df984454800a7e611152005df584454801a7d611152005df18445480037f211152007df884454801f7d211152018dfd0045480633f401152018df50045480633d401152018dfd8045480627f601152018df98045480637d6011520189f58045480637c601152018dfc8045480637e201152018df48045480637c201152018dfc4045480637e101152018df44045480637c101152005dfd1642480ff7e459092007df51642480177c459092007fbd0a424800fbf42909203fdfd4a42481037f519092040df546424800fef219092007fb886424820bed21909203fdfd4242480ffee20909203ffe08242480ffec
  | 8 => 0x7d60517202edfd0145c80bb3f40517202edf90145c80bb7d40517202ecf50145c80bb7c40517202edfc8145c80bb7e20517202edf48145c80bb7c20517202edfc4145c80bb7e10517202edf44145c80bb7c105172003df90845c800f6e421172003df50845c800f3d421172000cb50845c80637c421172000df8c445c80037d311172000df0c445c800f7f211172003df88445c800f7d211172003df08445c80637f201172018df88045c80637c201172018df84045c80637d101172018df04045c800f7f26117203f9fc9845c800f6f261172003dfc5845c800a7f161172003df85845c800e7e161172003df45845c801a7d161172003df05845c80637d061172003de41845c800fee42c572000fb50b15c800ff721c572003fd08715c80d7fa20c572035fb88315c80d7f710c572035fd44315c8002ff46c572000bf91b15c8002fd46c572000bf11b15c8002ff36c572049bf8db15c8126fd36c572000bf0db15c8006ff26c572035bf89b15c80a6fd26c572001bf09b15c8006ff06c572035bf41b15c8006fc06c572000dfd1715c800f7e45c572000df51715c800f7c45c572000dfcd715c800f7e35c572000df4d715c800f7c35c572035fbc9715c800f7e15c572003fd85715c800f7615c572003fd05715c81237d65c572029bf59715c80a67d65c572000dfd0f15c80037e43c572000df50f15c80037c43c572000dfd0b15c800f7e42c572000df50b15c800f7c42c572000dfccb15c800f7e32c572000df4cb15c800f7c32c572002dfd0715c800b7e41c572002df50715c800b7c41c572002dfcc715c800b7e31c572002df4c715c800b7c31c572002dfc8715c800f7721c572002df08715c800b7421c572035dfd0315c80d77e40c572035df50315c80d77c40c572035dfcc315c80d77e30c572035df4c315c80d77c30c572035dfc8315c80d77e20c572035df48315c80d77c20c572035dfc4315c80d77710c572035df44315c80d77510c572002dfd1b15c80167f46c572002df91b15c800a7e46c572002df51b15c80267d46c572002df11b15c800a7c46c572002dfcdb15c80127f36c572002df8db15c800a7e36c572002df4db15c80227d36c572002df0db15c800a7c36c572035dfc9b15c80067f26c572035df89b15c80d67e26c572002df49b15c80d77c26c572035dfc1b15c80d77e06c572035df41b15c80d77c06c572059dfd0b45480177d42d152005dfd0745480177d41d152000df8c745480037d31d152007dfc87454801f7e21d152007df48745481677f40d152059df90345481677c40d152059dfc8345481677e20d152059df08345481677e10d152059df44345481677c10d152005df49b45480ba7d26d152005db49b45480177f16d1520029fc5b45480177e16d1520059f85b45480177d16d1520069f45b45480177
  | 9 => 0xb7e150c72011fd85431c801b76150c72006df45431c8047f4150c72002dfd9431c80037e650c72003bf99431c800e7e650c72000df59431c8002fd650c720009f59431c800b7c650c72003bf19431c80437d050c72003fb90a21c801fed428872003fdc8621c800fef218872035fe88221c80d7ee208872035fd44221c800f7e358872036df4d621c80d77f258872035fbc9621c800f7e158872003fd85621c800f76158872006df45621c800ff4158872000bfd1a21c801efe468872000bf51a21c801efc468872000bfcda21c801efe368872049bf4da21c801efc368872048fb49a21c800ff7168872001bfc1a21c8006fc068872029bf55a21c802b7d5688720299f55a21c800fee42d172003ef90b45c800fae42d172003ef10b45c8006ff26d172059fbc9b45c8006ef26d172000fb49b45c8006fc26d172000bfc5b45c8122fe16d172048bf45b45c8167bf40d172059ef50345c8167fa20d172059fb88345c8166fd60d172003df91745c800fbe45d172003cf91745c800fbc45d172059fbc9745c800f7e15d172000df45745c800f7c15d172003df90b45c80176e42d172003cf90b45c800f7c42d172003cf10b45c80177f41d172005df90745c80177d41d172005df10745c80037e31d172000df4c745c80037c31d172003dfc8745c80037e21d172000df48745c800f7c21d172059dfc9b45c80067f26d172059dbc9b45c80066f26d172059df89b45c80177d26d172005db49b45c81677c26d1720019f09b45c80177f16d1720029fc5b45c80177e16d1720059f85b45c80177d16d1720069f45b45c80177c16d172059dfd0345c81673f40d172059df50345c81673d40d172059df88345c81677d20d172059df08345c81677f10d172059df84345c81677d10d172059df04345c81677f60d172059df98345c81677d60d172059df18345c8166ff62517202efb98945c8006fe625172001bb98945c80bafd625172001bf18945c800fee425172003ef90945c800fae42517202efb50945c800fbc425172048bfd8545c8122fd615172000bf18545c80baff605172001bf98145c8006fc60517202eefd0145c80bbbd40517202efe88145c80bbee205172059bfd9545c80037f455172003ef91545c800f7c455172003ef11545c800f3c45517202efbc9545c800f7e155172000df45545c800f7c15517202edf98945c80ba7d62517202edf18945c80067c625172009dfd0945c800f7e425172003cf90945c80bb7d425172003df10945c800f3c425172009dfd8545c801a7f615172009df98545c80277d6151720069f58545c80277c6151720029f18545c80277f415172009df90545c80277d415172009df10545c80037e315172000df4c545c80037c315172003dfc8545c80037e215172000df48545c800f7c21517202edfd8145c80bb
  | 10 => 0xffee1090b203ffb44242c80ffec1090b2003fb85642c800fed1590b2003fb05642c800fef1690b2003fb85a42c800fed1690b2003fb05a42c80ffef0690b2001bbc1a42c80ffeb0690b203ffb41a42c800fe90690b2003fbd5a42c80ffee5690b203ffb55a42c80ff6d5690b203ffb15a42c801fef4250b2003ef90942c800fec4250b2003ef10942c800fac4250b2048bfd8542c8122fd6150b2000bf18542c800fef2150b2096fb48542c800fec2150b2001bf98142c8006fc6050b202efe88142c80bbee2050b2007dfd9542c8166ff6550b20599fd9542c800fbe4550b2003ef11542c80bb7f2550b202efbc9542c800f7e1550b202fdf45542c800fef6450b2003ebd9142c825bef6150b2007fb98542c825bed6150b2000fb18542c825bef4150b2096fb50542c825fee3150b2096fb4c542c80bbef6050b202efb98142c8006ee6050b202efb58142c80bbec6050b2001bb18142c80bbef4050b202eebd0142c80bbee4050b202efb50142c80bbec4050b202efb84142c80bbed1050b202efb04142c8003ef6550b2000dbd9542c8166ef6550b2003fb91542c800fae4550b2003fb11542c800fac4550b2003fb85542c825bed1550b2003fb05542c812bee42907204afb50a41c8123f7419072048efd0641c80ebfa20907203afb88241c80ebf510907203bdf8d641c80ef7d35907203adfc9641c80ebef259072006df85641c801b7d15907202bbf51a41c8123bd469072000bfcda41c8126fe369072049bf4da41c800eff269072007bf49a41c800efc269072001bfc1a41c80eafd069072001bf01a41c800eff569072000dfd5a41c800e7f569072002df95a41c8002fd569072000df55a41c80027d569072003bf15a41c800b7c569072000fb90841c8003ed421072048fd50441c8123bd411072048fdcc441c8156ff461072048efd1841c8002ff361072049bf8d841c8126fd361072003bfc9841c8003ef261072003bbc9841c801efd261072000fb49841c8002ed261072003bf09841c8003f7161072013fe88041c804fee201072001bf98041c804efd601072001bf18041c80537e351072014df4d441c804f7f251072013fbc9441c801b7e151072006df45441c800b7f651072000df99441c800efe6510720039f99441c80037d651072000bf59441c80027d651072002df19441c800efc651072000fb90831c8003ed420c72048fdd0431c8003f4410c72048f74c431c8123d5310c72011fdc8431c8047f4210c72000bfd1831c8002fe460c72000bf51831c8002fc460c72003bfc9831c8003ef260c72003bbc9831c801efd260c72000fb49831c8002ed260c72003bf09831c80deff160c72049fdc5831c8043fa200c72010fb88031c8043f5100c72001bf98031c8042fd600c72001bf18031c80437f250c72010fbc9431c801
  | 11 => 0x597f543c542100fd10f150840ff742c542103fd90b150840ff542c542103fd10b150840ff732c542103fd8cb150840ff532c542103fd0cb150840bf745c542102fd917150840bf545c542102fd117150840bf735c542102fd8d7150840bf535c542102fd0d7150840bf725c542103ddc97150840be725c542164fd9031508593f440c542164fd8c31508597f530c542164fd0c31508593f620c542164fd083150840bf750c542164fd9431508593f450c542102fdd1b150840bf646c542102fd51b150840bf446c542102fdcdb1508402f736c542102fd8db150840bf536c542102fd0db150840af436c542102fd49b150840ef526c542102f949b150840bf556c542164fdc1b150840bf606c542102fd41b1508593f406c542100bf9195008402fc46540210fbf8d9500843efd365402100bf0d9500840eff26540210dbf0995008487f7315402102fd0c5500840ff5215402102fb4855008436ff61540210dbf58550084037f455402102df91550084037d455402102df11550084037f355402102df8d550084037d355402102df0d5500840bef25540210dbfd9550084067f655402102fdc555008437fa40540210dfe8c15008403f9305402103fec815008437f8205402102fec415008437f8105402102fed4150084377e50540210dfe14150084377c50540210dde14150084037f435402100df90d50084037d435402100df10d50084037f425402103df90950084037d425402103df10950084037f325402103df8c950084037d325402103df0c950084037f465402100df91950084267e465402100df51950084037c4654021059f11950084037f365402100df8d950084227e365402100df4d950084227d365402100df0d950084127c365402103dfc9950084377c26540210d9f09950084877f415402102df90550084877d415402102df10550084877f315402121ddcc5500840b7e315402121df4c5500840b7c315402100dd0c5500840f7f215402102df885500840376215402121df48550084877521540210ddf085500840b7e6154021019f58550084377e40540210dde90150084377c40540210ddf8c150084377a30540210ddf4c150084037930540210ddf0c150084377f205402103dec8150084377e20540210ddf08150084377820540210ddfc41500840b7b10540210ddf84150084377d10540210ddf041500843778105402103fb90b42c800fbe42d0b2059fe88342c8167ee20d0b2003ef91742c800fbc45d0b2059dfc9742c8167ef25d0b2003df85742c816b7d15d0b2003efd1b42c8002ff16d0b2048bf85b42c8122fd16d0b2001bfc1b42c8006fc06d0b202ebf55b42c801f7d56d0b202e9f55b42c8267ef4190b2099fb50642c826bee3190b2099fb4c642c80ffef4090b203ffb90242c80ffed4090b203ffb10242c80
  | 12 => 0x840b7e101142102df440450840b7c101142102dfd80450840b7e601142102de98045084067e6011421019e980450840b7d601142102de58045084027d6011421009e580450840b7c6011421019f1804508403de43cd4210ff750f350840fde32cd42103f70cb350840bde31cd42102fd0c7350840bdc31cd42102f50c7350840ff521cd42102fb48735084037f45cd42102df91735084037d45cd42102df117350840b7e35cd42102f78d7350840b5e35cd42102fbc97350843fdd30cd42102dfd4335084037e50cd42102df1433508402ff46cd42100bf91b3508402fd46cd42100bf11b350840bdf36cd42103bfc9b350840efe26cd42103bf49b350840efc26cd42102bfc5b350840afe16cd4210efd85b350841af616cd42102bf45b350840afc16cd42102fd05b350840afd56cd4210fdf55b35084b67d56cd4210dbfc1b3508402fd06cd4210dbf01b35084137f43cd42104df90f35084135e43cd42104df50f350843f5d43cd42104df10f35084037f42cd42103df90b35084037d42cd42103df10b350840f7e32cd42103d78cb350840f7c32cd42103d70cb35085637f41cd42102df90735085637d41cd42102df107350840b7e31cd42102d78c7350840b7c31cd42102d70c7350840f7f21cd42102df88735085637d21cd42102df08735084037e40cd42100df10335084137e30cd42104df4c3350843f5d30cd42104df0c3350840f7f20cd42100df883350840f7c20cd42102dfc4335085637e10cd42158df443350840b7c10cd42104dfd1b35084167f46cd42104df91b35084127e46cd42104df51b35084267d46cd42104df11b35084127c46cd421029fcdb350840f7f26cd421039fc9b35084137e26cd42104df49b350840f7c26cd421039f09b350840b7f16cd421029fc5b35084137e16cd42104df45b350840b7c16cd421029f05b35084137f06cd421019fc1b35084137e06cd42104df41b35084027d06cd42104df01b35084067c06cd42103dfd08350840f7e420d42103df508350840f7c420d42102dfd04350840b7e410d42102df504350840b7c410d42102df8c4350840b7d310d42102df0c4350840b7f210d42102df884350840b7d210d42102df084350840b7f460d421059fd18350840b3f460d421008fd18350840b7e460d421029f918350840b7d460d421099f518350840b3d460d421008f518350840b7c460d421029f118350840b7f260d421039fc98350840b6f260d42102dfc58350840a7f160d42102ddc5835084037e400d42100df100350840f7e200d42103df080350840b7e100d42102df440350840b7c100d42102dfd80350840b7e600d42102de98035084067e600d421019e980350840b7d600d42102de58035084027d600d421009e580350840b7c600d421019f1803508597f743c542100fd90f1508
  | 13 => 0x840b7f219142102df886450840b7d219142109df90245084277c409142100df8c245084037d309142100df0c2450840f7e209142103df082450840b7e109142102df442450840b7c10914212f9f51a450840b7f3691421049fcda450840b7e3691421029f8da450840b7d3691421089f4da450840b7c369142102dfc9a450840e7f269142102dbc9a450840b7f1691421029fc5a450840b77169142102dfc1a45084067f069142102df81a450840b7d0691421009f41a450840b7c0691421019f01a450840aff64514210fbfd8d450843efd635142100bf18d4508403bf435142100ef50d450840eff625142103bf989450840efd625142103bf189450840fbe425142103ef109450840aff615142102bf985450840afd615142102bf185450840bbe415142102ef10545084bff7315142102fd0c5450840ff5215142102fb485450840aff655142100dfd15450840bbe455142102df115450840bbc455142102cf115450840b7e355142100df4d5450840b7c355142102fbc954508402ff60514210dbf9814508436fc605142102dfd4145084037e505142102df141450840b7f645142102cfd91450840a7f645142109dfd8d45084227f635142109df98d45084277d6351421089f58d45084277c6351421049f18d45084277f435142100cfd0d45084277e435142109df50d45084273d435142109df10d450840f7e6251421039f989450840f7c6251421039f18945084277f425142103df909450840f3e42514212fdf509450840f7c425142103cf10945084037f325142103df8c945084037d325142103df0c9450840b7e6151421029f985450840b7c6151421029f18545084bf7f415142102df905450840b3e41514212fdf505450840b7c415142102cf10545084bf7f315142102df8c545084bf7d315142102df0c5450840f7f215142102df88545084bf7d215142102df08545084277f6051421009fd8145084277e6051421019f98145084277d605142109df18145084067c605142109df90145084277c405142100df8c145084037d305142100df0c1450840f7f205142100df881450840f7c205142102dfc4145084bf7e10514212fdf441450840b7c105142103df908450840f7d421142103df108450840f7f321142103df8c8450840f7d321142103df0c8450840b7f311142119ddcc4450840b7e311142102df4c4450840b7c311142102dd0c4450840b7f211142102df884450840b7d211142102df084450840b7f3611421049fcd8450840b5f36114210097cd8450840b7e3611421029f8d8450840b7d3611421089f4d8450840b5d361142108974d8450840b7c361142102dfc98450840e7f261142102dbc98450840b7f1611421029fc58450840b77161142100df8c045084037d301142100df0c0450840f7e201142103df080450
  | 14 => 0x2084b67d56cc8210dbfc1b3208402fd06cc8210dbf01b320843ff7430c4210ff5d0c310843bf6430c4210ffd50c310843bf4430c42100f510c3108403f7420c42111fd9083108403f5420c42111fd108310843bf7320c42111fd8c83108447d6320c4210ffd4c83108447f4320c42111f50c8310840bf7460c42102fd918310840bf5460c42102fd118310840bf7360c42102f5cd8310840bf7260c42102f9c98310840bf5260c42107bd498310840be5260c42100b9498310840bf6450c42102fd114310840bf5350c42108dd4d4310840bd5350c42108d54d4310840bf7250c42106ddc94310840be7250c42102fdd94310840bf6650c42102dd994310840bf5650c42102dd594310840af5650c421089d594310840bf4650c4215ffd900310857ff4400c4215ffd8c0310843ff5300c4210ff54c0310857ff4300c4215ffd880310857ff4200c42102fdd80310857ff6600c42102fd580310857ff4600c42102fdd40310857ff6500c4215ffd1403108403bf43d142100ef50f450840fbe42d142103ef10b450840bbe41d142102ef107450856bf731d142102fd0c7450840ff521d142102fb487450840b7e45d142102ef917450840b3e45d142102df8d745084037d35d142102df0d7450840bef25d142102dfd4345084037e50d142102df143450840bbf46d142100bfcdb450843efe36d14210fbf4db450840eff26d142103bf09b450840aff16d14210dbfc1b4508402fd06d14210dbf01b45084177f43d142105cfd0f45084177e43d142105df50f45084033d43d142105df10f450840f7e42d142103cf90b450840f7c42d142103cf10b45084037f32d142103df8cb45084037d32d142103df0cb450840b7e41d142102cf907450840b7c41d142102cf107450856b7f31d14215addcc7450840b7e31d14215adf4c7450840b7c31d142100dd0c7450840f7f21d142102df887450856b7d21d142105df90345084177c40d142100df8c345084037d30d142100df0c3450840f7f20d142100df883450840f7c20d142102dfc43450856b7e10d14215adf443450840b7c10d1421029fd1b45084177f36d1421049fcdb45084177e36d1421059f8db45084177d36d1421089f4db45084177c36d142103dfc9b450840e7f26d142105df89b45084177d26d142103df09b450840e7c26d142102dfc5b45084177e16d142105df45b450840b7c16d142105dfc1b45084067f06d142105df81b45084177d06d1421009f41b45084177c06d1421019f01b45084277f439142109df90e45084277d439142109df10e450840f7f429142103df90a450840f7d429142103df10a450840f7f329142103df8ca450840f7d329142103df0ca450840b7f419142102df906450840b7d419142102df106450840b7f319142102df8c6450840b7d319142102df0c645
  | 15 => 0x5885237d414162102df10505885237f314162102df8c505885237d314162102df0c505885237f214162135df88505885237d214162102df08505884037f464162100df91905884267e464162100df51905884037c4641621059f11905884037f364162100df8d905884227e364162100df4d905884227d364162100df0d905884127c364162135df89905884d67e264162148df499058840b7f164162135df90105884d77c404162135df8c105884d77d304162135df0c105884d77e204162135de88105884d77d204162107de48105884d77c204162135dfc41058840b7b104162135df84105884d77d104162135df04105884d77810416210ff7d0e430843fbf4390c210efdcc6430850ff52190c2143fb48643084237e3590c2108df4d6430843fdd3590c2108d74d6430850f7f2590c2143fbc96430850f7f1590c210ff74c2430850b7e5090c2142df14243084cafd4690c210fef51a4308476ff3690c2103bfc9a430841efd2690c2102bfc5a430841afe1690c2106bf45a430840afc1690c2102bfd5a43084037f5690c21029fd5a43084137e5690c2100bf55a43084037d5690c21009f55a430840afc5690c2104df15a4308436ff0690c2100bf41a4308436fc0690c211cf78c44308477f52110c211dfb48443084237e3510c2108df4d4430840afe6510c2100bf59443084027d6510c2102bf19443084777f2510c211dfbc9443084777f1510c211bdf940430846f7c5010c2103fb90b420840fbe42d08215afdcc7420840ff521d08215afb487420840f7e35d08215bdf4d7420840f7f25d082103fbc97420856b7f15d082169fb88342085a7ec20d082159df94342085677c50d082103bfd1b420840fbf46d082100bfcdb420841efe36d08210fbf4db420841afe16d082106bf45b420840efd56d082107df55b42084be7d56d08210dbfc1b4208402fd06d08210dbf01b420840eff64508210fbfd8d420841efd635082100bf18d420841fef425082103ef909420840fec425082103ef109420840fac425082103fb0c9420841aff615082106bf58542084bff7315082103fd48542084bfed21508212ff9485420841f7f655082103bfd95420856a7f655082103df8d542084c37d355082103dfc95420840fef25508212fdfc554208402ff60508210dbf9814208436fc60508212edf94142084bb7c505082103fb90b320841fed42cc82103fb8cb320840fde32cc8210efdcc7320840ff521cc82158fb487320840f7e35cc82108df4d7320840f7f25cc82103fbc9732085637f15cc8210ff74c332085a3ee20cc82168fb083320855f7e50cc82157df1433208402ff46cc82107bf91b3208402fd46cc82103bfcdb320841fed26cc82106bf85b320843bf616cc82106bd85b320841afd16cc8210efd05b320840efd56cc82107df55b3
  | 16 => 0x1458840b7c105162100bfd1b3588402fe46cd62100bf51b358841fdf32cd62107f74cb358841aff62cd62106bf58b358840bde31cd62102f70c7358840aff61cd62102bf587358845ff721cd62102fbc8735884d6fe60cd62100bf58335884d6fc60cd62117fd44335884037f45cd62102df91735884037d45cd62102df117358840b7e35cd62102f78d7358840b5e35cd62102f70d735884db7d65cd62102bf59735884fa7d65cd62102fb49735884037f05cd62102df817358840b7c05cd62104dfd0f35884137e43cd62104df50f35884137f46cd621059fd1b35884137e46cd621049f91b35884137d46cd621099f51b35884137c46cd62107dfd0b35884037e42cd62107df50b35884037c42cd62104dfccb35884135f32cd62104df4cb358841f5d32cd62104dfd8b35884127f62cd62104df98b35884137d62cd621069f58b358845f7f41cd62102df907358845f7d41cd62102df107358840b7e31cd62102d78c7358840b7c31cd62102d70c735884137f61cd62104df587358840b7c61cd62117dfc87358845f7721cd62102df887358845f7d21cd62102df08735884037e40cd62100df10335884137e30cd62104df4c335884137c30cd62104dfd8335884137e60cd621019f98335884137d60cd621009f58335884137c60cd621019f183358841f7e20cd62107df48335884037c20cd62102dfc43358845f7e10cd62117df443358845f7510cd62102df043358841f7f420d62107df908358841f7d420d62107df108358840b7f410d62102df904358840b7d410d62102df8c4358840b7d310d62102df0c4358840b7f210d62158ddc84358840b7e210d62102df48435884037e400d62100df100358841f7e200d62107df080358840b7e100d62102df440358856375100d62102df040358840b7f460d621059fd18358840b7e460d621029f918358840b7d460d621099f518358840b7c460d62102df49835884b67d260d62102db498358840b7f160d62102ddc58358840b7f060d621019fc18358840b7e060d62102df41835884027d060d62102df01835884067c060d62148fdc85058840bef214162100bf9190588402fc464162136bf8d905884dafd364162100bf0d905884d6fe264162106bf499058840bf7164162135bf85905884d6fd164162135fe881058841ff9204162102fec4105884d7f5104162135fe04105884037f454162102df91505884037d454162102df11505884037f354162102df8d505884037d354162102df0d5058840bed254162135bfd9505884067f654162135dfc15058840bfa054162135df01505884d7f8054162135de01505884037f434162100df90d05884037d434162107dfd0905884037e424162107df50905884037c424162107dfcc905884037e324162107df4c905885237f414162102df905
  | 17 => 0xdb45884177f42d162105cfd0b45884177d42d162107cf50b458841f7f32d162100df8cb458841f7d32d162105dfd8b45884177e62d162105df58b458841a7d62d162105df18b458840b7e41d162102cf907458840b7c41d162102cf10745884677f31d162102df8c745884677d31d162102df0c745884177f61d162102df98745884177d61d162102df18745884677f21d162119df487458840b7c21d162105df90345884177c40d162100df8c345884037d30d162100df0c345884177f60d162105df98345884067e60d162105df58345884027d60d162105df18345884067c60d162107df883458841f7d20d162100df083458840b7f10d162119df84345884677d10d162102df043458841f7e42916212fdf50a458841f7c429162107dfcca458841f7e329162107df4ca458840b7f319162102df8c6458840b7d319162102df0c6458840b7f219162102df48645884037e309162100df4c245884037c309162107df882458841f7c209162102df842458840b7d10916212fdd442458840b7c109162102dfcda45884127f369162102df8da458840a7e369162102df4da45884227d369162102df0da458856a7d269162102dfc5a458840b77169162102dfc1a45884067f069162102df81a458840b7d0691621009f41a458840b7c0691621019f01a458840aff645162136bfd8d45884dafd635162100bf18d458841aff625162103bf989458841afd625162103bf189458841fbf425162107ef509458840aff615162102bf585458840afc615162102ef905458840bbc415162140fdc85458840bef215162100bfd8145884d6fe605162135bf1814588503f5105162102bfd9545884037f455162102ef915458840b7c455162102ef115458840b3c455162102df8d545884037d355162102df0d5458840bed255162100dfc15458840b7e055162102df015458840b7f645162102cfd9145884277f6351621089fd8d45884277e635162109df58d45884227d635162109df18d45884127c635162109dfd0d45884277e435162109df50d45885037f6251621069fd8945885037d6251621069f589458841f7f425162107cfd0945885037e425162107df509458841f3d425162109df109458841f7f325162100df8c9458841f7d325162102df985458840b7c615162140dfd05458840b7e415162102cf90545885037d415162102df105458840b3c415162140dfcc5458840b7e315162140df4c5458840b7c315162140dfc85458840b7e215162140df485458840b7c215162109dfd8145884027f605162109df98145884067e605162109df58145884277c6051621019f18145884277e405162109df10145884037e305162100df4c145884037c305162107df881458841f7d205162100df081458840b7f105162140df84145885037d105162140dd44
  | 18 => 0x185250c4b77f21494312dddc85250c40b7e214943102db885250c4b77d214943102df085250c40b6c214943100df901250c4037c404943107dfd81250c4027f604943107df981250c4067e604943107df581250c41f7c6049431019f181250c41f7e204943107df081250c40b7f10494312ddf841250c4b77d10494312ddd441250c40b7c104943100bf899500c402fc265403102f74c5500c497d5315403125fdc85500c442ff615403102fd985500c40afe615403110bf585500c442fc615403100dfc95500c40b7e255403100df495500c40b7c255403110bfd95500c4067f655403102fdc55500c443fa205403102fec41500c443f5105403110fe041500c40bfb505403110df941500c443f8505403110df141500c44378505403100df909500c4037d425403100df109500c4037f265403100df899500c41e7e265403100df499500c4037c2654031039f099500c40b7e315403125df4c5500c4437c315403125dfc85500c40b7e215403125df485500c40b7c215403102df985500c4437c6154031109f185500c4437e205403110de881500c4437c205403110dfc41500c40b7b105403110df841500c4437d105403110df041500c44378105403143fdc86438850fef2190e2143fd44243884cafd4690e2136ef51a438841afe1690e2106bf45a43884d6ff0690e2135bf01a43884137e5690e2100df55a43884027d5690e2104df15a438841fef4290a2103efd0a428841fef3290a2103fdc86428840fef2190a2140fd442428841f7e3590a2141df4d6428840f7d2590a2140fb49642884ff7f0590a213fdf016428840fbd4690a2100bfcda428840efe3690a2136bf4da428840efe1690a2106bf45a42884d6ff0690a2100bf41a42884d6fc0690a2119bf55a428840f7d5690a21199f55a428841fed4210a2103ef508428841fad4210a2103efd184288402ff3610a2103bf8d842884dafd3610a2103fbc98428840ff72110a2103fbc84428840eff6110a2106bf58442885d7ee2010a2175fb08042884d6fe6010a2100bf58042884d6fc6010a2119fd440428841f7e3510a211adf4d4428840f7d2510a2119fb494428840f7d6510a2140bf59442885027d6510a2118dfc1442884637c0510a2100bfcdb45884dafe36d162136bf4db458841fbf42d162107ef50b458841aff62d162106bf58b458840bbe41d162102ef107458840afe61d162119fdc87458840bef21d162135bf9834588402fd60d162135bf1834588467f510d162102df917458840bbe45d162102cf917458840bbc45d162102df8d745884037d35d162102df0d7458840bed25d162100dfc17458840b7e05d162102df01745884177f43d162105df90f45884177d43d162105dfcdb45884127f36d162105df8db45884167e36d162105df4db45884227d36d162105df0
  | 19 => 0xfd95420c402ff6550831009fd95420c41f7e655083102bf995420c41f7d655083100df195420c40afc6550831029f195420c4bf7f155083130fdc55420c402ff605083110bf981420c442fc60508312ffd441420c4bb7e50508312edf141420c403bd421083100eb508420c502ff261083100fbc98420c467dd311083119f54c4420c447f7211083111fdd84420c41aff611083106bdd84420c40afe611083106bf584420c447f4611083103dfd94420c4037e651083102bf994420c40a7e651083100df594420c402fd6510831009f594420c40f7c651083102bf194420c4677f15108311afdc54420c442fe601083100bf580420c442fc601083119fd440420c4637e501083118df140420c403ee42c943100fb50b250c4fbf741c943102f74c7250c4fbd531c943102fb887250c40bec21c943100dfd17250c40b7e45c943102df117250c40b7e25c943102fb897250c40b6e25c943102fdc57250c4fbf510c943102dfd43250c4037e50c943102df143250c402ff46c943100bf51b250c402fc46c943102fbc9b250c40aff16c943111fd85b250c40afc16c943102fd05b250c442ff06c943100bf41b250c442fc06c943103dfd0b250c40f7e42c943103db90b250c40f7d42c943100db50b250c40f7c42c94313edfd07250c40b7e41c94313edf507250c40b7c41c943102df8c7250c4fb7d31c943102df887250c40b6e21c943102df087250c40b6c21c943100df903250c4037c40c943103df883250c40f7c20c943102dfc43250c4fb7e10c94313edf443250c40b7c10c943103dfd1b250c4167f46c943103df91b250c40f7d46c9431099f51b250c40f7c46c9431039f11b250c40b7f16c9431029fc5b250c40f7e16c943103df45b250c40b7c16c943103dfc1b250c4067f06c943103df81b250c40f7d06c9431009f41b250c40f7c06c9431019f01b250c402ff464943100bf919250c402fd464943100bf119250c403ee424943100fb509250c4b7f7414943102f74c5250c4b7d5314943102bfd85250c40afe614943102bf585250c40bf4614943102bf185250c4b7f7214943102fb885250c40bec214943100dfd15250c40b7e454943100df515250c40b7c454943102bfd95250c4037f254943102fb895250c40b7c254943102fb095250c40b6c254943102fdc55250c402ff604943110bf981250c442fc60494312dfd441250c40b7f504943100df941250c40b7c504943107dfd19250c4167f464943107df919250c4267e464943107df519250c41e7d464943107df119250c4167c464943107dfd09250c41f7e424943100db909250c41f7d424943107db509250c41f7c42494312ddfd05250c40b7e41494312ddf505250c40b7c414943102df8c5250c4b77d314943102df0c5250c40b7e614943102df185250c41f746149431029f
  | 20 => 0xfb14325109dfee10c944278fb44325109dfec10c944203fb51b2510816ed46c944203eb51b2510802ad46c944203fb55b251080fef16c944203fb85b251080fed16c944203fb05b25109dfef06c944203fb81b251080fed06c944277fb01b251080fbd429444200eb50a51108037f359444203df8d651108037d359444203df0d6511080fef259444200fd8c65110867f5319444203fdc86511080ff4219444203fdd46511080f7f519444203ddd46511080f7f509444200df942511080f7c509444219fd4425110802ff36944421abf8da511086afd369444203bf55a51108677d5694442069f55a511080ff7169444218bfc1a5110802fd069444218bf01a511080f7e429444200df50a511080f7c429444203df8ca51108037d329444203df0ca511080b7f319444202df8c6511080b76319444202df4c6511086775319444202dfc86511080f77219444202df086511080b74219444200df8c251108037d309444200df0c2511080f7f209444200df882511080f7c209444202df842511080b7d109444219dd442511080b7c109444202dfcda51108127f369444202df8da511080a7e369444202df4da51108227d369444202df0da511080b7d269444202df09a511080b7f0694442019fc1a511080b7e069444202df41a51108027d069444202df01a51108067c069444203ef5095010803ad425404218bfd9550108067f655404203fbc955010866ff615404219bf5855010802fc615404203dfd4550108037e515404200df545501080f7c515404203fec815010863f8205404203fed4150108637e505404218fe14150108637c505404218de1415010863fa105404200fe441501080f7e425404200db90950108037d425404200cf50950108032d425404218df109501080f7e625404200df8c550108037d315404200dfd85501081a7f615404200df98550108037d6154042069f58550108037c6154042029f185501080f7f215404200df485501080f7c215404218dfc81501080f7b205404218df88150108637c205404218de08150108637e105404218de84150108637d105404200de44150108637c105404200efd0a420c503f7419083140f74c6420c503d5319083111fdc86420c5037f159083141fdc56420c503f510908313fdf942420c4ff7c50908312fbf51a420c466ff269083102bfc5a420c403f7169083102bdc5a420c41afe169083106bf45a420c503f5169083106bd45a420c40aff569083100dfd5a420c40a7f569083103df95a420c402fd569083100df55a420c4027d569083102bf15a420c40f7c569083110bfc1a420c402fd069083110bf01a420c403be42508312ffdd85420c41aff615083106bdd85420c41afd615083100fd185420c40afc615083102bd185420c4bfdd31508312ff54c5420c4bff7215083100d
  | 21 => 0x2df4c4515080b7e211454202dd884515080b7d21145422fdd484515080b7f3614542049fcd8515080b7e3614542029f8d8515080b7d3614542089f4d8515080b7c361454202dfc98515080b7e261454200df8c051508037d301454200df0c0515081f7e201454207df48051508037c201454202df84051508bf76101454202df440515080b7c101454202dd040515080b7f601454202df98051508067e601454202df58051508027d601454202df18051508067c601454207ef90b50508037f51d414207df947505081f7d51d414200df14750508bbfa50d41422edf94350508bb7a50d41422efe883505081ff920d41422efe04350508baff56d41422edfd5b50508067f56d414207fb89b5050802ff16d41422fbf85b50508befd16d414207fe41b50508277e42d41422edf50b50508037e31d414200df4c750508037f21d414207df887505081f7d21d41422edf88350508bb7a20d41422edf483505081f7920d41422edf84350508bb7d10d41422edf04350508bb7810d41422edfc9b505081f7e26d414200dfc5b505080a7f16d414200df85b505081a7e16d414200df45b505081a7d16d414200df05b505081f7f655084203bfd9542108027f655084219bfd854210866fd615084200bf185421080fef215084273fb485421080f7f51508422fdf5454210802ff605084218bf9814210862fc605084272fb88142109cbec20508422edf94142108bb7c505084203efd95421081f3f655084203afd9542108023f655084203efc9542109cfbf615084207ef98542109cfbd615084207ef18542109d3be315084273ef4c5421080fbf215084203ebc85421080fbd215084273eb485421080fbf515084203ef545421080fbc515084207efd8142109cbbe605084207ef58142109cbbc605084272ef88142109cbae205084272ef08142109cbac205084203efd4142109cbbe505084272ef14142109cbbe105084273ef44142109cbbc105084200ebd9542108032f655084200abd9542109cfaf615084207eb98542109cfad615084200eb18542109d3ae315084273eb4c5421080faf515084273eb545421080fac515084200ebd8142109cbae605084207eb58142109cbac605084203ebd4142109cbae505084272eb14142109cbae105084273eb44142109cbac105084203dfd0b25109037d41c944240df4c7251080f7f21c94423fdf90325108ff7c20c94423fdf843251080f7d46c944203cf51b251080f6f26c944203dfc5b251080f7e16c944203df45b251081a7d16c94423fdfc1b25108067f06c94423fdf41b25108ff7c06c944203fbd1725108176f45c944203ebd172510817ef41c944205fb50725109e7ee31c944278fb4c7251080fef51c944203fb547251080fec51c944277fb90325109dfec40c944203fbd4325109dfee50c944277
  | 22 => 0x3fbf18315908037f35c564203df8d715908037d35c564203df0d7159080f7e15c564203fd857159080f7615c564203fd05715909037d65c564200dfc17159080f7e05c564203df01715908037f43c564209df90f15908277d43c564200dfd0b15908277d42c564203df10b159080f7e32c564200df4cb159080f7c32c564202df907159080b7641c564202df50715909037541c564202dfcc715909037731c564202df8c7159080b7d31c564202dfc87159080f7721c564202df087159080b7421c564202dfd1b159080b7e46c564202dfcdb15908127f36c564202df8db159080a7e36c564202df4db15908227d36c564202df0db159080b7d26c564202df09b15908277e40c564209df50315908037c40c564200df8c315908037d30c564200df0c3159080f7f20c564200df883159080f7c20c564202df843159080b7d10c564240dd443159080b7c10c564202dfd83159080b7e60c5642019f983159080b7d60c5642009f583159080b7c60c5642019f1831590827ef424164203efd09059080fef264164240bf8590590902fd164164200bf05905908fffa404164209fe501059080ffb20416423ffe08105908037f154164203df85505908037d154164203df05505908ff7f054164203fe81505908ff7c05416423ffe01505908ff78054164200dfd0905908033f424164209df509059080f7c424164200dfd0505908277e414164209df50505908037e314164200df4c5059080f7f214164200df485059080f7c214164209df519059080f7f264164200dfc5905908037e1641642069f85905908037d1641642069f45905908037c1641642029f05905908ff7e40416423fde90105908ff7d404164209de50105908ff7c40416423fdfc81059080f7b20416423fdf88105908ff7c20416423fde08105908ff7e10416423fdf44105908ff7c104164203efd4a425081faf52909428eefd46425081fbe51909428eef5464250a3fbe31909428eef4c6425080fbf219094203ef4864250a37be509094207ef5424250a37bc50909428def8824250a37bc20909428def8424250a3bbd10909428def042425080fbf169094203ef85a425080fbd169094203ef05a4250a37bf069094203ef81a425080fbd069094200af41a4250a37bc069094200dfd4c515081f7e531454207df54c51508037c531454207ef90851508bff551145422fdf54451508bf7551145422ffdcc4515081ff621145422ffd48451508beff56145422fdfd58515081a7f561454200bfcd851508c2fe361454230bf4d8515081ff7161454207df940515081f7d501454200df14051508bff6101454200fd04051508bafe601454200bf58051508bafc601454209df90851508bf7d421454207dfcc851508037e321454207df4c8515080b7f31145422fddcc4515080b7e31145420
  | 23 => 0xfef21d0a42a2fb4874290a87ee20d0a42a1fb083429080f7e15d0a425adf45742909677f05d0a4259df017429080efd65d0a42a3ef8c74290a8bbd31d0a4203efc87429080fbd21d0a42a1ef8834290a87bc20d0a42a1ef8434290a8bbd10d0a42a1ef0434290817be16d0a42a2ef45b4290817bc16d0a42a1efc1b4290817be06d0a42a1ef01b429080fbe15d0a4203ef457429080fbc15d0a42a1efc17429080fbe05d0a42a1ef017429080fbd65d0a4207cf597429080ebd65d0a422fdf58545908bf7d31516422fdf48545908bb7e60516422edf88145908bb7e105164203df50b25908677d31c964203dfc87259080f7f61c964218df08325908637c60c964218df8432590827ef42c564203efd0b1590827f641c564240fd5071590903f731c564203fdc87159080ff421c564200bfcdb1590906fe36c564241bf4db1590903f510c56423fbf9831590802fd60c5642
  | _ => 0
def innerJ6 : Nat → Nat
  | 0 => 0x1703b4102eda0d4d0d8014a18f85e0c80419362164a060aa506e8693072fc0cabf817184208d92aa2011840df9004bb1f0433e2d3421cae8d44547ec9288aba3130b01015e810c04dca9d89b122a3a044e60d4702aa4c5c823291d8ea8d24dd20864eeda58810b230e5800b85972e421553f3094d57343d381630d6655889139166b2c811325ab1bce20ea1244f8a4c770be07b2eca59658902d24c69920bad038f600eb3c95c32c874d3c89ed44f110c095abb58039964f5f52f1281b5bf632e0859ac21192c638841d3130e324607a4ced523239295f06fb1cd1d0dbe7c2a00c9cdc3e2e394620540289232180283ce0282c501020a23cb818f767ae27d6d7a0b13332dc5d9cabb29ad537c0fc8a720c887ba06f34bca8d98671a29aca0ea6b844c8b3794d2051463065b4c373b0c14ebebe80c4b210c263250b1be803a44dd0ab7c52d25227cbc8500e708bb2062a246150108d4726c271047389f23142c0e16f72055632097d8b971b9c3a2c039872d96c37b205c148940547402e96b01cc3516405a59b591f224d34fafeccbaab4ba01a295e4fde91fc50f47cf03d7b9d5001e1440b7a02375dae13d024a921c44b29d6987a8292656e6b1171e1c4978546cc598db26f45888f5206a0f125762bb6c7ed036474ce6a4573d896e5d7a67e0b0029ca2a0cc18c3480a1d2f42aaf14c5b58425990328c9a3fc9094eb63078b945a03c8258142701f41bc8b8b0a5c05b049520a216abae1962ee73f5e2ab37e4bf4e50066c0308539ca6e58172ab176201ec814b20870562a7c5a4985200808cc083d49f6a361046a2018a96024d4e4752fbb5a165f8b7a1e0225c529280d958bcb924442a27e137eb0602a22406cfeb11545ce2c6ec52c10d4500ab34c4f4a12c4bd4157c746a8985c5eb1f0f93015c1c62b17c36f1dd4339e90809aa86f945ce3bdd4161ef2407c8b8dcce2c248036a7017c123724f205630ff61c8f7a0265f02de1655805e8a942fc2ff0130c4f0d292250165985731532183f75843419ad94025031aac482faafab61d2b2013d2115661040731e7cb5d82414b4d145229bf339074c8fff03bb60f85b9892993b202348b6c2e2870923d0d4206deabdc639879e5400b20a46167c84ac9ad8a623d00a538aa9f6414816bdf2819cc27f08822069084d523e716d94aafed308cf4419e61510490c99758e7bbd253c4b138fedb08d1c643ab5ce4ae455ca8acfd69891d00620bc088fd03ca472662d400cb48956b8a69dbf3040d64a6c5117c2318730985ef9b6c1dd954b64b096d68fb04914a250f8ca9574a1cce78464afdb7f4064a9f4529cb1d6820c479daed1468243d06d9130e4c6ee1511761c4050ec8a9d84d9d2f5ed65d7d98514ca58240d004cf0c76043afdb58b71192711864d57a1aef24b987338724842613fef710e71a019
  | 1 => 0x280ac3908dfb3a780790c0c4d1c89a34fae35f0e332cd9415e3bc924c3522444e9a051d406784d2af080629a203230afbf998f8d9569c06ae53a038665c7c049924e9849710257d87ec97d4055a05a848b284133e076694d114085c96dd29c3fa6855d2a5b888738d6f53f6de901289ce53a02d248324bfde188c6bc03aaab08636ee0b827531d87fd6032884627f04c5899b40c5907c1d26ccc9232a7200a3a52d985b257f53f88d84ff3af5d5e166df9fc33a1d4364f39159ca671424456f9a2c211a5caad02122236f03d70672cccd2c094ae6a4a5c3602e947887ee40df857d1220c6e0b302c578164e7c01c82ff52780d4008e21ce764f84bc5c9e2cd8079840e800b1b16398208b4548315c6968f53426f3ba7294014854e90110798300b8a22307b2ec843c963d8c9a0cea4681858814659ca810cc892de955488391783bdf0792c25692ea3834121417d18fb0b4f60d2bd6597bbf5e10946c38840303317b902f020d212672743820dea1f2e4bb46d846372e281db85a54bae048155305a84777b88d076495b97422317699e03c43b39916411845052bd35a42eeef501ec63fe8508097345caab02293a07f5cc08b29768880b8e6f314147325f9909c15e71dacaeb9316b42d02707f84078157a2bb06349c0d9d6d3eeac9e848480113d34fb3ddcd1fcc742659e0462264223bc221420996ba47488d8dce8a66f02fa496593c24ce0fd615e95e6852b61d4b1ad67d8e81014285c164e38ac7b0102f99ce355a40008010521259952ca05b5f9c9d2d103c268053a0802479022e5bc094dc3f966321c3eacd51f9ef738bd48d42408249d5125894b5de6d1a011904e45f1cbd2185dbdaf587432b007eba7e5f784c9893390be1fa84266056173a4c165b80aca827c57dc92918e41fe41426ec807769c9f1d886f1c2308cb03d16ccec528b97172204805a80905a05aa5eb491d2c0c2b7e52d11dd264425b88729ab703a92026c9917f7878d00129360468afc0139ec2102c31739553693011ed0f2d78c03c39f3f2b2205685871a75101e566c10044a997e902f6654c47422ee59be0c313c5a63d06348370895bfa10f0e812ccd80ddb0f803bec2c1829d281ce65139a0acc40a031c01da3ab20a587f24de42b0d1e2c3ca0be4318a68f0df21415a56c6f566ef99c009bd3e507b8008219264e96d3653b8ac6361ba15cceeb28234d26c1c5f9d8e40220ce11153d8ffa539ef828ae9b2242fea56ec2b5bed31b341af5b860c0e0a923b093d7b4fd2dce30a45fb2cf63034493136daa63542268687cc17ba413e2975fccbdac3848a5c95ff849d5c90422571fa43c7b3681758403d245eae7fe0373235b3c707469ae620920964085911904c71dc46ac170a1df411ec528d7338d3679008f49a1ea36801dc29b17c83280482a6e380872dc2641e954
  | 2 => 0x919040b9455ae62147339c375696ffe95b525b947bcf51192017b354844071c78970e02048c707ae9401264ac735cd4b9b40fd46834131242c54aa7b50b60bf6220d4a1697bb89f140ec45b128dad04350cb3cc30b401a4a800bb9639a94547e06450f408b185d866b092dd29d111d8ab045ba84066200596dc1908541ea0947d204bf5978a4dbd0dbe384522ba9f7128380de81281b1028902b54d0ea881541c0b939eee91960e9f9c63388f257e2b470786826e53c50115652644e4da3b74147d808306a59d30075c19b9933acaf4b2c0880cb11750503634d43eb276147d0d8fd9e00f1e7e26952c01d20df4f9254e16ae1e8a47d25dbd6f33dd94880c14116ab15f52d24e453c6051c396c6ab91f2b2872f18d9e1eae89a9328edb0151ba6fc0104bc142ad904953586f1174fbf220604f8e89a11c86378c1cd59a7804c657ef78cf5b80574d9ed21d31395b67ca461806c09fba5e4903888289c085e00c5651d705a655c61bd0030bddf1fdcafdc12dbf7d0f28ff95ff7216b24e0fb4941424d46b3a0f084aa01b358d47f10245a06772f893dcf0e0e8852b0c88cbff939318d44c544e618db629ac0c932d351c5f6c82585209aa62dee5e7470b938001b882e9bb80053640a9d8015725a61f74cb597451a126f40525d2b2852528228e3d9de9279554633408afbc5b367c28517ab1f0a2b0ca494e26afec5dce9708e4181531aea52f01bb104b53d092bd58016f91e62e601953202f3bfca11ca16beee3f8aa99c4d6a94f2e6e99992aebc5c50a2b29c88c312036a6a4d075f31fd17e6509806422507bfc34cd51aa9916bf8289435ba3cb3c1011c473e22cb644ab4687c2206f07cc42088a929855b3819317df17fb7bc0a1c03d6ad23540ab944f4a2d783dc81ec127689954f4ada38b5e832b231055c5dbb06b60b50d8486a9a6292f4eba08fb5bb8c5b661cb4c320a441c2aa9c026d215f499e760881202972d682d3074f34d0020a86f987c80a9230880894bf021c5ee09e7c64c010934b408a582011d66cb89f7df888dc0633af151b2b24b3050a306481b0369562c28d8d25119655f8bbe0e63b46c107e7505083b2294e0e067904bbcac1282ca752da3c42730c9661e768be86b74ad0d4fc80852ee840012a511195c242eccfb1932e474c84590fd282a36cccbd916ebceb0248d33996ba63e77d2b1b1920a26a34ecdaa89ed2dc751989b584c399c27dd60b8411105193d80a3cc02f13c74ed6cbe9842a7db7d8839142140928228090457e7116e4f94aaa58b9b958440e62c1b432344644e093de34282247a2acb45d0bdd764286611eca2920713090d4fca3dca42fc3da997fbf08607a8b180b01f0d28a8a29e062b1043bdc7e844c7b00312cf0365c1f016942828125669327534586071d753c88018b0035e8208494d76a13d34d402
  | 3 => 0x4450c81f09b5131011838a685a453d2d39481030e3da697045ccb006262ea11478a830fc7a899606c324c7e4a4994a9060b80cda0f0401eca05b4c0cca3a68fc1570c00ab559af9098b6358e129ebab4a6208ac66bec2243c8b44a4106dc20efc26f836740a0114f97a252d0ec0016633067be46c80fde1ec845784498dbd0e57352e6c09e1e9dd546a809d58e922464f441bc0095a5d9554e3ba15833b800428fe5194c0e643570a6b9c03925624ee6bd1fa0af4d0a8c5cf993891fe0ee6bca8dc1b0a838c0447937616442f3406ac5ebadda323e4d5c29f279b08d0a559754920542646c89ef13b66278c42ed1362e324ffa7e7cf393cf21d0c9f78f1931c47d40506c77531b6208847b01502ab82016d63d624949f4a32239978c9dd011fa7e38f7e05ec376ce8d89018add50f89d90526b58245be7ed18d688264b781dbd70090ad44cccb3cfcd13990e38bfd9c80b49e68c072d5ff085c9100a3bc0bde24521ee6da24342abfc659611c977b966e6010fd30f9cb37f6b7cbb2492735244166bb680621b4a0920e2a811da184431832804a11540205802995f1059161028dd95fc8d625774b86d5df94b26b300e151e685ab08b067897559b8754dcea28996013626ecd748f1ba8002bc8af20357020f0d7cc259dcb9f16720c0a6d8be8bb04c763bd1ab11c2a01decd6c0f789006be62e40b2d0ce03d880af409dae8730e00c2d843b1a513fcbe01b9c33092f16267539628841a4ce794057099a71da6d020510b5520a6a4844e801204f5053983610ea37ffeb39cea2b874113aaf6c61290270168b9300e30665589603e56f888603e840d6554206636cb6b12832830a04e884c88e9d80664526c8fdffb039a5d24e7f06ee003c4ad6a6c9f56152453cc64b54c9258769089554a94b4da49b43a4000991011aaa4570c1c07e555ee56658e11138071837a5f16b9873b14ed419b528f405f224b9d2215dc132c7e746d200a043c461d0bf218c244b44ed95e22c8f06bcc941260bc0c1a1afe1190d1988566831410cc904163b47434aab2299406ca4e9b58aded1e0aa06962eae4708f2b01c9af3c9226ba39d1548a3c34d82fdf05d5039e466ebc050c328dd2b38abe4464166f00da370981280fc473620898b3167c6f60d5e143494e81cfc24cd57717692570eb8dc863f242dc8c51d781b3c469d05e3c7910f3f2056c4844a60b451450bea0dada76d551209ad4d4b384614a5ced4212bf0339a12a94ba0dad77609aa42c6bf2b55d21e605a72812750e08a920c2cc45ecca43d48e80c6769c90a4b5e20ee673636d0db10d24808e6970f6e0def601c8ca0bf5b9881036c4e5a6e9f30563ab424827400166f2fd1d3f6252d5b7c9a95b0e02b84f0436a4346320757a86cada0107a54196e254a98835145289f59e188d2326ac8b3107e1a1b095e4f
  | 4 => 0x614643afd06630c83874bc0242e44c23d626aac7197649ee0109ddc4c1e90b4ad5380608b688798ad17963480353ce0c00712062201d85237b17f069d360570de308fcd8c17652d8514723cf1e9eaae13936c2302d91d403b688a398269c4b814a70a43e6387c4728c86527ca0021c4efe8c210938662a0ebb086e233960e4e9a0ffe09521fccffd49200b3520fe91845aa16922068b490ea8b18922dacc7596d20780e60d0e0bdb0447574e2b05cd09f2a2f1c8959051030142aa65f81fa859a636a97cdf30292b60d83d0172ba3e304e8526806705185e2e0b45d690fea24cac6388d523b50956b1c889227f40380775d5d4ad331b7050295a6af93541636edf5c110d3f6ce0688bc1643124aee251b111ae6ef0ad44fd21a6a534a9330be88df75d2e7ed54bf8ec95be4c8b503a041c4b9e2860b7b0c4d694c60bc608b47e65cef4981d9af625bd6c83130a27782ea435145efa304363803e9aca9cb408449cb82ba168c4fa2b698cb22f2647648358c0c83b979a8d3e5e0a2f101b20361cdd912fa6488063c6cd99ac51509b6822faa76263c42f05d6232b79dc80f54fd0c235b0c70f1cb4154c2dacfd197fe353256e851f04f78e685a20a52416a27267722f6b4ffc93f477ac115850714152266379d990a3b61dfe1dd448aa6a3547e28282e62f0e521883d87ac0e3e57d8fdec4f607184bf2ca81f950d782022e81564f98ec02a0816597508cb3e4e610c74a3e990e207c446e4a4802b30f62404733b831e4299d91927cc3fda2778ec802e476e08bacadc0644345c4d018aaaa88154a1cc41ef317666f0d5b0415bc28063eaa78d0f075c698278a9183a3533fa6d3548af179f0116b4a580abc1d35a4caf5fb793461d16a5794e1b2db38ac9720867a02015f2c0156b609631cf4feb1d940da612425a4cba63f4816e0074cb539d31473e4b4097f0ed8073a7d90f4e1be431bee471f44b63d090ec1307e9a7087d2ad9395123f0e63e4ac7c25a9af35d02da34fc99ca937048cf0458213457ce8c9885fb54f445c28a897e2b492842e9c056038f4649e71a8dcd094a498ab5a19f081763b0cb6e9a3203db040cfdb874d168f646c11c1aed2dc61cd2075cd753e3c20321c501c12a49459ca1fd80dab613244bfd0fc5117903385998b94af5c4c22661495a0c5c463c3ae80ab873813f25f586d2b115274c45fcb5fb5b004900cf5a642d3853f089044ba8dd61bfce0e8b2997151bc0c1102b883f7576c00b5ce83c6401a81f89f162d8f5eb61f2d0b919d01da6cef0a7a39ed77428ac820bafc639eca22c6a69ca0370cb2dcb4300b33272f4b0b9283780a18ae144448ee630740fac29792ce14528d4184ab95119b43af4140af2e606e8e0d8430ee461c0646406c23180706798003210a1108025ade4685660bbc8578530229e466813fdcc7b5
  | 5 => 0x5373a42c5c92ac9ccb7332829c3f99cf414165c9c6a4b1680564fa781c32cb95d8af4e4826bb8e1d8265a04c8165612249cddecebf9151768de9504baf03f62603d9cc36ac555081b126482a802883ac08e01941423ab4b9932bf444a0c6461fef8489628cce0c7de35ee0a6aec10edb00c07d902cf427d86ab432879f00123b814e50d258f978dda55c4a27109aa47056dab809f22139c5ba4dfb1145a6df42ba58b1d390eda45cc6174b5290797fc40115575b3003e982451f192db015a8eba52f3180b63165129148315d2ba0826ce67a9030fee25c80f3805f4bda64113ad96914b3ed1400d932a746189c8877e1f2971c8ae593aa223e2f7a9cf4f10a2a41d9cbfa97e22fd14e62c470c1821611528f0b1312859f271050e1392bae10da03a656441cba6ffc134029ca22834e0e5cd0cea79a5544b0ee055968a59784a10dab837d660aab09afb994469ce6089362a613062e66f806bb28c2e8a73249690f8a7ac841b9b940b69084ab3f4fca81182c2cf784a3c092b66a471f599ab0bc5b26b2f957c05fc301a7031a56170b1878e6e4c0e8c8a80c8ae81efe2ad64e849c6880505fa42b0241947289265ca6b0e1514a08152763b3460a1d6e1ae4008860d0eec453415088a9b5e251d6ec90fdda2c0658472158212b8344f4ae55d48a4920f1412a0d3a0314292c2d057efb0525314b3759782616745063391710e737b707dc57691f911756bd61c04abd17b2255e1786b64a60a27fa0c1a275634785b39e10a14c14f093d5671239643fea38107296367a929b98c448f3a25aa84005be8d9c3170ca2123a2895233860cc8e910df3c88e1ed02c2f6a14ae45619fd2a53406847087ef22494d6a07b4ab71c165c18b7853f429d96610890876a1ded25dc3c3c518be714ffe84bcb2b90e07500ecd193f00cc48082bd07c831f379e83865e7e85b52b866fa1a829de611caafc84e885326cb44391b5226b96aa4084cef1a9674db88d298df003301848299afb261f32984ee5df834fb1c4a74e81b991833aa06990c2505da583c74a59f30f6869a2d6ccf1d2276415a06d914007dc01f0b1bd75534c34d4e25c0483a34232a0200462b331c7c40c779976002a0384c63d477147e60c2bdb5525011f17ac5dad33290e63422a969ab32adc077ec97978abae650fc6aa0b850119119adf813820d560c12fa600f09a320534614c823b1630e907f08485af4f01180ca8351277663ce89306878d9d74a8272de5210d908babcc941b8830058e16c5f6b28631adca4b5ecc40487bd0fb784540c8b0e1ea97a07403330986e1710a4a6386cecbc8d92c80750754f6f5077811e2e70418d3a29e901c9643dd956bd784bba288116d3ca922b210f4f7512725e767a4d5862888095cc4d5302b54c1ef0208437e138a7a38e93027c3d990bc821302759a4755d09
  | 6 => 0xf91170231324441ee4994bdee366a87d881532c455b2980133b812376a4ebe4ab39afe1d72fe684cdb69207324131b82a52321346d64dfc261a775a133082832032c30e2918c01e1e5dc8d46160e25d756808a44852001b1fec24f0792a3bb0a74d88ccb63a103058cd8c03a25475922806178da1ec0648a0c5bf43f8f67fc944910ea1230b0e44389c681d005b6c90801aa86c28e4e06040e14914de26a7177a8197444264c19293e1e706e89dc3c206e5483833c978f2fcc0472a6c100730024412acf0b7901f83902c18991e2799458e0dbd695c04c01208945606ada02f6a730114107ee6662d8f8a8aa0b61480b9cc74195184704e6ac65c09e65e7e9e359d201a15b4a3be0584a08b085c3a31cfaa01613564c6df76b1966714a8bc25e94a146d21a617e982ba5d5e5231c4ea2ed7d641f2169b9d102cc4c87863d293856b2af0177195697fba2db1384b52e43505a71b033e623e34ac85dd906dd488a8df9e86a80e328a62a5ac584c0041cedf0aaebda41a783f54a821c4e559094e83cb903d515a51d932dab4657c0736dff3bad745f2798923024f0283464b1e813d6d2da4ea496f3b93d42c85fc98c981480c8a5641ede113512a0b6d9c9a986d80fc2a70c349a481b820cbde79bfb10a8a0c3416093be13cec6052692d586f689b4586121761b2e7d881a12f991148e69c1be22a63f3cc28ca51044b7ad900d51fc83d87a52fa4dc02aeee0e22e9f094c3a504546b3a45c2a28a089063416c1331942c07ef94623f5f7f52ba710a220262f9c940c7da33a05c72b8703530d9e314634814dda0a36726aa3586e04805736969112f8d80410cc9c8c30a9752e9266602630504046c41ed8163a0c59042f84145a81c0122e5d496f0cf67e7aba415dcb8832eac7e013dc3fcb484819817ebae275ede2475e2420f829c0835ce7e2b334fc653591c71a9d2e26aba9cf8942536ec347da18a120242006f404b18945b20b7bcd882dbd36ea4ac80dc81323b30c1bdac317b837741f39d5f0d54138acec0d4caacc65caa02d3b31c7210c226e0ebc2517216a9441be01d4964d4b351a712f1f3d94026d8d78189732aea2519faa624ddca34403bb8a86b8cfcfc9ac29c860786a15437baa86386bee404938d81c6833a896997190cf8fb9051a31dc0016668137a2c132ae4b3f9b6340c75aa46048ae50c2a816c647110590298100c520d5d9b70395e6f258a70ba57d24d86918c920705fcacfa072ad72400aab0d00a98657ccc3c6c8f71e86306c04c500422c37b2cfc2911182c91496d508c7a2cc63248bcc51eaaba8229887181c50bc32488cbf55f7aa82637e8c44350b9c1634ece594128aac679aa184d122e103eaacb553c3974b1628c9c12de8f1c62321f61168b5897b089571fcc20ae4e862e2497b89010406809c00a20fd13be243550ea
  | 7 => 0x2c2c659a8888d983b3132cccba0c4c14ba3af4a6404fb204a5cd4d840659077167843b8dbc2298406a43250e2aac6113029a71d01b74873a8200d7f9000a162ac08c817a39a79f0b9786c5a8e83410f9b5220b568665ee5808f8324c501a3460e3d0531066caaac356381432b45b754d89960061eff5cbbf269023b4a0106c2a03c548e635950f259e11f0c274097136e37fcd6686060d5169f0753c6c32eac524e5601b5d18275fccf55955ca9c1665cdd71fbb22b31d7834694e3866b3b484730a3025b370ec0bdd1f01d223710b7a911b2a711a5c6ff1fe325330d82d35cb7aa96b0ab8a9349de8a1a33489379428405f1d4056e861799551f48c7b1abb13203c08ea38fff958e2826a8f89d11aa277e82a447f901391ae658647683ee036d60444e36b2c366b074652560506352c7791a402ce11e022f78b5d9b2d7e4c12c1344b86a24aea85d360035b7afa529100a086516e4fa1032e173c5196b43df09aa502d20eaa8fa383f04f68e6d4c5639e869bcc1dca6625890864448142d8b0c00e453b8b9ebeaa2ca2daddfa48920405213f8c6ca4b7342c6e801140d322124604202a267306ba5ba17a83f5111948545d042a187bde754d98210cd5aaab38c1e83ba321bcc138fbe37bc06da2f0967d150168ba5a2169f03ec0b2e71dc1c4bc986e8abb0147e1e9781a0cbe01afa94d3df03f9599617614feacc552f42d9e338a4fd927eae564658809582f87c42f306030872a79e46be27e9dfcbb491bf2c874ab201640258f385bad3a8136f26afc9e5022673b028b0da827015428a36cfd79e981518fe7df97a9ba2d94283d63abcc072ca2ce49da028e49f8700874c3b8247420b881b818295d78281c00e2e742e8e5f299ec9ed243e02f754331d37617e888073c21bf68da3e395ed382040fe7db1d1f294e0f7accde05480587232a708ae32df833bca42d608a02869e0ea989cd8c740f78831d40b0a522bd482c88070c3453664e11a5811822578a77039204dc1a3ada4c73123cf64d8f250e083ec25c2672282703e5c75781b65fb39d925060a0e8e800578068cc70148d99ce798aa84d7b0a3cc581c490994832b3204c98188dfb0d80b2c7528836250825747e1d5a2318d1e203b3c135150d2b4ca3b12990356416a7d69977bf3420c2b9fd592b17b306e6b91696a6cc54b8d9a93fd944e00aa6749afc126b13d0424c20823d74f0226a05ceb6822e348b651461cf9731c59280b38bf23690546424122e14f2886e9f669ff422689c2c0272f4066b876786bc905e314c2ee4efb2aa66a94a22440c87cd5eea557d369be6951e4aa74d2225a55dc235d14a395461e6aaa41f1f09c13e6cfe35f4b8848301c2da00ffa2167e0eab9cc8f32067a404b00f989c1e26e0453c68bac4862fe2e4507496cb171871bd75cad3252c8960e06d33204e1a
  | 8 => 0x43a1130480003dcacd9cfc685c043687190bd92e776ab0d69439c948024d2c155b193510303e2095295848304a41f49228b6da2ebacaa5d1526033eb0c4b1979928c4a6802e836520fa36889df86b01f2b27b8bf6888f861412f61efd4be30c97e5cfd358fba1625d60e76547fbd4e19029d8d4f09f8b52b245c5fe1301649c6a8013cea3317b43016109722f3357cb8953150499501ee8643e5098320ec8a1932a95970c10a21c785b7d419f49605db03cd913b268991d2bd4841eade31d210a06814e7b40d4dbb405e08cc8d5568fa051247f54dc2b48d2df63254f5e267f4b46a4c142b138c3ace3d494a5a4817ca817c027d27702812f51828d01ce51ae50c546e0874248ce121b3720a10eb0c631b26aea32ddc421c3acb2f15cf2fd3d0662ae0462495c44021be64f8e2bf57bd1e0c5bea1f5c3d4270a773102f53f78a01338cb0892e70522039e87f8f6b89d5408a7a901d3314b6454cce145f284c70f4e81deb4b1612f26b229b13b8422f60c2ac6a1895902ac2144279387e2c7c5c80a442c7e2618e0b0c903cf02694f77184fbca5440497810b7082017006e5d012373125c8a1549e81a50394e0b681e0332570c87535e3caa2d307c8669e5025421deac8445ec374c5e8c2ed025bab9d3d76dfc0e68b9301e7c144dbdaa13132a44475c281ea65e6a5e4017797ac0bb0fa75a6a137c2fd8b7fd7251d704e98af98f760cc05f0a8a800449697088c51a19b9b6e15820098047214c04fe2320c5d0265f412636c5d60b7ee113090011de87192ab07bd15fc294438fef749fcb05001d2c8f291b98dcd30b039d8cd42f8b32e4cab07ba8dcf8168584049a9abc2c641581523403c6548058dacfad4070324a493cb9b5d12fcb0bc53e8043230e90e4b9810af662ee984b868bae3214f16842bade37594ec72073824c6dc42bbd26690d81082b9907e10c643cd06e30858b73030845e29435abe93f0619c1d4a8bf937aca36551cb4547fc008ac62796d5739b022c207a1574f084629dc5b73965a87dd869c04b96c82408d927309910c7007987e10ed7800060cb4c1a93187e10d06d5a590485cd308b341a5e1fd866297af8070054439304ee1b5c50767445fa73df6219cc2c98f2b5f07dce853d702a3024680aaf8298207e8022a2a5d96341c7378d3000022af527f4f3bd9c784f52060d8f027687e844f0eea0e5e8fe902688484bf10ae1392ae2813f901903a5834510263160470c207cfc81cec0acaedb9238a2f73d62e9893051ca21e30f7e91a69f8c77dab8b475c21de62183bf9eae0ce4134a446c3bc2d6074041cd1b103c4e1df489f12c73ff2401610d43d5ba762f482835151122c4f9a5fe13e184d5590aeec4b8d89dd621ae129191863c1e90e301320a77f62f016d83cea64e6d3ca054af134fc582abefd2bc3b72117a8cc97a1
  | 9 => 0xa8b0412641809fb8a5a109b6bc68ad83fa22c542ebcd8f228948a09decdda194a62e0e031b9aaaf32286298d61f28e11400c68021c1dec510aad09f9610eb313e73087b640841ac634c569e3e671cb87eb0812a520136e4540b70b3a838b25584fa68c5206363facf8019894132c1d552cc07069c2969db6a9f78646af5d0b75b58a2e5a5364df510ab59a0d9b1ac43da97e04945170fa14b0596431c49a1a95566442b04d80de54c2e98481930e60669c9c79ee404a0637a98847d51cee728afdcc8d80ee0523cd90de84396a3f32a18893017e3014a9eb156da71015dd028119218e447109ad09b93be858a22fe021024d057aa8b5d10037f4577aa4b8758a73e31c4d739c5c0654611406d43b02f95032801a995f2c02333ca86c755848d1d582f245d4981e7b8c3965c090d0b236a9ea9692b4f759548d9e04d101d100c1fc9f86157069d8753938c9cf2490a11358d581db53a8ddf1882acba6c68372d55a33945264d519b3d14fc757e64dcc9f046519847db46770de64d14b3d013909517478bc4480119a23a144b814f81e28434659183541ac06880806d15b953909948a216f007a43b5903557d12c0b112e4c90c6e9ff66d7c66d9c1832e63c4012991d037884fdca438e2e2ecf163a044ce9eb86132b024707071fee36780d891a4078e21c65118d9b9d9442564bb0222b7bd50e2b3fd2a2b774101ece2cff83f5d3e7ca8b96c59521020e4b35019a64c2e7e0380b542f604abebaecc0287b50a4ebdd148931254178905133ca5fb4a4242d14ce22a918b0963514eb59331407be898b9d52563018840baa981011e39211da18005f18825518d2c197706f99533a9fc6702a199d4f3ba5e7a64a7a4b4f079e5628958d7781d5547a6939d361b1e122e0ce75df287aa31c0d74138b0c920082fa407d13a437c568cf956525c64a7a4d6c814033e3e36667123a895c36d05570e6b3edc37ea238469f03376a1ced35a832796056e1284121a09a33d0e5a4b38854c781069f044a02cd6d40d138fc205a5604813085f884d43da277807271fb8507e0a65af68c2e208470edd35a90463629dd4615c074637237d590b0e3c19f281f40ea83300e1ae05dfb0922a08b25bb0bc03322512ee6905f8265335947348268ac333dfc5ad4123bf4549ba20a96ab0be330a2323d3382c9368002b55c58192f6466b1e9fde319a034eb4898f3097d7870a6344bc14ea66b49f65a47280a099032dda900dd87fac7e21777bfb408deab60fe39aed66a070b9bef400a0b045e49a7d04e7502669314639b962468c3e094f28e67e70f310fd80f5f3a98bc84c00b4b608a62b1108794aa10ea74b81ba347c2188a6813b40f08659409b997d9f4461ca70183269cf06abaf054e3614d25bf4c074f7395da45f09f099b9135f0e00033c404b1855d7c67d03c91b265fc
  | 10 => 0xfe32d9534071d1338d6d9270a2252ca4545092e029851440f1d388b26b336901192b020705e0c9de86e2400e08825198d7025ee7d28cc486c51cd52e6c772cde5128635ee3378e3e0e77437227617d8b13c365901b0bc10aeb56fa29550a4116b2d928701d520fae17faf8a04a2aa65187411ad1e32b8738fcb1fc4db16e913587895613842b542038d8c188ac90f5c41e9102b3f81f8c5a387b807fd286c7c91f3c18dc7c229f94dfd079077783b183e0ae4e519e98d4b352b67089e0fa857236dc07267ddcdaab06e21985970cee21bd61e20ba195ca0d26b5049d028f177b6b782888dad09eb5356ac659cf9fea0ffe21f49f00f4260b00620024170652f2e370898405c54f0dda1af0047f4f9cfe902d08178181e8bf0ed038384b6a4328b8c353a2f80c95c4b690a84898ad4008e2b2415f0c6cc1c0802e13a8391d4b6110f24508c0137f1b847ef40abd3f5833b00428214217a39536fea3086b5ad3642d08ee0181b60031247bc0c242e0631565ba93c199c9415251b07be257712cc9b109e128582ab45e99a4a1cea05d88028536815b20ae4149f0da86a10d089f92d82df638a2300c48992b02bd6305d1542f2d4138e119f84887c3408f0717898d0e35a8a41c19695ed750c70b08659abd5de2fa312ef053f5fd2eebdfe6267a42507c88182220e291a0e707773de725cc7e243d0b27b40d0ad60ff1122e53c0566c8c30cf757aee924f9c105d692229d54b303205e66ce40e700e2e38506408b119ee11b443d69520895559da11409c910146626a1d592c35a06e80caa15aea5302d342c9501521787696c7e887dabd811526a8582522196dd46c9c2ae89943ba47450a9605aa5fba112803c8b61361807052699dae5c60dbf19d29a2239b4606d35400955f1aaf4d37113141b187d48f5d180743006d0cd408d9f43b806154ed02fc25ea87819922ae66404891522ba07c04ccaddc0343e086c84ee653021d3c77dec78d8dd1e2c58682a545f69b7d7c987e89e5b1ada52bafbbc9ea0e39223447a9319306444b8cb61fd80e661a72af74fec1bce5ee2d268ecb2a2c79723098fe8b3865290c75d05c331a36e88be990e0afc69feaa31fe20cbe1bbee8b82d6910047e2d7d13ff3e6e17d8b9b8f5035e9574a1231dbf275374520d8d91d2b2c4e0acbb4f270bb16b20817d2f63db551f201296b82bb33ad63f80ee4bed076d8c07819a3f1b24ccd898f553dec200863e8205a9396082a779453167e3d0a384cc3c38e61b742aa08bf0651567018345f78caa8120c98d8a53aac417ed901fe02196365ca69927327b360b81fc58759734213c9f694cca15c3a6a3a281fc00cb5248f63484bb2e1025278c5172022321fafba4a5831a63cfcc5311bf8df6615a7788e3803e3573e8eb4b8806a06eac0afd01d96ae5738a674769156832d45dc83f
  | 11 => 0xe717cf41944b5c60925b86abccc1dc928b600f3eaa640dbb2e06dac07a516f0b211f040918d92b0c02f9ae71605d83914202a66886eb94c4920aabd38a112a033083646e3324b46e8986e074a2ad009a1a451390493220e6fc918eaa126cc85f40aea3afc1dbe00e16a4016e4e5e3f85522bb786692a7d4860bb2d7ce8ee15cd7c03354f21ee18562fc20e8ace84b3981d427a41a111f72e213c786d49503b8c937a0ef11459816c546650cd141a3205f7029c02ac3e2f26d0608d6c707d503ee8aa8cba3d284e4eba2d629a6fa81c04cd932e0dd93d1e96bd9f89fb31b8622d400fa8d06544693cae03ea212ac39d5b6a2b7c000ae8446adb22f5a3eb1a03efabfa04d2a2bca000dc537a6bb1052700b24384722ce8c12cf77540fd1a16276c1c8860e4fec8c725c2eeecdf0f8d840b307df407217144e1c35c06413fd82210611d62e04ef6c32b434892a83c6bac60109790e5a2d8cb7ccfd1a44d2ca0bb3598f0d4437860048d8320c509c48dc1f9826763a401990807a7d010f25650331009a00ecc981bb620f245a09f4dacc8c8656e043e41eba7ea57c840b8cfd162020ce13cd9c383001c764ba049d08a10822ac7879481fa3c2499e15c435ae817073f8eac9330602e8d241602fc70bfcc970baf2b7f33289210c5a1a0f68de3f489322e8c57d4dba0eb52d8d67a0e26416e16c45b98ce0986a8e33216086b8d5d2f79650829253dba3af3b9e7449ace2ece083ebe74a3a1eb62534bce4870b6d705d457bc65e0f1a3fea3454d48123657e6406888e3f32701500e01a1aee25ee6587490029bc4276a7f945a08d53306c0696170ef36d208978c2696b2772c90a1425838e4e6488d0ed90ebb04b8f55dc3438be4ddab8681b52e7a0762847ce7211027c0a0e7ce9590f1392806c0e470e6b4154a2f4bf5174f202a6f053d4b5f200021191dfab2484d56c46cb9586cd12eef2e1e6ea52756c87184b71b0d95136c3b4a17a8321ca2429c4f08af5151a4af87541d02156a456dcae9248371ab30e0043d5967c851e874e8a1547b009f5a223df852b829400e52a6c18424b20725014f4d2c00dda93264b73e9017543c850b04de804118329d65a9483f9a542ef94c1006c465333d83e1ecd35530815e1fe8f9d545b261e7022c5d45d6b1d35312e7209b53c514c403bac1e484cf1ce4ca1972fb9c03652e15445e09f00db8ca7daf51f6e1790dea8478a8a5598077c184401ea608effb5d04a9ee2c502768ca1967401b63940e181ba81a0aced07b22458458450483ba0d8e2edc3560f3718a542d2383c28b83a3020ca0301e8946a785c49cd555408944c6eb88ef9bf666068202ca4d898a5e9c3a003b304c57888e42047001e240e6056818b3a7a46549fd9018af372f7248606a903e86d6842e8836a99b51de068c5e9894049e8726418c38ec00
  | 12 => 0x308e591252ad213b1b001141ebc7c25b0ac5c7153d4a1db68ba606b046200ce5375ca6ab520b3c4c49587a6ef776cdf613a4b8f838befa1c8dc8e2911d68db434405161850d28934eb3273528bfa0a02902056e608c5ea618da7c9c9badea79c7959925f556ad9fda4960a5a9aef29ea6aa8bc9d37cb4654c8a0acdc98ab534e4205dd052ab797d80834c105be707c6c0825da7993d2f22552178933b94a725e25389a3662fb85fc027b11a24c3affd160a0ab41baa56e49cd1a0c19183acc6691dc07d3ef4744e49f3b1c6a140ccc3ac8c3ae4c7ecc6a40c874ca5c0557f96c81b58af844bb34850ab20555b4220c62de6b5e9f7a0f39457a6e25d86319704fcc8818ec9cc55ea809a0ab198824408e8b0de2b8f94a1432012aa11be59b4e4dd36397b472f29d446a0204e200c3918b268f2b6e0045f189c0ed15e8e3c1203c26e75b8a00d813f8d4a7cb45e78eb180940f68903531fb36e369698d82e686f722d45299854855739f0af0c71182a70300b46078a243269c83ca962a332918cc32713ab81dd08369f4817f88781782706946532945f864d91ad3bac3370242dc51bb12e1b90a369329095f1be40a24a24257e08f82f9184a00785dec3ec9026c0eb2296d20c5781a6e1c2c448c1d806556d28a30d6d8975b2830b964c539c84139a3428376aa0a5b8291a14cc2eea072ec02d72c1e140f0ad838a2f2561446016b19b6a4ea5262271ca11b108397c83693701e8445e02edd2b926432d722ba8c5222734e5afa915561a280aea1da0fd69742113871b9c0b39c4222a05c405faf7d17a43935b59ac1a5ceaf415fdea31b4b946a30dac01a97a66aed1cc4aafb4c783f911dcb68012b005ac92a17fa24124eba04725be024ec72dd7229e3587241f56cc189a3e12fc84be5b9e93faefc499e53fb764561e4cae49c9a15b0c344c25bfb5107a016c510b09c3a500ff9dc40bb675d0c751eac20530e78cf75706a23a4cd4fc719b23914588047d09bc1a807e46a114106bd2b0bd24b1032419d61830aa5d514083540809785d7a149558f085514e325ff263493cd0328f370d6476718fcbac7131a6330864a6ea4d0c935cf3a37f61500d879356a1120162c8dd0b1a5046dba7d850648a3f2c3e73e885725c04d62e551e88a00122fa8df180e402700f60779829a34624c4f3c44eda6c221100c3870f1d563e381df487f0e5237dc6c4814611b8129cbc71c9017080b12e0cd4912a0e1ab21fb02770de241b0207482cab68169668d0eb2b28f14bc7b19f0b2dd82b34f1f818c9e165f66c8b8616be313088a8e14342c524b2208f925434902d547cd59628e822fee0a84a431d0f549e382909981d63910a125de6336f13ca3cc19b01c910030a37db7a8be938c6b1d9cee804222845ea14a321bb3d8439a87601ab43270c84d094baae54ee83b15
  | 13 => 0xd5d2f18142024b08631c8754cc7de536a970c5e7aa171c413cb0023abd253fe032c57ea11a5f03bffd56bf018060f8ae3557ed184eef9070373c8559b7629ed3ac830b1a180e0641a83d29792987553d86bd86b507fa080004dc2839ac65f28bab909caf7816a28bc9f5a239c2f28e4843bcb354091ebec981ca77d283ece8c9411b0477e20a90c27a4b577265b157513e38348216719c70ad908f0bc257ec3d3875104238d0a980359e0acc4bb810747d500b495b7b33e53e878b58b3aa8b7208f616003bde54212300099f11dc1638ff34db527ad60520174ec7a0cf26c01620b182c817c32a9113062e1e176aeb681678563504243a84e998bc74567ea4dc5b0bd4eb21b1d6b216a439eac55014f92020758bc50d55206a39660af1d6339845d485a086e73bd437eeca38c1e8c9153d67fdc2691ab6179a280dc3836961d4403b4c95a94a19328848f2a08f5807c84089251f1342e89a2ce32b3331ba619e411209be4ad44a716a219ea7e74a7150a70daf24d8c984361c07a6368fed8ff78dca559e11980728bbd2bcce6802d4a96e5c8805c87939288111a2f45bc00ab97a12684d71d8c6042202749b72034553aee0d566b2549131277086c995034ac40235600939655025939e5a1cb8329ab11c1d01b7181aed1d01c6bad0467a7ac8d4c1fca450820b52d52b750728c4a09e733265c68ea14af83f2d4430846d8e0a4ad0828972500891754a3b0279fd2b3164570d94e00b057b163246e9391ad2a4ca8a1ece38a44809963288f822d0a0414377911cc07251621215b71ba0644dc33a1d2008347e169ca975389a17aea19a5610209804c6a35934ca43d09d0c1b539ca1984ca23a9151a01686409031139a95051abe6148f4a9b7b5a323ba5136aefc24e267919fe3f8512ca7fc4318925e7860458533e819649ec88709899aef2ee29db9048b67e422822fdad8b2b8797872f18498c9f77202305d6aaf3407c027cd7da176a41d62204654a4e46bd68db8e93245c2ec680acc840bbf39fe8f71588238b04ced6bc9f411ce34769a096730bc02e8224e07f831b067a80ca0c20294c5fee84709d200604324602846825e922884df856e26de5d30b658e279e6a7289022819885412018fdde005b7fa2b84b9b488a31a84ce4dff1330350429d84c188ad22107d8a6ca1b1db2d27ea6cb4dc25ab6326f4f9a800badc469e808d54d40fc024245b4160d9cae594a91654f9127625b43a95b6422d237e08b3d1e3a93762c87c55fa819f665f281b5ae53deb17d42159cc62c2a019a8491580a4053d7cc5603e4b7495ece397d7148e094478a600c511ddd233c8c05191267b5de864e835289c65fbc9d7082322955c62692d1828eaf3e5843bc1002bc75048807c0e498845e7861f920814357e96203880c21112c4c64b842d305d1474b018c15031d1
  | 14 => 0x79a2fb60f929e5e4576fbf544340e67a685889a851b731126c2e5763a5e2394a4fc04e1c0a465c813b14049978570820bd0cf1cbb36cebb613f02e8e168896484d7079540c21b21f582f4b40b620a4071033f2b586f004f740e47e62c1a19caafca1ec0e92dfe9a610560600993319039214470f9f64ad4e78c244bc4da06bc29e009c004eb0097c3a17401dd25133e3a11ed3d8256701ac1078e768405099c24ed5358971040225a97631c483cb0e0086c91c5235b0449d3c8aa1f1a086e9960fab1a0c5c8529e0c9c3a5c704ad945093283f36afa05923d305966ff9032c333f00dcba18a021ffd2416346583a383c1bd0b03d8721c543ede6a2167e00ad17dcabf4d6e20c81262b6bc6b098110bda891dacb2d8813c6ad30bb61fe63db244b59d6a0510c4883418e39b217f5ca630d4183c6034a85a916b0f131a42e9159969eae1c34ff4080684e622c063c0f1725052bd28508952314954a89d3dfe513fc3028cd090031f2312c4bfe921996d4367ac9b971526843a96ac44102898b3ece390469611b176b02d64df4886c4912b2e0477a8444ba0a790b2f2859349cf550405396b458258f1769906b5d6c60919a5222c81809ac0d519a7f03e072319ae9a06544c9ca49d403661c5e5071651236a757659b0b6607a72a88bf59894842a6674e66199404943ac47585fa5210e577610fc968bbf344fa80dcba18aa104d8cc35e8ab8d080d4678068f1821667a8f41d1fbff76a7867c8fa99b807f9099283ae945674ccc7f81cd8cd62f86a95d298a8c0143c0aa564d3a323962592d17fa36f36005d4466a08882ea8655c28537f8655ca23582f3e616e405b7c628bfe311e078cd75036cc5d501900d77340616207ad46e88d22777cc4d19b6405e0adca76cd1e9b49686b033908235340da8dc716638f7704bee871656bc583d9c2ef0fb991e463480710438890c4f7286854bd17a041823db8c04174a2aea52781a09dd839d022011c8b1f873c84255f7626c91c3e8541b53265922cc09e145aaa4012886311b0231d16a9a96b8d1fbab44b7616cd74d1f065efe0168aa725dc1b3279d9e641f10068e42517400a260770100803ead1b6eb0ce440e4191178784eec06492ea50dc61c469d25860dd68994ba32817651a3e5981788a556e4bd8c12119865c8063a8ef0b05b0fa282105a48fcb72dc75981de3ece13300551200884f73503120b212c4150ba422931891745d12928568ea51e4c8c99783d8ba6e76c4390c2aa330f1348b59861825ef803264cd1f7b67406b8cd0d72e01876910451604c0ef646f0d0f04042ddc1f501fbcd9c1b691f889bd8284a0a84c505549660988d108ed8a8e8f3346655470d8129959234c00a8d73029b809fa6be0dd5361d63a030dde462edc03cad98041203ef4f6c1055cc28da8408ee0a8700b20b41867e61
  | 15 => 0x815c8a270b0ad02995ab2f56c28ae394501b422ec0f9ad59d40ad6054ffa948ab3a714b8e220007321236f000c507a28ae6d3884fc0cea2752abcb82d5e121433a883e00c4839821e14859c4c8a5eb2b3c5f7c67d98ca697082b051190f67f8a82ecca5bb8a78f07f0c34c8a8112086d8d5e48a6505bc57e114e18022106c07d2bd8d89797a26c4b810725519c099055e99ec7ecac019a5f2a9a5806fc645e3a91c73b85d618ca9b8f030cc73939d96a040b409252c0174d59069065cc1bcd040a81579e3a91d47fe2fa5953a26f04c4cb2d911c060f207c2d95317843b0c2a91581b907c55e18a8c5568a8b7566a29585243eff0ce2230d48bac3107dcc0fdc4487dd739808fd33403573cf493a192d11b20a54c47cb99884331cc756d488096151f095c0300256f078668702b92a9c1d6a7cfcbbfb00449f470b468492f028801e3cd0c812561d01dc9b2c3ffc0f2cc68d066b80e08d459253641ccd35a0cd88e2f027b8138bc7564b02335cb610f112917265dd6145452daf4a612429a43b2b6881748df8982c86306efa5340e0707f035489dbd2a62f9a1fa0acdd217aac9742900a98b5aa7216904661c202f7c4a5297c80909fdc002040fcb8395fc028ebb80868a9fd332c057d96481d20f4c03dc3f4b3653f04aaec12aacb221c5014405c24695b4843203a89b333950f604f242d6a369ebca4e839fa524b64ee0a9688b42be49fe147e90604590b2397cf3ee5386493fc025a62e41ce5830b6b944c042aa8ac34a2efd6392b2d015287862f546648bfeaba61c220348052385801feee1dbe22cdb5bba7645cc82e360f7c268992290ee81b0a0e55859e4030d0a8f476c96fd5998ef199a289b54ad2d31563b934462300bc5758943033743b2c2f11a3e3646c1f9ab9400200d801ac1ee3cd81cd8d28081c04b60824b88d6190a4c21ae7ea12fea7e105e6bbecdb9160675601f4c5e62c16002af21040b373d6da6a4cd9ba8f2e6bea34940180a1646f62a11b160bbe3a1c02a1ac8b20127d885b0622be6c7a8af7796810a2d38c4d2a822d34753fd6b5b8a383d606076f324bdbbb7a4dfe72ae051afeb0700d22d95d3f8c4dea746d15a401059d69aa81db2e947ba82f41924b6ae3504883052cbad84f0a407d892186c2ee6a1e13f11c907a009a81d23ab9e7544b5f8dd832ee0bb8b01189eb65966900e9d55731bc504ead21a8d17ab0624c0e8ac68e122f8cfde4bbe257d26a460b4272afae5a2c27915e58d8d13c4dc920409dda7820954c88491b77dc442154aa07c6561c8b25b4596b065780b08a1407b320b8582861a8250503e9d95506be023daa89ac57681ba00c6c22d98735f12fd0381200b87443d2411d9b2aa8934f249f2c6d539284b0890d18f88b50470e7580bfa0ab83a06d678da72ecc1af413850adae2013c05f11f0a0e07
  | 16 => 0x422145da0494aaef3a18b78934c047a1adac87d311a4d14720a85901c21057be828e129d982616220ac1f4db69177dc6fb14a9b1aa272ec35128007500fcd0319455a93d75acd55956a37dc54de1c80b23a7a1656c9a316f8176654a23a3ccbb09fc3b6007f9a7319405d06bb41da4038480f8601938c0d0163d29b91aea19902aee9681df62d067520fc781bb91bb0f74b531429b62e4f8281adc26264d3c141ac06fd0e028068b7f13338d83003c593192fb1ae58526bd447a38d450a4ef90cc137a80812371cddc2b6e2378128ce2b88336e8819b5a1a0e9105be46d0576131155b404cc7dc2dc94b38a379357a11e143286981f38fd762bc813d2b22c550376a6201f2b9415c3ac0494cf2ab71bfefbf03c5aeb46a580f65fce260e115a8f5823ba5f4591a42e48c63f184594add844621b60f10f4f08b429875fdcdae11d3ada901be39f5fbfb02d0a3e4efd9a58a0c06c248589d501ec366cb6fd19c298f2fdeb5f002a0f7269a472009e082ac2b647d0526e1c5a28b070002c032af1222cb4499921155d4a896069d8f3408980561726a7002c42255c04e23aa7aa02f68f4403440dc27050b90b5070d6202f5737af9777582600eae91f20a46aec972801e001d010a45ffaf0a20421358482b9162b5c35394eab3993744dc40b8898d34304c029933312d5bfa9e4d7f2bb9c7317007028100b708488c5129f3a4a2844c13c66623302990f41dcba132a2d2c2300dd72f7237b83c0046cb334159a22f969d01da4b8eaf59be623dd3e64f9752e89e42051e5e700719e29216c9254ee6bbb42d0007c8fa407fe26a806644d3a2fd7a622e9829a0e53222ed4d9b1d401833a8f09010fb1ca4712995cec0288c41bafa711a6295a086c1529e7e25930554d5c0a4e00af0c24ff488ec25f1094afbe1fd6a6a60af2280887e330c4cd67b4c04c892a672ea00dd5e92f651467fe8e922b4a4ba615497fca0e82a0046b46f73e837f10c32000d21273bd49d284b6228d599c6b591f6a39e3c20c974f3d849a7ce42255c002cc818d8e1e5e6628e9617468d8492409240cc162c0d7876a013ef58449f990e5f74fd81f120a473912ff0c50e2f517048764cd60ba3069a604f087c1c98701e640011d07415020a1950d22beb4436c7894391ed82d62d1480fdaf085e7caf1496cb27f813a9b3535e9cf16fd42f1541330902d70bda124a05336a805d010f92e3a308a251de382cc219e8aef8f3c3de90a4871ad2f188ea2668b19808540bf1b4071e12729eda41feb72803f2351536ecdc493e0fe24610f901a658bd936aca2c8f4dbf70526c965522ebfe9406abd1064da81e58300edca92a69b41b69f51d622dfb521a2d6194cab7b4b3a73ed5bc03a85230e46161080d04f5cf380ab786e05cc6c649d4cb4697f048ad810896c20cd46e90b7f131024dcb64
  | 17 => 0x4c5f327891fd0500d0503f5477b0b19442724883d3c89845e591651a90273831c387276a25850d619fa766e00ef51a5813a5730084040d00a32594cf20f4890547f70835424883fd57a46440fe023586d50b224219b0218028b40174ea7ba125a0904af2879c6c9e5d108b3b2f465bc4c70e6e9ac8060e8f7cb7d0ec74274724c3661b926022b2d5cd299e681600c14fa181ee2fb69c0c61c281131b02f54619bcad7e060d311f38639009edfc9292bb181fc6b33c1e09f025bca8edd67aabb71ac810b1748aaf2089c071c22a02083c0c09158cf1e8c20e6b98955988843be2127811c2b650910fb451faa85f1640abd862088f90d9637f1cbea39707ba47211b026582e3c7b78744bdea4b5af0d44231b347e788d1d8e2938f48f895999abbe7c38a656453ce20630d8a58100f988c77268f67170228ac65224590e0e0902074aff4490202d70154b29051e86664b44fc501792ab54de457800580c9d3758fe7876f2a30208ac85c51ac06810e007f0e56b68f40060034788b1301e6cb7dc0ec32c70aecabe994595e876ac0638b011faa00f450ddc1d9a9a06f702087aa04bf23f00f3d02f023420acb800001024a4012b261315a88209363685604138237a2f700fdfb8801f38b6f0ede13277c38c86d868370949b6416d848919a73c04c008d324c606e20b60ead2c9212e874209ca8c856cccbf9c51daa8f6f58115d0471ae63076fe00a0f04601c9e80784e0154251ee6768848951c527ebe609acaeb85fe6385180013e622eed158e399d460488b0f0606b3d147c83ccc75b814546bc1290a06bf780260827519987ac3370514121c07e1126ecfa17a9abfb5500dcd15583f8746accb7cec4365e06aa0bb57ea3f10550e340cef7834869ac95117e4903c44a658691c6a4bc7cbe28252eaaf6e707e7419eda0c155f54b10cb513fa755d80db9613157c000c63794170e1d3b74a46501caf2f7a820860c4f1d472080845de231c766ca4508117526f34a1243cdd7c2d4259d05cbdd1a2edd0ad27cb43022a5d6f7057b05b221da66c26ba1d5c8abc1e48bf0413c9c123c4e774c6bdb74b5f4ad888faf04a98118c75870e0ff81d3628c8be4abaf363ac90d1a71e006af8c158fb32c7d24d03a7c46c00625e8a8c24936ad9a6724a415d4daac617105f654e2257574b5003ca9a03af449cb70d09e806546fad058781a70f3dd0c3105b69b144b7e7c38f3e9e5a428abd95f5f38c435e2f8251f99d5746b838b15e522e55c1eae89c7e0c8e6512c650ed1108b1888c1d987e8be71650267c81bbbfc507cdb119d881ae0348abc01b432093ab8a2e849cb40c6facece0a49b23107e6fa2c27bae4242a61afcc1e1a186a908ab1eb407f6064b0081328255e5514ed70fcb37c102c2c595210a64f16e2f4a8e2324787fd803cd3dd8c2426464154e2ec04
  | 18 => 0x7b4ed2f3d45a01d1f3ef4e6e9f092ec872de6808162a2fb5e2c2a90f7320c227286fac4069d7e1c162b943ea1afa67ece4e50a32d130ac4ea2cb8eb27342cc9f75e58995e0966e034f32041d211aee8963c9a0a6d60e6c0b0908426212f51cd1c383149b2eea4761808426cd02147c433557ed0730cc6b8a6a202e71a018f3fb23f9cb421d9087c73fa8943c688bfef03449cfd71e87a0128637d1730a2063a7e6d34a5f0291201234d15192ffd153049440f8b09a462aa2f0fcbb20d66ec804d1a1b110597e8b511a9316d5dbe8f08b1d0f0234b0ab78598222452c6a504ed51e0e21a020e8d43860c10c405e824e17a54e820badf40afcf199025a14800f867eb4744e04dbac83a0879316dc1d3830a8ea808c0b3e21eb895b526ac02c464a1d24d4f9e8942161061c7e994f46b43995eec3e465c14bfe1c74017e5ed860a066e16b708b81c38ae085c47038e8056fcbbb8747a5de1ad12bf4044297d57f231c66f8a7ae5fea17e04f1ccac4cb81d680ea8458c08b1cac56147940de1316947f88a60a0ba26f105c9ccc60804b42f32150c604295143d4b240ae6834b06ce2cd143bbeae0d2a05313630e611bdac06080b02f553deb2a0700292f81740d417cf9f604046127d42f2ad25b5055b4e58367c0ec2d9445ff03d421d26e5436c252e3154bbfddb51fcf2252b4387473a154974c2e1e9a95a03252be8e05332d009ba00bc6dabec63e7aee354d79ccc3cea08b1058a1885f0cf48438920e341dac20cd791cd0585641296ea11486322fb9925a2c0075280fc486dab044e905c8d5ef9c226caebe91ccea8c93f0c3be5d8407d9049a3ab956e8838756ce9804162bac34544194755047d5eec864125928d819ccfe558662b602d8004bc48700501e0ea18131cae080b18b77c043150c3b7cdaf080834183808e9d0493a27f0f007fc8396302b41046c2878a8d5e05c0096075927c425c501055b6171f5ce41cf4710863435bc34bc869b6392528b1a4578a4e00378fda5edc8999513a6d911d11aa046ee2f10e50bb5a539204a82589d39279008f40d52cef03ea541ca033e001fb6f3a089b892f69b851718ffa32f67c6bdecdec24301a983138515a5b704a8fc5d772b4867f2e8c401e5b6d2530635dd086a66c3aa87fa56f62b1b18a8fea983d02255454acc0f17b4e3417a48f019c9f4651e284f90303e0b1aba4e791699b5f0f4602600df0b9957603d10477079975d6ad5083133e5280ed3a5157043e3ebf03081bd2d1563de9e009e2925010b6d5a8da0843a1a2ceca591107ed735a35c50c51a7b050f0031b701f086622f554be9084547b2ee6c20191e264d26b8854eb344751866302d1b00f338855a8a290b816bd81db15aa8dcc658236dc19909922d66faf0ca711054cc2b45dfc83e6f029c5ca06d8113b16948f84731b13209e300
  | 19 => 0x408205221a45749a3d67c026d53a6e6b0e4e1c3f3898d4f8b120444810eac1d42a2c4642545b60434b32a64ec7455e72b6d14114b569c3c3f3539b275b01911cd707f8e6a99af35305b58b499c1b047480cab3153a314d87f36aa844e506a965fccc41529113a3276029c3dbbfab6a9c3d304b7a5410c22a1190de097c0d1ae524e77a7f7707a4bbc5d3bddd3c8c81b9967385d40908301b0b1f7e17caec65acdaeb5549c0ffce1eab2922944f116572296478af899b8235a35cb4e5b15bf392d744081713fc96f14e6cfebd35b3b647cd0972cc2e31ea5a22a27d473885d04bcc774c7f05950fa00fec2219e3e36bc32d462f0ac87e6e572d0db8f7408a4d808bbeacac4a303595513ad8743705a51808019f04f414b945c91ca04805839de0252a4b361ab49f1158434a67d751cc1fb765ba81199cd0b7459aefe394241b453e74db7936c9f5409742c050ce06e91b10e9a57ad40af63448e2905b9c501962df34611174e7bac9f9001487c375346f81010aa5660184d886468c7e3a16a3ec2510101800a306cb9521d20092fd5c59e17ed40f20f10706b389698efca1e089a9247b6fa083d12b9716f0acb8b380c965c9e83815683f89604e80c93ea859417761e6958a8a5438b044c46620a334e2ee315d022f6444e203d4a8411694a8c02f83523336466a1abc937ba6a498e240c0349716588484b59f3a71b594240d4602afdc1a109568b98a41d5d822c14fb817f63eb88b1483a810b0cdedcb03f034045cd03c3527135aa665670e146329616948285d75b9c7407562e34efe1e243d6016d019d24fb1e18fa1948b00407f165be11972fe32a3a9b5cb173f5856f4c7b5b733a00587af8a9975b33c4d4891b45e535e4457e4441212bb8406ea91b1a263030447a99b912a18887cee92f593a06f5161a8c0c1680e3a254ce8915e62e7e22ecf9e8d231ca63c68c8546fead0763d1036c5ce17240ff05090f8a0c3275eaee502aaa54d645037a8364a582617cfcd8d2a070c3db6b3448c033855c2a2608ae904e95a50c660890a8741c482f192efb75036ee2a20a790bd434e445ed560329b7d34d975a6c3ffe050c6638acb060b12d2464074ab4cd4c802ab57731b935a28b40584bac844e8e43591c23fc709b0a3552e904df188069b1c711d36195f0219b22857e5b809b50888857f1122bc89862a8e23894c8411b884c10b70e7e5dd2390025a82a15150bac527fca50c08b9a002226fefc390a01d60d470e49a41a1027587d0191ea1255b0889740acaf0f63c8f921859961b5ceccd98b2c35941876c66d419b76064fa831154b07692cec63f1f99b48c6b243470b203ca8322abb087132a3c4ea44d31bca32f20396f494c9426fb7a0627f55258d695c2c55981398dae5c1c24d9b06110b5d96923864f03df7d1ce5e1732b4fe058689e5275a9
  | 20 => 0x12d3cacb919dc9081321eaaf19a1236f802cafe99f9294641c20fef8796053b4cc4428dc05ad03693834ddd1d25a800b26cc8a70a60204b434406ee9c26766a87b85fa1acc3d986f79611ae7d263055f983c1e5c08926ca91bca568473af680e5bab9101fc84f11c6358d7a0c4160529a66945ea57784633c713efe00e552c0cb44502ba6c3c62fbd4172950dfc510c3464296ad35b8a6647809df0eb4b2a30b02b15867f0800750812f1b3809080dec4e404fabaf12d0814dd8bd2a365ccc1664ce53f27079a891087d30b53c46a8687788d132c8a965cb46b884028274f95a09809759c30f577f2e93799a386052f86204f90d86dbdca7f343b0022833a2b9943a81bb1410191a379820516aa3ecc1610a885547093001ec6698847ba971b4ee0a11df85ae65b2117988d10f062a214f0408b02866ee5e112fe1b1860b442e097a11a474b06d1862d0d0002f8e2145d42ca34ce8af050711432313a520987620077628aa4cae7bf72593603747653ff03378fa9888b18f841c2c609f65b47a0ad069451241eac02f23e30fa70290353c83441f1053d544b01d95f1b3561e5eaa19f0300bb14c8885c9b61b911a0438a14149d6f533e94d974f217c59b8fc344c60309521048f9941327962b6440d15897a3622202e59ef9e180d66069883f38a53e665248a480212491e7d408a303da1ab4036507d803d4d96a7cd61f8ea668b255811aeb2c64128cce4f771fe033027bd919d855130648200218838b1ba4d699367179b42b4f8cd5a708fc51a6ffce04b3b4a1c600d801732bd981d4ed7968936b23dc46e5164a89f4581469e501d28e43ff60b29c7027bd469eae84b5b1f0c2090ea59248b84e74705c24e33969d491658d18ed87294d7ccad1134ab62247017210348a7934ccb7411b2b256426ce24067c33a21f34b2a533e258f55da5689fb20d8f39909a491a282e35e58aff829328431064d3112d8ba5c5fb233d568e37546978b7910482431580aeae090a244972583cf4f5432344d22ab2cfa4ab6b2f620a0c36fa0ab699242a5a7aabcf2e1eda29a81ae0978d4986019702e77e2ac96cee725945f90a01c61f2ccd00189458a7c3230461a0a993e7a32937f29a356d9201c3a3a970da6db6b6218ae181597a6bf1dfa4ab98c2289060901239d4106e355ca57b96c8b18880249469f073c390c6a2929d49a82f2b4826f131212067168169d1c0965977c0f5455adbfc16d0e56206d9be04226c287d8580db94084185cbfe3b9e481002f0819bf752ec4a795981a3a315c0c7f16220a3032a8fb292652ed95234ab38d3411e60ac81c117c78044322e5d95f8022266c98868856828960a9af0618ba2a1905f05e0563889b20ab4f46427814ce3e9442407c90d827c341364414191b7b2a421098b3420465a15bddd716d16a70079923e84085ab25
  | 21 => 0xb9acd3f0d073ca45f752933ef24560a3f95a299c70dd4c080522a4df54e70285359226765c64d693248fa65c6e94fd5fb04860c388ce948139f8557a0bd1bd4b81d6430cd303942dce271200f94a910782816263918b146e71e0ff551c293080ad4a0e13af03c5140abba0d248f386ac0bac90e2040e01e494b0a612a60213a081d9edb89454daff3c7df1072649a0bc030807cf15620d6872a2e33227a75610e40837685014a440ba4544dc270d1633ae8547d48a5c00e83a1214ad4781c3af4c78ace84994bc02d66fa8fc85960ffc0ad80aedeed91bd184ebacdb282f5252461b9140a15fa69bea0d13aea0710dc4ac71738011203ec03a89de1e8308aa45cd3fd0680328ca97c929042d70dc35b1c4881dc1076548145fae2b3f9014352a8821e03c6beec2c920304e608aadaf4346e08cebe1c09a8a89069a8dd50d6099739246f49dfc2c4579b8a1f5b2a133815a21db833409797178ae513922453703e1a70dde25a97d745990950361859eec4c421386060a22fc04daa35c80e1073cce3aa7bc03d6027936c30c3594cc1954c72c8b2d9e804812bb0543d2c34a074e062c6b585e1c15b2a152ad60fd97171e2b1ce2008dae22ac502cc87e16ba1fd24d1ca3a964eac285f24a9f948a289165b8105899e28cd11e631a15903f7e1c4427a81e7282d625e2988f8f06f145e85ff808d9f37530cb219178a7c52102c9a0014307d7538e860ab6297162f8b3b93bbb9700ae05b1cf5a06d55250725a04c86aa1b2877214bea7bf0ac294bc9f910e85f9a58220032c177b9903700b11956320c311d0fa171c025025fc4d794104018166cbac85054ed4be21870a978020061f06fc1712217a034c78eb1f43cee734cfe690b33abe0e48fd70d574aec63446f62fa16dbe0b74fef8d305bbc7234f85912c3ccc815c172be762642f35588e8c1d41106d940442be55a3c1100676323902845d4d311276778ae5f691490d124dee03d14769a7a68b82590e4120be1886df690a3825942f4e565cc53f1a53a0890d62d3f5222245bf06a840a86682d920770b8f57e1e3430ff18bfc05b28c3c8ca00ac73c2fbe9fb53de64210c781eed3f554724251838ab4eb5e74be9801a3c4009700bf426692f880dc8c39e2c9f2049dcfee4574b2b019fac928ee89a0e2e6a196540111b3310055d1e2988534a18aa7c086bee80b26c5bd0d52e6c0bac264cda6208d349a6430a1a375116009e3d1f32f366eda8ecc8bd3db005a6823c42fb5142e2ecd1dfee1530295c887da661cdc1afe962884b08a0509a41bd9ee07fb708ebbb1b223f5620cc08c0604ab56244881d53d9229b042e1dc1de407fc78d8b6d0d47236b4fda96d9682a4ef78985f5da7b1a204bfc9d54c0c329c4b6492ec27cb2ab3be4f1d092d30704476c5a8a07bfbb2f984ab053099fc1bd6ff6c8278
  | 22 => 0xac250d8cc1fc9513ba04a50349df6d17c51422b8d4b6f114d561250b809f286d3ae8410d6d3819248f2d798f3840235f02fa44bfc8c905b96325c11e3ed42dcad430bc315d658b210dc32ea14d56ccc15c87f955465242179177a268182637844df993263eaaeb46b40beb7e525a7dd270a121ee25de9daa01226cd06949dc30d472460d3186b3b7641caca30492c00070a963a1daa8076d4d660ce0287161e5d1ea4b0280bdae7cac312cf9a0da31b2c23dcae8ab5e39d69a885be19b21d6c2dcca4c8a716af4fdad552994220e29a001672da22d7c92b80d623571cda8eb0d7e35fa6b18b2c073fa51c48188ad542ba88a511c3a85824a73c574834a81640ecc774c956067892082b7a1d01319a5c14e9cb7f8bc43fda188438f4ce01c0a54eab250598a3e22fbcf7085dc257c076a7610e6fa6017756448889f84196c422d75936a6ae236cee948502c355aa0cdf0954308e5170fd0c6711caa244c40896a325db3b8809c48c729821e12d32957f295560cc2ba175d105f4e389ce1130295b304a9de4ac7af9c5d2c32109ba23a91ec49155a40ad204f46d8204bd2052678cbcc125b00c7619abe9cfb93f9250941a7525c0313053877e947a805c7c2eb25d0feab470d70dd885fb84920710070d9130e20252cd6e1ed2925559f2f3a58d9017f13aea6a90a909235f9668c14bb0dd43c0459055c004d76f30b181ed412788000f5956ca293e547639b9fdd3d791e40748cab9a6d04778426d998010c0c14fa213d89b9065c44a3a04f85e05b003f3585b886d7fccc945be907f471d29d602a21f68269c1500461293c614438ad50329f754082464d312808348a752171122b935582aa40878973016c93e153e055360446fd172e86fd40ac05bc04187e42d4ca3d8fd03b537eb818399aca5521ce03d980843a415976db09f4000ec238c4bcced426e346aa3c7d1e080c1060c6601a9421060bd0d394e6a30797e7c97618338df0007693f84ad9d334f7c3cc9f2503d60614f270ee50e5e47622de4a0b02c47c600a29d6010da5564a0d8e4ea4e95994aad841b3f6c5f6a6db4f8ba92664a8c12d3cc2a083dacf2407bd10d51fac09940c611af3bd0eeea015807c69e442712810e1b1e4c307959eb71458daa4a9d41ac5e7cc82f6d6fa0bcf7ee8aae97769a174d10e320b3917975c48e2711e701037ae0f84029403a24d3f00c18cc984e1dbaca8559194d42264bb79341b14f42067da509b834a21a5007cf47395c7660ba987e8b81343ac06691741b8a6c7020e4a45101258c4a1cc029209e6a04690c55023803a540984a9aa5e53cfeeff594f2b90569e39752e2355c39d26c7c236abde45b80205caaa69440ee3e784d52b1308d8ce0562d86d150320a79f318a437490be6c783114714d0ada5e12879b243c5260f4cbb395bac55947e6148f2db8
  | 23 => 0x837ed31a28816b802e10353ad0c0622301884fb03e4160ae286449e227530f8d163717002fe20b5908c9e6c1ba048800e68c167fb2e54063c30a77598c3d19a98550090862304eb40285190b9253959cca55e238fc624b414392e42985041d8e1a5a0dfd582ac370df00eb5eeaa9cc1efc73114338080045eb4bcf132d2744c430c42e9289a0404d57d549324740f6d448245300d5c8630d988a2af42d9aeb8029c2113526a5bb4ea1056758e90115b0539fd2b9c32e6004b014650a50a97b492807de039bd3ba18d57376b0b507c81a832b81610ca88e375df4000cb780fc86bf2a68cfd336d03aecb2640042a4815c49669d6f31a9554046b111fafe01caa35709810db641e2ca68d671d1c35d8893cc7b29621170e5855feadaa1f942709ef2098876e80f541bf220a7362e2d93d5a7124f80b3800a690ec51e01df024c200d5f2c8ef8b51afd254d200fca21112e0976cf54fc914a80b441e248f017d875a87acd5dc338811b80cf17af26562b9045c94daa70633545efc6ebb48f41bc9af122787643a0aae3c0c213984ea02f38fe09948287c9e54655ae033fca9ab01ca84d34be0986533f3cec7f2670d4a0ca01a0c5081e9f8225155da860580b81b605a6aa8889e63cea12bad590ebe1e367ff09b2869f93d83fba22495118f563e30b6ad594357401d27b8c25f11493e8aa4196b12fad38563aa4d97895e597a81109eb3e580d6859e82f885902dfe866c264b5fb2c909ae894835dc7d0a0f8498217764a701a8d4ec29934bc838e1488b019506a7718ea18f19088444f0231a5f8107c82d1cd31f12586052b10c70ee507f42b1585a32e94940a42973c24b1608ae1449c5ab8228c48798930b790335c644ce7123f84e1894f1ad682041d241ad40f43eea4260df244660fac049c23158553bd0593ca404a0a16543a4a5cb129a829502a42e5c5023e0c0cd85d21264230a7f9c4cad84c193c552a3f393320896148cfe74eef1dcc73226f3d7290850050402890da870515604d417f0809309887579f8b09493d44981d5ad36720a908d653f48cad39cc4830fac915706d8c7b9de1153c7a308bf9b3102be5e70a870581987a0b3a896d286998b149eed306670a2457e2efc83f1a2403d04380c6df94273730d87cbf9847337b4fc1991602ab02808facaa8381e60e68b60425975781bce0218ea93a003be690a019130a3a12736127908186680963113a1d172cd2a0191d81b1a2ef2ad5d1b62b8b541e21114b833f07c30bdf8fbd993f2fc21dadd06a7e70304ac9d8d607b645ec039d5f68d7d07a64190bc68b9862c4f43065d140c6904146d95903965712db29795b59702a223a4ec61f855cd2cda0330acf136a26a288a7008717eafc810ac8e0c7a287928a42288074c6a2a9c9c1850195cbfc4287b6b5004003ace2204511670ab540c9
  | 24 => 0xe00080020038010000b29c000802400280160020002022249801380104191ff602600000058001a6e80058d6802202600100000000754800479e380c839906721fc4c2a7a1ddee2d2c5a60d1217c4948e3b70b13c9ae271f75b8bd54380bd2f5328991dfad835810c8fd002d219ee3c3456a1c08127a298c5f4d9418d1b24fd007412b128a5778a35096d80c33b2ecd45f8e81a00d8027ee0418a3e5d7e647406d09c86c8c57107db322181546db88aa97ee035a64c59d4b3da121e2a6538e84ac2076fbd931d093d7a4e57f963808ed19e0ecf112519d84da42ee85cb2ee9811065253ec182b491a0a1067f87de0af8e9918f5b98d30269ce8b778cf37bdac278f4035b4210c4544e93b4b27276fc7c3fcb3de1b7862a182180e11aec23c8fa7864151069b748b7881256e258e07af01435676a9a883b8e2d74ac6300581338c67587d448612a430322ba6431e80b52eea8680c74207260d622c417b15bc02e8dcf06543d9a3ecae3317d80ec8134cb191cb683be55a6beb13c4156225ac00b12eb2064287839e4be3871310a49f196e4249c61e0b2ad249af20423007e57d7a1654ae860804139bfb4428142131805a051f4a6f598a30ae550aa424d9facec66e824f96858d412f764ce83dd83e9213089c0194b6283840c5000e2b4ae13da44f9dc7a50b604c9e80ada2d5e0692d0e8afa002b47e810c01fc8d4669dc3b14271a9cd64c45ebc62504fc628a7f7a00a8a7c31381629850b2a517c454a067e025d049614d9ec425e72db492e58531fab0c2692312763e733082c8e19f639bd5f6eb32c75facea65760c7073d81b467e8c04c07db62566167a35b42b0465b5c41a17088fdc1d0aae3515f13b052be873126b3a6c800627dcdb79cb2819842a833ea9ff43a0a9e919b2ca04f0cf52d76a852d393c0fb5b2f846e220817500c0a55b5f223009b239b2470726a114db0ea746c8b0d87f38d7e7f508ff559312ed1f28a6543a6b23b4b1641a55c0a973606a07654da260d5226074442e202c772ac77c2b6b2005c4c7319af7a8b006f28a3c146ace427741f9cd0a0b2d34f08c9c5ae1e300228932cfa5a6a143c8e7b030c3c50280406e108521e84e047f40de5a97762fc21617c51b6c57189311471bd2e5ff6ce9819ab804064ee6b9ebe358000ac70bc2bbba251436fd086c88cc608ea301041e24f1031416dd40e8d3d33fc9ed472c015d080eeda0f1aa089455eb9f09f7402640c432cd1d5af2867c0c67d8b89f81651426cc2f3089052840a4d18fb68c38d27fcc1aa2a946e30ab907a328c5122e40c80b992aa1290a5018c3116270925cc998097c2356476540378ee76c6cb160fba120e1018bf55e06b1a1615e72e501f97c15b12a5407ec2e880f02aed52438556180efad9ca400d537c45eb89c720f758985e1593b9f1f052
  | 25 => 0x29800c000992e0338000002005000580079d72660000005e00380000040008000001600800000068042000801800000009488006000800e002002a0000004006800200000080008024c61bcf8006002000500060028014003002c0080006000000400000d000000080120010000d7c60000009178004c0068000011000d3f2005800780000010070000806a00166f8005000a00080e600100000018002000000200d000800e0070027002601c800e002001000f803200180080000006008001a0000000000000000000200018000013000600600020008056000412400000058240004021802c2cd8002000806c002000600b80000070000000009e0008038009807c000000201a0000006800000013c40000000000803a000800c04480000001f20004d5ee0000010000000c003000c05a00000008032c3380080000008002000a007800a026001e001000af8c800c00b000603580040010004007003400a002801080020010f3000080000000000000bd700000002001000600080009aa5840009801f2e726c0d7f00320010004016800c0148004000000801880013fc80500248008000800e0000000013804a4c18000000104600500020098002078003000100000019e76017000a000801a1aa8000000001000656660001116dd60010004800001000060000042fa9e68a000000200100ba00048c0019008c007800a0008002002000000080000088002000000e003000c00c0000001800000800140018032027000e000801203700000000002cc045b00018002003800400299440011e0828e001600f800c048000c0120006000002c00000060000032000134e000800202900040128006015a2a8f0e55c402d0004017001a00d00155d38024001001c01b801800c800000e0024f58800a007801a01580020000000000003200300020058004001b3b40008006011008258a002a8c0a3b4001000200421ee00000000030048000800000180000040008008800603d002000366be3140002001800801180018ab0002000000000000260088008000006202780bc0051f660060000002000000000040008012001000c00100040054cca0020000002801800c8059945bf94000000c014800a0020032014000a000308e047806e0000000000000200080020020000001001447d800000600120028a515180000006000000000582e10010001000000500100048000000000600180e40000014000000000000009fa000005a80ae001800ab65800000480220088030006800000300500018002000000e9cb0002dc10012009800800100300070018000003e4ce0002006362e02080540020008006631a000000000280020000000000000000180400028000005001200000020000000006000400000b60128000003006000000120000c3a0158
  | 26 => 0x1700f0012000804200c005804f002608200179238032005000401b01ea00f00569a00012014805c00000667fc0000000800c000000400680000000000000017c0008038007001c003001800f000e0010000004800c001800018c800e006d8b400308ca000000000000162aeb99a004003002d0026009851600300000000004005802e003001c00680000068f7a00080ad7fc802200a807987000000030000024801a88e80000020002348800000600020038016a420046000800000901d200200380038002000803c00f8070001bcda0000006000009200039a600b0000000801000480000008002002804a00100048f5800000d0002001809a00f0000f3a801000000020038004019017a018000203e0032000800600000000188001852bcc402d0000b2680060040010000002e00080035bd8002019801c0030000003801a0078006005001991e80180018004000000000d800139f0000002808e7fd0d30005000400500000000025a3e0008001800200000012b7801c0120000003005e00000100018000004800001539b0000800400080040000d22baf8000014800400080084be001a00184ec0128008009004c003000c000c12602d00000008002000803001a0002002800001b00c6000ae36000001a00500060000004014808e02f800c009801484e802d7e7801600700cda06801a000001600000000021b980148000003431200fac120008012002800a009000a03b00360030008002000c0298006000007e02f802e004801a004811c004695402ae9db28900100008016031800776f0000000000200200020050000008555a009807400e000000d4d4e004000c000800401600160080034012008a00000015be8000000803417f0054000055400f800001ed2da00000000070012003819c0008004000000000e004e0000014004b7d40418002063800f6ab00000100008009800203000a80078020012802402280020010cd800c8000005800000080020008040000800200000200040000005000e00b80320000028009000e02b800000000560548026057802a0068002000000c000800a0000000000003000000420100000007000076900b348780eefd8002c002000000200000498002004001e0090012001d04c0148000003000c002000c001800e00527ac0000050e81590800580020000002001000a00580260008002ddf000000c804c0013eea0120034635801e001b27a005800001080660198002001001c0320174003800679900840260004002000000705900008006000000e000000a00a003600180020000030003000922280160028004002191200100060018000030000600f0004003001e000800000880d401000177e28030001000c00700f20030008000800a92c00018fe801b6b38000000002a000800200080060038002
  | 27 => 0x2bf9803001e8006000000a002800403980012c3010c015807005cacf804a80060088002038004600e275c016002e01751ae008d9ac0028092009003800b800e000003a004008c006008ca23801200100040000010003802600301a3a1b0044001803a003bb700028054016800322c006a000801c000009400680864a60020004000a001000200080000000132000001c0000026007a5b4005003b0fe000000d80480058006005811200080580010002f61003a015002000780d0000000801a000c00b000c0060e88005800c0020008006001a00000000650002020808400a80960088000001000600fc5a72d6002e02b8122006000a014801a01d8002000000200000020030000002802800c800200580140010012015800e830000204d804a000800e000ce10001003e0092e9e000001200e00000000000edfd98d4450044002001400b0002000c138001583c00100000018000011800e004800001080600048024020000200000060029012d87005e5afb8a0027002400f8000001800c00000120020042007801a007005c00b0082000001c9b000b20018006a95801600b002a024000e0000000011800e00080010a8800c0070006023003a000001c004bbe8003e3de054003000000c5810000a0148000001a1f6005809e0040000000000c005000e0d7002e006d098003d9e200406a2008001a00a89f2004800000a8060001d97a00d800400000300000036000000000100487f60014005800c0050055114000a01500280000160e44b6aa0030064002800e0019c18004800000100460092dc8000800a701804e02d02b63d812c60014820000000174f0002013802adb6002400a800e00080300030024a73800e00d00160000010dc380000005f280020000faa0024012802000a37f90b5b88e000000e0008024000032e00100020014ade0038028000800600801436be00289bc0000000002600000033cc004e00800d954400000000078003e3c6000806cd76000401c000a000802202980aa0000000000d42a00001260030004000000200000000000042013000e00880000028035a84801000080880194f2e000001a812800c025800a002b37803ed6ac001000200080060030018000004600000060000014003800002280140038002005bb8e0038004026000c5dd00000000000009007c00480135cd800201a004c000000000380080560000003802000200360008022001000800000000034f66036619b78231de000806800f000133080fa00a806e018cdee001001e0a4001a000804504b007381100060020000002803e00300060000096010803a0000010009000c003a9e600062f4000800876080080080002000800a00000c6003000601400060d180160038008001003800481060000000005801600ea5f8008809400100260000016005
  | 28 => 0x8007cf1e009201200c7034000c000000c0000006002000000480a20058000d12807000180080018046000000402000180000000000019a02a6814000002800680140ed001c00b0006000000a000803400000380000004000000c000015c00258f00000062027800000e022004b00020010000010023c0100016064804b0e43cc40004c6401980220000004011800000880460020e8000a00286000024000800000000080b5e8c1231a79400881cc01c003c0180030002800e0028000002464915ed86e01280000091dae04f9d5202f001a002802001000000008022004d68000000460110012090000200298f40020052395800600500019a98040003bd4200380009e4001a000803140a80de0018020006016004c00be000000c009017600080e0000111a00500026a5812a00e000545e805600000100000006000800003a8006001000000000000088002000007005400020015aba00e0000000011828480060048006014800405200917c9800c018c4f0ac9000200200a600d802c000047a0008fac005000b9a780120005b24d11ab5e0000262001804a4af801e00000a400004387ab01a810b4df090f80010b1807e00980000003ca000000b800c8006063564a00000040080062004000002e800000025380008020052000400801f60290010024000009d0f2e0118008006003c004000a002800003a8010000004a04f800000300240005e2e000800200014db5f880bc00001d4005000000b80000048008011805002b006200000360000140001800200083c402b8044e98000a00600c0021aed0002000000280420070002008801000480440188002000804a00100620143a2910c00180008000017800e04180220040e60009002a003800e0088062016000000338780105e7e00e800a00700000048000000001201e00c6000001c022000a00300000000098005800000080140005576004811800c800949b80c604e8006000392c001000e00ae6aa000013e001818c000001200000015ff009601580f800b80280000018001004801b00060070062016801200354d20090008002006c000802200000740010006022007865580ee00500080050048000001200000100003d390c0805e0ab65b0050000030aacfc013800e000800201b80020028000006ab020050058000ca5000f000cff200040010010fdb0018008003e005b45e0270002056000e04a810e0050d32f0c800005d802e00580ca000009e6a8804e009000200080040518076015800000000020000204014800400101e2001bc7402f80200236542590c1b000a804e018802a00000080258000cc0825e00f00360250030001014c016017e001355000e800000000128b05b795c38126003ca60000000000800ee002003a0000002018008e006000400b8044030807200120de005000
  | 29 => 0xc00900179ae000a0aa023e004809e00321fa01081c000f190000080002c35e480008008fe980ea007002c0a0001003a81f807416f20008000000002e04d082e007016a020800401c0000dcc8258001800005402b20320022000800200000c6001800000201c331c80000071350001009f230800000100c20000db80010072000000e019995600001760008d72000001c002805a032a05400180000700042000000000b002400000000018004030800000400ec02da17000001e4002007400f0076002000203b001c00f800400056752f280240008000000810b964809800080bc029000200c8276000000600000080450000000803c00ac6a400b13860028050000000000480000008000006005a00d80d20108136001022c0b78072008806a00000236de00000010fbc00280000020248001005e02c0016000001a00500bc03d8044000801e012804c00f80040000002031000000500a6df800040080006065000000480d60038000018000000580256cb4d945be801c0150000003800000000000a0801800000000bc8020d29800200080c400016d4003801e0000002e440000002800a000805e0548258008000e00c00e8001c50000b000000000d3177db16015007200b80040172540b008016001002606a0048006800a03aa8b800100402bd006c009000e000173e000015603d9dca073005400003c52c6000000c98e602280040308060000d74001d0000000801402883fa00d80921168000fff801400100ce0132a1c00100020905386000003741149b800e0052016001d483800c004bb1d17a802a0058078000809207d80040000006003b6a10ad0058018e7a600d0014004804000000aa00300c40018014003807a05b800e037000b208005202f003a024aa2c023000407180bc0002ca800080025e0807134500000000000016800f5fa00100099aa6001800376580b201c82f800a803540900000160048000000200300067d08063716b0e400200980008008004803000581c6004800000180020120028000a03400867ee008814a0a0005005a01b8008288a0018006001817e00280d6000800001a00b800b00680118000000002601600080000028006800800b001a2d7800200000240010024001056203a00140000042008800802b006e03682c806680036a5000400102020110088000008601d801a00300e00000028005d4f60108000015003802882700508000004816a000002c00000540000000002000077c801e02d000056800100008050014800cb39807000080a30c78000002000c0a282be00080045ed8012089087397600000040026036806a0018000034004800419784a280040058000000809e00d00062a5d7a204303a602a801a0558060000000119081ec002010a00802c8560cf6000780000000008005000a230011c0a
  | 30 => 0x2a752001000000080017c0800203b01d8000002600081f601d0000085008a0b901d0025016e01f809800380fa030b5d80db800000a00d200e48fe000810601902bc608800e008002532d000e06101f200d803184e8068001000400d800004c80b0013809b5220004000800e4e30006004000001000000138096084d99e01180078fc1c840005c3a04300760010000004800001c00020370000005800002681dc0000014fb75be002900240099ddc0c7000404e0002000b8b6020804800380100000020000263a9d7006e00180078610244001800e0000091a09825b61080700028000006001403e0002000039e014004000082200000016000000404c8000050002c00003340400000002494a00080a6034007800d000800381340000024067800b7a90004013002200001840000000010800203b33bb0db000e001004a00000060ba803c00006fc000001c0298006002800005a818748081d400100360a500012b4001c0078077474809ad0a800a0040002001006400ebefe005000406100060648008002002200400013cd800000501f804444c800c000c04e80b200c00a003b0000000004a000029800280aae71802c029e2ca01ed01201b000c0000012003000c001026802583560058108010800e08f66ca0e18030462000600a806b7fc80160080000003000000280320040000004801f01780040190190000800a00200a4013800001980e0000000e083000005f801e0030000002802800301b205181c804000920bc80da00400020060010823000400381a5484000002f80080460200005862800b803e00702ba00615cb84c60d60260fb600080660004cb20078016007002e0018002009145600e000006e22f8011800007c0010011004579c0004002001200c054c00800100070022ed701160000540048003a00300cc0000108004434d1df871400480020140066001000801400000020014a2600060030006000000600081ca023000200000020048028006808a0000016020000a0058004004800e00e0032010802c6478006000003c0008000acc0034c570034014805e006802a01e8018010005a0029fba000800e02f800002891c2000000a08d80aa01201ce0ce824400a0044006ae66002800001380a0000000e00801e6000060a4390000008800007100c013b800a008014a001e2ae0070720025003403a00ec05880020820000003a1c200a800a0000070007801802d800d0b2000a001827f26800477c1824e0080002000005405482b60068018000c4140048220d82801600c0030011a15600b9afd9b8800c00302d000780000020046002801e0dc0d7d8e5000008b015400123c4008800602e85e6008806e032000e013873803246800080000a9a05b802d00d400e8000001800600280160005d3a0010004026000a00900020015a
  | 31 => 0x800001bf2f5afba0288058008810404a80ac0a5001800a81f609c001766083a200200aaa920034130814a82c00f602b8ba8083801401080020160092659834001f000c179801c012800f37e031800a00f6379000563c10ec23734ba013800029c0000011803c0468000000008200680280148000029c8b80270042020802012c013c01f368f2a986240b249d02178000005006f5d0196e00884ba00000000131c9c00c808262c8006004b54c00a800002e802400080b0009c3b40000004001db9800e03c00740012038800cd9681727443334004830204b803a0005aecaada34601680028d002b206a017a00780660178000000ab44001001405b01e20ac3de20020026b5880240008d9e023006205f005a008807c9f88000003803603b80725930008002800400000080038ae4001bb6400580c00048050003800e05d80000395ca40558056000025ea8b005801900ea001039600801f407b003600780000008f48018001835700b8000002c08f0028009801200f003c00380e875881c800987f6076002e039d602000000200c0000005800400c008a6290032014805a00380659df80a601a805c002e6cc006d3aa006005e00080000019e7a00e80b40080056006007401b006cb3d0168ab7814803680100118270018001c00000fd3a8812800ec5b2014016cbe98006006801c0a85e7c0065716000006003381b800769ea00180000020094000017e070802a00200020b4011a00081cc00180c000280000db001000000980004fe55b0011b9e001e6015801c01700120000276009800008100c41be012c09500200265384029655605ea78e05780fc08d008c06d009404500300090806001d98c01200160000006012800801e81cc0182b8605181bc0218008055000061f803c00c00000390ff8000014606780028a2803c001a2b600500d60110148000395602a81bc006805c00b806c005003404c8180000009006900bd9be802399980000000004013800a013000000780a6000800600e804e00a001002b84ec02300000018018016800002e018201c817000886360098016071000000100e40000000049000c02958ea0213c5a0038032003801001e800001200c202a0e4000100120430000008b6c404b801a006000602f0018000001600d6216027800e04a002a0048119a2081f003d805115702180380efd90800000bc01bc00d810200680e403b6a5c03f096d8ce042000d03343aa819800d80e002f031a015819e000800e000016c0ca002600680bc000000000f004e00b010002a001e002001000552620070000000020003d01580003b7e00000bc00c00060f780000108000010805006282960299d5600280c2005045c0000046006006c00f800000b00451cc000c00881d200300800c861bc01d83260005754006004801c80b0030814c0
  | 32 => 0x16ac00a013e080000201001c013a002e001a3c800f80be0198390011804000a0768e199e9408a043206c00001291a00084d65001f000005085c406c004c09e883c14d000015a80b69f0000000400c195503d811e0070005800605a01c4005800e015000600600cc00580fe14e8380055801600402f8068800000000840199a4a0028032020000202781fa005808028c007001900b0011807400a8064db380ad3cd01de01302700050016a6986f83460058084804001880cac1e80740a5473e025802a00a801e03408c4157000000421300068466da50079633800c0008004018027c13f0004013000e000804200c87fa12b800410e000402c851a0bcacb40b507ec0238016002814a0a900040068130005029c0089ef38810018000804800c002e928008200000333f880021a081940068005a1c060403b802602200b004f80a0000000a00c801637a820400000160208006003037a00280200e7803e0761ad6003501607b540a00882bfa6458ce048010a004000c0010018026000639085489cc9fda0d1016001401780082f5000f00020006070002a7960a100cb0f0919a142814c00103c600401b00264ea591c000001c81b200d51d6040000a00f0006064294a00301d80088001818000200b08b800001720b3000e00c0068000008f0800000009800e00122e2ad6816e00a8000000000005788f2000531c00300ce002034800f8018003003e0bc02481258000052000d6ee8c5401f81000088008001805200200b800080020d28220001800000c812a0654c092660000015000c00f001e02900b8761001e003000206b000200181be0218bee00180520008024000498e004815ea9e800001a94760038000003800000902fa000803600080280768002001802802600741068000034514767180000ee8420004800023f800c041000000080000fc800664a001001b81dc006009c00280018c5806a00d80000000088044000007300000380
  | _ => 0
def innerK5 : Nat → Nat
  | 0 => 0xe6da1c4b880465d36d0e25c4002b793e8712e200f5b49f4389710028fecfa1c4b8802c7e67d0e25c40023eb3e8712e200b8fd1a438971009c7a8d21c4b880147f6790e25c40123f33c8712e20011f59e4389710028f8cf21c4b8810d777150e25c400aba38a8712e20011fdd94389710028fceca1c4b880447d7650e25c400a3e3b28712e20055d9c4438971021aeae221c4b8802e3f4610e25c40271ea308712e200997cd8438971008cba6c21c4b880247f7610e25c400a3f3b08712e20011f5d84389710009be6fa324b88234dd37d1925c40067b8be8c92e20273dc5e4649710069ea2f2324b8800cf67151925c401a7ab8a8c92e200d3edc14649710019f0e0a324b880047f7551925c40ea7b3888c92e200d3d5c446497103a8fcea2324b8809c7c7511925c41127b0be6c92e20033d05f3649710008faaf9b24b880b6d4310d925c40de7b3886c92e200d3d5c43649710378fcea1b24b880847c750d925c40031f2368a92e200b8f11b4549710008fecfa2a4b8801c7c67d1525c4002b793e8a92e200f5b49f454971029aee2fa2a4b8801c7e7651525c401e3ebb28a92e20011f1d9454971007adee4a2a4b880056c7251525c411b2f1b66a92e2009970db3549710468fecf9aa4b8801c7c67cd525c4002b793e6a92e200f5b49f3549710048feec9aa4b8801c7e764d525c401e3ebb26a92e20011f1d9354971008cbc6c9aa4b880065c364d525c401eb7b926a92e20015b1c9354971029ae8e29aa4b8801754314d525c427337b164a92e21379d587254971002ecc4392a4b8800c7f67c9525c418ab793e4a92e20535dc5f2549710008fecfa1a4b8802c7e67d0d25c401e3eb3e8692e200b1f19f434971008cbc6d21a4b880265c3690d25c40023fb3c8692e20091f99e4349710078facf21a4b880247c6790d25c401e3fbb28692e20111f9d94349710078faeca1a4b880047c7650d25c40232f1b28692e2009970d9434971007adee4a1a4b880056c7250d25c40cebbb8a8692e20055d1c54349710048feec21a4b880047e7610d25c401e3ebb08692e20091f1d8434971000adce421a4b8803d6d7210d25c400abb3888692e20675d5c443497105dea863a184b8802e3f46d0c25c40271ea368612e20075bc9f430971000ada4fa184b880157717d0c25c4122ba8be8612e20051fd9f4309710058fccfa184b880047d67d0c25c400a3e33e8612e200997cda430971008cba6d2184b880147f6790c25c40123f33c8612e20011f59e4309710028f8cf2184b88245777150c25c400aba38a8612e20011fdd94309710028fceca184b880447d7650c25c400a3e3b28612e200b8fd19430971009c7a8ca184b880265f3650c25c40232e9b28612e2039d50c44309710048feec2184b880147e7610c25c40023ebb08612e20051f1d84309710
  | 1 => 0xb44388016d737cda21c41136b9966d10e208bb54cb3688710069eae59b4438800cf670cda21c40067a3866d10e20a53ddd736887102a9eaeb9b4438829e7725cda21c400b3a12e6d10e203d9d417368871002de20b9b443881eed431c9b35c40037290e4d9ae206b3dc5f26cd710069ea2f9366b88034f77149b35c40367a38a4d9ae208bb948526cd71002aee2f2166b8805d751790b35c40123fb3c859ae20071f99e42cd710008facf2166b882355f7350b35c4012ae39a859ae20011fdd942cd710078faeca166b880247c7650b35c4002bdb82859ae20a55e1c142cd71000e5a842166b880255f3710b35c411aae9b8859ae20071fdd842cd710048fcec2166b880047d7610b35c400f37934841ae200f9b49a420d71002aee2f2106b88265751790835c400a3fb3c841ae20071f99e420d710008facf2106b880057b7050835c4042bc382841ae20011fdd9420d710078faeca106b880147c7650835c400f37932841ae200f9b499420d71000e5a842106b8801c7f7610835c400a3f3b0841ae20011f5d8420d71000d6a83a364b881d4f717d1b25c40ea7b38a8d92e208fad50546c97104d9f6e0a364b8800cf71711b25c41136b98e6d92e20213d05f36c971016da8621b64b8800cf7170db25c40171fa368b92e20018f51b45c971055cee2da2e4b880175431cd725c400eb793e6b92e20015b49f35c971004cbe6d9ae4b882365d36cd725c414b3b8b66b92e208d1f5db35c971000adee49ae4b8801d6c724d725c4142ba38a6b92e2005d50c535c971000cbe6c9ae4b880465d364d725c40ab3b8b26b92e200997cdb43c971008cba6da1e4b882e67716d0f25c400abb8be8792e20155d45f43c9710038fecfa1e4b8802c7e67d0f25c40023eb3e8792e20071f19f43c971005c7e8d21e4b8804e3d4690f25c410b3b8b48792e20071fd9e43c9710048fccf21e4b880047d6790f25c4002b7b928792e20075b1c943c97100aaeee2a1e4b88015747150f25c40023fbb28792e20111f5d943c9710038f8eca1e4b8818e771650f25c400eb73908792e20015b5c843c971005c7e8c21e4b8804e3d4610f25c40132f9b08792e2011974d843c9710048feec21e4b8801c7e7610f25c40023ebb08792e20071f1d843c97101bcee2c21e4b8800757430c725c4003aa2186392e2023d58c831c971011ea86418e4b884ed77370c725c400bab9b86392e20055d89c31c971011aea4e18e4b8809677460c725c40473a2306392e20239d8d831c971011eac6c18e4b8808e56360c725c40233a9b06392e2023d50d831c97105fcee4c18e4b8801767260c725c41b6bbbb06392e20db9d9d831c971002ceaec18e4b8808d75760c725c41b7ab9806392e20dbd54c031c97106dece4018e4b8836f65200c725c41b73bb006392e20db9d58031c971004cb
  | 2 => 0x880147f57d1832c40023eabe8c19620053dc5e460cb10069ea2f23065880147f5791832c40023eabc8c196200d3d5c5460cb1047d6a82a3065880047f7551832c400a3e3aa8c19620053d9c4460cb10069eae2230658800cfa7011832c40027cb808c19620051f9d4460cb10008faea230658801e776598432c400b3a32cc2196202b5d55e610cb10028feecb28658800cf67159432c40263f23aca196200b1f11d650cb102a8fa6eb2865880247c3759432c40a63eb92ca19620071f1c9650cb1000cea82b286588226773159432c405b2f18aca19620899d0c5650cb1016cb862b28658801c7f7159432c40063f38aca19620071f5c5650cb10018f8e2b2865880347f7059432c40063f382ca196200d1f5c1650cb10018f8e0b2865880067a1059432c40033c882ca1962083d54d6420c7103fceacb2106388225d73790831c411aea9bc8418e20053dd9e420c710009eacf2106388015775790831c4002baabc8418e208d75dcd420c71044ba8e6a106388005f37050831c4042f83828418e20015ddd5420c71002ae8eaa106388187553550831c40bb3ab2a8418e2001e9508420c71046bac6e2106388014f67610831c40027abb08418e2035d54d4420c71002ae8ea21063880c6756510831c4002eba386418e20897511c320c7106cbae4e1906388227c7270c831c405be39306418e202df1498320c71016baeec1906388226d5760c831c405aeabb06418e20d575dc0320c7106abaae01906388357d2600c831c405be8b006418e202dd5094320c71016eacea190638822755750c831c405aeaba86418e2001555d4320c71016eacca190638835755650c831c41abaa8286418e202df4414320c710479ec8e930638822cf54749831c41127a1ba4c18e205bb50dd260c710069a86e9306388006e64249831c411772a124c18e2089b9cc9260c71045dac649306388226e43249831c41176a1924c18e2001b10c9260c71002dcee49306388006d73049831c42476a9824c18e20033d9c1260c710019e8e09306388006e72049831c4117729024c18e208b9ddd5260c710509eeea930638814cf57549831c400b3a3aa4c18e2005b9895260c71002ce84a9306388016e42549831c400b3212a4c18e205b9d415260c71002de20a9306388014f46790e21c400abb3a88710e20015d5d44388710029ecec21c4388004f57610e21c40ff3aab48510e20333d59e428871045f4a842144388204f57610a21c40633aab08510e202db50d832887103e9eaec19443880ae75560ca21c400b5bba28d10e20053ddd14688710449e8e6a344388034f77251a21c41175ba128d10e208bad5094688710019ece0a34438800cf47051a21c41567bbaa8d10e20573d5d5468871040cea0aa344388016f10551a21c41127b23e6d10e208f3d51f3688710029ee6f9
  | 3 => 0x6f331d8142c41177910ec0a16208bbc4876050b1000de62fb028588034f917d8142c4003788bec0a16200f9e8976050b1007cf24bb0285881767b15d8142c40bb798aec0a16200f9e9d76050b1007cf2ebb0285880347975d8142c41173b30ecaa1620051fd9f6550b102eaee2fb2a858800cf717d9542c401a7db86caa1620019dcc76550b1045cec43b2a858822e7521d9542c40123f9becaa1620111f8df6550b10088fa6fb2a858802c7d27d9542c40063f8becaa1620019dc5f6550b10018ee2fb2a85880347e17d9542c401a3e8becaa16208b9d45f6550b10018f82fb2a85880066f20d9542c400336906caa1620019d8436550b1000ce821b2a85880347f70d9542c40063f386caa16200d1f5c36550b10018f8e1b2a8588016766119542c41173ab08caa1620012fdd94210b1073f4a42a10858801f2f2550842c401f9712a84216200fcb4954210b1003e584aa108588006af7650842c4002d7bb284216208be99c54210b1073f4ae2a10858839fa73150842c41cfd2b0a842162001eadc14210b1072f50e0a108588396af6050842c41cb56b028421620e5ea8414210b1072f4c20a1085880072f7550842c401f973aa84216200fcb5d54210b1000e58eaa1085883a72e3550842c41d3969aa842162007cbd954210b1003e58caa1085883972f1550842c41cbd38aa8421620e5cb4154210b1073f520aa108588226d731cd842c406b2e9ae6c21620893d85f3610b10028feaf9b085880047d57cd842c41cad6a3e4c2162001e950a6110b1003ceecb3088588016746598442c4062baabcc22162001cb50a6510b1000e5a84b2885880147f7659442c40067b38aca21620111f8dd6510b10088fa6eb2885880247c3759442c400e3e392ca21620071fdc56510b10018fce2b28858801c7d7159442c40063e38aca216200d1fdc16510b10018fce0b2885880347d7059442c40063e382ca21620019e8416510b1000cf220b288588014f671d1b32c401a7ab8e8d99620051f9d746ccb10008faeba366588224f61791b32c40067d83c8d99620013e41e46ccb10028feaf23665880047d5791b32c401a7bb8a8d99620053d1c546ccb10008feeaa3665880147c7551b32c41133b0b6ad99620059d05b56ccb10019e82eab665882bd741755b32c41133a0b2ad99620051fdd956ccb1044cee62ab66588226743155b32c41173b10aad996208b9d48556ccb1000cbe60ab665880065d3055b32c40263f23aad996200b1f11d56ccb10038f86eab665882847f2755b32c401e3f13aad99620031fc5d56ccb10048fc2eab66588226761755b32c40123e8baad99620031f05d56ccb1000ce82eab6658800c741755b32c40063f83aad996200d1f81d56ccb10068fa0eab6658800c7c0755b32c40035aa0e8c19620053dc5f460cb10069ea2fa3065
  | 4 => 0x70d85148006769386c28a40033e9c03614520039f2e01b0a2902ef5431d0c51480171fa368628a40138f51b43145205dcbc6da18a2902ee5c36d0c5148002b793e8628a400f5b49f431452002aee2fa18a29010d7517d0c514800a3fb3e8628a400b1f99f4314520008facfa18a2900147c67d0c51480132f9b48628a4011974da431452002aee2f218a29010d751790c514800a3fb3c8628a40091f99e4314520008facf218a2900147c6790c5148086bbb8a8628a40055d1c54314520008feeca18a2900147e7650c51480223ebb28628a40051f1d9431452005c7e8ca18a29004e3d4650c51480132f9b28628a4011974d943145201cea862218a29010d777110c514800aba3888628a4039978d843145201ccb86c218a2900247f7610c514800a3f3b08628a40011f5d84314520028f8ec218a290417652190851480ff369348428a40055dc5e421452021aea2f210a2900147f6790851480863eb3c8428a400fcb508421452002aece2210a29010d7571108514800a3f3b08428a40431f5d842145203dea863190a29040f65218c851480f3369346428a40055dc5e321452021aea2f190a2900147f678c8514800e3f33c6428a40431f59e321452007e5a84228429006d6d72114214800abb3888a10a400d5d5c44508520028fcec22842900147c76114214808b2e9b06a10a40451f5d83508520028f8ec1a8429007f56350c4214803baa1a86210a400f7949c310852022daa6c188429036e77560c4214801e7abb06210a40018f917460852005c788ba3042900047f57d1821480163e2be8c10a40073bc9f4608520598feeaa30429004c7e7551821480ba3ebaa8c10a40011f1d5460852009c7c8aa3042900063c4551821480ba76b928c10a4007ab90946085200fcbc6b9b042900265c35cd8214803e3fabe6c10a40591f55f3608520048f8af9b042901d67b56907204800ef593883902400f7a49c41c812013cf6ac20e409001cfa7610720480027cbb0839024127f44c431c812003bd64e18e409003de9270c720480433dab06390240073e9d831c8120009f2ec18e4090224f771cda42c41072f1ae6d21620051f9d73690b10008faeb9b485881fd7575c5a42c400f3b2b62d21620059d15b1690b10019ee2eab485880147f7655a42c411f3b20aad216208f9d5055690b1000cee62ab485880066f2055a42c400336902ad216200f1f91d5690b10088fc6eab485880447d3755a42c40123e1baad21620071f09d5690b10018fe2eab4858801c7e1755a42c400e3e8baad21620031f05d5690b10018fe0eab485880347e0755a42c401a3e83aad21620031f01d5690b10029ece231a8588034f57118d42c40c32e9a8c6a1620051f9d46350b10008faea31a858822ef261d8142c411778b0ec0a16200f9e5976050b102faf2ebb02858800
  | 5 => 0x31480031f2288c18a400b8f114460c5201dceea223062900047f57118314801e3eab88c18a40073bc9c460c520079da4e230629000cfa7011831480027cb808c18a40033b89f560c52000eaa63ab062900157417d58314801e3eb3eac18a40019b90b560c52000cda85ab062900067741d5831480033a20eac18a40019dc43560c52000cea21ab0629002c7f47d5831480263f23eac18a40131f51f560c520058f88fab0629000c7e27d5831480063e93eac18a40051f09f560c520028fe2fab062902847e17d5831480063f83eac18a40071f81f560c520038fa0fab0629000c7c07d5831480029f23aac18a40014f11d560c52000eaa62ab0629001574715583148207e298e4c18a4005d9147260c52002cdcad93062900166c56c983148003753064c18a40fd3b59f260c52000cdc8b93062900066d45c98314800b3728e4c18a40059b147260c52003cdea1930629001cee47c98314808e76a3e4c18a40013bd5f260c52003cdeaf930629000cef07c98314800f7503e4c18a40033b01f260c52003dd00f93062900856c7549831481fbe298a4c18a4005d9145260c52002cdcac93062900166c564983148003753024c18a40055e15d600c5207cfa262b0062900177051580314800b3c2b2c018a4001bac99600c52000dd24cb0062900067a4558031480033ca2ac018a4001ba909600c52000dd284b006290086eb5258031480433da92c018a40059e95d600c52002cf0aeb006290014785758031480037513ac018a40073e09d600c52000dd04eb0062903e6f351580314800b3d28ac018a40059e145600c52002ce0a2b00629001577179145148086ba8bc8a28a400fcb50845145200dadae4228a29001576711145148086bab888a28a40051f9d84514520028f8ec228a2900465d368d4514800abb8bc6a28a40435d45e3514520068fccf1a8a2901165d360d451480863ebb06a28a40051f1d8351452082ecaa3210a29030d6f5790851480039b2288228a4001cd114411452002aecae208a29003d7557104514801ef29388228a40e19dd58411452000be2e0208a29000756350c45148003aa1a86228a40055d95c311452007aeaae188a29003de5270c4514808b6a9b06228a40db9dd583114520079eaec188a290005f1700c451480031f22e8c28a400b8f1174614520218feafa30a29002c7c57d1851480ba7693e8c28a40011fd5e4614520229bee6a30a290004dc73518514801a3f3aa8c28a40431f1d5461452009c7c8aa30a2900063c45518514801e7a38a8c28a400137cdc4614520229ba6e230a2900047f57118514800e779388c28a40033b49c4614520019f4e0230a29001cf97011851480032f1ae6c28a4009970d73614520218feaf9b0a2900247c57cd851480025fa386c28a40012f51c3614520008feae1b0a29001cef2
  | 6 => 0x163fa3eac20a407f1f91f5610520048fe6fab082900447e37d5841480223e9beac20a40031f89f5610520018fa4fab082900147c27d58414800a3f8beac20a40071f81f5610520038fa0fab0829037d3e4755841480169e23aac20a4029578dd561052000ab86eab08290015747155841480179622e4c20a4005d9147261052002cdcad93082900166c56c984148003753064c20a40ff3b59f261052005cde8b930829002e6c45c984148003371ae4c20a40019b4d7261052082dce6393082900166e51c98414800b3628e4c20a40079bd4326105203f9dc8f9308290004ef57c98414800f37abe4c20a40033bc1f261052003dd40f930829000cec07c98414800f7403e4c20a400bcb115261052013ad8ea93082900176451498414800b372b24c20a40059b159261052000dd4c0930829004f3645c5841480179a22e2c20a40015dd5f161052002ae8af8b0829000cf567c5841480179c22ac020a40055e15d601052002ee0a2b0082900167856580414800375932c020a4001ba499601052005cf68ab008290006ba4558041480173c22ac020a4001ae115601052005c708ab0082900067a3558041480033c9aac020a4001ba909601052000dd284b00829009eeb52580414804f3da92c020a40059e95d601052002cf0aeb008290014785758041480037513ac020a40073e09d601052000dd04eb008290006f24158041481f778a0ac020a40fbbccc560105207dde6a2b0082900167a51580414800b3c28ac020a4001d54c7450c52002aee2fa2862900357517d14314800a3fb3e8a18a40011f59f450c52000eaa63228629003e6d2691431480ff3d3048a18a40055dc5e450c52006aea2f22862900147f6791431480023eb3c8a18a400d5ddc5450c52002ae8e2a286290007553151431480023fbb28a18a40051f1d9450c5202ecf4c0a2862900075531114314804abbb888a18a40051f9d8450c520008faec2286290417c531908314801f36ab48418a407fba982420c520009dacf21062900856c7550831480039622a8418a40fff14c5420c520009deeca10629003e6d565083148042f43828418a405dba981420c52000e6c8a208629009734451043148053ab1a88218a4045754dc410c52000aeeae208629001574571043148002f39388218a40017c5c0410c52005c7e8ba306290006ad42d18314817b3ba8e8c18a40059d147460c520008feafa30629002c7e57d18314801e3eabe8c18a40073bc9f460c520079da4fa30629004e3e4591831480031e22c8c18a40011fd5e460c520078faaf230629001cef27918314801e7693c8c18a40033ec1e460c520009f20f230629003c7f75518314801e3ebaa8c18a40011f1d5460c52000c7e8aa30629004e3d45518314801e76b928c18a4047ab509460c520229e8e2a306290006b441518
  | 7 => 0x6b164222a40059d987211152006ceac39088a9002d3f47c8445480029ea3e4222a400b1fd9f2111520008facf9088a902067751c5a42481023fabe2d21240033e9c31690920009f2e18b4849002f2f45116424801f96a288b21240e5ab5184590920019daec22c849001f6b50d5a42481cb56a36ad21241435bd1f569092077ad88fab484903bd6f70d5a42481deb6b86ad21240e59b51b569092003e5a8dab484903962d46d5a424806336bb6ad21240079b05b569092077cdc0dab484903be6d06d5a42480fef53862d21240017a5c3169092000cdead8b4849002f2f67115424801e97b388aa12400b8bd9c455092007e5ec222a849003f2e61115424801f96b088aa12400fcb184455092000e5c6222a84900072d31115424801797b888aa12400bcb9c4455092005e5ae222a849002f2c7111542481cb97b008aa1240e5cb980455092072e5ac022a84903972c6011542481cb97b808aa1240e54bdc0455092072e5ce022a84903972d7011542481ca96b808aa1240e5cb1c0455092072e5e2022a84903972e1011542481cb968808aa1240e5cb040455092019ceea330884900cc7f57984424801f1f2b48b20a400f8f55a45905202197aed22c829003e3e56116414801f1eab08b20a400bcb9c8459052076e5ae422c829002d3f71116414801a9eb888b20a40edcdc40459052076e6a2022c829002e3d7611641480029ebb08b20a400f8f898459052007c7a4c22c82903b63e0611641481db1e8308b20a40138f917369052000c788b9b482901de5e35cda41480023f3ae6d20a400f1f5d7369052006a7c8fab4829003c7d76d5a414801a3ea3ead20a40311f11f5690520048fe6fab482900447e37d5a41480223e9bead20a40479b90b569052023cda85ab4829000c7f72d5a41480063eb96ad20a40051f1cb569052000cee83ab482900147e71d5a414800e3fb86ad20a40071f5c3569052000cee21ab482900067510d5a414801a9f23aad20a40ed4f11d569052000e6ea3228829003e3e56914414801f1eab48a20a400fab49a45105206ea7eaf22882900073731914414801f1f1348a20a400f8f49a451052090c7e2d228829037e3f6091441481bf1eb048a20a400d4f85e451052009e6c2f22882900353d1791441480279a0bc8a20a40014f59e451052009c7acf2288290007375111441480171f2b08a20a400f8f55845105202197aec228829003ead2611441480179622c8420a407fba98242105207f9dacf210829009d6c7550841480179622a8420a40ffe95054210520829deeca10829009de87050841480bb753028420a40018f917361052005c788b9b082900a65d35cd8414810f3ba8e6c20a40059d1473610520008feaf9b0829003c7d57cd841480067713eac20a400b4f11f5610520078facfab082900067731d584148
  | 8 => 0x878ae40051f19e43c572048aeee2a1e2b90015747150f15c80023fbb2878ae40051f9d943c5720088faeca1e2b900147c7650f15c800abb388878ae40915d5c443c5720048feec21e2b900147e7610f15c80023ebb0878ae40051f1d843c572005c7e8da162b9004e3d46d0b15c800abb8be858ae40915d45f42c5720028fecfa162b902447d67d0b15c800f96212858ae40915ddc542c572002ae8e2a162b902447f7650b15c800a3f3b2858ae40051f1d942c572005c7e8ca162b9004e3d4650b15c80bb37932858ae400997cdb32c572008cba6d9962b900157717ccb15c8122ba8be658ae40051fd9f32c5720488facf9962b900147c67ccb15c8122bbb8a658ae40055d1c532c5720488feec9962b900347d764cb15c800a3e3b2658ae400997cd932c572008cba6c9962b901666f264cb15c80132f9b463a2a4011974da31d1520058fecf18e8a900147e678c745480023eb3c63a2a40011fdd931d1520058fcec98e8a900347d764c745480163e3b263a2a40014fd1f519152009a7a8fa8c8a900367516d4645480033ba8e2d22a40533b49f169152000a7e8f18c8a9004d3d478c645480132f9b46322a4011974da3191520028feed18c8a9004c7e768c645480023ebb46322a40134f91d319152000a788e98c8a900047f764c6454801a3f3b26322a400d1f5d93191520098f8ec98c8a900053f47c8645480269ea3e4322a40131f9db2191520008faed90c8a9003e7642185454801f3aa10c2a2a400f9d108615152007cee6430a8a9003e7632185454801f3a990c2a2a400f9d0c8615152002cee6e30a8a900167637185454800b3a9b8c2a2a40059d0dc615152002cee4e30a8a900167627185454800b3a938c2a2a40019dcc0615152000cec6030a8a90006753018545480033a180c2a2a400f9dc80615152007cec4030a8a9003e7420185454800b3bb80c2a2a40059d9c0615152002ceae030a8a90016747018545480232fb1c62a2a40099718e315152006ceec318a8a9001674618c545480023fb3c62a2a400f1f59e3151520028f8cf18a8a900347f674c5454801e3f33a62a2a400d1f59d3151520008f8ce98a8a9003677614c5454800b3a30a62a2a41438fd1b561152007e5a85ab08a901fe6d62d5845481ca9ea3eac22a400fcb50b511152050cdac5a888a900367561d4445480169fa3ea222a40014f51f511152000ceea33088a901cf1c438c445480e72f1b46222a4009970da311152037cdac51888a9001676618c4454801b3ab0c6222a400b4fd1e311152000a7a8f1888a9002c7f678c4454800a3f33c6222a40011f59e311152000a7c8e9888a9002d3c474c445480023fbb26222a400b1f9d93111520068faec9888a9002c7c764c445480ab36b126222a40059d985311152006ceac29888a9003f2d42c8445481433
  | 9 => 0xe41438fd9345517209ecdac5a2a8b9001f2e42d1545c80063fb3e8aa2e40e54fd1f45517202eade4fa2a8b9004d3e4745545c80029e23a2aa2e4001578dd155172000ab86e8aa8b90036776145545c80033a30a2aa2e401197d8e315172004cb8c718a8b900047f678c545c80263eb3c62a2e40051f19e3151720068fece98a8b9004c7e674c545c801a3eb3a62a2e40011f19d315172009a7c8e98a8b900053c474c545c801b3bb0862a2e40059d184315172000eaa6218a8b900047f670c545c80263eb3862a2e40051f19c315172000a7e8e18a8b9004d3d470c545c800eb793862a2e40015b49c315172006ceec310a8b90016746188545c80023fb3c42a2e40131f59e215172000a7e8f10a8b9004d3d4788545c80263f33a42a2e40011f19d215172009a7c8e90a8b900053c4748545c8002af1ba42a2e4001570dd215172006ceec290a8b90016746148545c800397b8a8422e409dcb9c542117204ee5ae2a108b900072c7150845c81cb97b828422e40e5cb9c1421172072e5ae0a108b903972c7050845c81cb970828422e40e5cb441421172072e5820a108b9001f2f7650845c800317bb28422e40074bdd9421172003e5e2ca108b9001f2e1650845c800f968b28422e4007cb059421172072e5a0ca108b9001f290650845c800396a146222e4071978da311172038cb86d1888b9001677168c445c801b3a8b46222e40071fd9e3111720028fccf1888b900047d678c445c800396a126222e40011fdd93111720038fcec9888b900347d764c445c800e3e3b26222e40059dc59311172006cea2c9888b900072d420c445c8003aa9886222e40239d8583111720028feec1888b9001c7e760c445c80023ebb06222e41415bdd542c572003e588aa162b90006ad42d1b15c80fe7793e8d8ae40913b49f46c5720008faaf2362b90256ad4251b15c80027db828d8ae40033e1c146c5720188f8eaa362b9000cef2711b15c825a769388d8ae40011f5d446c572053cec2b9b62b900167415cdb15c80f23f3ae6d8ae40033bc9c36c5720959da4e1b62b9008e76150db15c800b3a0a86d8ae40011f5d436c572035ade4fa2e2b900157717d1715c8122ba8be8b8ae400b8fd1b45c572000c7a8da2e2b9002c7f76d1715c81223ebb68b8ae40915ddc545c572002ae8e2a2e2b902447f7651715c800a3f3b28b8ae400d1f5d945c5720028f8eca2e2b900063f4651715c80271ea328b8ae400997cdb35c572049cba6d9ae2b902447d76cd715c8122bbb8a6b8ae40055d1c535c5720488feec9ae2b900147e764d715c801a3ebb26b8ae40051f1d935c572000cbe6c9ae2b900465d364d715c800eb793e878ae40015b49f43c5720028fecfa1e2b9002c7e67d0f15c80023eb3e878ae40051f19f43c5720028fecf21e2b900247e6790f15c80023eb3c
  | 10 => 0x31fc9d6510720028fa4eb28839000c7c2759441c800a3e38aca20e40019e8816510720078fee0b2883904cfc53190831c800f3732c8418e40013b59e420c72096f8a62a106390004ef7650831c800f3732a8418e4093754dc410c72011bce4e20863900a7563510431c8046bb3a88218e4001ab50b460c720039de4fa30639003ced27d1831c800e3fabe8c18e40011f55f460c720039de4f230639003ced2791831c800e3fabc8c18e40011f55e460c720039dce4a306390256ad4251831c81267a38a8c18e4001ad105460c720009f6e0a30639000cf87051831c80023fbaa8c18e40071f1d5460c720039de4e230639003ced2711831c80067d3808c18e40013e5c0460c720038fcea23063900047d7511831c8263e298e4c18e4005d9057260c72002cdecb93063900166c65c9831c8042b6abe4c18e412bf14c5260c72002ec82a93063900166f6549831c800b3632a4c18e40953b91d260c720079da8e930639008ee77149831c801f7238a4c18e40033b9c1260c720019d8e093063904aee51049831c801f37baa4c18e40013bdd5260c72002cde2a930639008ee61549831c800b360aa4c18e4023b9055260c72000eaa633286390015741799431c8003aa98aca18e40055d1c5650c720019de4eb28639008cf47159431c80473a0aaca18e40019b909650c72000cda84b28639004c7e4759431c80163e23aca18e40031fc9d650c720028fa4eb28639000c7c2759431c80473b90aca18e40239d085650c72011ceee2b28639014c7d7159431c80033a38aca18e40051f1c5650c720028e8e2b2863900067a2059431c801e3fb82ca18e40019dc41650c72000cea20b28639003ead42d1a21c80fe773928d10e400fab5094688720019f0e0a3443901b65d35cda21c80da3ebae6d10e40a79d8573688720a1b5ee89368b9000cef7649b45c81cb57a324da2e4007cb91526d172003e588a9368b900053e4745745c80169e23a2ba2e4001578dd15d172000ab86e8ae8b9014e6f2645745c80033b8b22ba2e400d9d45915d172004cbe6d18e8b900465d368c745c80df3793463a2e400b1fd9e31d1720028fccf18e8b900047d678c745c80029f23a63a2e400b4f11d31d1720008feec98e8b9002c7e764c745c801a3ebb263a2e400b1f1d931d17202acde4c98e8b9000755310c745c80169fa3863a2e40014f51c31d172010cde4c18e8b9001677160c745c801b3a8b063a2e40051fdd831d1720058fcec18e8b900047d760c745c80d73793443a2e40059dc5a21d172006cea2d10e8b9002d3f4788745c80029ea3c43a2e400b1fd9e21d1720008facf10e8b900053e4748745c80169e23a43a2e4001578dd21d172000ab86e90e8b900047f7648745c80163e3b243a2e40539bc9921d172002cee2c90e8b90036751648745c814277938c2a2
  | 11 => 0xd8365402100cba6c1b2a0108447f670d95008403aba1862a804201d510c315402111eac6418aa01088f54320c5500844b3a23062a804201d5cd8315402108cec6c18aa01084675360c55008403aa9b062a804211954d831540215fce84c18aa010b3577370c5500840bab9b862a804205d9c9c31540211faea4e18aa01081765270c55008402b293862a8042059dd9c315402102ceace18aa010aff72400c5500857fb918062a8042bfd54c0315402111ee64018aa010aff70200c5500840bb9b0062a8042bfdc9c0315402102ee2e018aa010ce6772688550085933a13442a8042c9dc902215402164ee46110aa01081f73208855008593b810442a804205dcd82215402164ceec110aa0108057737885500840aba1bc42a8042c55d49e215402102eca4f10aa010b26776788550084d73ab3c42a8042c9dcc1e215402102ee20f10aa0108057a474c15008403ad21a60a804201d650d30540210deb6e6982a01086d7b734c15008403b5b9260a8042075e9c9305402100ed0e4982a01081d78724c1500840eb439260a804201d6cc9305402100eb264982a0108157a764c150084133c3b260a8042055e1d9305402104cf66c982a0108075a364c150084133c1b260a804201d60d930540217cee6e2982a0108157a714c15008403b838a60a8042055e1c530540217cee662982a0109275a314c15008403b818a60a804249d60c5305402100ea062982a01080772214c150085f3b890a60a8042b59d45716d0b205a8faeb8b6859017e751518542c80be3eba8c2a164143abd936550b202eb5a8fb2a859001f2e45d9542c801fb482ecaa164007cbd936550b20a1cdec9b2a859003e6e61d9542c80033630ecaa1640b39bd9f6550b2072ade8fb2a859001f2f47d9542c827b96a3ecaa16413d9bd836550b209ecdac1b2a85904f72f40d9542c827b96a06caa16413d5bdc36550b209eadae1b2a859001c7e75cda41c80023ebae6d20e40959b90956907204acda84ab48390006771055a41c80033a882ad20e40b31fd1d5690720068fc8eab483900447e3755a41c80223e9baad20e40091f0dd5690720018fe4eab483900147d2755a41c80063e13aad20e40051f05d5690720078fc0eab483904b4ed6790841c804eb6abc8420e412de95054210720999deeca10839002f2c4550841c80532e9ae6c20e40071fd5f3610720008faaf9b083900166f65c9841c800b3632e4c20e40275b55f261072002cdeca93083900166c6549841c80ba76a3a4c20e40033b9c12610720019d8e0930839002e6f4549841c80173622a4c20e40019b8d5261072000cda6a930839003e6f7549841c800277baa4c20e40059bc55261072002cd82a930839000cef2759441c80ba3ea3aca20e400b1f11d6510720088fc6eb2883900447d3759441c80123e1baca20e400
  | 12 => 0xd42102aecea21e2a10805757510f150840a7b9be6d8a84205b5cdf36c542153dae659b62a10a9ed532cdb150854e7bb966d8a842a73d5cb36c542102dae6b9b62a10816d535cdb150859a7bbae6d8a842053d5d736c542153cee4b9b62a10816e725cdb15084026f9b88ca80421f374dc4654021039de4e232a01086cf57111950084031f2368aa80420b8f11b45540210d8fecfa2aa01086d7b07d1550084363e3b28aa8042138f919455402100c788ca2aa01086d7870515500843f2f1b66aa804209970db355402102ea8639aaa01086c7f67cd55008436bd83e6aa8042031f9d935540210d8f8ec9aaa0108465e364d550084032e1b26aa804205d50c535540210daf0e09aaa01081de8724c1500840a7c3b260a8042057c1c5305402124fa062982a01081578754c15008403ad9aa60a804201d64d5305402101cf6ca982a0108465e36d0d50084132e1b686a8042075bc9f435402100ada4fa1aa0108047f67d0d50084163f33e86a8042011f59f4354021058f8cfa1aa0108157717d0d5008486ba8be86a80421b5ec1f435402100af20fa1aa01084e3e4690d50084171e23486a804211974da4354021008fecf21aa0108047d6790d50084123e33c86a80421b5ec1e435402100af20f21aa0108047f7650d50084223f3b286a8042111f5d94354021008f8eca1aa0108265f3650d50084232e9b286a8042435ddc5435402102ae8e2a1aa01086d7a7050d50084271f23086a80420b8f118435402108cbc6c21aa0108265c3610d50084023f3b086a8042011f5d84354021048f8ec21aa01086d7a7010d5008402bcb8086a8042d39b09b425402169ed041a12a01086c7f67d0950084023eb3e84a80421b5ec1f425402100af20fa12a01081f2c4250950084023fbb284a80421b1f1d942540217feca42a12a0108057b705095008436bc38284a804207dac81425402168cd84d992a010b476820cc950084363fb3e64a8042011f59f325402121aec2f992a01086d7b07cc95008402bc83e64a8042011fdd93254021018fcec992a01086c7c764c95008486bbb8a64a8042055d1c532540217eeca42992a0108057b704c95008436bc38264a8042015e41f465402100c7e8d232a01082c7f679195008402afb9a8ca804201571cd465402103ad8e4a32a01084e3e46519500859ebbb8a8ca8042055d1c5465402100af6e0a32a01082e3f4611950084031ea308ca80420157cdc465402100aba6e232a01081d6f271195008436b69388ca8042131fd9c465402102aece2232a01086d75711195008402bc83e6ca80420197cda3654021048fecf1b2a01081577178d95008436ba8bc6ca8042014f91d365402100a788e9b2a010b456f724d9500840eb63926ca804211978d9365402166aeee29b2a01081574714d95008402bdb826ca80420997c
  | 13 => 0x10faba6f2066a108247f6790335084063f33c819a842011f59e40cd421018f8cf2066a108255f37103350843eae9b8819a842075bc9c40cd42100ada4e2066a1081577171033508562ba8b8819a842031fdd840cd421048fcec2066a108047d7610335084063e3b0819a8420957cde20cd4210faba6f1066a108247f67883350843e3eb3c419a842099790d06cd42100cba868366a109265e3141b35084932e18a0d9a842131f91d06cd421058f88e8366a108147c3741b350840e3f93a0d9a842af1f89d06cd421038f84e8366a10a947e1741b35084aa3e8ba0d9a842051f05d06cd42104cf6608366a10826783041b35084133db820d9a842058f8c7460d42102c7a63a306a108163c31d18350840b1f90e8c1a842058f887460d42102c7a43a306a108163c21d18350840f1f9068c1a842078f883460d42103c7a41a306a1081e3c20d18350840b1f8868c1a842058f843460d42102c7a21a306a108163c10d18350840f1f93e8c1a842078f89f460d42103c7a4fa306a1081e3c27d18350840b1f8be8c1a842058f85f460d42102c7a2fa306a108163c17d1835084171f83e8c1a8420b8f81f460d42105c7a0fa306a1082e3c07d18350840f1fb928c1a842078f9c9460d42103c7ae4a306a1081e3c72518350840b1fb8a8c1a842058f9c5460d42102c7ae2a306a108163c71518350840b1f18a8c1a842058f4c5460d42102c7862a306a108163f21518350840b1f10a8c1a842058f485460d42102c7842a306a1084e3f7051835084271f3828c1a842138f5c1460d42109c78e0a306a1081e3f20518350840f1f1028c1a842078f481460d42103c7840a306a108163f10518350840b1f0828c1a842058f441460d42102c7820a306a1082e3f4690035084271ea34801a842039e982400d421028fecf2006a1080c7e6790035084023eb3c801a842031f19e400d42105c7e8c2006a1084e3d4610035084073d300801a842075bc9c400d42100ada4e2006a108157717100350845eba8b8801a842051fd9c400d421018fcce2006a108047d6710035084063e338801a842131f91d600d421058f88eb006a1080c7e27580350840e3e13ac01a842031fdc5600d421018fae2b006a108067a4058035084033c202c01a842079ec81600d42103cf040b006a108167b70580350840a3fb82c01a842059ec41600d42102cf020b006a1081e7b42580350840f3d212c01a842079e509600d42103cf084b006a108067b4758035084033d23ac01a842019e51d600d42100cf08eb006a1081e7b27580350840f3d13ac01a842079e09d600d42102cf682b006a108167a41580350840b3ca0ac01a842059e105600d42102cf462b006a108167931580350840b3d90ac01a842059e885600d42102cf242b006a108167b71580350840b3d38ac01a842059e1c560
  | 14 => 0xb8859b08a108165f21cd8450840b2f10e6c228420597487361142103cbe419b08a1081e5e20cd8450840f2e9066c228420797083361142102cbe219b08a108165e10cd8450840b2e8866c228420597043361142103cbe4f9b08a1081e5e27cd8450840f2e93e6c22842079709f361142102cbe2f9b08a108165e17cd8450840b2e8be6c22842059705f361142104cbe0f9b08a108265e07cd845084132e83e6c22842099701f361142104cbe6d1808a108465d368c045084073d3046022842055dc5e301142119aea2f1808a108147f678c045084063f33c6022842011f59e3011421018f8cf1808a108056f724c0450840eb63926022842335ddc5301142102ae8e29808a1092754314c045084023fbb26022842051f1d9301142104cbe6c9808a108465d364c045084073d30260228420997cd8301142108cba6c1808a1080e7a600c0450840a3fb386022842031f99c3011421008face1808a108447e3758045084223e9bac022842091f0dd601142100cee62b008a108167431580450840a3e38ac022842019e8c1601142100cf260b008a108067830580450840f3d902c022842079e081601142102cf6e0b008a108147f70580450840b3d882c022842059e041601142103cf484b008a1081e7942580450840f3c212c022842079ecc9601142103cf464b008a1081e7932580450840f3c192c022842019ecdd601142100cf46eb008a10806793758045084033c1bac022842079ec9d601142103cf44eb008a1081e7827580450840b3d98ac022842019ccc5601142102cf462b008a108167931580450840b3c18ac022842059c0c5601142102cf642b008a108167a21580450840b3c90ac022842059edc5601142102cf4e2b008a108167971580450840b3c38ac022843119755a43cd42102abeaf21e6a108155c5790f35084038ea1e8b9a84205d50c745cd42104abe6fa2e6a1087d5d37d1735085533b0b68b9a8421f57dcd45cd42104ab8e6a2e6a108071d4351735084123f3b28b9a842091f1d945cd42100eb2612866a1080e7b069433508412af9bca19a8421f574de50cd4215dda863a366a10814df37d1b350840e7793e8d9a8420f3b49f46cd421029ee2fa366a10834f517d1b35084171fa2e8d9a842018f51746cd421058feeba366a1087c7d75d1b35084023eabc8d9a8420d3ddc546cd421029e8e2a366a1087c7f7551b35084223ebaa8d9a842018fd1546cd42109c7a8aa366a108e6d43111b35084023eab88d9a84249b50c506cd421689dc4e8366a1081cec2741b350859a7b0ba0d9a842053d05d06cd4210f8fcae8366a108067a5041b3508412af9be859a8421f574df42cd421048fecfa166a1087c7d67d0b350843eafb9a859a84209571cd42cd42103e5884a166a1087c7f7650b35084123e3b2859a8420957cde40cd42
  | 15 => 0x9868a108465d364c345084169fa3861a2842014f51c30d1421018feec1868a1082c7e760c345084023ebb061a28420b4fd1e20d142100a7a8f1068a1082c7f6788345084033b98a0da2842019d0c506d1421028f88e8368a108447e3741b45084223e9ba0da2842091f0dd06d1421038fe4e8368a1081c7c2741b45084173da020da28420b9e10106d142105cf6e08368a1081577178c24508502ba8bc6122842039ec1a3091421018feed1848a108147e768c245084023ebb46122842031f1da309142109a7c8e9848a108053c474c245084023fbb26122842051f1d9309142104cbe6c9848a108465d364c245084073d8326122842031fdd83091421028fcec1848a108047d760c245084223f1ba0d22842111f4dd0691421048f86e8348a1081c7c2741a450840a3e0ba0d22842139e901069142109cf2808348a108067a3041a45084033c9820d22842079ec81069142103cf0408348a108167b1041a450840b3c0820d22842059edc106914211cda86231a8a10aef9431d0d45084171fb2e86a2842076bc9f435142102b6e2fa1a8a108153f57d0d450840a9e2be86a2842056d1c5435142102a7ceaa1a8a108153c7550d45084171fb2a86a2842058fd93455142102a7e8fa2a8a1084d3e474d545084029e23a6aa28421197d8d355142100cb8c69aa8a108071d434d5450840baa18a6aa2842019ed82505142101cf0c12828a108053f4794145084269ea3ca0a2842098f98f435142104c78c7a1a8a10aef1e31d0d45085778e18e86a2842134fd9f435142100c7ecfa1a8a10c4d3d37d0d45084278e9be86a2842074fc9f435142103a784fa1a8a108153f17d0d450840a9e0be86a2842014f41f435142108cbec79928a108265c63cc945084023fb3e64a2842131f59f325142100a7e8f9928a1084d3d47cc945084263f33a64a2842011f19d325142109a7c8e9928a108053c474c945084232fb1a64a2842099718d32514212faeee29928a1081574714c945084273d206c0a2842139e5036051421018fe8fb028a108147e47d81450840a3ea3ec0a2842091fcdf6051421088fa6fb028a1081c7f27d81450840e3e13ec0a2842051fc5f605142109cf20fb028a108465f638c145084132e31c60a2842011fd9e3051421018fccf1828a1084c7d678c145084063e33c60a2842014fd1e305142109a7a8f1828a1081577178c145084beba8bc60a2842111fd9d3051421098fcce9828a108047c674c145084269ea3a60a2842099798d305142108cbac69828a1093f1d434c145084232fb1860a2842099718c3051421008fece1828a1084c7d670c145084063e33860a2842014fd1c305142109a7a8e1828a1081e6c62881450840f9621440a2842131f59e205142100a7e8f1028a1084d3d47881450840f2f2166c22842079750b361142103c
  | 16 => 0x2108e7556510c310841f729368418842b7d54d7420c42107ceacba106210875d737d08310843eea9be84188425f5d55f420c4210fbaee6a106210875d4735083108447d2212841884223f10c9420c42107dca4ca106210ad5777550831084c3aa9aa84188420f9d595420c42163dce869306210876e643498310858f72a1a4c188421db910d260c42107dce8e930621083ee647498310841f72a3a4c188420fb911d260c4210edce6e930621088ee6374983108447631ba4c188425bb94dd260c4210edc86e930621096ec437498310840b73a2a4c1884205b9915260c42102dca8a9306210816e445498310840b739aa4c1884205b98d5260c42102dca6a9306210816e435498310840b73baa4c188420f99dd5260c421029ceea9306210806e6404983108403722024c188421db9cc1260c42163dcc609306210b1ee530498310858f629824c188421db90c1260c42107dcee0930621083ee670498310841f72b824c188420fb91c1260c42102dcea09306210816e650498310840b72a824c1884205b9141260c4215df2863a1e8a10d263d56d0f450840ed793e87a2842056dc5f43d142102a7eafa1e8a108153c57d0f450840ada38a87a2842054f9d543d142102a78eaa1e8a108053e474d745084169e23a6ba284201c750d35d142102ea8629ae8a108465d364d745084073d834a1a28420b4fd1e50d142100a7a8f2868a108065d35cdb450840e7613a0da2842053d05d06d142100cf4a08368a1082f1f7350f450840e9f39287a2842074f1c943d14219fe6ee2a1e8a108153e7150f45084039a38a87a2842054f1c543d142102a68e2a1e8a10cff373150f45084029fb8287a2842018fdd943d142105a7eeca1e8a108263f3650f45084178f1b287a2842098f0d943d142105e386ca1e8a1081e6f26ccb45084169fa3e65a2842014f51f32d1421058fecf9968a108047d67ccb45084029f23a65a28420b4f11d32d14215aaeee29968a1081574714cb45084023fbb265a28420b1f1d932d142112eae8618e8a1089737430c7450844b8ba1863a284201cd50c31d142112ea88618e8a1088f36420c745084479a21063a284223d58c831d142111ea86418e8a1081737470c7450840b9aa3863a284205d5cdc31d142102cee8c18e8a1081737460c7450844b3b1b063a284225d58d831d142112cac6c18e8a1084675360c7450844baa1b063a2842239dc9831d142111ce84c18e8a1081676760c7450840b3abb063a28420b4fd1e30d142100a7a8f1868a1081577178c3450856aba8bc61a28420b1fd9e30d1421018fccf1868a108047d678c345084063e33c61a28420b4fd1d30d142100e3a869868a108056f724c3450840eb639261a2842b55ddc530d142102ae8e29868a1080754314c345084023fbb261a28420b1f1d930d142104cbe6c
  | 17 => 0x3e7a20418358841f3c9020c1ac42059ec41060d62102cf0208306b108167b70418358840a3fb820c1ac426b3d45e46416212f9da4e2320b109acf51711905884d67a8b86c82c42018f91b454162105c788da2a0b109ac7e76d1505884d6bd3868a82c426b1f1d9454162109c7c8ca2a0b108063c4651505884d6bc3828a82c4205dcc41454162136cbc6d9aa0b108265c36cd505884d63f3b66a82c426b5e9c3354162102ee6219aa0b1080c7e764d505884d63e3b26a82c4211978d9354162100cb86c9aa0b109ad78704d50588402b793e8682c420f5b49f4341621008fecfa1a0b1082c7e67d0d05884023eb3e8682c420b1f19f4341621008fecf21a0b108047d6790d05884123e33c8682c42915ddc5434162102ae8e2a1a0b108047f7650d05884223f3b28682c42111f5d94341621008f8eca1a0b108057b7050d05884d6bc3828682c42138f91a424162105c788d2120b1083f692090905884d63fb3c8482c42011f59e424162135af60f2120b108057907909058841f96a108482c42138f918424162105c788c2120b10bae6e2610905884d63f3b08482c42011f5d8424162135af4e02120b10805797010905884232f1b46482c4209970da3241621358fecf1920b108047d678c905884063e33c6482c426b5ec1e324162100af20f1920b108057907d1905884031fa348c82c42915bdc9464162109c7c8ca320b108057b7051905884171fa308c82c42018f518464162135ade4e2320b10cb56d27119058840abb8b88c82c426b5d45c4641621098fece2320b108057907cd905884032f9b46c82c42055dc5e364162135aea2f1b20b10a456f724d905885c6b63926c82c4211978d9364162100af6e09b20b108265f360d905884032e9b06c82c42111fd9c3641621028feecab486108063f4355a43084031ea1aad218421d9dcc55690c210ece862ab486108447e4755a43084123e1baad21842071fc9d5690c21038f84eab486108147f1755a430840a3e0baad2184201974c15690c21008fee0ab4861080c7e7055a43084063e382ad218420997cd50690c214fcba6a83486108047e5741a430840a3e2ba0d21842859e9410690c21038f8e4b2886108147c7159443084732f18aca2184239970c56510c2100cde42b288610806752159443084033690aca21842011fdc16510c21018fce0b28861080c7c70594430856f2e9ae6da1042b71f5d736d0821069ec2e8368410acc7e5741b42085673d2820da104261974d46350821308faea31a84109767a50d8142084ba3eabec0a10420fab50b46cc821069eae3a366410834f77151b320841a7b0ba0d99042af1f95d06cc82157cf4a083664108e7c72610c3108473e2930861884239d5114430c4211cbaaea2186210805557510c3108547ab928861884239f1c94430c4211ceacca2186
  | 18 => 0x474d545884232fb1a6aa2c42019718d355162100cf6c182a8b1080e7860c1545884029fa3e0aa2c42134f51f055162100abe6f82a8b108055d37c1545884232fb1c64a2c42099718e3251621098facf1928b108053f478c945884269ea3c64a2c429d8fd0b60516214ec7a85b028b1084e7a40d8145884273ca06c0a2c42051f91f6051621028fa8fb028b108247f37d8145884223e9bec0a2c42431f89f6051621338fa4fb028b1084e7907d8145884023fb3c60a2c42031f99e3051621098facf1828b1080c7c678c1458840abb8bc60a2c42815d45e3051621088fece9828b1084c7e674c145884023e33a60a2c42134f91d305162100a788e9828b108465f634c145884132e31a60a2c42011fd9c3051621098face1828b1080c7c670c145884029fa3860a2c42134f51c305162102aee2e1828b10a0575170c1458842b37b1040a2c42019ed80205162101cf0c01028b1084c7d6708145884029fa3840a2c42134f51c205162100abe6e1028b108055d37081458840abb8b840a2c42815d45c20516212f9da4fa366b108047d5791b358841a7bb8a8d9ac42673bdc960cd62100de220b066b109265e3558335884932e1aac19ac420957cdf45cd62136aba6fa2e6b1082e3f46d1735884031ea368b9ac426d1f5db45cd62136abee6a2e6b108255c7351735884da3fbb28b9ac42111f5d945cd62100c7e8ca2e6b1084e3d4651735884073d3060b9ac42019e58305cd62104abe6f82e6b109b55d37c1735884da3eb3e0b9ac420957cde42cd62136aba6f2166b108247f6790b35884da3eb3c859ac420fcb50842cd62104abe6e2166b109b55d3710b35884123fb38859ac426d1f59c42cd621048fecf2066b1080c7e6790335884023eb3c819ac42031f19e40cd62102aee2f2066b108bd75179033588412af9b8819ac426d574dc40cd621048fece2066b1080c7e6710335884023eb38819ac42031f19c40cd62100ade4e2066b1083d6d27103358840abb8b8819ac422f5d45c40cd621098fc8eb066b1082c7c47583358840a3e1bac19ac420997cc960cd62126cba64b066b1099c7f7258335884863eb92c19ac422b1f1c960cd62124cbc62b066b109265c3158335884133d982c19ac42099e0c160cd62104cf6e0b066b108067a1058335884033c882c19ac42014fd1c20cd62100a7a8e1066b108255f3708335884daae9b8419ac42091fd9c20cd621368face1066b108157717083358845eba8b8419ac42039ec1a400d62102aee2f2006b10ac57517900358840a3fb3c801ac42031f99e400d621008facf2006b1080c7c679003588402b7938801ac420f5b49c400d62102aee2e2006b10ac5751710035884063fbb0801ac42051f9d8400d621008faec2006b1084c7e4741835884163e23a0c1ac420f1f89d060d62100cf4808306b108
  | 19 => 0x5500c442bc3824aa806205dcc41255403109c7c8d212a01882e3c46909500c4023fb3c84a8062011f59e4254031038f8cf212a0188157717909500c496ba8bc84a8062215ec1e425403100af20f212a0188047f76509500c41e3f3b284a8062011f1d9425403110af4e0a12a0188072d42109500c41f3713084a8062079b0984254031008fcec212a0188047d76109500c40e3e3b084a8062215e9c0425403100af2e0212a0188057907c99500c403379344ca8062014f91d265403100a788e932a01883e6e26499500c5b6bbb8a4ca8062055d1c5265403100af6e0932a01881e6f26099500c403369304ca8062014fd1c265403100a7a8e132a0188157671099500c442bab884ca80620d1f89d5690e21028f82eab4871080c7f0755a43884023f03aad21c42031f01d5690e21069eae39b48510a0e5d35cda42885063ebae6d214427f1fdd50690a213fcf60a83485108d65d35cd8428846a3ebae6c2144251ab5096010a2100de220b0085108c47f7558042884633d82ac021442673bdc960d162100de220b068b108053e474d745884169e23a6ba2c420197cd935d162108cba6c9ae8b1080e7a60c1745884033cb060ba2c420b4fd1f05d162100a7a8f82e8b108055f37c174588402ae9be0ba2c420997cda32d162108cba6d1968b1082d3f478cb45884029ea3c65a2c420b1fd9e32d1621008facf1968b1082c7f678c345884063f33c61a2c42011f59e30d1621018f8cf1868b1081577178c34588466ba8bc61a2c42014f91d30d162105a788e9868b108047f764c345884163e3b261a2c420997cd930d162108cba6c9868b1083d6f724c34588402b639261a2c420b4fd1c30d162100a7a8e1868b1082c7f670c345884063f33861a2c42011f59c30d1621028f88eb068b108447e3758345884223e9bac1a2c42091f0dd60d162105c7e84b068b109463d4258345884ce3fb92c1a2c42431f5c960d162105cf680b068b1082e784058345884173db82c1a2c42019e84160d162100cf220b068b1082d3f4708345884029ea3841a2c420157cdc20d162100aba6e1068b1082c7f67083458840abb8b841a2c42335d45c20d162102aee2f1848b1097d75178c245884132f9b46122c4211974da3091621018feed1848b108147e768c245884023ebb46122c42031f1da3091621008feec9848b108147c764c245884932f1b26122c4249970d9309162102aee2e1848b1097d75170c245884132f9b06122c4211974d8309162101cf60c1848b1080c7f760c2458840a3f3b06122c42011f5d83091621088fc6e8348b108447d3741a45884123e1ba0d22c42019e0c1069162107cf4408348b1083e792041a458840b3d8820d22c42059e041069162102cf6e08348b10814f67118d458840b1fb268aa2c42054fd1f455162109a7c8e9aa8b108053c
  | 20 => 0xc40eb793c8192862015b49e40c9431038fecf2064a1880c7e67903250c4023eb3c8192862075bc9c40c943100ada4e2064a188157717103250c4faba8b88192862031fdd840c9431038fcec2064a188047d76103250c4063e3b08192862079b90906c943100cda848364a1884c7e4741b250c4163e23a0d92862051f09d06c9431028fe2e8364a188147c1741b250c40f3d9020d92862079e08106c943103cf6e08364a18806d531d19250c40a7b8be8c9286201b54c64649431029ee2f2324a18834f517919250c41a7bb8a8c92862053d1c5464943100daa62a324a188047f75519250c4027db828c92862213e1c1464943100daa622324a18814f471119250c61fe298c8492862079bd96424943102bce2f2124a188156f57909250c40ab62bc849286201ab119424943102bc8e2a124a18c2fc531509250c40ab73aa8492862055b1d5424943103cdecaa124a188063e46d15250c4171e2368a9286201cb50b454943102ce8c3a2a4a188176421d15250c4023fb3e8a92862071f19f454943100ade4fa2a4a1883d6d27d15250c40e3f3b28a928620f1f5d94549431008f8eca2a4a1883d6f72515250c402b63928a9286201cb509454943186eaa62a2a4a188167461515250c40bb210a8a92862059bd8b25494318aeaa6392a4a188167461c95250c40bb210e4a92862055bc9f254943111aec2f92a4a18806d531d81250c40a7a0bec092862059d186504943102ec8432824a188067b60941250c4073c304a092862015bc9e504943107ada4f2824a188157717941250c41737a3484928620b9b11a424943111ecec32124a1883f6461909250c61fb288484928630b5b51e424943107e5a8f2124a1883d6f67909250c40337b3c8492862055bc5e424943102ad82f2124a188056d07909250c4271f23480928620b8f11a404943134ce8c32024a188047f67901250c4063f33c80928620f1f59e4049431018f8cf2024a188056f27901250c41eb693c8092862055dc5e40494312daea2f2024a1884e3e46101250c4171e2308092862199d184404943101cf0c02024a188047f67101250c4063f33880928620f1f59c4049431018f8ce2024a188056f27101250c41eb69388092862055dc5c40494312daea2e2024a188066e42d81250c41f36a16c092862019e103604943107cf441b024a1883e7920d81250c4163fa3ec092862131f51f6049431028fa4fb024a188147f17d81250c40a3e0bec0928620f9e41f604943100daa63132a018814f717899500c4427a8bc4ca8062012fd1c26540310097a8e132a018806d531099500c40a7b3884ca8062213d5c4265403100cdc4d92aa01881e6c26c95500c4423fb3e4aa8062215ec1f2554031108f8ec92aa01883e6e26495500c403361324aa806309d54c5255403102ae8e292aa018817642149
  | 21 => 0x3e13aad21062051fc5d5690831028f82eab48418806751055a420c4023fb82ad21062031f9c15690831018f8e0ab48418806d53141a420c40f3792a0d210620d3d45d0690831008fcae83484188147c5741a420c4ff3d2820d210631de54c6425083100a7aaf2128418806d763185420c4036a318c2a106261754dc615083102cecca30a841883e7565185420c41fb2928c2a10620f5d5d46150831028fecfb2a841882d6e27d95420c4036a98ecaa1062053d05f6550831058fa4fb2a84188147f17d95420c40a3e0becaa1062031fc1f6550831008fa0fb2a841880c7c07d95420c4babd380caa1062015e5c0655083100daa63b02841883e6d25d81420c4bb3c286c0a10620d3d85f6050831028feafb0284188047d57d81420c4025fbb28421062e7e54c5421083111f4e42a10841881f2f25508420c41f9712a84210620fcb495421083103e584aa108418806af76508420c402d7bb28421062e7e9dc5421083100f48e2a108418b9f8d31508420c5cfc298a842106223e9d85421083111f48c2a1084188072f75508420c41f973aa84210620fcb5d5421083100e58eaa10841881f2f65508420c40f9632a8421062e7cbc55421083174f4e2aa108418b9fa510508420c5cb972828421062e5cb141421083178f8a63930841881e6f65c98420c5ced6a3e4c2106201cb50a651083100eaa63328841888e7761994420c40b3a30cca2106201cb5096510831028feecb2884188075531594420c446ba38aca21062239d185651083100d5a84b288418806d531594420c40a7a38aca21062019b909651083100c7a84b2884188062d42594420c40e3e392ca21062019d8c5651083100cba62b2884188065531594420c4473bb8aca21062051f9c5651083100ce8e2b2884188147c71594420c40a3a38aca21062239dc85651083111ce842b2884188047f70594420c4063f382ca21062031f1c1651083100cea20b288418806ad42580420c4036a98ac0210620d3ddc56010831029e8e2b0084188047f75580420c40a3e3aac02106201bc441601083118cf4a0b008418c67c53190b250c61f36ab485928620579c5e42c943102adeaf2164a188156c5790b250c40af238a859286317f14c542c943102adceaa164a188156c7550b250c40396a168b92862039ec1a50c943103ade4f2864a188056d27943250c40abb8bca19286201b54c746c9431029ece3a364a1882e3f45d1b250c40a7a38a8d9286201b54c546c943100c7e8aa364a18806ad4211b250c4036a9888d92862053d05c46c943100daa628364a18814f41741b250c4033d2820d9286207cbdd142c943102adce2a164a188156c7150b250c402b7b828592862019bdd942c943103adeeca164a1882e6f4650b250c40f972328592862079b11942c943103e588ca164a1881e2c4650b250
  | 22 => 0x284a808401ab508615404200e5a8528aa0210ce7761945501080b3a30ca2a8084311fd9e515404218af60f28aa0210055e375455010802ae1baa2a8084031f9d95154042188f8eca8aa0210072d42545501081b3bb0aa2a8084019d185515404218af0e0a8aa021007a94244150108073db2a20a8084077a09d105404203af0ae882a02100772514415010803b8a8a20a80840bdad02425404277ed081212a02101f6b6090950109dfb508484a8084e55b51e425404277cdecf212a0213bf6b07909501080fb483c84a8084011fdd94254042188f8eca12a0213972c4250950109cb3631284a8084015edc1425404218af0e0a12a02101f6b2050950108a31fbb284a8084e58f1d9425404205e5ee4a12a02101f2e6250950109cb1e31284a8084e58b189425404203e5e42a12a02101f2c2150950108a39db8284a8084e5ce1c1425404203e76c0a12a02101f3b2050950109cb9790284a808407cac81425404272e5c40a12a0213972d2050950109cb9c10284a8084e5cb081425404272e7420a12a0210072f76509501080317bb284a8084e5cb1d9425404272c58eca12a0210072f7150950108a39738a84a808451cb5c5425404200e58e2a12a0213972f70509501080395b8284a8084e5cb9c1425404272e5ae0a12a0213972c7050950109cb9438284a8084e5cb841425404272e5420a12a0213972d1050950109cb9608284a808411978da315404204cb86d18aa0210072d428c550108023fb3c62a8084051f99e3154042008facf18aa0210147c678c55010862bd83c62a8084015e41e3154042008feec98aa0210347e764c5501081a3ebb262a8084011f1d9315404200e5a8498aa0210c57a704c5501080396a16c2a808401cb50a615404200ceec330aa02100579079855010802af1bac2a808401570dd615404200e5a84b0aa0213ad6f72585501080eb6392c2a80840d9dd85615404200af6e0b0aa0210072d42185501080b3b308c2a8084019d5846154042068fece30aa0210055e374855010802ae1ba42a8084011fdd92154042188f8ec90aa0211472d424855010802bdb8242a8084315e1c1215404200ed484882a0210073942441501080394a1220a8084015e8dd105404200af26e882a02101d7b67441501080ebc33a20a8084075ec9d105404200ed44e882a02101d78274415010803b413a20a808401dccc5105404200ee6c2882a0210167a614415010803b830a20a8084059e185105404200ee242882a0210c773714415010862bdb8a20a808545e54c7429083141baa6f8b4841881f6725c5a420c40ebabae2d2106201b5cdb169083100daa6d8b4841881e7656c5a420c40b3a2b62d2106201b54c55690831029ee2eab484188147f7655a420c4031fa12ad21062239dc85569083111ce842ab4841883c7e4755a420c40e
  | 23 => 0x1084e76b55c615084207f4e2e30a842103eae60185421080356300c2a1084e7e9840615084200f482030a8421395ae701854210802d6b80c2a1084e56b1c0615084207e5ecbb028421006af65d8142109cbd5306c0a1084e5ab983605084272f54a1b028421397a810d8142109cb57b3ec0a108401cb95f605084272b5aafb028421005af17d8142109ced70bec0a1084e76b45f605084207f520fb02842101eaf7551b251081f17baa8d92884072bdd546c944273d5ee2a364a2139eac7151b25109cf5698a8d9288407abd4546c944272d5ee0a364a21396ac7051b25109cb562828d92884e5ab84146c944200e5eeaa14a22101daf7550a511080f961aa8528884e7e9dc5429444200f48e2a14a22139fa53150a511080fd3a8a852888407cbd45429444203e5ea0a14a22139fa51050a51109cf57bb28528884e7ab9d9429444273d5aeca14a221006ac7650a51109d3571b28528884e9ab4d9429444203d5aaca14a22139f2d5650a511080f578b2852888407e9c59429444272d5e0ca14a221396ac0650a511080396a166b2888401d54c735944421acba6d9aca2210cc7d76cd65110866bbb8a6b28884055d1c5359444200eaa629aca2210347d764d651108232e9b26b2888401e950a319444238eac6b18ca2211c754358c6511081b3aab46328884075dd5e319444202ae8af18ca221007711094251108073d834a128884055dc5e509444219aea2f284a221006ad42cda51108132f9ae6d2888401974d73694442198faeb9b4a22129e7751cda511080b3a28e6d2888401ab5090694442198fcae834a2210067a5041a511080f962128528884335ddc5429444202ae8e2a14a2210cc7f7650a511080a3e3b28528884079bc99429444219aeee2994a22101574714ca51108663fbb26528884051f1d9329444202aee2f184a2210cd75178c2511080a3fb3c6128884031f99e3094442008facf184a22100c7c678c25110802b7b926128884075b1c9309444202aece2984a2210cd75714c25110893ab18a6128884011fdd93094442028f8ec984a2211265e364c251108932e1b26128884055dc5c309444219aea2e184a22100c7f760c2511080a3f3b06128884011f5d83094442018f8ec184a22101577178825110866ba8bc4128884051fd9e2094442198facf104a2210447e3741a51108223e9ba0d28884091f0dd0694442028f82e834a2210167b1041a511080b3c0820d28884059edc1069444200d5eeca12a021396ae7650950109cb56bb284a8084e5ab1d9425404200e5eeaa12a02101daf7550950109cb57b2a84a8084e7abd85425404273d5ac2a12a02101f2f51509501080f9628a84a808401eadc1425404272f50e0a12a021396af60509501080fd5a8284a8084e5cb941425404272f50a0a12a0213972c5050950109cbd508
  | 24 => 0x9970da31d41422eaf60f18ea0a100579078c750508023fb3c63a8284051f99e31d4142008facf18ea0a10147c678c75050802bdb8263a82845d5e1c131d4142008feec98ea0a10347e764c7505081a3ebb263a8284011f1d931d41422eaf60f90ea0a10057907c8750508023fb3e43a82845d1f59f21d4142068faed8b6a0a1007701085b50508033b8b42da8284015e41e16d414200abc6e8b6a0a10055c3745b505081b3b0b22da828401dc04016d414202cee2c0b6a0a1006751605b5050802bc8382da8284079bc87655084207cdc43b2a842103e6d21d95421080f3610ecaa1084079bc83655084207cdc41b2a842103e6d20d95421080f36106caa1084311fc9f65508422e8fa4fb2a84211fc7c27d95421080a3f8becaa10840d1f85f6550842068fa2fb2a842100c7f07d9542108023e83ecaa1084031f01f65508422fceaa230a842102ced2718542108be3eab8c2a10845d9e9436050842729da4fb0284211747d57d8142108031f18ecaa1084018f4c7655084203c7e43b2a842101e3e21d95421080f1e90ecaa1084078f087655084203c7e41b2a842101e3e20d95421080f1e906caa1084078f083655084200c7c21b2a84210063d10d9542108031e086caa1084078fc9f655084203c7c4fb2a842101e3d27d95421080f1e13ecaa1084018fc5f655084200c7c2fb2a84210063d17d9542108031e0becaa1084018fc1f655084200c7c0fb2a84210063d07d9542108031e03ecaa108401abd87655084207d5cc3b2a842103ead61d95421080f97a8ecaa108401cb547655084203e58a3b2a842103eae60d95421081f56b06caa108401ab183655084203e5ea1b2a84210072e50d95421080f96286caa1084016bc5f655084273b5c2fb2a842139dad17d9542109cad783ecaa1084016b41f655084272b580fb2a842103f2f61d95421081f9730ecaa10840fcb587655084200e5c63b2a84210072d31d95421081f97306caa10840fcb583655084207e58c1b2a84210072e10d95421080396886caa108401cb043655084200e5e2fb2a84210072e17d954210803968becaa108401cb05f655084200e5e0fb2a84210072e07d9542108039683ecaa1084014b41f655084200e580fb2a8421006ae31d9542108035698ecaa108407abd47655084203d5aa3b2a842101eac51d95421080f57a86caa108407ab943655084203d58a1b2a8421006ae10d95421080356886caa108401ab04365508427295aafb2a8421006af17d954210803570becaa108401ab45f655084200d582fb2a8421006af07d9542108035703ecaa108401ab41f655084200d580fb2a842103f2f65185421080357b28c2a1084e7e9584615084273d5ac230a842139fa73118542109cfd2a88c2a1084e7abd9c615084200b5e6e30a84213a5ae3718542109d2d69b8c2a
  | 25 => 0x8342416423f8fecfa120b211fd7b07d090590802bc83e8482c85438f09b424164203e7641a120b2150f3820d09059080f9db068482c85438fd9f42416424ec7acfa120b2150f3b07d09059093b9c83e8482c840d9d85b414164202ce82da0a0b211fc7f67d0505908023eb3e8282c847f5ec1f414164200af20fa0a0b210265f368c505908232e9b46282c84011fd9e3141642028fccf18a0b210047d678c5059080a3e33c6282c84011fdd93141642068fcec98a0b210347d764c505908023e3b26282c8401578dd214164200ab86e90a0b210047f7648505908fe3e3b24282c84015edc121416423faf0e090a0b210057907c5905908033b8b42c82c840157cde164164200aba6f0b20b2104d3e4745905909be9e23a2c82c840d9d859164164200af6e08b20b21016771605905908033a8b02c82c840d1fd9c16416424ed5ea483484a150e3f5241a4250a365e2ba0d2128407abc9d06909424ed76a083484a146eb85041a425080f5d9020d212851babc81069094203d564083484a146ead2041a4250a375c1020d2128407aedc1069094208cba6da98a2a10157717d4c51508beba8bea628a840d1f99f531454230cba6c298a2a117c7d7614c51508032fa9e6c28a84099714f36145422f8feaf9b0a2a103f692014051508073d300a028a840157cdc501454200aba6e280a2a1015771714051508beba8b8a028a840d9dd58101454200ee0a0080a2a10157657040515081ebaab82028a840f7949c10145422f8f8aeb00a2a10167651580515087f3aa8ac028a84019e14160145423dea863190a2a145f65218c8515080abb8bc6428a845f5d45e3214542028fecf190a2a117c7d678c851508073d3046028a84055dc5e30145422faea2f180a2a10147f678c051508063f33c6028a84011f59e3014542018f8cf180a2a117d77714c0515080aba38a6028a8449d50c53014542008feec980a2a10147c764c051508132f9b26028a8411974d9301454201cf4c0980a2a117d76170c0515080aba0b86028a84051fd9c3014542018fcce180a2a10047d670c051508063e3386028a84014fd1c201454209a7a8e100a2a10055f370805150802ae9b84028a84055dc5c20145422faea2e100a2a10147f6708051508be3eb384028a84111f8dd6014542088fa6eb00a2a10247c3758051508033b98ac028a84059d0c5601454202cec42b00a2a10fe7521580515080a3e38ac028a84051d1c5601454200cf460b00a2a10067930580515080b3db82c028a84059ec41601454200cec20b00a2a10167810580515080b3a082c028a8401dc04351d414206cea2da8ea0a11757b07d4750508063f33ea3a828401dc04051d41422eaf4e028ea0a117e751614750508ba3ebb0a3a8284019dd4716d414202ce8a38b6a0a11747f57c5b50508232f1b463a8284
  | 26 => 0x132f9b66b8ac8483974db35c5642408faed9ae2b2120577714d7159080aba38a6b8ac84811fdd935c5642068faec9ae2b210065f364d715908232e9b26b8ac84039e98305c564200cf2c182e2b210157717c171590902ba8be0b8ac84811f59f05c56425dea863a1e2b210157717d0f1590902ba8be878ac84051fd9f43c5642408facfa1e2b215173541d0b1590a8b1ea36858ac84079bc9b42c564202aee2fa162b212057517d0b15909023eb3e858ac84815ddc532c564202ae8e29962b212047f764cb159080a3e3b2658ac840997cd932c564208cba6c9962b210055f371031590802ae9b8818ac84075bc9c40c564200ada4e2062b2101577171031590902ba8b8818ac84051fd9c40c5642408face2062b2101577178c31590902ba8bc618ac84051fd9e30c5642018fccf1862b210047d678c315908063e33c618ac84134f91d30c564200a788e9862b2120577714c3159080aba38a618ac8449d50c530c5642008feec9862b210147c764c315908932f1b2618ac8449970d930c564202aee2e1862b2120575170c3159080a3fb38618ac84031f99c30c5642008face1862b2100c7c670c315908073d304418ac84055dc5e20c564240aea2f1062b210147f6788315909023eb3c418ac84111f8dd60c5642088fa6eb062b210247c37583159080b3b20ac18ac84419d50560c564200cee62b062b210167431583159080a3e38ac18ac84019e88160c564202cf6e0b062b210167b10583159080b3c082c18ac84819d85b154164202ce82d8aa0b211fc7e76c5505908febd3862a82c84031f9d915416423f8f8ec8aa0b21036761645505908033a0b22a82c847f5e1c11541642a1c7c8da120b2150e6c26d0905908279ca068482c8543da
  | _ => 0
def innerJ5 : Nat → Nat
  | 0 => 0x7a2a8d1f91e902c9727e38954379504f48fb22a936184a5378cde7535866a2906e1524460382e4bc96284ed7063a96c057f1527901ed430298fae73506b6d5d962c344c145f349557552ece57ea5a2bfa1ccc30edcb50b58e796874de381fdb8e5e9b57468229623e36fb0cff69351784347926cf35090cbfce202aa56eba7d801462905d1b44d41f23d47f6b7e20070d350b22ec44dd002829ae70d0588fca7ada6c8d9b38e1b539f3a016f83d4e3c8454fd2940d7c2549ee0a59906f13504d2c9beeae9f4a1eb6c3a4c83a173c6c07888a49b5816d9073200c019472665301c2ca687de4e9615c4c2c201e347e556ca45a8f6805560842832cd0b9e8cce7b17c4c763b0dc8aec1eac020d968051eb895a84ac3b0f79e32167851f935d6f2a824e8814fd50f8cb8abf0e5160f2a82069764048d17de27f60390bc0b5d34d93a422705a0a0ae866d322d35ac82f3e3ce06cc91e150d39e858daabd218a3d4ef356402d363235d041bbb158b52d06d210133698199c7db12ad0a8abe7a0cf7b01b43752ede8ce1c320a59480f95115300f503d06ef8a7d0d3e7d1319119975ba22079db03086d257e0c56dc6d6a71636245bf51dac6115e6453549b779b5a014a07c822410ce6b5b39581043938fe5498b07dd2e51909e3682c4b4aa395dfcc2a902a91d3b99d3f8891d9ee8f1b99952de22f3457fb8a26c3cca80398baf2e61d683c26946653dbd009969faa1c0ce061c931b85c9d2137c1fed6ed79921044700939e480bb28821655e9cd5484f708e717f89b7c7a5783cad0017419aedce72331ab8d089b97686fb0b6aa51405e0461af2871bae686431d4c819e11877b4413131c77d1c0d7b7e338989cd6bf0727c4f3163c8419d2e79b466b35d166ca9be5d3b3083969e7914ca7e198f68c05285abc1c595463244103b250c17bc0438800d8f47f9e2fb0f3a0a9b6a0b13baf577ea0276e93da9f98327aa0b9740fba9f507ac2945986ae887c926a4e5a029a2e156e5910ddc29a07c8d96e8a1b0aeda947069e8628229b8244123044d36d069cabe5b4e42184015eb20482402d271d60eaf1160c362fb0383aedb9f36b86f902815f7c648ea58ea38a0a87c9e4bb8c297be92938857178281906e5906c2d24cd8b161a2985a448eda4f1a7a34824e5f70929ceeae879dda6a84239e259fac74746241aea87e3c49c6e73d297ec1000ff4378250c642d61b5b1d8d2c0d70609c9bc92e521f34482d375754f1045be2e0ae38b228fc5be10909a54a679b6294c4ac19579170a88c46c2e3a26cbafa8dab612bff57a6e3884602d1a5b46d14ca23cf92823766856054685d130c5f2a3a6721ee4b7183fd50d0a387dad677e411efc8b16f7520a7680122376d5121bb71170fa9abc59fa6493384127d14f9ad235a6ccc6716979f782ee513e237dcbd4ebf8a4
  | 1 => 0xf8919d1663376058e0b5dd738635601c22c45eecd721589da8a474f3c74391177bc45996cb2c82c86138d480217ccc02a01b5122c6d795b9c3c908ec59c19b726d00df2e567c97abc59a96323f4422d19c493690708c2a330931abfa68728460a0a5a8adcf5a8322998aa61210cc62b3390f3091116c2535f9f7d4528da393c9c62d128e85d8212960809de96536d40cb76e9787b42de83099485c1a6a6666ba757aecab6f374c6a172e4f4834e6cd07bac7a883a42a548cef05452c4fb75667b1a8fe1ebaaf26bcca31dd0887d76aae127bd411986a07b9ff5bd85af1187f9b4e6bbac8bd41901e4f080c75818ee9ed1f053b5b664a52dd64552241e0e70d76007808caae27f1e6210e76b32075e70e9d02dc06e95b6aa1ca53c73c5d78def49e51911e025edc89278199f44ce2b3d7c32fd191442d5361aec0d923b9143f4730296b4b10c5081a9001629d94043032bada0849294d75379b9c953a2f1b489ee77fb631438bac588c7ec0011381351c9aa9ffa0df8f9830863a2e2cbb9db0b88055e060e87e741d3269da004df8129c2829f7a975bb6c8e61e58a6770c7680aea988e743b6726b3531d34f22240f299ebb5a72ce13988382b6de04c06a2f2a55138dfa409c5196925c607507583084c2df420f5c7d5f53a44c63dba456202fba0ee61943c071452e502385723c11ae15e4618094dd0b24414ed94daacef1689135d4817f2d0e99e343887d5b814b6f979993eaba953d8ba86da737deb2fb27144f4a53968b7960dc8e5d6801b4ddfa9ec2f07663a28c038019049c739d28d73091470589d955a292202ce0617f8e94a2c5c4db496f124577b1e430ebaf1e5a3b7d0c2f6f034b22a06b276c407a4984160e51d3f1ee8c5fa75f1d1242c48c9739067af9cf4479dc0ae37722be13a08a6d31cf6e3cf89e2122ed271d2b1070b3756d264ce2efed667cb902b9fd6316e1ea2d66cc8d0b345395a27b83dded0fba499c077828f3519d1b59947ba032f76017014f0de1064549e465f30502b24ee7011a240a6c0379427226030ddcdf4e9e4e6795d7724a10633926180e033455f8f3921c3d7c4045ac1e423e5540e2be73206af91d507e06964cef4609d84691130083f1f613709fdc304d0011089fbea9e49811666484c7b5085b6395d994cb3b5c4248bd33eec9f05e1c228f49fb18a48aea61ae63aab936a9383584c1058df5a1ac1500924a750a91c6d3d1ca428c0e9431972956662577573a38783d83dd08c81beba6a8052258031e6ea2b8cbde8552d7657b0d6a63b2138641ac229e9a76e53481cc005eda25c6dce0501dfcd8679787923f749ec3b1e03244709a01a52678b02740756850703e503a190ddcb4c1ca447204b895d240635906f5509a32fcd50d98029246bc07227f3c70368749b9177819bc8c370f450e6a243b92a5c7629
  | 2 => 0xe62e38d82eccd1563ae09375eb0bc6d96ae94dd2f8d417dff107095a7294736a3318cd9be87fb9b7b82bd2a454b63ff82f3ac787c135e1489a525ee858c5c85012613226778537a6e953508acfb9a82b55ed14ce700d3e29d4c1c2cf8022d6251c6e766004977200a0abe95bba4b6897243318e3744979ee12514560a52ca747a6cb0a16f6edff30c6d8070971b85868a9f154efa781e961ca7ae0c7bc1ac00e305b76393710100ddccb9af9116a135056674ca7fc2110b14aa4b293ec2da4902ba1f27e60006299d7013ebadfed5495e3c8c4792a40e855441f0c04c07697a28540b76601f7c51818513a9564136d7a195cef427e93fe08d26026af1560d3e27a5d9f69c9194d22c280592eb857b324e438709eec97ce515b53500b22d08477a9c3d71c15958de1333870a44aaca254b201beb4c7f11cbe97dcd7067ce6925ddaf1ebd84e2641d757995539d21b4540e74ab6b434a35f957983046e7512f7434b23401e111f3f1d1fb0f61d4a3a1abac1a5ca94a2a68d425226dc9e1e34ba36c933e83a397486f83164a491ca5124e8e79f998044a025bc9bd700159724c64db10d0392227a70f3a2d7dd8e82be9847018f13c0885827e2e9c7e4a04c84f0c1d880a0c8c349bac884a8bd909722b591d79012f5156dbfbf3653e40725b4b6ca350c99568f7f891ca9a7e61ec4515949bf67281638cc619270b2a380bd48ce1fbb254e3f7a28827cc4454461c5ea671a5e777eea860947180f8ab206bc5fb804734377ad14b38a31baad2b38f3ac18f87186e3d0050195bb142e069dd08713c762c5eae644c5945557b5d131c225b58ab5852521c78aeef4f4eb06e0e2441bd92decb8bdf4a70e738ab81956a941d24236805ed3685e758ceedd6bcdb8516c727424a5d1c2a694b458241d5611aee87cc436808e2d519bd2314474cdf45f66310b660ae19673472dcc67caec036e0520976c026185e1e9059ec945b5b2987289d1e62ae5acb5752dfb970de7eb5974b90d974096a66507e7c9af93f0b9086b416c7a229c849a3b3f5a0e709615a6bf29b414b97db9d841aa6f7b1165f151c961863f3ba0b6f48af0ec1e8e300801014fa31c2a09b8d3d89e26d434c7eee4b4948d302921ae5f7e9ea538b99d1e52c230a407104e7f2c9ad3485da1085ca32b56fd628122669900e05896c01231923d28fce2f50bb6ed3abc0c427c33026469a70c56938e2b8070d0da2dd3205a0e392442424e8fc1c056616b8eec00e86b495ba03696d97a5b54a977791fae8b2293a69431089a3767537ef4475324232a21dec30e811cae4fd4bac6da40ddad0a050149525d82d4fce2dd448f9dc7b42abc2224a0393b5542f209e35141b7f14cf64c931ff5d323ae01ca99a37c84781c65b6584f33d0ac155d90c68ff201e8b3e5d0eaecd920726ef05ff0522e78425dda3
  | 3 => 0x895550e64592c54b6510f04299adc013f1bd39d04dc02fca26a76443b6b61a6c4d5427ea27026f295967fb40c2ce26a139904905761af59411815e4d72711fc48ee6d3a6d671f3e1c66489fe40afc4c84ecd8e7163712a28c6cf5a805f1c6a262bc16fc64835d4e8cf29677000b01899d9a6dd2d9eb9c2933e590ed33e17dc9c0d4a5889c51b15ba70875e92165898a095f5ae29a71b2e82921f3b182c8d8eb3ebcd1ea756c0019a79454c820927518a1d12bfead64b6253817109251f9b284ad90eb0c93cc0b01fa07c2b768f178f92396071b00dcff3db010d13dafd01d66a5b527a128868440caf21cd28a9b64dcdd0421e46601cb0fa2a1535d2f77fec04da598d2f90454d0be963b268c5a7fe0b0fbb40ba87400c53f70619e0c5ecef82b09c47ede6094fc5ab504085437806b5966c6bfaa4a0dc23f35e923587f30224c154d88f7eff1185a7894cb090c720eba67fa045126180cb6d13a8a5c728d18e964bb566228b331c0919bb827d0c0dc6864f95e84f097159d3ae166a09f1724760ed7d13acadf256fb6779eb1491f7eba1b2e1b80174c4c8d75243f2c4a0d8b1c670f7d4606987ab8948248901f19c6b04d60c008ea20aa359323ddf72f9532b78baea2228c0d01a56c6450d651fcead02236d565d5a6ce2c31bb810e5a902cc64426980696aaa08ba8a9d9b9cea68803b7974df1583a21af357306289fdae5877a8aa1be91657397544a4f42ab7271968deba922aad8d46b338e1e2a7113bbe0a68682aedcf737a04d1abf7915b1eb9491e4595f508f6c08c5e3d817ff92573ea2d898a32688eae1a5905ed9858c02e204d3bb834e9d7e825d9bc8c629261d05a71b749bedc7dd9d4d4a6a1f8e2db1b1389ac82ce9b88a1d9d238dc7219bd36b553061b258cfea3b7ca91851f1454fed2c55141792997e4e97f993ae5a4a35dad676c35696570203b1dfb5cd1f9f26680ae7eb8f0483c04f07ab413304b94f154dd62e3bad496f683e266d9a13e90df5e67cea1ab8a2e2b3c8a1cc0f01056a1b2fa41fb44958c2bc2ae4e2c2403a7d426010d19d10d8957028828c27fc969ee4e239ba236f16b0053567670f90432a92a33a1ff33d36ef02996b2862d5380b159c663dade63b1019ace12037cdbb321ca032cdaa54c1543f19f7d524ce2822c4be7b1c03f515a18942f7d5e1aa7da387b352527f08536227587d6ceb2da7d1e2d9256504e7cf26ae107e7e27d2ce20314298eace99d68872d1a6d4657bafd0bb79d10f17b212378a07c123155717a0e824f12ea90f8d30652548e0a1453ea64bdb773f04f12643e8c54f12420f0bdd20b44264177ac67344594b9486687ab6945961e0ae7d4bc8c743599cc245671bc33093241f37959a699e6bb1a8374d4e9b7401d5e9da77be283c8ecf80c035e2028411602a911604411deae5bc934893e
  | 4 => 0xdbcbe65481cbfb3f230188aa120357a77446d971ae0c505b9124eb32540664082b6c8b77514c1b960f41381f0f021200975572d40db0f31ac96f285fc36bd8cb6d289d7cc2a41f790ebde32c808659cf6a404b122f19bf3e85d18e841bfad34649a95fd082c020d80d16235c9ac74c9b13e82cea4427a72a1ea97dbc644b521aef5cf372d8df0c2d4435acfb2d2accd9e2a548ec66998e4969032925eeba22151d2914284d52a5ee75546873c5f8592d4718c31abbcead2aa10c9280a1b8f27c7730c9ce6327a030b1c5ddf8d190a4f7bb622b1a431d52969755e6a391f10a7a4cd198ea9b690eca410845879c9b1aa3e6696277caeaae1888c65c8eb2f5109085c5931c22289e9134878fac908d6671d9877998731d64196d493eef11c978b02df26748b9604f7528a63db4a253b2d21934256a2a1cd41e54e9a93dcef7294a5c919b0aab39f40547be1b706a9f520a64c3166bd150fe27c58b58f20d87daa6c1e571847b7782c21bde8cdc00251210d4ce64c8acc869962a3d302a78324b19586572f6a550f4f5f48aa422009c80c14ab30332e7a2cd806f7a446c707401325b218b899bdd29aa8d10a58a84317c0376b1d0d8f64f823f586e76a16a464ee7f1c0612a956cb910d7ea3a62b7980b0cd6b4e5c63193ab9e43124fd994e2b4e5d6bebb30174400b21c08308dd4756d6b12d2c4d496e3ac4878f4bccb9a77e9850a220954935dc9dbcc6ca3afeea08f00726114a6cf0524a56b4ad8e3aec214ec3271b12be528360bdeddb2fe00912d64468a07b480ecb0e16be8734c1c5ed165bb2c26bda804dd5094c097b42a2d1699116149d1a68925b6779706715f92931f15a9a44610609b791b94356a4a7269cd01dc52e8d09beb034bea805aabc62e7c3eba4cda0e52906289b2add154bd3c445907f96b7c803ec3f7ff94696be04b576b03381c7618c7404115d2841b8b5d02d4e833ba3ea379b99f012d44afd9c10dc51762f38a3152a073fa7fa3e98bf01985445a42cde530c4af76ac14e69bbc428ac62c3f2812f5845e0b62c60786d8a9aef9eb2dd3f70ac78525f0d122641f74a874f862115d51a7d3f20a97a9ab2258d064c56d1f2c4e105f20b9f6b15de9db11e2b11e5e7a5ce3a2da45d27dd099e98b2fd7b4b172632c0b8874d35578a9fb2862635250e918243f701013c27b51f656feb1698bddf9a67c23897c9c650b5a8c9dac35a01a5b65220ad1757228cc19d2791651fd16e37e585004c96ba9c227c6da6e43841126a4e5b09f57016158e5fb904ababa0aa28965dbb3a71cc6e265765b765e18c6cfe1575966065ab722584d7d69ec44d85963f96740056c0c36bb696bcba8e6cee65ebc0767a93383bb918b403f93ded1f8164b334ad386e86f35822ac25ffd6a1824b72a84d8a35e8e8d3541965dc0aee1453a72906a5a7a8f60
  | 5 => 0xbf48613250c1708a8d1c916899d91cd78c89f36c6baecd967ae501200c1a421f29add0364a918e582a2b47d88fee1417ec02e0d5cc0e08516f687937a094d16b35115bd7b32909300d30909109db06a154628a78216ebca4ae10dec6c47aa04d143edeb18be0e0e5901d713dd8d26bdceee513ce50656ae0251d97862b7971291c895c3f7069b81c1ca1008257352c61ec26e22b65178cbaaf00f1a1806b5270af2384d0d0bcbfb88f89541b73cc689a2b5f0121b470ecda907825a06c62b63296547f4c2a01d5770893d63007c4d514deccfa323c8b4faad696167cc4574d007d48d0e70a74ec9e214087636bc3939b1719823ebe85286835b07b8574d0fb40bab87365048b61fae192f5ba0c2d9499af9c1e432b6d7c9042b983a4ba93d966ea3259b0a1269918d8417c3bc9cfb90ee7cbcc98f8c38dc07788145c16a646ebbf922e8bb5b6a8634102f3c1851eee24dfb2b446bfc0d0178ed5314642312b91da9f66406771a3fa211c1270a689b4d3bca37859e004871307383ecc11447cb6faebb9a1d13a63fd395ae040e3b451e8c1af4018bef1d6a0bbd561b31fac2742131ac660a96a6f4073a8b6b949507b010536d172c6ee76409a7d391b514e70de3aa4d6199e2fd98bc959ae5692d2fd412a94ec6fc6c58e28247bb16fa079ac19f9673254e45afa5c4063850c73044a2aea7ab8d3b578a5616a8d35292da2ba03f010a21a2caa6d78d0242d002208d0d6ea19c715c242a04564a158ac818fa3ad70fd69f9a02e1050f29b179db3c0c2909382e669066d0f48d8fcf83c89f0df523a46786ab5f093ac1ac0817bb9f1244dff706a1c964210cf62621316a356fc2d2434dc7cb9e0729c8ab53f16342d7c63025081462d739b224fd481941e2063c29fefa2270d027b07edacb2fc8273dbc580d5de8623b8458180f1e1989d84664b3ccba70fd0673671e21513945090f6764ff757cf9071ca69d96a397834568f85800d83430583a56f35c05f4c5b6a24e4c671c95b648d238c9c13ef698715826a7444a75bdd1816102b539d1155e437c6363128b6f209466c15eaec147a83a4ecdcd12544ac0213e4d1f5ca440c6c2f89fca49734083e772f886ae1ce8ca74aceac969b087b1d218ee10c2bb51046a1c508051279d889a20b405f1158bc59278cc21db4c426819dcdf216b460dc1395440bc08f0d8270a75e8e8ad74fb78cd6abadbc41ef7ee37b62537b61c06eafc9324a80c387e729f92a5176361ec3d6423f9b5ddf626d1ac2e3a9bf1c937dd1df2eb91e7816216cea911eaa3a8780817b5dfa6a6e9ef77d19ceaa2649c3e67271996970d76da9dc5be40bd516596842c0e916c1124f370811d26f29d2801d4e98c2a0586fe051339da61050c1b64ab3884aa9aea092aab3c51cc61c1026df3e7bb0facd8839d0e8984766f497804b046882
  | 6 => 0x2dedd2c4f578598ed2805a2281586a25b0d918bac956f6be24e10651284c96092e6a124f90ac4ecbcaaf2b328ac188028da5b90325843399ea564270b05a72a6b295254d1ff753df412418b40f5b1e2bfa9a5c9244644fdee6e6a25c3ba324101b45716dc748efa8ca7d4f3b03aeca9ca6dace688ec1e7b7090e005de75252490e464eb5d58e934204bcd3924914c829eb4142120cfb985541ac8677897dd56b538b33b69b79bb2b0b7190aeeeda3bed3747193ae99c8ae2b48b411035352c86115dea325d58843deaaba0835380ce688f863138d289a42db43168a6c293a9d90ed1be97eaae175f40d528cb15242dff182502263853d460f4d48c333e684418597a7f01e6ab4063d7fc63fa72234faa7daf4922b57b636daf29a5cb298a5f03443432d9426482e1f558bdb09964a9a037c2050d19a9eba47d5b686bdb7647c2b9c8049e2354743b31b8aede2c1832b18bf9700a86aa029b573887085f7bc4c1a750bd68e311a39c27f662540f9a0206c52e262af90b9d497509ec84fad94468807820b424194bb423838b49c42105427a6ef89bdc85e7661b162b8fa669137bdc368516d4b0cc42435ef25c892958c4cf193a00d382eef119540ba68763c71a0dceb0c1c16a0765067e4744fbb9735de3c63bcab0ea89d12df837c00366522d950c5e40fa291046cd5404b78791f13b681e72cde4709a6324a093dec0373a0aec1a9e7e14e15c7631f0111c80afec8425410bfe69ce66cd2e1d0da184cdce584d310183a38b09861571d66462663a235c661da627200249ba7624e456797b0168a43e6af574429ea504a1f62544238ba0844ba49d72097d4ebfe3d4ecc0a2449742923845428fcf05750ccaa32967078527c057851892327d04b0ea2e3f1458555f0e3465ead9a74298cc9062238931168b24abb1c4df530b486948ab97db169edeba88c9899cc1d0ffcc3128e46d339ace421d475a541007afb5118e16fc4c4607b1904d1e618282beea4358821a6c3214e387d07a225edb70be9d827601b50034f7b118b7a3b131598203253c95e6425104a45ba81f6ae6c28b9eb892e02a5d2d9eb1dd265ca6d095a10b63681f588ed569929294ce9d9e177c57165a73bbb349c5577950aa1e670a9dfc1da19a892c16ad0167540eecb207e80a7ca402186c418639ea4e7a5e0039c4f33050e381000c49c6374b75d02457f60c32cbd24571ca1a20af2dd064a46dc374d9b79604874201a5dfe695eb9608adb60658e9ee766262214de65d1abdf676acf3981a1251f6469e59de715c3b0daaa609468fd1510a6f4c5a65943f01c8a1c8ff55cc10e684ad32e2958e8c7a70dce15f304477711d367f7b1b0e56fb63dc9cb13c239ee12c1810dc941ca88083e0acf54c089e1b4f70152a8d032b6a984c4a7de965dc98c2f07bc2d8775979c5f7925f90cd49
  | 7 => 0xe1210381eb808e9a0446b18e466d8b3c88071a23bebb9892868072d9faa58cac5933c317dbdf848756584fd53aeaa64604c60d3f82468c5e2bef1541d4a4929e894032f0c01319a649d689c4de706c4007350a4d2a05cb017171505111c190b0e965e1d6017228eab055be58d43c051e07dc5a81c50af166dbe29448643024522e32b6c7341aa36efaeda64da9b85ca601e8ccf42dec095adec0dd820b920323f275a8076b468d5767e37d3d349c7560b0116af591a31ce2434aba1873f5c9d5627a71101c134085b48c61432947ead3b6368b50344a7e72846b44ae682c58621034ac12a175ad8c6e7e8df80a042bf36809b1d3e946462d9097003610637d039246c1c81d9f7d0155cac9c926015c0d960f9eb022394c970e9d12e48bd8699363c632fed4f2d6a31c04fea2b92675412cf021b0430da8857c0ace3accd1fcd16df737af0dbe83a89afbc24aeb34091fa1bf6e6ec292472a6c0525902d3b045f0b3d027956e52f063594794a211d7b5b2b877604cadce0bd53e177945e1014c8bcc2f19a748dc41739d67a5391324cea37cd385913a9e8cf737583417f4fa2e87251a58f5c2c58c7778da910d68d3df119f10194704251ba8a930951e9d4fb091cc0a76e69788f6d70918e022766a0990bff1d92bf31a4dd05f3615ec779a1148e81b1853500f1d2fb7e8c1deaf4ac592bd0a240097ab815ad1e8c45ba18828567dcf103f895df1203a171847cb5717c439cccbf30e46b5dee0d485ab1a7d09680e416a461e8c74c56c558adc498b9180d08890ad7245422be7868f5be7c3b774548db6c2f63b76b1544480b64044c49ff97e66a14585aa49bfc8a991700b564b694414dcac5e70d9ba31f86247dd400c83f043405a9e29780ec22110540227a4f6f68c8c03e19edeb7d704c19d2f51e30338f46ed78fe6a7b597ed76267e3bf405a74f9baa1ff6475c4a338029635d135d199619af9e43a8d3354d8127886e02a7b8890d894e6030b498fb22c12f7eddaae96ed396a2ebb829a7c706a98f0e5646e5af741688445b024b76ae8e817c8c0735b53125a6534ad2aec6536040b9d3a94d7b48bb386c1a50beb8bfcf1f20012c2930145b8c826f81a554c2ae462eb7ff28f2d461aa0a778e95a717431ecb444241fc971dc639586a3cdba8c2d8b448f02321b764ef67c0f21731619b310a0498eed8485ec6135885d8022170ebe7a18abd575395dea10bdd2f211cf7ffc751caf19f73e3c3357640aa84700a5d0c821618e9d00eb6db905938248aab25f87be694832a0019cd9324b17e462b9a005b9e2e1c482dd5bb394e30ab9876471e2c9d7665de262d475e2a5e47d7ae9824e867d949cb869dedc5eca03804a0b6b90574c58e56617d4d7ac61c48ea90a8e9993a1d4f603f9ec96666199adc21c895a979424ae79532326ac06845e8ec74399
  | 8 => 0xc620c4d2305963ee772fefa31b84d72c1aec8f69abd1331224bb7d06d2b52840d5048357d6e76b027266ecda46b2b3328ef6528ec33fce798ad191b2c7ab878eb510419bcd07a66335dcedb2c737c0b12e05cea366f3ebe4c6c6c869e289bf111e1f918fecf6460026851a9a243f90218a53181160db599df74b92ed232009cdb488a6bc595ed93035b3a4f7a96ab742a17e6e0724449ea05905d1dc48599199afb579de5e9da4ab768631c46ff3895a48f91b14a8f4165c1d0ba27bb9505925ab1bccbdb9d72cb04dffac5901c59f573e56735ba6ade27904ce3552de28664d321b2220a132b29a610d493b862035a5f14c4035e4564399e9dd822cbe174b116572bd16816aa738e8fbc489cc2f4e717e6d1fa5a83f6915d8d15e9a9a1940b70e200125d8b9d0c7cf49ddb025237faba79d46a162c825a0ce043d99fc3aa1bf454b0e266e0ae7441046370626908909a70eec2b5aba8237f9b0944896ea8c402bdb0979eb504f034e5a538047a8331c3d38203143191fa30dc0089c28b23989de0dd5240e2ad01e0706e41038c97d85415f79e2061440198c62df91dc4436d8f1a0d58d102e65e0aa909f1e8881e6bea052da9484304e1a66d78e9612c5b34a8091d928e8bcbaedfe1a6b4b5c5c4069a396b628fc074f250460ba1910d9e5e3a43243227a0df45b154d9b591a556884e92ea310223e7e5cd32bae70125212639b8bb5aff1c4d1e5ecd400c9bd62e7f774de78d6fe1d47658aa45f0b149e006e82bfa9aa16e09436f4be50011312f925e5769d1ba3aef22113f7162f2db8b399a05c5ed85217e0917a80ea145a6080c5883d0faec90530d0a4a2cbeaaa225b537120b5e1c593a97a9bec646a638874512362ab6ca668440e64717d50707b0d196b2871aa27ee550ed3734a08f96bd4506a7aa75db707893057d8daca763d4a2188a77aa9af7c1fcea1e12ccfd1050ea7621421d9cefb0812f8488dfe470a5d667cd18621b4bac0e1556af05f50dc20fa8824093544784e616d1758bb5600dac01ae9fde2e1a9e7c0d71e8a68b18e26dc0a11c8a4f1bc72ad3e4646c6faf6d840f53e3c235d436e17a1a3b1883c0605f0b2c290090d500f7d3902c0385318b0ff012081edbc06c2032acf133281b6f1eba7c773eda2465be990f2c299c74087d190f2c558f9151b444ac51f684a727827f806693308a93e555964a44cf4b6889a8a028eba976a887d43471b08ab40e1b819f27c72d3e53e507e08cb8de21dd0de641de0d5590fbc56d0228a304228daab6ddaac6275a4375c31be607b5e2f39e8441a2e960e01751aa8d9ca45e5429b00ff67d080908b3a90db75c394edf08ae0f491e421c15eb8334c4810a25d5754d752973900f5322bf72ad5ce421f2711b15e3067a9ab473622c1cc620a8c626a169b44c3664919820d1d975d098802d99c
  | 9 => 0xd64ed81a6821b86b71012da95d655a2a7d580e0ce1d046041113870f13a28edf85d92f48496705e2845ab08fd16dd00547d19f67cf59ee80602e61d71bced1b047f9356fb34962ef48d6e7c63d01a7b0801b5e6d0af7ca0dac2c1414d2d6b3963895894323d4f978e241bd5dc1760ca5790c655363bd28128a0adbb4823828b2b9ff40e72779a4102d032cebc1bbadd7272ab0610ee86584bba38885158d81a0dc72843828d92c459cd3b704515783e33fc309d0fe91106b628a5b8a0234ec274c905905707f984a4548aaf57b0142fb26652fab5c2a14165fdae8ae1623dbd7a472b0962b8c19e90ac9bc21f7bb30adfccc0c40ae482f36e1e2237bb77a2199e3907ca25911fe1ae50881b7547891b0a78059c360b1e9b89c192d7b0810aa8a5fd6e5739d437cd46bc4aaace76e7c79e700cf8b1d70fd91026cb6c2acf089c273b5f912cb9505c89e1e720d058556c412b628dd1c947079cc2b2201097c11dc8dc1a9952d37bac59f9ba20795e8d33143ac30a77d5820833631f1b5fbd393b004645742b61d2aa18278b9a523e8829036aa5a865d29360e1e52126284aa606769a50039ef368b96c5a59fd20d18602e60cee05786b8d45dc7e4614c8110908f1d5a950b90a69dc006e98ddb2052b09ae58e572cbe3161e091833f70b57e4c4a6a0d36a22b0ad0d4e23508a92a7db78539f92d10726947940819ee99b2fb15d771ed23384cab34a0c64e63ea4e84279aff6a1592ff54d1a971663efab5fed96342e78d540c58b454a13b5b84938a5b27d5456492ca3d19a323cb739afe60fa109803a517214f5d90a39d259a79c03afe579c1267681191e9d818df6746ffdd1ccad0131bc22f49934ba98073d0806e5eb3104daffc2a246fe56d169a07ad6885ff69daee43730135e0e423c5cfd6b7f96db8047a125e2b35633dd349796c214560ae818a7bbc6a701bfa7a07b41aa28cb73a79097922e90a92f1a0a4e1b1ea791685dd1c4ed2b753b71e626ec58ca2597193196d186f2e86ddf95cd8f94d63571c69e195d200ec4448c3f4597cde90aa71f88d66920f96935f8896523a3e3b39b1e835422a68a18d24d3220635e315376b98a412a46f70bca8e9c92b347d25a288ea5b06956bb616aa8a915c2a4f835301b59a99bf6a119d4e67d6388a3fc0c65dce7550b81cc811b96ca903e81d7298d0f5d7cf738c2581e4336555b01d1e88f58623a4c76b92cc98f89da9a6a251d34729efafb1bf03d0af5ed02bddc39157966ab68f563faaefb1f060857ad264a1b867e48692cdd2023d54cb1e27342c0909ca15c64d15136f367fda87890dc35357e161520c4cfe330def461d38e0be501d279a967f148da51686e621abb55388c2362886f86ca56ea2a4668847bd521e12e476e84175228068aab8b33ae379b2f2e8da5660257dff215d874a0f6f1e53
  | 10 => 0xc6741e4950bf830fe29d7a8a4ef2804eea6661dae8d4b5a00c968ba78025498528a56658aa57a0a98a51a220727168b9d16e887b1871cdf3468e2438d52764a6417cf88a7084da33b818a4bd7180a572c3de71c573b3b0a60db52ea0a06b8499c1520ca0fc3150d8627693790e9361328dda6283ce214654ba66ae91ab44523015919b02dcf602c2e36e1faa88785809de7151bebb526bd2da1caf825b2ce69437ab3a717f259547e80c31691cb629d4e3959bb404c9a0725b861ce80c5471c1708a02388c9b2f465285eb903479e4659d259c8076f0e226a55195f9b137f44ad6141ba779f395b02520cd84018c20d3976f41b003e90440dd5d085b1218b9b9d62ffb288d18b0c8f7029ba61978c42b86cded8a328ea7cc8a22e2edb1d1a546d782eb4e2bdbe5b360eb522944c1e67a00cdfbdf9a014c025eab6f8008bfb8d3732bb3540747bdee639a802df6daf0b14ed03a3576e6721498d8ae0036ec0a1e16894984a00d37590570af467495f1e7e80b897e0f90c2b9a317429b0c44ea1a8f68b0ee3ca2de42d5954f1a86791a197a49be4bd31f396d626e4ea010ef3db654d9beeff39b31d38155c155ea641012db9cacad2d3f039f29509577a7dc7f1a321ec1a0c30227badc3f2758dbd3bec3e686e2b68ace0826a0f75b88092a102573462098150e2c341f8b167b9e27491397c15df011136fa99de8d115cab829217560c351c7c5b59005fc1a5c79edee2f1e8bc41f811970aa624883bc1426b88499179a663992d149cb8a979821fb94260fa108e7267159ec3f7a94499a9ee68c517aa14b9f07dee37e871e26ba6620a983e82a749a2169660995183cc272ce9b21b5c77311d11ac8b9c635a1022834574b92589cbbb4e0764e5ea258ab36c3a1b3b735b61ce7844362462b514f3676d761b4b03e39adc88f2f1e70c20c9d3c40eb1225aeb42059e60977918d655942bdb27583f9e4a99b86bf17360796e9f063148a4d0ce8a50a5709a634173240d4ad5f77ea9c04f64349da72eaf5e090553c8282a70e3b4635d5f530d5c4cd10b60823c4c5273dc381c33a36410f768ae466976ac49ee453daf101bed042192da75b46bd5adeaecd6c44868c9314777b931685617a9d93bf59a08792bfd9337ebc0a5168c1073f8a5481ace9d7452237e67242c76b1a9f805da8272da636a43d6a03bd0afdcb88167c942e1107344dd7594827b5a18171591e48314f1f06e25126a0e7e5f8a152b108ff4af84ba7996ca45e4495ad20a2f19ae61454116a22d037a745c011b7fa36c472bc1995db9ae5b2034970288f3529bdf39c2a3c9358a4218758e568d897d69302ab0254830a4c0738b38c2b72bbdbef46ea9978cd5c7f6b653f227e2d6009b919334982020a46037a34f9b3b7c0a85db90005e1ff0cc1ce94bf71b228878d8b514fa2efc933e9d595
  | 11 => 0xef1b7816a5ee5b3113b35c0ac1182420c3062f8d104ec9588d78295302c658d64341a6c14ea26d04d9a64ef3a4947ac9c3f13ba58bca2e243dd3aacf21e152c932f26e9c94301ec4bf16d8fcc77c32ec5060d044d44363eca8ece2b1cb1e78babae02503f41c8e38d1142cf0ab531c07038504430a3070d7271bee527391e65382aaa55511df394c6a0df1f2505b028204b1a2e8451f9efd91ea47c35a596390fa55c453593847d46e1ea453500d48116b83e7af0ba46511a62343b04a2aaac57a0a5f08ce5eb4c6ba2e647799c2407cc5c3b83a752ef8afbebe2915bc29b4be153a9a6d6d85c277c4b7739d6069b1cb3848ba5ca4477474ad95fbf5aa42fad36571fa0947bd2c8d6002f5d67b4fef2484964f6999822ae1150eb437ab19fa8036b4775abe63af62498fb03987839420a6b6776d7e2b7ab8946d31130e9f7de8019616811e2ac5931dd625bf32a9e7cc43088c6f0d0fb15394b897b2fd88d9ee1e79880835ae9c54440f01180f531e1879ca0eb3ac0669b14e72a0caeb1d77159d3f6f2c8f09a0a52be0238f82537253259684f6c0f2d6c1fd709e209671393d0ded085df32e80ad2b7806dfa334eb8af64aad82040a7693c17612dccf35fb181e008625ad5efd3c2a4aa3a9d8a9485acb64458a335124c1121d163b5295db7f7e0113dbd937d3d18ed80fbb16afe103bcc231b543ad8dd8f9d59572327331b7137674fc11cc7d99b4e072f00b5e225fd7f1107e9fa5d6ca14302eba46cb2355926b036ec821495f2e77a24a528254a4d2873e5c8e3606835bf718621ba10e78d873cc67634f38aac277a0016051a4d0945e9b7502807fe0b107d14bdaebeae9a71566e83f4cc39e0665d48527b123d12fc0af77b082e68349256d48d139c2ed596d311bd83af679065ccafb9640b781d8c19651517313324a0c4885986242f1e90126061c6049d084d302ee4ac97d0009b44013f64d4aa333f0c88afc9b7c2e6c37619c8b86c66ba88d0d4cb04501b6eb150eb7a08a9a84c602a9c5537b5c5c0f203089a76e274485b2600ca1ca9b3eee8bbc630f86ff0774de0d7f65ef872e4818988d8626693ea24dd9b25a4ea5f00e40ef13a0fec921c7ece3a76e01239afc35221aab0176f198acdfa53a2d5656ef2ffd894fb51315d1907dd3f300c192b30693bd01d2704e28785c35f4013ed33018c27101b420e6ff0a2245ad73576f68b391a01f503698cea102118d1a3ce69430397b718b3d1f1ae652c991db90aee23568e3f10b20d0693e10982a496e4be14e14fed6f793de83401220d450cb871360428439bb0051405342a322d4f68472a1860e1ce428f1c12b5b2e46a8b3b3db93990023e5041c6224b046a4887a05d4c6790726c82598b3bb5dc533b49cc9cd51228ae91158f8b3d5c432a8f8c5640a46a69560f180b25a333e4fb44e5c17
  | 12 => 0x56b4f304a27691069936a7889a56b893e11995d8d4fcd400ce84e56eed8140ca3f4b368846542e0f4cca5e116bcce4dfa671919832dc126862a088dcf5aa0e7067a3e3d72758ae1040de2294159e30c8442c87fceff7997176817624430013fd20a2ad94785154035b534c52a63cb4039bac5052ff53cb7a85636f388ea16f05d90cd4684f2f91205602bdb96e63712275b4fa698963e563aa6e2550610989ac07ab1149ab7302781a8c7b2672b2009f67425a16290ea9088b5c810707af9b3e80f39b71c56b6e00a133b28d80195b00cb935ac6c7227ebcf11a8bcea3777c8a3a123de91b5914ebc213a863ccb3911981c346ecf0cf42e17b0a67e369413fad92b8a97719669f255be09569a46a048cdc1b998bee6ee5524826b742a88e652b493967fc85b62b5b049965640caac6b35d2418153da9fba0642dc747a397c49d2492ee452a9000c9324311ca4a5e3cecb7d7ab44f1ba39f62d7d23867b2c0a0ede0bc46417bae9b1a8e505141b192a051c9b281683749672184e886b64d9d04b627498a885179df6efabff67eb355a9a92405917e8969a643d96047d7c70211273bc1c83b227324988e6828284b82a99658125788ac67743b1e8b3d665a4d0615d15febb6bc3d273885fdfa7602bb537ab2fcca4fdc0d9f976b07ee24bc63084f267560268f9146f90adc5a8a3edd826f67938af2713913201a50ddceba730212590830eaa68f6592a85bc2255ad4e42f355a930d20263948e3fe9b90943a7d9af82ed0b0a3304ee86b9cd0f64b81a64a1a516a7e052b53d8af8e90937ddf4643507645ee1bbdb6b2c254a21188b83056f021795022228989b7b0ac8742ff85a966830a61d30a9166e38dca4dbd7231ef25d5fa63a36a2698950580843a833e6dfe92d1869064bd39378826688fb45d009bc5199aa4c8ee8b9102a703144572ea1820d290fdcaebb7c4da2fd3a26a1ba74db21cd9622ee9e4f1d4c029123ac53b4629f2ccc09676013b95bc772a4e907b5ae745267926a042f970a060ce7bcee8c95004b610c847b2b24099c9ecea9643b85d204c5887e2e5e2d2b27930f1d0c03f3564da7209e09d52433ae4f7c0c6e5a52df98a812bc36e1bb9fd79b46820dba2ab26c2cb1495c036d11becef8fc0efeb4e0cd009656b896b8c2371128903fd294deea31c9eec1144ed481f414073a1131b00ce2aceb68f1b1fa6ea642e2d600e20d7a2de4405b835e793e7c50ca30622042d2411b80aace6b947da5eb1a6ace13779c353cd2ce8e7289404df1c49151d9d7191539e1b52572885667b86f719e83f5741a2c355c4d65d72627b9b6ad50d8cc7b66f442f9337d70370d04d54a426c27fa3cb6819a2f463d17e6d2e276cc303540cb6dfa9cca100054519cdc87a04a7f810a9cb88246cc987315e2ed40a5c69b5c7a3fe5d151b25c7b249bae09
  | 13 => 0x45e0f4c64d0ab27ba4cbcec8df758fe8aad21ede5527088a48289bee00d5bc1adf7549c9e2b24e31149c9905c6aa4a2981911cce2a09a9635326042be8ac1b79707624ea1f011c41c18a444f14cf6306898f4f7188d207c8d993f11ee7a337570eb2951f8119835a973983888eb69b0a620ac376eb4f16ad739be4f22373b9fb72989dd6c9b392d5a29c44ada4dc26bcb835154bb2adc636f4243abb44cb131b3054712e882525092bcc462a9bc611eb4badc2b2e33d0643ab9096908ab646a561d85bb9a25bb70a65807f209380d435432385d5184a9437c58521d783583b8ed33143d2bc96e80a519fe78379c6423b3ecb605160a69441e8313a19402ef3097182704b15ba896f91a0cfd6d46b9b2b1dd1e28bfd8d0c17d7e4300a796b7f23e672d730e64d503cf58eb625546848a25e795f9759333580a14207529d46c4bd2a8544f09f04bc8ba54e8a068058d1fe3e928e699582619c31e97ded251012e99221a241c71017a9475172693d1ef5a9622e284e622d58eff45265b34fc99569be5e14409b1066d845fe6b29418a26b010a0e9629a2739e25246e4a4d91a8e1ca51d14bedb0554c4e39eea2f3c3759e3c26d998699b4261565211055c94cfb84b6bd703697d940672f8a6999e3fbccf9758849c93a2f6562815646c8d530d9443c46b124ecee39050b0b35b10532aa5d9211c42da97a181c3ab0dae3f0a5359cbd3e2793298dbb6542b9d75e5ac6f319b82a01d4630cf9237912fccbc18405bd18909296416e90a2c8446d0f43ba5b3fd38584504de21b91208f055277f42445c658d96bec03f59f4a6f2a9d230246515f9ab96358c94879e2e486ee6fa7cc4fdf6eedf7168b62f0578ebbf1af8627721942ca2d11bc2d85aaf09e0fe33f44c849b6b851398dc525ad0bb64930d7f460591c4f1a82d13e43da9d94348912a21007613962dc9436cb781f1405bbb1cd904cb144b67c304b49c2fead3229f7933b920be5aed609fd263aeb68d672edca8ff00815e1e573ac740d943067fb26ed2ead7a063cd6c417e3b812337671a07b7d8745d9e16475ecc9585a2f8214721999082d390272b08680b720e66c9e2ce98c1b167c2b1471d1a9b88d972a6804cb5ae5d085d798d474eb87055fbe2ec04f891d02662fbfb20d2a79005e2155d292d945ec18ae50b4916a8e0053a9162556474a4bd38b828c97f9879ae162fa01546396729d62523025c1b0f9bd98d7378046bb63c7b8855b135abb46aac4981d119226ea8f8a6cfb51cc5a16cb08c66f3cbb87b9ca7a40c66548092c957473e5f9636c365127806f81a75fdc326a88caa02b49915474d3ff61258f35a3c62758fb90c327d10e866510ecf2b624b790617ba7a2c67258d602024a1707f56dac1cb88c24d0487905a179197497f0a28adc999beb40b6ca2ad5287c79c842140b1da02c
  | 14 => 0x65f3385a0fca0557b98cf8679a508ea5928c4245f14299a36d2ac776f117b0e45985ddc2f2c581a943191164b891f896dbd236b706a29906cf664181db18f2dd560cce3246d70b82676206c4d0998a78138b1ce5270753ad4dcc3f97a28748de90e6fab36b2a68d87c774a029da9d4db9f35eb7511c6776b5786b02670bd910b1d41943eed2ad57f32fa097a472c0596ee6b372364a6ad681ad84f2a1ee17cf8da053209daf9e9e8d212ed70f0e898df944d179d42bf43f1058320b6e949a66c30e30e3f70f07f85bea460fb4fbb7a87a9c69eda90e2eb88c6d67de83fafd12a1620e0c0c93918786570e540d6db277b6a580150267bbea24ba245d15e248d2762109dc1402c0313e0ac5a065db59aac45869faf0c6d76b05b35c9b506ce471a684e7c97918da451bb4835556fea60334b3149c862f966d59da0e0896a592a39399e5113d2447c064834d88b2abb4a78503180853666ee23d0dca1e280dd07486c99e3dc0e2bf6571ed11930b34a17144a1cd125d70229b39a4b976e37e10e80aff48069c0e5cc4b2bea2feed15b8b3ab72005443877633b33c14b629908405946c55c421313a3c15c46e26cf4636039e6458f03714c75e6cad46e10fe3ac0b7d48238b2c598ceb6704a339bfb1f2ba464961bc2a693eb9f5deab06153b87453a6e53f80f01a80a4c94fda26a9f1f4c23847f49872f7f17d7ae13dd403810be4a248e464c50288dd223681c79406486bffa169d14bf0ce734550a73ab6483ac50ceb2ac05c27bc0c912496edd21248fe2eea31291fb6524bf9a2bc1a7a00dd059f4ab2d0cd2651a356949443d4ccca805895256b958d892cc80cc02108991d4cb41c9903b0a33a626647990ac4ec1e3a18a4a583266e8b48b713a9c2c7e38a45faccb61182aa85c78e46ec4a61677d6b535e6a3973cb8f10a870bfc7f8ed5e9cd6d866626a00f71a959b51b8c0a0edee511c61a94ad0f279b2d5e8bbe6003a5c9ad003deb38048d9eb00a83810ba3afc83792ca7edb2d739b0b89c2c9d193e836b21d017409383b8733548f184a492380a9e9a554d327b5c0eac7d252a9e0dbbc5a4a1d7d69334890d169c16198e00b6eccea90de4a3d0b21151dcfd4e315f604f5021b896e791877d91baa3fb0cbe3a38f5f80029544ce18092587f050c350190010edd965d96b49e342b29efd37614d63edd734e7c6edd932faed0656425a3bb65cb4235bc4e0569811213dc43fca571586dd029404610f50aae384a1a85cf84f426ee68251990117e3517d2de1509137b70b63c1d117fac9b17cacb83ec4554481fae08e3a0f6e69882e95398473eeae768a5c10843a6d16d682789a5b90fdd7102b976d5a62aad14652ae761c264021fbcdc190bb7e210d2e25bd971f98deaac06fb6f62a312e5ce6a98802632b09a348b0b92d4f66ea469029fce93a2af
  | 15 => 0xbea5aab1622abe1025c94989c46c285e10bfd8e244bed61f48ac739cb11b7b5b1cee5a1af4dc7c78c148715c05adc2d98fda3faa11e82571480af411827688ee2b4bf80d098e3eab377c325824f8d4dcec23ccda47f6f7bc970d87851406817fab27069904d09517b8aad3fab015244bd5a74ca2909b2640c74ca61c0d64634bba7b251947f3a509a818205bd32194894f7496527ec5acec249fca18a17e7411fa5bd1bb5f51ce5824f158c0510a031d750e99a8a214d6c89675cc0b261292649140a98d41197371b064acdae0a2f7e7486d861f05c9157a4ca5681f150f7b18e97796fa966caf4cbe83729b3621d10534ddcb891153930235a62f07c8f880e996e821dadf90c33b06766795056c723f0b01cc33d4a87563bb0aa97525d2aca4f9ba3e9450e90480b7267a793c1c62759c8b450784de0eededb7869a5e5f5d9890a7792404467d5af26b9025807d6910567f04bc045d80070e93fc4d1ae191bb304c0f30c60caa2965b99b7098f25ae08772c380be20f10dfe6b5c74e932daf053f2761cedbfb2936a704c1e2c07428b81656ca8e2b083b4e685311000a8c693349ee0811c4ea9649931c046e9bb7290149e99be5b2ed0540b62dcdaa544318423cf8ac0aaa3ade7f1a261a2fb4b4027cdb208cc6028e0e581956413a9ea002b499a65f2fa1c6d5773a74282260c92ad969679fb054dedf0d4403456ee79b107bcd453457eceb702ee9247b1ad3a78a9f242ac45d494041c91e57506e137688bbba923c4e9203ffa22f59212c4281a5b397e9cde93e7679670f860eaa2296c8a741c0b30a398b7cbc26eaf06d51c456d0f6ebc9c575c5e63a315e541e97243cd8ea9bc52bb51b6c646da80ded4f1c1c23d866e10824e800323cc74aca3596cb8c01c92cd27364ed43be0edb6b68610a3e673b3300c46ecf4edf25910383a822b19082e788b95b9f49c9814d4b5b34ea5fbba186e2f4a33a9011d7c625593dee331eac5373a80f1a304cf25592712bcc8cbe64a422499fe557cceab5d7d869514d9316e637df64e651c7202592497b3ba8602b360862fa73f8e4609569bc8a1820cdf6461ec357ac0815be1d40696490716ec317e517031870264f4d2e4d4049b0d024be98eb4f3e7c88aa26e6ee69a5367c4148704820cb6342f75d2a4c379cac7eb81ed9e53ed452a9f9204435f17d45c8ae63728027ec61c69c8f5326e852731cd854d5cc325d264f671f0ba123d0b67b57ebd40492345a071f3462c5b893411b791aee100b06ad065e26a7dc4ed170c118f8edf632b0a740c70b746c8ebadea04a346f891df19b5f16dcb9afd63ca6c50ad446712480b556e065071c6e7f0451aa423f0e08022108d1f437c1740c9dd3f0c4ffd011c61062497a961ab0d94293ae6c052010e2442703d9dd78b6ed83030a3eba520b7776f21a450ec1b4aef
  | 16 => 0x7bb6771d9d3a9353b96504e2dd99515a4ecbaee87865918b6e806c96b66e2dcd9fae40f123a538de745a3a714258edfd04e022c54c7b47a759c8b61b8f500ad163773c39e70c98159054073d85cf984a2b5cc1eaac269d3a1d44e271c794985b5048509ab98c467514412c01298fb441bdac279c064252d54bb8bd5028ebd080d020582a12a6ca074028e1e326eac957e79f4074c1c110da0e2ec87a027420a151c3138addc808a939bc62910a1e0ab8ba87cbfb491376bb82ea430a4f25c908aa82ce25772316d69c4610cdaa63cbec76970a49e8530bba99c5c60036825429c81cd38ab3e05ff94390c5f38c6b1e58b4c399ffae4c309474654b2e736d0ee0e7fee7d8b30b680bcda89438646d062223265a6b8f03010e01c3d2204ff70af03973889508a3105b183c2a2b907032ec740ac38f11e7a260663e4fe2ff45b327d11675fd4d1f1454a42d17497905b05c590af5d3f439bbca8c881e68ba8b689b327160a50779b5296342376d5428137f1725e8c1530e5049f4dbb6c48ebbc72e5934ef07d8e101130b80064302e51c5a5434c10b60d7a0898259ca32671c1f93b02fba931ef706ba0016908d84144a112ea8c12f15df6b3916986f26de8071946052f7aa26639ba7702958022adfc258e59b24f08a0c9cd288d4008f562cd3bbc81955e0c1f269285842777ed02f04080cb79dd515d7becdf34403401fb3605b6a04450c68ba6217b0a5e5778c7a5292651cbba1107c16e1894a0e1102c7c7454de77f0fc5c9357cc696e745565790402a47d28bd27079a0c284da372c7fc55c9deb9a7c2e018d980296500354e068dfdf8f21e059761c1736424898a9f87bc702a9b03a412424d8c09f267bcf5637c515620e1fa8a73d6bee9e0cb462b03a881f78685f65ad0a819662d1dec779ed824d4258bb341a0106108f30e15080ae8fca4fee0b5be301169923d79a8b053a918ee9dfa2e79a6a48a1404e4befa1125fd9be2134ef51fc3b867c672a467b6ba547b7538967c9ea7e0cb7c2313208088b4699d225404a84b8401a147c6f11231b381ec225b0e6157379828813b194f282904e96185ee0221398161747b4dd0207c8eda41488d44323a21e8f0231701ceca27844d99e64dd13b78308e75e9ce2c4aa7f97e505571166d9b9384ab77da435a82a33cbbba754b05a0ae870e0c09aedede1384b4eb509a7e40118c18ecd1d85c32a515981fc80ba8377ae61c5770fb1fba5381ec73fa30cb8d06857d0e3c07f24dd01321e0a45f26d60ce45f1644a1ed077ce96cc4a6fe1b584cd8e803f08864666d20fb36a3ce48858ba2392d5c166042f1cd7752008a7cc6ed40b5222193e1d53f85a45064fb1e73e391285c2d2aedfe39de0612dda96ba89653a98367960c6a6e97e8916d15aa6d7b8fbbfbb1008f5d1a711c075897582ca0006abeb5e84
  | 17 => 0x30126cef18f6669cad805fe90abaf7ed82fb409fd3a0aa5a30ee672cf890e73597976f5c770b05a76eb8b9ee7001f6783028022df266a631ad44d38f00a29bf0c8294ea2f326b6aa49b5d7d0665b15d942776d215832823ba1bc076dbfe5414a053b41eeccdbc31e63bc64e09274554d225563473865f2747c6af547bfd57148a2925c0f1659b23122606662dce980a003bf3b07c2d1fa95cb9aaca6e67026e53a4c50b6af85ce26697500c780102f680601b740ec85073d8230dd0358500bd31f04f4c9b9450804ac0c59b9eaaa3dd14cca166fe7142448ad5f023db1907edc82aeed010a4ad5126561db85aad3ec482184e763812a2e7ab3fd146d88816763c6ecea6574c6310e6aaf0434d0df98fbe87c3e1f3602f0cae25b72e0e5e598e729e64995ef017247828d26789ff4c16019d964cdf301f8a735706f85a9cc9dceaf9a678d7dfad90e8f0f77b0b53a5bf7d10c78ed214c5d7c31daf72a970969944f41be0404ef8411f86e436c3c0391232cc42467c728634ec5d74e5299a8cb05cfeb9deb0c23ccd8b09cf06daa45333c8db229b161222569e2f14019cf3659911ce806494b1e040a20d32c33e4d473453e199053d08911c302d08834bd370b91ffb8116c29efad2594f6c1daa04f81306d37a60e8bad4711dee7d379e2427ceeb6a6a83d5759d42ad79ccf25cef4a924db775cc8c2529a77692bd50c96bd6994aa1d419b7927ffcae4fbfce16d0c29055ee57614c40c8acd6ba6f91000aaa4d053e5d8dcc98e94d72a08dbe858778e07fc90323215db25af9f7a4ad93ee61b796f9fe3b9819f6aac7903d4504887b8fd6426db0988eb86dc8986ac7bb8f548c092be2e836e53a909ceb58cd684d3864a48c1775c5c507285068fa096fa8535f22216eb0cca042a8fb260f3f9129679767edae43b45ca335624e45284fefe69af1a688d8b305ba93ad61225072c84e95540be02f46a9ca31e3c8e024afac9020ac90b11ef28852fe3898d625bff78c431c6328d7722c15971741b56f928011b18457857f0cc43f805476858a611f0df1012c4367960e6dead8c3629ffd6a5240a3152200504ee286537240e1f9b8107541e304e5324eb6a59e2a6d6e8831064d3b4a3b79988e4d86264acab39fa94055003a7b1485c14469a9c8080b9a0b8b72ad3efa56cfaa25bb5799744f82a6aa57948dddf8309141f3cdcf5d010e8f173a1d966b54bd0ca71c1410f936a743fa12982a09ae4523eec4d01ef120035f68c19c001d93b23054784aab8848d12006dd6621e84e29ee2e89c332e596485b1c87d50cf50eaea8da591438bd82465cdb693a27d656e9059a5b5147d40c72c5402e34af37d00bf1684cd32717d3d41f59d310884f49d22bd12c2d7e122d2467a61f02ca50f972e36e6bb8abc001e5c1391022da0b92f013d74191310858ce266266b
  | 18 => 0x27fa2ce85647f588927417de6e55c108aa42aa3632c84f9768517f4451838f9f30945b461d51d58736da9201d6d05e1a97da60887d65707717240289497ff2414edd4a517117b210bd3f4966aeb374b129f0894065da1ced58b6d410d95e62816879c3dd41ad339590788ec55f086706be53575a08d66e4ca652de5a853c9b25df41cd5fc537e454ac6661115c8f7e8b25007ab7536264f1782c4f1cdc362a2ac9a9423b91cd404001005f93fe1eaa16a168927e4f203705341a367a202a0500ebff7ece9c54f0389222c9170d8e9a69ecab7b135fad9cfb68689ab7d04e5236e611f78dd700556d5bb24c3f8dcbd4a6f6147743c2ca2b6658cef5833a46b75418804e074a24b051b319f3c5e5d0509aadaa47609e305fa4256c78dbfb5517f5a3b8bf7634ba471de2bee140998c9ae25d274055f2d65328d901e87bc98c1bf43589d8d48862055c87f75fd58e30e9394211ee0001e61a6bbbc333a9bfd6f755a83ee2b6b7a40c047cceb32a3a6c71a84cfa81a9d7e28e1d78a1166212938c064c83323499171c8be20beaa95fa1329e15ea5056a347a12903aee443ca9b76750ab5a56d554a7aa14511f73942e1e485e8019858b9152a051d340ec4ece03697db8b05e96a3814d11ab2b3f9aa994e87945670b028b05cbede9033bd2565a397fe370692db159a6c2dd62b45e05f388c190a2d502f06f9c0cf202f922f79ace44920afb719d4ae11dc2496ceedc4fba6e9da43d5d803a4a8796aaaf571409b3c2cb6021f5ea78cb0d5dd9f2c72b77cd3d70a46e83b16f0cf8bca8a4ad544cfe59d08a68d6708254482306f48d51dd9409435224dae72463239f0e74987a03c51acac1118174503a8541c32a93de1c188568cc8439ea4ec620877392568968ed0aa4d0babac25b1798061c93227564245cb49fa23d366e134d3d918069a8411f8786f1c2616e0dcf45ed5525af48bfc1fbaa37c81469265f737ae29c6ad31a972ddae96fec2ac30305dd1a6189f8130a1885665d31db2bde949faae2a81fd21064058aa2a11933206f9d14f5c5021e8a989065bd864e40888fb94403b774e1d33530026a7ed7bbcaec2c1e47a51f6b8a8e5c9d2ec2fba9212fb372cd1fa1d4024e1a9a28298d2b5e1aaabb3bc2627503dd9ec6b428b630a7f36ca692552c6f419b9c0787c961ede91f4433a42b535b364133aaa5d55cc89c8cc6998a6272f1475a67e83e8d466499389074190cdec61601c48ec3241ed996443870788a98641983d539734aa97ad842bdce365d1fa57cff89cf9b17e0d56d2727162c181a2931f9451113900b197173dc68944229679cce55f4284dc0129812b0d379c0399aad58af792120ec9dcaedc47590760208d240e30a373bd95d39de0a955267600a79b9b05719ab61867af3ac476843c894ab6d521006bea4405a26055a5f2a84dec79
  | 19 => 0x485133e5cfdae346412549302182ec65dff916691ae4c0491fde2e34e109d78bbd3d840f976fac6ede28b404c70736d026294a9c60433e9c8b468a678ec80cead621263fac85b0ea77d4843ffc12bca217a48446cc20ca0727ed02dd593cd726b03a8f7c126c66a13e78542ccd6d7033479b9125c42c70f05b72895a419dfa02ef1e1785f6429c7952ed0fa01d186685ec7f0123f599b7d94153b87afd55f0a3b4f7d3fed6b795eafc1da22ae1dc11c1dba1b8f8b6ba1155f96b75b659c4b95c64dd5deccccbd01d35097c183d0d2615e4a49ccdec8dc837f55aca621fab3d0d70b5d6617a82c7b75d7123fc9ceaee26ac26ceaf661fd80a67e9691fa1dcce1baf6dfde02532aa4272225dac7e0afe858043d68acf78e6f26b847cd67a15e782111e8fd75b4237bbf8029e7cb677560697ca06316ec206279e7a62c101c39762e7110878f7b8ae572b5546df53df9d929bf641055dc201c088921051e961ddee921d6c05c3a06e9c001a88df83416a118e86604df6d9ce00e054b526384beea9de7dc7ed1a7474e5a8e9fc9353611107910a4ff11cca48e259aaab4e6b15a0abc0d769e82b96b11ea20793b7b945addc60921d4c486265dd3605f9db34a542d13ceea3eec57f3d6ded8523058670ba4130dde4be18b88bae5649a5a0a2e665ed22169dbdc1e300930bb8fab1b3f0141cb665c00ce3d2ec95c9ae6039da1034ed9abd09b6d141138a4be5f2bdd9c8db3171ac45a4a889d349eb8ccac6207aa4bebde8680d7b76cc47a681107027b32bc764993327b04d3349d22a49c3b1d70880224036af4063aa4383884fe6d3c2ec67cd64c22d70bacc2e6c7e515767ab4d7d4b570018e24bbaf3289014a1cd1c8a92c6e09fbc8040a276db42c6ba505545fb297685907339003a8b981265e9e3691e425f20127ff97cc7d5efe26c9e587cc06b52aff98627520b46d84f552e3c4d505a720557d16764fb92f9122c1a4386a44f797e464d2d4f32a7c026a7b3df0e3ce930a4944c9817702c3ccdb3c9e7f14970ac104700341dbd4303926ad52d022b66776a20b7ac80a1fe61d9e3f8ff96c665666af91dea3562c9124aa1a1142b72a918ac88644438f26575f92862a96b27dcdc43c44015a0bf7a9b438baaf517ca3ee8acbe49add4b794ee24e86054581c3d7c81370c528af7b6a9eca98a86c2d5c6cde94153fc67dc3e0d5a71af0c02cb82288d36a757009f9e26962b3eb545b44199d885e3b6f8c9144d6e86f629633911068e8e542f02759ad6b21d89144aebeb9e95280d4b34ffead1eccdfc395f7030260aa7b1549c89c2f80ab0c51c23a89c96171228023f6cb939b0bb8cc5fcf2874f53362950337e82d0942d64319298c82c2d54ad3494d8540902e0089e59461b3bb468da533822c15d08b4ed29b63b8380ae944c8058ec86b63b4a03ba8185
  | 20 => 0x400b001c00050e0005000c023008800f0018000000400d00440105534024003404100000000024000000801e000014300180012fa400a0030d980000001b3380210018008006c0397cfc00d00ac0185ecc0000628023151c0020180bd00004000008800d000a68001d0035005000100100034f2863100000010038003001801900000050000000003400300a800000040020068063000000700b14150014000002e3ea0024004000006900000160000e8a0034000002137f000000000180010000010002c72e005c02500393270015dd100063430009b3200d40030014000009eb7301a8b440005321a080000000000372bc00a000c00300000059cfc0190004000002c00f3b30001001000b004c0040ec40080018004002e1ff001cd98000c0010004000000ea01001c003001c00e0014017002000100bc01e002c02d00000020010a4618400060000011001801000000000078007019c0003f08004002800f00500048d380057b194fb00280002a9e312e37770e7ce11d99fcea2c94b10420b7a1d1479e4dfbb1c20b0621186754924281b4a0b9f17820b77e53867a12a502607118e9ab50df222687575dd57e4935a98e68b5ba79a112d7b545d241f325c9e8b9826d5c2512580c1734bb83fb84e65645429a120af653e58642a8899e080635524a603c458932aa034c0d4cf78143959bc2498e7af237a3445268e35bafc5b915a89fe7d5e207e40431100bc1916d9a2f840528bba9ea7ddacc09ac4fdb2215faeef89f5b539c9834cde0e49924c207bc5b02304192eb8f6b6c3705d44d309372ca836992d52e890b88760ed828573a59dbedfe04f9f8b071a6d210958e66f52134b1a0600481884c4cf2daa37bab376601e1823b68d072d9d33b98b18aaebcd3369283e242ddf4eae19b726ff849089a6acbaba2794ad907153719f8aaeb30d46f2d7cc12118d3245531784b6bccd6d0248d1d56f2b80cd5c39a33f1a61797d67a8b4cbc25d46a4694c5a832b8785754b41a91bd11aedef99e591dba0bd5f67f2da481191c1f4b84ab69572cf261a2dd6ebf0498adef7e7dbf12f6c71c8682808f7f3aa1b4d5892e6a082149021e8a9e8deadfcce35aa85e4a627a9e52553f652fda5d3a52b63cbdcb29022e04e5b36731942f40cc6e4c0795e08f471fd2e9ae641fa7ad16669783070cb258ed9b91c4838a88d6175c3e710208331fd03369bda2440fe952a4f631428ee58fd895768ddcfc0340cb22a2e8dc9f07a466219bbfb5624701dc2ff566114aeee5d3fa05b7b2c6c9f9c00dea70e274df5181954f31c35b2fe330463af198b60b3587e8e617dac55a85e1c97740e480a6ac5ce919de12841531941c4f6d4e44c0412e757e60b5612725a0d11fc8200edc2cb0d0eed64bed3f606f6a5cd50c95e177401a8396bbb08714923b137dcb711cb3f
  | 21 => 0x80005c7400004e85230080000000000c002c013002c00100000060000000000003953a4002001c03c002c00e00f648f00240000000000000806f0004000000e5d40000015000801f71dc00000662c4021c00e0000003641800e002405d00ec002003c0ba000d564006c08e0078000004dc750004080000800000000ad007800500ac0020092651001800400fc03100d400000027460002cf5000de57005001a00280000068003000c04400c40021924038000002f00066e500800000004012ae580040008002040401c000000201b14d100000210024000004226f001c087000068f000caed28e80003520006000000300080070000055000400212e00080b4006000600010004009000801b545800000d4001002c00400a40040005e210004014035c0030070000000401c88a800c0084028000a5ed008c001002c01f00000065e6c007005809800140040018042000c00e00029f2001c004011284e00d40000038004006004b007802e006800000007e50000005001c028000c006000001700050bc000c014004c0000034007001800256200050004000559405500040a20120003000400e374801b0000001009c00000001a0000801ea60c0060020009952c001000400600340000006b1300018f501c97e6000400b000000100000000138000a264000000002400dc00b000c01b000c0010004003000c006afbc031000400a004c001007c007000001a007c000033401f0028009000001231f40420072532304465000b00000004f1b002000300d001b001c40e000802500487ba02f8003000000000c0000004400000c800000240000018044008400100510d0a588015002c0000c280376530000000402100d401d000c000000c0164f0034e0068000003c051000000b0082d2a0064048003800000280050014006000a27f006000c002c001008d9da021400701740002c7c0000001763000c00000a8000000402b00000010020005b96c00c02dc005001802700f80070008003675000b005c007011400a00124ac00400000004000002002f001400000057a6008c000000400095540000020017000000c001000800000150011b6b008400a002000201c54ec00200000000002000801d000d35c002c000000800200947a3003000b0014000001c000001c0030d280070038000000a7690030003002c02000d000d00180254315b6b001c000003c00312a80010009f430040019000000a0000000000000200f400d00000000014001001c0010060000000001700200008a0c00b00040000bf8005001800b00340500009f4500228c1000000000080003518000009687d00028800064002000000301e800702a8007003800200080040000004004401200040000000004002000500018da0008098000c00100240280000001000800100040030014ab1
  | 22 => 0x8000910701504f5853000800380750008e5000c8002001405000340410160002000c00600ce8ef0000021008800100080000020055000000100d00006ab401900d8000000c00000590dc0060011000c049000000b008800200bc01901b000f005c002a1f4007000003400040021ce1d90009802e0020006008400801c0000000c000772257c002400200000061a90009000400b00480140038001000405200700280014010bb500050090000000c00a0000000011c0740038008002c011000c0013300011001401200040126e4c067002c0020004012000c04b0000019003462e0000017000000b002c003b6f4139916c009b7b0028000000502b000b01080090020005000803d00018c4000c0009e380940010032000c01000cc002024000200040020088008001000d006000000840110061b570014004498c008000800300b8012004c0030010000000801d013401664fc000002400900008fc003003b003c003002d76e001c000004c0070006779005000a00080035d8000576f0b9d000003b0095f23003400501bc002001001200040005c58002000801e000801000100067398001002400a00000010398002000400000080010018026014405e001c000000000500700050010000004c000005c01900a9df6966400e000c0001b8802400000090002043000000000300060014000001804100d000000ec000000401b015c003002c004286400a001c00f000000000080040084029000a7a7000dd440000000003401f000002100700001078005002000b000000e010c87a0011950000800000dc0020014001000000700000030234003448800701a40384cbc00300000008278014000c002009401c0000000001005a000000300000000014000813c01c000001315c400f001804644fcdcd00661bc0004000002000500000370009880002c00b002400001440030000020004d3c60004001000405b0188000011000000d402b001c0080090001001400f0004003002c000000002100218da000c01a009c0000000cfa0000005af38001007000e001000e001804f004c004000002002f40040011b20015c0000004000998ddc500040000020000016c009000400100340005bc80055d600040030006000260d00000000060001009800a00300850000001a1d00020001175000000000c80000030010001400400f000a00600010008003003800100bc0010008000a3a8007000400300b800f0014002000001200000000011a2fa9e000c00040400024023000400200180050070003000402c00090c8002800300140060170012003401e001801a003400d000802b0010024005400b005000d7634007001400f003c02d01400070000036b4280005b58006002c0000110046003c000001c00400000050008007000001001f800100440090dd18f3008
  | 23 => 0xa00164ae4004005800a001003600080050019506016800400000010bfc0090224030001000103e091a004001d0040002000c0018c3c02100d00048aa4061003c01a002c0010048006003c003000804300062f9028400e00240370000051003c0150296ee10010001004c00000140022bec012010800900000d6000400c0030002003801c00040310000043b98c01c0018000009002000d4000000c01c001001c0060012002c0b80040004000c01e000006e000400300b0062002400900040240000035001800000000190074000005804d0174a480d1a5cc00900391a2c034005c017004809d021804400e40060000004000ddae006c065000408b9aa40000000039005800a021800000180000048020004000100980450070007002ec8800140fc003400a00340000004000019800b0029d3700280010012e0e0044000000000000f800400100760018015001402100180020018004004c009000c0000001cf8001c0190032554003c004001c0390040029328c942000001200ac005174413f024400200080270008000002800f00000c400480070180066000c00400000000050000000881826f00150014005b10006e01040060014b50002c0025f1c00e02500019299d02000000200000130014017003eb0c000000400e800403bd4a225dc0079e0401400063b60008003000002b000444a00000a5002c02db09002401d4015000000b000000b0000715000400003cc059021c0000039e1c00000300004010010002c89bc01100000000004011000000100000050008000000812f745800d006aaf0005962a01b8002000001d002c004000c00b0018000000400a000218300bc000000004e003c007002c108000c0022f9000000405be000001e001c062007c001006800400440d3002c03b00e800b007c0020018002001c01ab8ec012008400f012800201c4000009000b00000000018000000294b000c00200000ab01240670138000000000800340004fba69a001400000180000ba5a0f009800000000189df2b170004001001000000100dc0054006001400c012800104080000008000004007d0004ffa00102ff0000001511c000672802527b0005000400d0000017003c01a000402c00200000114007065c12f003c002000c00200680220000000004400001680070030003005c02e0240024008c0000000006afb0ed30250004000004a0008bca001c00b000800100b8084383804c00000060104027002803c0008000007c04600080020044003000404400000760000009000000d01b400200080000095f67005c00b0050001015c00002ac01c001800700e000000c0000005c00100a6e8f000c000001800001c068e00b4055005c015001400a0040001000000300e800c008400a02780000004003004000700e0043016000601c004c1a612b
  | 24 => 0x86068a7690018002010c019000403559bc01300a401d02f9d4c00ec00b0180079003d78f31dc002002804600001510034c8500280060030003020000101240dc43f001240b4006000400f002400a00040040010020000c002006812b59ac0860001c7f00200060034a090b8400000119ab00100200034006000015d76f00b7000002705580000058000001800001000000004001005c00000040cf0018aa958bc00040ac09400c002600000280084d510034021006805d3044412002c0ae006c003a31400500000400014010003c0010144005a604078008000000100030224002000000a0008000005c00600b807401cc00f00240000068003017c00b011c7200008031000136303c63c5003400ebbb800009800a1003403803c80360098005001c024244c000001004d007c04d001800702980770448050003c013523401600155c2001800c0004000003c079011400017940a1139804500000169b04013001a44d000c0450000000022c01d002400f006c00395d000000100200039385000001a00024d600481953ce401300d0000025800003d400b005006f00255ef00a00180004006000000f00200150000000002800b001000da5c800000b40000000000000085c005000204cc04f0020012002c092000d604000c01000000083c00000000800603f58921c7001e003001000c000800c40180000000aa5801c245c03c011c0020064073000002ca2a401502a4002009403a00044410000037000164800000010014015348c02e8aa000001180000021a9c008c08d003400000164d900400232cfc19500b40092b901e396f22d4041c06d0000002008802b018c008117800c0924002001800800080000000433000000003c95647474004000000803ec00300000120000007004011e00c8000008c28f658400a0000001003c9feabf8059000400a0000008000400cb3cc00100000010000016001c01272060ac007403700040330000006004c0000034e7a0024001000c04f000000001119850078015019c01f93ac00b0334016002c0210034014269c11903f0000003005600000093750024001c008000000000480b4001401e00a801300000590000041000155d3ad402300000000010021001a5f5001400200000aa00500740204008000009700200010008003005805900000650038046000005b000008b000002c00029cb40e400c004000300003d86c902b894ac00a8fa402800080050008027007c00a010990e00980000024001011c016001000a018c06e011c000000d7a600000600035d7200080000038008000800200ec00401c800c000000000180080031442030000100000050054011000000e019c13bafa0000005002400a801500ec010258000100040010004000001011f000000101e402a28cc000000000d000802a0000000b5
  | 25 => 0x4c00000065e9006800600100050008172001002700100920b9400c011c019286c00900092da000c016000800001481bc000405906c800f00640be00600018914003050c0fc77200010014027000587d00fc00200900a0024823500f000202b962400bc004a34c2fd06f802500200050048002002c0150284028000005508940e201c80505a2800300081b9029c0023c169550000002000001e00080981420c4a004804d002c019004c02100000d0001000b01e800f000007501088e6040001b00000099525d3f00b8002010400a380c021004c000951c02a002c35700100030014000001eb8900200390000000007400c00cc009013c5a3725c00100280040000000759000e8fbc004024c00000382bf6a88019000400100380013556eaa00480100034139001803500040040064b61010d710b4c9c1b034c05802283780648cf40000ffa000000c000402a532c000001c00b014400500ec03e7cfc3c202b000600680145fd23d800d800000194f50450010af5400701c14aa0034024006000400940330050004014803f06ec185006c001000004900100000005fb10000006996c02704d0004003400000057dd046800305c00000000082012610f000000262dc01200880c200100124c0c0070000055970001603940000294000000000600340060024007009cf572b8400000207f500ac250002800001f8000052c000002c020000407b04b400000000030280004033c0080000008000400500000090000000000d83e000402a005400700e0056a3a940c6c980142011537018cd030000039002c00b288000200880020002e04000003e00580c9005010a007c000000800000040020029d5e00000220004017000802800000000000000043c000298c019044404200000000000000033e24c00d0084014000002826cd0000002004c0b3000c000052c0049d58001003400801d80df015812f0014018001419000780000000000000c04659a8000004000000d6064003c00800140730010251010c016005c036004400300380320002ab700340030060003001403b94800130048011000803b001009e00066be00680008c4c0a5000cec0026006801080020021aca0000000000c14500d0024009800a002c07b51466590000003000400101dc00100c801c0010001bb5c021005003e00000010298006000c000000000d14c80050002322038004b000000ca49ca8000ac04c50080d745c001300040060004000034400808480eb0eb6dee75740d701e90fbb720003004001501d19a300025fe009c0158410004074ebbe0040028000000c3eb4021003c005064400c00000002c2c028000c00900cc02a001800005280000004aeb001000c7860007000800b0014000008c107002c00f0004015001c000008c07b0130000000004d0035dee0028001000c0
  | 26 => 0x11505d401c00cc3c60102b1100bc025003d5b90500fe4000c0070278001003c4570004029000001f0000024000800a000002b004c0000000002000c00700380b0041c0030dea75e000c00400d8000b01c01b00a000002d8000003000605740020058000000401a019c0722b620ee000800007840e9002400f001c000003a85300ec12501b01550000006024c017130802301ac016000291d008df86260828a014c00301d41030264007064801601b22b1584000003400e500100030a540020a440040dd001200c400707980a700ec0300000000711804e0af000282980027acc003060dcf90814019000c06c000808ab0f8000411c00101b001b113805900600c6015000000000030038000000400000081510018015b59801e000c0060782f2a9c31e3966cc134000000d002000170500057c88001ae88028071ee31003802800a4038027019060d8000003452502fa2e00104085140002b00140180000008019000500000360d640010004145003c00000080013a9810a0acdbe3002804c0064009000406200cc04b00f0409002c2779eb404d014cff9019c08100413ee0002ed40011e6f015c1fe00003959b095a8012801101b402f000000f7e2803900e800200a4032009000f003000c001016b0138190015803f504000c000001f012c25501c800000000dc00d8012005c020003402d01440310400055025000800cc00002c0005024400e001c001001400912a82bb00280071f2000c11d80a5000000a0018005008405603dc00b0204009010401f00000f200d9e3900781900014019003000a00a803f05600020011fcc034951c0000058008000000a844200000030428014004800201480110030045021001400840100000000000022300fc0198ef001f0190014014c28600001e05b3c00d035c01903b406f01180c900100aa00e80d473d000b00100c000e400600380070100001018c000008821903c98f605a40160a1982f00f803e015c04a000089902e80010000a316db9ae600a0090000402b009406b000c01601200070000000007c0064f4400002c506400500094050006000088f008c008004c0f4000003a00b410d000415f0edc005329400f0ea400000680520040063007c1b1004a7d304386e0012806700c81f30000006a47c000006001e00001030010009000e8cc0478074017402100bc13c00a5f343214017002128d00d4095008400301cc13f027c0090000006480c04402c00f4004c0470090004013002201bc02b7ed8081000400900685860000000048834c012003601a018c002123d0380060000006200340000125e2c00352250001cbe000c0000205f9400e801a4e60007000c051300c02c03f0030000000200c001d012c0006350000481de3c002c05001fc00f00c400700b80af000000000040543d6c04b00080670
  | 27 => 0x41e032c00100280c381cc00001bc00001a4064000400300940000000037010400e00dc0a700000d401340770308081028c0090034261018002700bc01c004001e0c1c0020810131000800000f800400385c70878004005c233000004401e8133091801507740140944022003c648032455a0104113000400600040090020009005024d14e00a000e40041db009301dc0032be00fd56a0000003c0530454013000400d000800c0000304001d4de031001a0020f8005c0008020003000596d4002016e06b4007001c120029804202a8000034400e08cc53c2794011012806c687c0011ac807f009800c00d407a0034008000004002d939f0aa00846e3084b001422e00253dd01802260000176005c000005c05d0330035002c00a01e001c00023ac03b4023063c02e65a00084670225002c015006400400d8002045d60300004ab01000002e200170014016008c0130004001002c005119c04e01400fb03e803c016c0960140007004c2140238e58018400e002c01300204ba01500000000014010000a003c00d003c02418c039c000400700f801e000003100ec028001008f788c0030064000000001b02243da915800000b4000025c01e07980ff015c40ab69001c00053cf0196ba4007c005340400500e80980001566002c00100200850024004ba2a6b45e5c13a007c00027b40b5000005301b40480000001049405e610000b002800b000000065440000424277008400000000320024
  | _ => 0
def innerK4 : Nat → Nat
  | 0 => 0x460c52002878585c0460c52000c73515c0460c52002c70515c0460c52000954874c7560c52005c2c4750b560c52000a7180107560c52009c3647107560c52000d16474c5560c52000d14474c5560c52000954874c5560c52002a6481517260c5200086f87517260c52001c6875981260c52002e6051981260c52002c6857c99600c52002e6051c99600c52010a6885499600c52002c6857499600c520a6ec131499600c5200287887515600c52002a7081515600c520008e887509600c52000aa94809d600c52007d2527914411452007c357691441145202193587114411452007d2527114411452000d30455c0411452007d45278d4311452007c55768d4311452006a56688d4311452007d45270d4311452021a55860d4311452007c55760d4311452000d52355c0311452000d50355c0311452009c1e451cd461452000c1c73115461452007c3471115461452000d4431c9f43145205d85e3859f43145201c85c835d8431452002874815d843145201cc54315d843145200186d821d5460852072c2d7211546085200385c835d73690b1001874815d73690b1044c54315d73690b1044c54315d46350b1000ad03845f6050b1000a738545f6050b104587578cc76550b1001c68704836550b1000a57388436550b1045a65288436550b1045875788436550b1045a65280436550b1006875780436550b1073b2985dc14210b1072b2718dd54210b10018741855f3610b1072d255750a6110b100487b8541e46ccb10018741855e46ccb1001c5417cc156ccb1001c54174c156ccb1044a9483507460cb100187718dd5460cb1044cd0315c0460cb100387b855c0460cb1044c54315d4460cb1003875815d4460cb100187a805d4460cb1044a5483505650cb10089553855e420c71045ce126dc1420c7100895638dd5420c71074f0535508420c71072e2565508420c710448d4385d8420c71000ca5425d8420c71000c55355d8420c71012954485d4320c7103d956825d4320c71016954825d4320c71016957865d4320c71016955865d4320c71044957805d4320c7101e955805d4320c71016d52605d4320c71016d51605d4320c7103dac7780c9260c71044cc7780c9260c71000ac5800c9260c71045e47750c9260c71016e44750c9260c7101ee45050c9260c71016ec1050c9260c71044ac438c81260c71002a6485c81260c71044ac43848726cd71053877815d842cd7100787986dc1420d71003c2f76508420d71000c2d425d8420d71000a948350746c97106ba5418cd935c97100287418dd943c971011a5468d0c31c971011b468210c31c971012e174610c31c971011a568610c31c97100187718dd54649710018741855f364971016c54311d9354971016c54710d9354971016d44311c935497105687618dd943097101cc54315d84309710
  | 1 => 0x1c54371c5650c72044c5437c41650c72011a6428441650c7201ec5437441650c72038c4f268dd15d172011c4f260dd15d172006c55160dd15d172000c5437c5915d172012b14484c431d172000a57864c431d172006a55864c431d17206be47264c431d172038c4f268dd21d172011c4f260dd21d172016c57160dd21d172006c55160dd21d17200186c28dd921d172006c57610dd155172000c5437185155172006a57684c4315172000a54684c4315172000b14484c4315172002c646149c315172006c57610dd215172016c54610dd215172003c2f78dd9421172000c2f70dd942117204ec2d70dd9421172028a2f80dd942117204ea2d80dd942117203885e3859e311172003c2c76509311172000c2d42dd9311172003c2e76508311172000f05424c4311172011a56864c4311172011a54864c4311172002c57764c4311172000c2d425d8311172000c55315d8311172002874815d8311172072c2c7550b46c57204eca942dc146c57200687985dc146c572002874815d436c572002c5471cd935c57201185f78cd935c572002877788c0615152000875788c06151520028748119d31515203985e3859e311152023c2d6291d311152002878585c316909200092f874c445509200592c874c4455092006c3576d44451052007e2526d4445105200285f38d5f361052005a2c484d7261052002a64814d726105200086f874d7261052005e2845981261052001c6875981261052002e6051981261052005e2845c99601052002c6857c99601052013a6885499601052002c685749960105206ea3b58915601052000e3351115601052002a73188d5601052005a38484d5601052002878874d5601052005e2845909601052013a68855096010520138e8875096010520a7ea141509601052013aa94809d601052005e3045905601052000a7358905601052000957874c7450c52006955874c7450c52000b14484c6450c52000957874c6450c52006955874c6450c5200783e4859e450c52006957784c5450c52000954784c5450c52002c54764c5450c52000c5531dd9450c5200687618dd9450c52012b14484c4450c52012956874c4450c52012954874c4450c5206bd45724c4450c52002c56764c4450c5200583c485d8450c52012c34415d8450c52000c55315d8450c52002874815d8450c52000f0531115420c52000a2d86115420c520018e808dd9420c5200895638d5c410c52000d4635c9c410c52012d30455c0410c52000d52355c0410c52002970585c0410c5200283f48d5f460c520028785841e460c5200283d481d5460c52023c2d421d5460c5200186d821d5460c5200083f78d15460c52000c3475105460c52000ab180105460c52007c2d27914460c5200286c28d5c460c5200187808d5c460c52000c3a455c0460c52005c38455c
  | 2 => 0x355142102b148150d35514210283d4819d305142127c1d4319d30514210185d8319d3051421018751859e301142108c4d36dc930114210285c38dd9301142102a73188c1601142103a68824c1601142102a70814c1601142124e50314c160114214be5031cdd601142102a73188dd601142100a71188dd601142100a6b824dd601142103a68824dd601142100a73814dd601142102a70814dd601142124e50314dd601142102e5338cc5601142102b148150f45cd4210291c8750d45cd42102b148150d45cd4211cc543155c46cd42124a548150d06cd42105c1c4750d06cd42105c2f4649c400d42123c2d4649c400d42101c6a6049c400d421018758159c400d421028798059c400d42103a6b28101600d42102a7318101600d42103a688251d600d42102a708151d600d42103a6b2811d600d42100a692811d600d42102a728111d600d42100a718111d600d42100a1d38119455402103d4872cd5305402102c5876cd530540210d958874d5305402102c58764d530540210885e3859f43540210485f38d9e43540210187581d9e43540210883e4859e43540210585d381d943540210386c825d8435402105c38465c04354021028748159f3254021039682841f465402109c1e461cd465402100a1c8351846540210083f875184654021039682841f365402108c1e3611d36540210187b68dc1365402100a1c484d836540210085f874d8365402111b4728d0c315402112a5668d0c315402100b5108d0c315402112e144610c315402100a558610c315402100b518010c315402124b5108cd8315402100b14484d8315402111b44824d831540214bb53804d8315402111d463849c31540217ed443849c31540211fc678649c31540211fc648649c315402100d624049c315402100d623049c315402100d453049c31540211fd638049c31540211fd608049c315402102d636049c315402124b508150d30540216096b78dc9305402100d63711c9305402103d4872cc930540210d958874c9305402124b50814c93054021a6f41214c9305402124b53188d9305402100d60721c530540215fb50381c5305402111d60720c5305402166973780c5305402100b61280c5305402100f43720c5305402111d52720c5305402100f40720c5305402111d50720c5305402111d40720c5305402166b53780c5305402124d53780c5305402124f43280c530540217ab51280c5305402124f41280c5305402100b41280c5305402103d607288530540210097378885305402124b50388853054021538761855f36107200086f788d5261072002a64814d52610720018ad48dd526107204aca942dc1460c7200186f28dd5460c7200286d285d4460c72011954874c6650c72011956874c5650c72011954874c5650c72005c2c47509650c72011c56371c5650c7201
  | 3 => 0xc2d42dd5601083100ea142441601083100ad138441601083112a94484c746c9431008d7874c746c943102cc7274c746c9431008d4784c546c943100a94484c546c943111ac4824c546c943100e85424c446c9431118d4874c446c9431008d4874c506c943105c2c4750906c943112a94484c74649431008d7874c7464943100ac4824c64649431008d7874c64649431068d5874c64649431068d7784c54649431008d4784c5464943100ac4824c546494316bcd0704c5464943100cd131dc14649431118d6874c44649431128d4874c4464943102cc5724c4464943100e8531119424943102a2c8650b454943102b248150b454943103c2c6750b454943100c55311d9454943102874811d9454943100d45311c9454943102964811c9454943102a2c86509454943100c2c76509454943102b24815094549431a8f05315094549431008d4874c760494310296481c9e504943107c2d47d9e424943107a6928103604943100ac4824c62654031008d7874c626540316b8d5874c6265403103c2f2551c265403111ac4824c4265403100c97474c4265403100c95474c42654031008d7874c426540316b8d5874c426540316bc55754c4265403102cd1704c4265403100a2d48099255403100e453109925540310386f28d9e42540310586d281d9425403101875811d9425403107a2e86508425403100a2c86508425403100c2d425d8425403102874815d8425403100d29425c0425403102970815c04254031029701841f265403107c2e2611d265403100a2c4849826540310086f87498265403103c2f2651c265403100c2d2651c26540317bea1424416010a2108c4d361c930d16210185d83dd9309162109c3947d80205162124e503544160cd62104c5b3758305cd62104a5b3884160cd62124e503144160cd6214b85f780d935416210683e4859e42416210583c485d8424162128d29425c042416210685e3859e32416210083f8751846416214bc5717cda36416210085f874d836416210ea54384856510c211ce46314856510c2111956825d4430c42111954825d4430c4211c957865d4430c4211c955865d4430c4211cd47265d4430c4211cd45265d4430c42100957805d4430c4210eac738901260c42163ac538901260c42102a6758901260c42100a6558901260c4210eac738101260c42163ac538101260c421008e778101260c421078e578101260c42102a6758101260c42100a6558101260c4210291c8750d35d142102b148150d35d14215dd17731c543d14215db178350c31d1421549378750c31d142124b148150d30d142105c1c7650d30d142112d17470c530d142111d44720c530d14210283f48dd930d142108c56370c506d142102a73188c106914211cd143111d35514211cc547118d355142102a1c8650d35514210291c8750d
  | 4 => 0x15404206c57610dd61540422892e8750961540420092c87509615404200d0e37509615404200d0c37509615404200d2942dc1615404200a5438584615404200e254258461540420087787584615404228d0d428dd215404228d0d420dd215404228d2942dc1215404205d2847909105404272b294890910540420096b7890910540420093887509105404203d2b27509105404200d2b87509105404200d2887509105404200b288750910540420092887509105404203d2b67509105404203d286750910540427bf228150910540427bf2181509105404272f2371509105404272d2b71509105404200d29428dd105404203878864dd105404200d29424dd105404200b2a4889d105404200d284709d105404200b294809d105404200f2142cc5105404202c7067cc5105404200a7368cc510540421897378cc5105404200f2142d85105404200f2142185105404200b503848510540427bf2142485105404218970874851054042408d587cdb169083103c5575cdb169083103c55754db169083111ac4824c55690831008d7874c55690831008d7874c50690831068d5874c50690831028771895d069083107e4525d8c615083107c5575d8c61508312f8d58718c615083107e452518c615083107c557518c615083100ac4824c76550831008d4874c7655083100ad3804c76050831068d6874c76050831008d4874c76050831028748155f605083100c9531dd9421083100e8531dd9421083100a2d58dd9421083100d8531dd9421083174b85381c5421083107d25751c5421083107b25851c5421083172b2a801d5421083100b29801d5421083100f05424c6651083111a56864c6651083111a54864c6651083111d2471509651083111e2461509651083111954874c5651083100f05424c5651083111a54864c5651083102c57764c56510831118d4874c5651083100e85424c5651083103c2c72509651083111e2721509651083111e2421509651083100c2f87509651083100c2c87509651083100e2781509651083100e2481509651083111e2771509651083104c54378c5651083100e25428c5651083111877788c565108311185c874c5651083100e0d424c5651083102c54714c5651083100c57874c5651083111a56874c5651083100c54874c5651083111a54874c5651083111854874c5651083100e46424c5651083100e15424c5651083100e05424c5651083111a56824c5651083111a54824c5651083100a57804c5651083111c56371c5651083111c54371c5651083100e25421c5651083111a55381c5651083100c2d42dc165108311ec5437441651083100e2542441651083100a553844165108311187478441651083111a6428441651083172e2a505096010831068d6874c56010831008d4874c5601083100e85424c5601083100
  | 5 => 0x1f38843655084200a1d38843655084200a1f3885f655084200a1d3885f655084203a2f2885f655084205a2d2885f655084203a2f2805f655084205a2d2805f655084203a2f2881f655084205a2d2881f655084203a2f2801f655084205a2d2801f655084200a371801f655084200a351801f655084200b0e38547655084200b0c38547655084200aa718183655084200aa518183655084200d2551c5f6550842038af68c5f65508420792d58c5f6550842038ac6841f65508420792e5841f655084200ca86041f65508420092f874c765508420092c874c7655084200b0f38843655084200b0d3884365508420092e8784365508420092d8784365508420092e8704365508420092d87043655084200d271785f655084200b0f3885f655084200b0d3885f65508420392c6841f65508424ed286041f655084200b271801f655084200b251801f655084200a8f38843655084200a8d388436550842008af874436550842008ac87443655084200a8f3885f655084200a8d3885f655084200ca90701f655084200aa71801f655084200aa51801f655084200c2d57d946150842038ad78d94615084200ea060040615084200b25580406150842738ac685c06150842079a4815c0615084200ca8605c0615084200c2d57d976050842728ad78d97605084272a2f6895f60508424eb290895f60508427292f58c5f60508420092d58c5f605084200c2f76dd5429444273a2d86dd5429444273c2d7650b359444200f05424c7359444253a57864c7359444202954784c5359444253a57864c5359444238f043550a319444203ca67150b36944421185f874d7369444202a54814d73694442738ae875090694442008ac8750906944420185d38dd930944420287681dd9309444200c2c76dd5425404272a2f68dd5425404272aab68dc1425404272c2f6750a515404272d2b0750a515404206c57610dd515404200d0e37509515404200d0c37509515404272c2c76509515404200c5437185515404200e25421855154042009a887509105404203ca867509105404200f2142945105404202c7067945105404200b5038545105404200f214254510540421897087545105404203c7067545105404272d2942dc1425404200b2908dd9425404272a2f78dd9425404200c2f78dd9425404200e2908dd9425404200f2210dc5425404272b2808dc5425404200c2c761c5425404200d28701c5425404200f22101c5425404272b2a801c5425404200b29801c5425404272d2a76dc1425404272d2876dc1425404272b2b78dc1425404272d2b78dc1425404272b2b68dc1425404272b2868dc1425404200b2918dc1425404272d2b0750a31540420685e3859e315404200d294241e315404200c2f76509315404200c2c76509315404272d2a70509315404200d294241e6
  | 6 => 0xd143111d30c56420185d38dd930c56424ed294241f42416420685d38d9e314164200c5716cde164164206c5516cde16416420087787458164164201c5a604dc50145422f97187140101454207c7071141601454200a5938141601454202a73181416014542028748159c301454200a7308cc5601454202a73188c1601454224e50314c1601454200a57388416014542459718704351d41424587578d4716d41420685e3859e31d41420687968dc131d414206c56160dd16d414200a543845816d4142008778745816d4142079708141c16d414200a
  | _ => 0
def innerJ4 : Nat → Nat
  | 0 => 0xa4b3154b5885c2490036930b909085406b64abad9159b3966862892d52a80048aa803a558d66a42f05a66464a0cd5ab4197b465d1e02b91393b760b1b62845b13123b00384554305ae0c414913b01d8a20e92fa20015421e5f378c2927bdb1b2d72f64a9b2a3c583c4b24de4f347f9fd0c81a21c80179e92f86520fb40b0f0a456382941b54c1a78620758b55998706503b8c6370791c592aab15a90e45222a95825e707d15b04c59cb9917502064b52c2e56a055917c5b26897e865ca2527612a232a3004f053b51625aad6f000d4eb9f155c47b4029241d72966188013ce8b9b3b63045281f44f3110fdb883689058aca5007b9e12593967948908a808011c65731c1848d4ac994c43f5ce5793480dd5b423aaf01f71716dc63e53402c4263381021db5d42d920e92f2cda7ca486b41d093a41518d25801406663f29550c54e63947a62352877257c2ac4141ee9342352a661400623ebafb79078454a1db389dd589a795d2ad52c16360325210c5472224a1062d8c890d37d96408c6136de1ea4ad4ff25c0d45a58ae29c4538d92c8a045e87a00af26e2a59a817b2b284c227a5519e75a6da15c4ea1406947ac8cc1181f85a830a8221b43ac76a46f2d25e907e4b543aa9862b978a9041a3e932163b4f12547669c88104c666fb9c1f45a35e39dc2fd21caec4116026044cf4a12c64b7b15af82c950e4b42724440986eb23f38929b1452bf04b29f82864827c001b005d38aa553524615ba47013be75681b81c8e871c31958f0548413d24cd06239173c48b939a184566b28c47f42193b3a594c08f044c599b24365493a6000f53a5962ce92c4746494630b634906768c4f81d571e97c15a7884e91664d466e0a454a4890047a4704b658e95bf06e4d213105e2e7b64764156b1785d6f58a49793bfad08c6ba982010444698c37e2db76816a24c2b421593c6b88c06470686fe5f7ad46fc1a09204645d50842fc617610b914dd15247d7d4b013d417a91440394d42ea207260f5ad84d67ed3b68b6144ab0448b9f3057f96320691e458c7760ad169b2628b79b2df9150a9a8418c2ca935619449ac48500517b150400b127b3aaa53bb0e04c52b09e86ac4679d90b143185463c48c4d165416fa219fcaa892e4594084c70221215a197455433c3a665b4a42c5bae49119c6e089e43b160a680f81c68997982644360484719f9b9759520241223d4fc8d113e4049f028f37c6e28f85fb2c75653a01ce6d2626ba04f757038f1b036c005b2f42287852f20689c4b33a258e5e6a410d33af1765fc71772c00004a5be27ea0199c5c95c51ae9b113a38859e3285b8ba1ad12f9a9965978400c6ec0d81c98d0a885092a25265eeb337150406056031820283600ec8e14f90600b3baa1c74fd03056898059a2a7a7d3135f642308e5065df22c002b813aa9455a6
  | 1 => 0x859d71019a45123011e9261286aa4a58752235384bc14c3728bca585ea1476c85c153208a3fd34c51b4132f13fa7a841b42d47714343c2d553f5603149609a04107421154739584af3f4a314e31d29d537a3ae85c6f4ae02e25cc1b84f5119065a1c2aba6c5bbb4d93b6be1d90b530c009b80b616d875c4a267640db3e3f7685b7129d42106a7904820330138be9497e054d0736461f6b444fbb1452365841650d64064160a174b4612081d5830649b89437208886d65187ec96c9ac8b25cb5078384856218e70b23c048631b88a5803d85423e4072abc39c5f136a15e5102ba300a24008aa48a120c43242cba83679a101002751459889d7146ae64da8d0dc5af6089cc6ee8d876e51e01e3e81bab3546aaa19b9add60688c9c441d9385306353ee5056a60124399f846b6c45b546d2b58dca7156c6780e545f5c848782c1461bc5e44b80774edac59514e808f9651a69424573f940f4454bfb0d43316cb081305f4095b9592b2be60c7f11a928511405b6220708cd4d04f484406f662b4c62424057880da088ed5691550d038c5dc08b6cc36238e5745ef3b22140a55e28c15db95d5021700896e93448e44012c246972437f51257dafc3f2406b4829760daa019690411f81e62f6803705f012345c4ee67e70907674408671659bab50d905f00e20a0262d4b3f5cdb68093b308caa2d14db5065a3fca85236173ae862a2704359c0601651246b986448143940615bdb413c7320450728a1455da543180bd2cf4ec14a0560811361a12182d11813ec74e23c5ac2cc1d80a848409d21b698a4c6915de2bb3ed0448c72d05c0186b787c47d64b14d9034b1e99091c0db10a14e0d54f654f0375b029819413d8e08480ac65f808b450d2a0d0634798a01982af4e41f9b4aa0949d08511d7c804e5eb48e13866b79c12266d7fd2a44609e51901da2b32120837808b586805c51c91d77c60916461d38286c6500e8b4740e2a11682c02b12b75f51621e8b0453c0070bc0c953d05240a519ae40182ea1cc5972500d12f004d22e1485580d74d82d61dc3bc8a36880748f95cf5c73094294f21b20c103516e4e09186870311082aa2525508342da4b61c23cc809188208b43516a0c74a18a3b430e77841c3de6e6bac93ea8c45b5492dc4ef97d62c6904276840a18745755f9025ba2612b0c2bd3633a45431320b47038d55673b89f5b322b8799a3d0f1a9c61627814153e7c6b2db8db1956bb9622001993d68645d6724d33764075a74832a07dc39087c33448d06d8728b79f4a003c610d64eb09a5d41e0b817d225a942e04784953f55b3428734111133a3c0918c99284e289237b5c46d44664b072239eb1173648f105b89a7046e8bb0153641fe45e01f2a8488b6952d4436119489293ef78167a2d8840ac850a8701f25ffb743f166105528d1aa3a8b595ad1
  | 2 => 0x800014068017710479240480d0000740000903e0c8056270020000001315004c1280800a0640080815400400804012dffc580200801000010020003d400300007c0080000003c038005369f81a80000c01b4a02a044010070080020100100000a00001800000060038000020680002c5715a02483542218247a567490122a024b841ac8056f836e8fd3740cc49c3104209b5071ae12229372d343436b97010038b5a45649d4b7d01156a44b90c44d71ab2c1427d056d940a2c46244735cb9d5d108710c440aacb402742282866ca64564c0fab6c4da12c2342a37487b5ba395966c4fab5428c5b93f84684926ceb705c62372c3b374763b5a396a81ec58445a0035e19d06639554fe5b7126288a351344a88605084f0b5c9a99541586312fb1779094c44983a74a3afdb7cbab63d2c42917f8af9b60049af44d5a342de7461785d79194ca65691113544188083d0d64965d83dcaa92100ae8194cc40c8b861c6435855550cf0218c53d00752b60580f993629ea404ae21f62e9d129a950b16ab430b3e666516b3f0b0505d9b03861ca5208ec5da93f69ca511f50887d26c06556705d964fa9d0ce4c97f038ab42a292683304aa43d1839270160824cb8c3b9e21d6273668e65919859a57004587d809232474060703c2ec8cb5aa3ad1fc6533f34df931304110a8924254844e5449bc1a33da2809445515e56b028744a718a052dd340437379a6446c3a92e34db0da859ab89003e029902955231a045acd3ba1c039a06c4c2981b3d9d85fa4d75362ae3d64188a6bad5019e080cac04e741f4800e15414acb4979a1a8b345bc1038b0561994b286bc5e046177aa3807f67c0b00232bc3ca1804e14bda9154c96832c21a6343c468265e3b107a27a384b6d15000a2606421f00f44949ecb941fa921499b222cb3f65ecb750ed4e514b7b089f6c68dd3b943886498412e5fda750b77029616a430f30d8c22443500595c379d1cb2e13c824a3ea6e813716d2931795dd6ea0fc1be2567fc14fb2096923826c1ab47e2e813f3580995818618ba50b70c3eb6c238d405a5c02d24e4e65f876c13c3934a059474c3152ee8045f29ed28e83040949728a1fb1245d0a280902828b444236136938594181895c4002e417e2adb180b9b4b5ca2895edb2e5ba47c7703e2b85b9b988adc42a3c2a4407c3871b77381d46e48f45b642b08d9255a29e44c301c9b43013ab3bd4dc6001c450fb5863391052e2267521e24757f57544259a406b8fca816ba6a1b368845663fb4ce5d63ff470b3c7603fe5fe4be5904a7481750b1043e1e67740507bc392157b1c2e67304171d666909488d02f0572909ad09c7ca4c8a747087cc7a9465ac18e52f40a030842412551a63a02e8583801016d054581a378500894b1a7e44a6204172898accb9a59f6297c017f3980c06607b
  | 3 => 0xf20012c0880e0060022b90800078c5b00407601c0ce710240d87e6e70000e8588000060040d0a22bc130d67b0042004860163241a8008450080401ec7a3a3bf5490600da1b2400f0f460840500303e0151cb510002981580503a08408004eca00002060030030fb802000298880023f4036c98f100420ca401202f479dc057362006fdb1e0006a0000162a8010148110760000710001c2d50144a048004020040015e3c683b14804c0b8000014880282a3a603002c220e8037bf84a09e004017090022382815e0000100404c0260a06206a00d4e41104c0bf79c0001701e0480000084a0b0048ad01a0012e11c01a0040000c00008c107440302b4050070220001980004c11f650030020d80a79100c02c1d00924601403bc7c72d80250050660b45281aeae1d01200ec54000078210560945082900e0080900026e000c382a052004080020080032703c00c0340300602aa140058c0085ac0000412c1e80006116d974003840ac00c0000802c2000080200000008057034480009130308e01207710a2740004d0012f0008321a600c008010d69e018007000e441d0010005f40c0360d540c0081002c02c0280c0000140f80f0e00100402d000094000000b8004058110020080482101412c038042fc00408040efa1cc0307c0b1a80000008ba028018060000001201000c0080707903747000000000ee005099002014010150260085b07b0000000080d7780a80fd4901a008001c603610c0400000a01a2f03410a0240000000001c3501e0200200280c04a04115a4e01c02c00041b2c2180000305c1940c01f03e0380780e0020000d80c10200001023020021b90034b40000403803406c0100300ba100d04601c00c02137ed60368880c0500043680d00e0b4070050040540e000005ba001c110121d01f016b2800c8803702400401801000140240270320340c1830000080d8000f00a8010040000000a80200c0001b00400200802000001d482684701c0880002a0100b2740040077406780002c00003009004028078010431040029d004000003d10000a02204602400002001f5a08c0e82a0080300681d02c00c010033340040501a00000000001b00
  | _ => 0
def innerK3 : Nat → Nat
  | 0 => 0x5410e551c5f655084200c838be710becaa108401a206056010185421081f14102302e030a842129e81e19424c7359444200e021ba8430aa2a8084015209750a5144150108470a0ce1c2a2882a021006c00e142545105404200a904ba84a8a20a808407c2067509514415010803056f0846eca12a0213dcc8626101c5425404200c143b30038a84a80840130a3946370509501080244930a12c230aa021006810e14258461540427bc911090ea1220a8084f79212121d4244150109ef2430243a84882a0213954864487509105404200c91b890ea1220a8084f79229121d4244150108032432243a84882a0210044a261424dd105404203c14432849ba20a80840112897520274415010802a412ea1662882a02139648de142cc5105404200a904ba85b0a20a808401520975086144150109ef602841c242882a021004a1e6131dd9421083111d024328498cca21062239048750931594420c4471090ea1262b288418805814e481509651083111c0643a8498aca21062238448790931594420c4470290ea1262b28841888e81a09424c5651083111d024128498aca2106201a079850931594420c40340930a1262b28841880701e1d424c5651083111d0343a8498aca2106201c048750931594420c4474090ea1262b28841888e0121d424c5651083100d02a170098aca2106223c043750871594420c44740a70a10e2b288418804892614244165108311182a4ba70882ca2106201a05424e110594420c446489249c220b2884188062121d424c56010831009504c284882c021062230d0974e110580420c403502849c220b00841888e2121d424c446c943100c603810498a8c9286225284984c446509250c4460a930988eca2a4a1881641521311c94549431118a24c2623928a9286201c05311d942515250c44710904a3a62132a01888d1125d31099255403100d02a42621324aa806205a41804c426495500c402059129328e132a01888c912498610c315402112d082330021862a80420154139901270c55008446289309824e18aa01088c581e5280c53054021a5aa1bcee418a60a8042f5343794a0314c15008447284f294062982a010804d01e5280c5305402111ca03ca5018a60a804223140794a0314c150084474090ca12621888b9000701509315d831117201182a4c262bb06222e4025054984c576114314804a609309888aa106290006814c586115420c52000c183ab0020a8c18a4023054984d57610831c400380a849aaec21063880f690415800c9260c710
  | _ => 0
def innerJ3 : Nat → Nat
  | 0 => 0x580178bc02587aa8f8912dac6c9814088c04b848d8b80cf04c0008100000501004341029782e447c0014340014700408400000f80058693c0cd40879347c80501008240e143c1872c248da7b406805a16116423d8e118102956586983e3e1c072161bda50115508e09cb4090aad0487bcb5c93da4b8520843134805540a3d160947c421992918042e2dc269a21266b6412504b3f570a92e21890dd5501a71b12f881908e2b50460641a8ec647e3528af14840703f06c5207bc030d43d0ee9a095c01191354b10aa08db05c0e56d3c3e65605542601b3c900722958170d1ac4c3a1b1eb596eb3a72ec06220a1259c5060afd100ea62c418c02bad0b2926a30c29cb094a5a2104b000223a2c85c2f0ce5428168f0020e983029060278bd1934
  | _ => 0
def innerK2 : Nat → Nat
  | 0 => 0x47800670e142545105404200c400e0975095144150108029033adc4875091054042008812a5424e110594420c44700497509384416510831008a02a5424e110580420c44708097509384416010831119012a5311d942515250c44700497521310992554031118502a139901270c5500844700498509315d83111720128812a53161845508314804700498509355d8420c710
  | _ => 0
def innerJ2 : Nat → Nat
  | 0 => 0x12b0016b0000618004601c048ec20c4400670890db18b4c04f529428
  | _ => 0
def innerHint : Nat → Nat
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x7
  | 7 => 0x8
  | 8 => 0x9
  | 9 => 0xa
  | 10 => 0x117
  | 11 => 0x197
  | 12 => 0x219
  | 13 => 0x411
  | 14 => 0x414
  | 15 => 0x419
  | 16 => 0x491
  | 17 => 0x493
  | 18 => 0x495
  | 19 => 0x511
  | 20 => 0x519
  | 21 => 0x791
  | 22 => 0x792
  | 23 => 0x797
  | 24 => 0x811
  | 25 => 0x817
  | 26 => 0x819
  | 27 => 0xb11
  | 28 => 0xb12
  | 29 => 0xb17
  | 30 => 0x1294
  | 31 => 0x1298
  | 32 => 0x129a
  | 33 => 0x1317
  | 34 => 0x1319
  | 35 => 0x131a
  | 36 => 0x1392
  | 37 => 0x1397
  | 38 => 0x1398
  | 39 => 0x139a
  | 40 => 0x1418
  | 41 => 0x1611
  | 42 => 0x1691
  | 43 => 0x1711
  | 44 => 0x1991
  | 45 => 0x1997
  | 46 => 0x1a11
  | 47 => 0x1a17
  | 48 => 0x1a19
  | 49 => 0x1d11
  | 50 => 0x1d17
  | 51 => 0x2517
  | 52 => 0x2619
  | 53 => 0x2811
  | 54 => 0x2819
  | 55 => 0x2891
  | 56 => 0x2893
  | 57 => 0x2895
  | 58 => 0x2911
  | 59 => 0x2919
  | 60 => 0x2b91
  | 61 => 0x2b92
  | 62 => 0x2b97
  | 63 => 0x2c11
  | 64 => 0x2c17
  | 65 => 0x2c19
  | 66 => 0x2f11
  | 67 => 0x2f17
  | 68 => 0x3694
  | 69 => 0x3698
  | 70 => 0x3699
  | 71 => 0x369a
  | 72 => 0x3717
  | 73 => 0x3719
  | 74 => 0x371a
  | 75 => 0x3792
  | 76 => 0x3797
  | 77 => 0x3817
  | 78 => 0x3818
  | 79 => 0x3819
  | 80 => 0x3a11
  | 81 => 0x3a14
  | 82 => 0x3a91
  | 83 => 0x3a93
  | 84 => 0x3a95
  | 85 => 0x3b11
  | 86 => 0x3b14
  | 87 => 0x3d91
  | 88 => 0x3d97
  | 89 => 0x3e11
  | 90 => 0x3e17
  | 91 => 0x3e19
  | 92 => 0x4111
  | 93 => 0x4112
  | 94 => 0x4117
  | 95 => 0x404a1
  | 96 => 0x407a1
  | 97 => 0x40821
  | 98 => 0x41621
  | 99 => 0x41629
  | 100 => 0x42821
  | 101 => 0x42829
  | 102 => 0x43aa1
  | 103 => 0x43b21
  | 104 => 0x43da1
  | 105 => 0x43e21
  | 106 => 0x487a1
  | 107 => 0x496a1
  | 108 => 0x4aba1
  | 109 => 0x4ba21
  | 110 => 0x50821
  | 111 => 0x52c21
  | 112 => 0x53a21
  | 113 => 0x7a821
  | 114 => 0x81a21
  | 115 => 0x81a27
  | 116 => 0x81a29
  | 117 => 0x82821
  | 118 => 0x82921
  | 119 => 0x82c21
  | 120 => 0x82c27
  | 121 => 0x82c29
  | 122 => 0x1293a8
  | 123 => 0x129428
  | 124 => 0x1313a7
  | 125 => 0x131427
  | 126 => 0x1319a7
  | 127 => 0x131a27
  | 128 => 0x131a29
  | 129 => 0x132ba7
  | 130 => 0x132c27
  | 131 => 0x132c29
  | 132 => 0x1399a7
  | 133 => 0x199a27
  | 134 => 0x199d27
  | 135 => 0x19ac27
  | 136 => 0x19af27
  | 137 => 0x1a1d27
  | 138 => 0x2b99a7
  | 139 => 0x2b9a27
  | 140 => 0x2bac27
  | 141 => 0x2c1a21
  | 142 => 0x2c1a27
  | 143 => 0x2c1a29
  | 144 => 0x2c2921
  | 145 => 0x369629
  | 146 => 0x36a829
  | 147 => 0x371327
  | 148 => 0x371329
  | 149 => 0x3719a7
  | 150 => 0x371a27
  | 151 => 0x371a29
  | 152 => 0x372ba7
  | 153 => 0x372c27
  | 154 => 0x372c29
  | 155 => 0x3a1621
  | 156 => 0x3a2821
  | 157 => 0x3aba21
  | 158 => 0x3e1a21
  | 159 => 0x3e1d27
  | 160 => 0x3e2821
  | 161 => 0x3e2c21
  | 162 => 0x3e2c27
  | 163 => 0x3e2c29
  | 164 => 0x411a27
  | 165 => 0x40487b1
  | 166 => 0x131399b7
  | 167 => 0x13141a37
  | 168 => 0x199a1d37
  | _ => 0
def innerN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 18
  | 7 => 381
  | 6 => 4155
  | 5 => 3826
  | 4 => 748
  | 3 => 93
  | 2 => 13
  | _ => 0
def innerR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt innerK9 (i*13) 5
  | 8 => packedAt innerK8 (i*24) 16
  | 7 => packedAt innerK7 (i*35) 27
  | 6 => packedAt innerK6 (i*46) 38
  | 5 => packedAt innerK5 (i*57) 49
  | 4 => packedAt innerK4 (i*68) 60
  | 3 => packedAt innerK3 (i*79) 71
  | 2 => packedAt innerK2 (i*90) 82
  | _ => 0
def innerH (k i : Nat) : Nat :=
  match k with
  | 9 => innerHint (packedAt innerK9 (i*13+5) 8)
  | 8 => innerHint (packedAt innerK8 (i*24+16) 8)
  | 7 => innerHint (packedAt innerK7 (i*35+27) 8)
  | 6 => innerHint (packedAt innerK6 (i*46+38) 8)
  | 5 => innerHint (packedAt innerK5 (i*57+49) 8)
  | 4 => innerHint (packedAt innerK4 (i*68+60) 8)
  | 3 => innerHint (packedAt innerK3 (i*79+71) 8)
  | 2 => innerHint (packedAt innerK2 (i*90+82) 8)
  | _ => 0
def innerI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt innerJ9 (((h/1+packedAt innerJ9 (2+(h % 1)*1) 1) % 1)*2) 2
  | 8 => packedAt innerJ8 (((h/16+packedAt innerJ8 (280+(h % 16)*6) 6) % 40)*7) 7
  | 7 => packedAt innerJ7 (((h/372+packedAt innerJ7 (12232+(h % 372)*11) 11) % 1112)*11) 11
  | 6 => packedAt innerJ6 (((h/4539+packedAt innerJ6 (204285+(h % 4539)*14) 14) % 13619)*15) 15
  | 5 => packedAt innerJ5 (((h/4028+packedAt innerJ5 (169092+(h % 4028)*14) 14) % 12078)*14) 14
  | 4 => packedAt innerJ4 (((h/661+packedAt innerJ4 (23664+(h % 661)*11) 11) % 1972)*12) 12
  | 3 => packedAt innerJ3 (((h/73+packedAt innerJ3 (1710+(h % 73)*8) 8) % 190)*9) 9
  | 2 => packedAt innerJ2 (((h/19+packedAt innerJ2 (132+(h % 19)*5) 5) % 22)*6) 6
  | _ => 0
def innerPos : Nat → Bits
  | 0 => 0xfe0fffff03ffffc0f1f1fc7fffc7fff031f1ff
  | 1 => 0x1ff01f8ffc0ffe3f01fe3f8e07f8fc01cece7c
  | 2 => 0x1fffe00ffff07ffffe003ff007ff1ffe0f0f8f
  | 3 => 0xe000000fffff803fffffc00007ffe00ff00ff0
  | 4 => 0xfffffff00000003ffffffffff800000ffff000
  | _ => 0
def innerNeg : Nat → Bits
  | 0 => 0x422142011820040010304412314124a01050b5
  | 1 => 0xc464c51228e5284b00d21c8452c84860c6c65c
  | 2 => 0x88289244143501562002920849213460b0b0a
  | 3 => 0x81cb1648928a1ca6b56480012724818b700de0
  | 4 => 0x110c1800e30c6138c9893249c000020dada000
  | _ => 0
def innerAtlas : Atlas := ⟨9,rawDecor 31 innerPos innerNeg, 0xfeeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0feeae8a0, innerN, innerR, innerH, innerI⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_2_0 : Interval b0Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem allb0_2 : Interval b0Atlas 2 0 66 := cb0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_3_0 : Interval b0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_3_96 : Interval b0Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_3_192 : Interval b0Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem allb0_3 : Interval b0Atlas 3 0 279 := (concat cb0_3_0 (concat cb0_3_96 cb0_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_4_0 : Interval b0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_4_96 : Interval b0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_4_192 : Interval b0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_4_288 : Interval b0Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allb0_4 : Interval b0Atlas 4 0 302 := (concat (concat cb0_4_0 cb0_4_96) (concat cb0_4_192 cb0_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_5_0 : Interval b0Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allb0_5 : Interval b0Atlas 5 0 24 := cb0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb0_6_0 : Interval b0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb0_6 : Interval b0Atlas 6 0 1 := cb0_6_0
theorem allb0 : ∀ k ≤ 6, ∀ i < count b0Atlas k, checkRow b0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb0_2 i (by omega) hi
  · exact allb0_3 i (by omega) hi
  · exact allb0_4 i (by omega) hi
  · exact allb0_5 i (by omega) hi
  · exact allb0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb1_2_0 : Interval b1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allb1_2 : Interval b1Atlas 2 0 4 := cb1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb1_3_0 : Interval b1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allb1_3 : Interval b1Atlas 3 0 6 := cb1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb1_4_0 : Interval b1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb1_4 : Interval b1Atlas 4 0 1 := cb1_4_0
theorem allb1 : ∀ k ≤ 4, ∀ i < count b1Atlas k, checkRow b1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb1_2 i (by omega) hi
  · exact allb1_3 i (by omega) hi
  · exact allb1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb2_2_0 : Interval b2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb2_2 : Interval b2Atlas 2 0 1 := cb2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb2_3_0 : Interval b2Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allb2_3 : Interval b2Atlas 3 0 5 := cb2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb2_4_0 : Interval b2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb2_4 : Interval b2Atlas 4 0 1 := cb2_4_0
theorem allb2 : ∀ k ≤ 4, ∀ i < count b2Atlas k, checkRow b2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb2_2 i (by omega) hi
  · exact allb2_3 i (by omega) hi
  · exact allb2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb3_2_0 : Interval b3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allb3_2 : Interval b3Atlas 2 0 4 := cb3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb3_3_0 : Interval b3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allb3_3 : Interval b3Atlas 3 0 6 := cb3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb3_4_0 : Interval b3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb3_4 : Interval b3Atlas 4 0 1 := cb3_4_0
theorem allb3 : ∀ k ≤ 4, ∀ i < count b3Atlas k, checkRow b3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb3_2 i (by omega) hi
  · exact allb3_3 i (by omega) hi
  · exact allb3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb4_2_0 : Interval b4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb4_2 : Interval b4Atlas 2 0 1 := cb4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb4_3_0 : Interval b4Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allb4_3 : Interval b4Atlas 3 0 5 := cb4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb4_4_0 : Interval b4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb4_4 : Interval b4Atlas 4 0 1 := cb4_4_0
theorem allb4 : ∀ k ≤ 4, ∀ i < count b4Atlas k, checkRow b4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb4_2 i (by omega) hi
  · exact allb4_3 i (by omega) hi
  · exact allb4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb5_2_0 : Interval b5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb5_2 : Interval b5Atlas 2 0 1 := cb5_2_0
theorem allb5 : ∀ k ≤ 2, ∀ i < count b5Atlas k, checkRow b5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb5_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_2_0 : Interval b6Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem allb6_2 : Interval b6Atlas 2 0 66 := cb6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_3_0 : Interval b6Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_3_96 : Interval b6Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_3_192 : Interval b6Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem allb6_3 : Interval b6Atlas 3 0 279 := (concat cb6_3_0 (concat cb6_3_96 cb6_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_4_0 : Interval b6Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_4_96 : Interval b6Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_4_192 : Interval b6Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_4_288 : Interval b6Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allb6_4 : Interval b6Atlas 4 0 302 := (concat (concat cb6_4_0 cb6_4_96) (concat cb6_4_192 cb6_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_5_0 : Interval b6Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allb6_5 : Interval b6Atlas 5 0 24 := cb6_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb6_6_0 : Interval b6Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb6_6 : Interval b6Atlas 6 0 1 := cb6_6_0
theorem allb6 : ∀ k ≤ 6, ∀ i < count b6Atlas k, checkRow b6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb6_2 i (by omega) hi
  · exact allb6_3 i (by omega) hi
  · exact allb6_4 i (by omega) hi
  · exact allb6_5 i (by omega) hi
  · exact allb6_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb7_2_0 : Interval b7Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allb7_2 : Interval b7Atlas 2 0 3 := cb7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb7_3_0 : Interval b7Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allb7_3 : Interval b7Atlas 3 0 6 := cb7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb7_4_0 : Interval b7Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb7_4 : Interval b7Atlas 4 0 1 := cb7_4_0
theorem allb7 : ∀ k ≤ 4, ∀ i < count b7Atlas k, checkRow b7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb7_2 i (by omega) hi
  · exact allb7_3 i (by omega) hi
  · exact allb7_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_2_0 : Interval b8Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem allb8_2 : Interval b8Atlas 2 0 66 := cb8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_3_0 : Interval b8Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_3_96 : Interval b8Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_3_192 : Interval b8Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem allb8_3 : Interval b8Atlas 3 0 279 := (concat cb8_3_0 (concat cb8_3_96 cb8_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_4_0 : Interval b8Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_4_96 : Interval b8Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_4_192 : Interval b8Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_4_288 : Interval b8Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allb8_4 : Interval b8Atlas 4 0 302 := (concat (concat cb8_4_0 cb8_4_96) (concat cb8_4_192 cb8_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_5_0 : Interval b8Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allb8_5 : Interval b8Atlas 5 0 24 := cb8_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb8_6_0 : Interval b8Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb8_6 : Interval b8Atlas 6 0 1 := cb8_6_0
theorem allb8 : ∀ k ≤ 6, ∀ i < count b8Atlas k, checkRow b8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb8_2 i (by omega) hi
  · exact allb8_3 i (by omega) hi
  · exact allb8_4 i (by omega) hi
  · exact allb8_5 i (by omega) hi
  · exact allb8_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb9_2_0 : Interval b9Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allb9_2 : Interval b9Atlas 2 0 3 := cb9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb9_3_0 : Interval b9Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allb9_3 : Interval b9Atlas 3 0 6 := cb9_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cb9_4_0 : Interval b9Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allb9_4 : Interval b9Atlas 4 0 1 := cb9_4_0
theorem allb9 : ∀ k ≤ 4, ∀ i < count b9Atlas k, checkRow b9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allb9_2 i (by omega) hi
  · exact allb9_3 i (by omega) hi
  · exact allb9_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_2_0 : Interval innerAtlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem allinner_2 : Interval innerAtlas 2 0 13 := cinner_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_3_0 : Interval innerAtlas 3 0 93 := block_range (n:=93) (by decide +kernel)
theorem allinner_3 : Interval innerAtlas 3 0 93 := cinner_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_0 : Interval innerAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_96 : Interval innerAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_192 : Interval innerAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_288 : Interval innerAtlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_384 : Interval innerAtlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_480 : Interval innerAtlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_576 : Interval innerAtlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_4_672 : Interval innerAtlas 4 672 76 := block_range (n:=76) (by decide +kernel)
theorem allinner_4 : Interval innerAtlas 4 0 748 := (concat (concat (concat cinner_4_0 cinner_4_96) (concat cinner_4_192 cinner_4_288)) (concat (concat cinner_4_384 cinner_4_480) (concat cinner_4_576 cinner_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_0 : Interval innerAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_96 : Interval innerAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_192 : Interval innerAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_288 : Interval innerAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_384 : Interval innerAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_480 : Interval innerAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_576 : Interval innerAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_672 : Interval innerAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_768 : Interval innerAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_864 : Interval innerAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_960 : Interval innerAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1056 : Interval innerAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1152 : Interval innerAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1248 : Interval innerAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1344 : Interval innerAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1440 : Interval innerAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1536 : Interval innerAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1632 : Interval innerAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1728 : Interval innerAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1824 : Interval innerAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_1920 : Interval innerAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2016 : Interval innerAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2112 : Interval innerAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2208 : Interval innerAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2304 : Interval innerAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2400 : Interval innerAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2496 : Interval innerAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2592 : Interval innerAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2688 : Interval innerAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2784 : Interval innerAtlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2880 : Interval innerAtlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_2976 : Interval innerAtlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3072 : Interval innerAtlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3168 : Interval innerAtlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3264 : Interval innerAtlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3360 : Interval innerAtlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3456 : Interval innerAtlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3552 : Interval innerAtlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3648 : Interval innerAtlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_5_3744 : Interval innerAtlas 5 3744 82 := block_range (n:=82) (by decide +kernel)
theorem allinner_5 : Interval innerAtlas 5 0 3826 := (concat (concat (concat (concat (concat cinner_5_0 cinner_5_96) (concat cinner_5_192 (concat cinner_5_288 cinner_5_384))) (concat (concat cinner_5_480 cinner_5_576) (concat cinner_5_672 (concat cinner_5_768 cinner_5_864)))) (concat (concat (concat cinner_5_960 cinner_5_1056) (concat cinner_5_1152 (concat cinner_5_1248 cinner_5_1344))) (concat (concat cinner_5_1440 cinner_5_1536) (concat cinner_5_1632 (concat cinner_5_1728 cinner_5_1824))))) (concat (concat (concat (concat cinner_5_1920 cinner_5_2016) (concat cinner_5_2112 (concat cinner_5_2208 cinner_5_2304))) (concat (concat cinner_5_2400 cinner_5_2496) (concat cinner_5_2592 (concat cinner_5_2688 cinner_5_2784)))) (concat (concat (concat cinner_5_2880 cinner_5_2976) (concat cinner_5_3072 (concat cinner_5_3168 cinner_5_3264))) (concat (concat cinner_5_3360 cinner_5_3456) (concat cinner_5_3552 (concat cinner_5_3648 cinner_5_3744))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_0 : Interval innerAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_96 : Interval innerAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_192 : Interval innerAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_288 : Interval innerAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_384 : Interval innerAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_480 : Interval innerAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_576 : Interval innerAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_672 : Interval innerAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_768 : Interval innerAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_864 : Interval innerAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_960 : Interval innerAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1056 : Interval innerAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1152 : Interval innerAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1248 : Interval innerAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1344 : Interval innerAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1440 : Interval innerAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1536 : Interval innerAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1632 : Interval innerAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1728 : Interval innerAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1824 : Interval innerAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_1920 : Interval innerAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2016 : Interval innerAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2112 : Interval innerAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2208 : Interval innerAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2304 : Interval innerAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2400 : Interval innerAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2496 : Interval innerAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2592 : Interval innerAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2688 : Interval innerAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2784 : Interval innerAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2880 : Interval innerAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_2976 : Interval innerAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3072 : Interval innerAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3168 : Interval innerAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3264 : Interval innerAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3360 : Interval innerAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3456 : Interval innerAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3552 : Interval innerAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3648 : Interval innerAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3744 : Interval innerAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3840 : Interval innerAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_3936 : Interval innerAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_4032 : Interval innerAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_6_4128 : Interval innerAtlas 6 4128 27 := block_range (n:=27) (by decide +kernel)
theorem allinner_6 : Interval innerAtlas 6 0 4155 := (concat (concat (concat (concat (concat cinner_6_0 cinner_6_96) (concat cinner_6_192 (concat cinner_6_288 cinner_6_384))) (concat (concat cinner_6_480 (concat cinner_6_576 cinner_6_672)) (concat cinner_6_768 (concat cinner_6_864 cinner_6_960)))) (concat (concat (concat cinner_6_1056 cinner_6_1152) (concat cinner_6_1248 (concat cinner_6_1344 cinner_6_1440))) (concat (concat cinner_6_1536 (concat cinner_6_1632 cinner_6_1728)) (concat cinner_6_1824 (concat cinner_6_1920 cinner_6_2016))))) (concat (concat (concat (concat cinner_6_2112 cinner_6_2208) (concat cinner_6_2304 (concat cinner_6_2400 cinner_6_2496))) (concat (concat cinner_6_2592 (concat cinner_6_2688 cinner_6_2784)) (concat cinner_6_2880 (concat cinner_6_2976 cinner_6_3072)))) (concat (concat (concat cinner_6_3168 cinner_6_3264) (concat cinner_6_3360 (concat cinner_6_3456 cinner_6_3552))) (concat (concat cinner_6_3648 (concat cinner_6_3744 cinner_6_3840)) (concat cinner_6_3936 (concat cinner_6_4032 cinner_6_4128))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_7_0 : Interval innerAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_7_96 : Interval innerAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_7_192 : Interval innerAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_7_288 : Interval innerAtlas 7 288 93 := block_range (n:=93) (by decide +kernel)
theorem allinner_7 : Interval innerAtlas 7 0 381 := (concat (concat cinner_7_0 cinner_7_96) (concat cinner_7_192 cinner_7_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_8_0 : Interval innerAtlas 8 0 18 := block_range (n:=18) (by decide +kernel)
theorem allinner_8 : Interval innerAtlas 8 0 18 := cinner_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem cinner_9_0 : Interval innerAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allinner_9 : Interval innerAtlas 9 0 1 := cinner_9_0
theorem allinner : ∀ k ≤ 9, ∀ i < count innerAtlas k, checkRow innerAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allinner_2 i (by omega) hi
  · exact allinner_3 i (by omega) hi
  · exact allinner_4 i (by omega) hi
  · exact allinner_5 i (by omega) hi
  · exact allinner_6 i (by omega) hi
  · exact allinner_7 i (by omega) hi
  · exact allinner_8 i (by omega) hi
  · exact allinner_9 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem lowerb0 (cert : Complete b0Atlas) : Lower true (roots b0Atlas) (target b0Atlas) 7 := by
  have ready : Ready b0Atlas (asRow b0Pos) (asRow b0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb1 (cert : Complete b1Atlas) : Lower true (roots b1Atlas) (target b1Atlas) 5 := by
  have ready : Ready b1Atlas (asRow b1Pos) (asRow b1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb2 (cert : Complete b2Atlas) : Lower true (roots b2Atlas) (target b2Atlas) 5 := by
  have ready : Ready b2Atlas (asRow b2Pos) (asRow b2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb3 (cert : Complete b3Atlas) : Lower true (roots b3Atlas) (target b3Atlas) 5 := by
  have ready : Ready b3Atlas (asRow b3Pos) (asRow b3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb4 (cert : Complete b4Atlas) : Lower true (roots b4Atlas) (target b4Atlas) 5 := by
  have ready : Ready b4Atlas (asRow b4Pos) (asRow b4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb5 (cert : Complete b5Atlas) : Lower true (roots b5Atlas) (target b5Atlas) 3 := by
  have ready : Ready b5Atlas (asRow b5Pos) (asRow b5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb6 (cert : Complete b6Atlas) : Lower true (roots b6Atlas) (target b6Atlas) 7 := by
  have ready : Ready b6Atlas (asRow b6Pos) (asRow b6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb7 (cert : Complete b7Atlas) : Lower true (roots b7Atlas) (target b7Atlas) 5 := by
  have ready : Ready b7Atlas (asRow b7Pos) (asRow b7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb8 (cert : Complete b8Atlas) : Lower true (roots b8Atlas) (target b8Atlas) 7 := by
  have ready : Ready b8Atlas (asRow b8Pos) (asRow b8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerb9 (cert : Complete b9Atlas) : Lower true (roots b9Atlas) (target b9Atlas) 5 := by
  have ready : Ready b9Atlas (asRow b9Pos) (asRow b9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem lowerInner (cert : Complete innerAtlas) (ss : ∀ v : Fin 10, Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) v.val) (SBf v.val)) : Lower true (roots innerAtlas) (target innerAtlas) 10 := by
  have ready : Ready innerAtlas (asRow innerPos) (asRow innerNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip innerAtlas k i % 16)-1) 9,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0feeaeee0feeae8a0
theorem fullBound (certb0 : Complete b0Atlas) (certb1 : Complete b1Atlas) (certb2 : Complete b2Atlas) (certb3 : Complete b3Atlas) (certb4 : Complete b4Atlas) (certb5 : Complete b5Atlas) (certb6 : Complete b6Atlas) (certb7 : Complete b7Atlas) (certb8 : Complete b8Atlas) (certb9 : Complete b9Atlas) (certinner : Complete innerAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 0) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb0 certb0)
  have s1 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 1) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb1 certb1)
  have s2 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 2) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb2 certb2)
  have s3 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 3) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb3 certb3)
  have s4 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 4) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb4 certb4)
  have s5 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 5) (SBf 5) :=
    slice_correct (ms:=fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb5 certb5)
  have s6 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 6) (SBf 6) :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb6 certb6)
  have s7 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 7) (SBf 7) :=
    slice_correct (ms:=fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb7 certb7)
  have s8 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 8) (SBf 8) :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb8 certb8)
  have s9 : Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) 9) (SBf 9) :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerb9 certb9)
  have allCuts : ∀ v : Fin 10, Slice true (roots innerAtlas) (target innerAtlas) (sliceDomain (roots innerAtlas) v.val) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9
  have low := lowerInner certinner allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,6,38)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,6,38)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_43706.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[0,1]⟩,⟨.and,[6,7]⟩,⟨.and,[2,3]⟩,⟨.or,[0,9]⟩,⟨.or,[8,10]⟩,⟨.and,[4,11]⟩,⟨.or,[1,2]⟩,⟨.and,[10,13]⟩,⟨.or,[5,14]⟩,⟨.and,[8,15]⟩,⟨.or,[12,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 17⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 12 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_43706

open PEqualNP.Outside.L_meta_43706 in
theorem PEqualNP.Outside.L_meta_43706 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allb0 allb1 allb2 allb3 allb4 allb5 allb6 allb7 allb8 allb9 allinner)
