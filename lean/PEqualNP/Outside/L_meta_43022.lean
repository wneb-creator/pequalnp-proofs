import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_40411, which copies L_meta_10856 (same repository, Apache-2.0),
-- which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_43022.Model
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


end PEqualNP.Outside.L_meta_43022.Model

namespace PEqualNP.Outside.L_meta_43022
open PEqualNP.Outside.L_meta_43022.Model
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

def SBf (j : Nat) : Nat := [6, 8, 7, 7, 7, 7].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

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
  let row := code / 2
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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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

end PEqualNP.Outside.L_meta_43022

namespace PEqualNP.Outside.L_meta_43022
open PEqualNP.Outside.L_meta_43022.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s0K4 : Nat → Nat
  | 0 => 0x800003020097000010f441bc41ef32be41dc32cc32de32f741b441ec32
  | _ => 0

def s0K3 : Nat → Nat
  | 0 => 0x800000400000200018c32907086420e58c841a792c65a432107286420e30c841e21968337159074e6420f10c841
  | _ => 0

def s0K2 : Nat → Nat
  | 0 => 0x287268c841
  | _ => 0

def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
  | _ => 0

def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0

def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/21+packedAt s0K4 (160+(h % 21)*4) 4) % 10)
  | 3 => 2*((h/23+packedAt s0K3 (297+(h % 23)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt s0K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0

def s0Pos : Nat → Bits
  | 1 => 0xfeff7ffffef777feffbffbbffaf83fffc3ffff
  | 2 => 0x2ffdbfff3ffaef5fedee7ff7bf7fffc03c7ff8
  | 3 => 0xfdc7c7cefb6fdffffb7bbfdf7dbfc03fff8e3f
  | 4 => 0xf7b7fa6bfdcdbffffb7bfcf8ddcfc03ffff03f
  | 5 => 0x7f7bfffdaffefa758cf5ff6feff7ffc03fffc0
  | _ => 0

def s0Neg : Nat → Bits
  | 1 => 0x845a21b804049d7d097810934103cacac1b6db
  | 2 => 0x520010205c658260e6349b7f9c6cd5d5dc5b78
  | 3 => 0x20f18c0aa41963854592986470f167676e8e2d
  | 4 => 0x618444550344641898a2aa2a83aab9b9b77036
  | 5 => 0xb8145c83ab68318c2a4b660836433e3e3bed80
  | _ => 0

def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000fcc0c0c0cc000000, s0N, s0R, (fun _ _ => 0), s0I⟩


def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s1K6 : Nat → Nat
  | 0 => 0x8000000000000006920000000009804400260020000004090269e608000096635e0172005404000000000000130000008a700d000000400044000000fc20fe40ff41fd20fd30fe41fc10ff42fe30ff40ff20ff43fc32ff10fc30fe43fc40fe42fd32fc21fc41fc42fe20ff32fd43fd40fe32ff21fc43ff31fe31fd31fe10ff30fe21fd41fd10fd42fd21fc31
  | _ => 0

def s1K5 : Nat → Nat
  | 0 => 0x417f251037a86a05fcd642dfa0c837e45082fe8a18f74c832be92863f431042f8a4a07bd0a20be9ae417f524c6f86a905f14542fb08221ef324cade4b18fdc5410ba8ac65dd35d0afa8a987b48720de22a217f3510ada4b20fb14943bfa2865df318c7e86310df09410bf8ac65f741cc6f8a0a0df11720bf9a8877d0590fdc4290ded4143fc106215d35d07ea8220df49621be22c217c354437a87215f09510bf92e877d35d02fa2b21dfc1741be9ac41fb20482fc8b10df0d720ef1aa217f5050efe2b905f8d510be12c217d35d06faa421ef91530bfa92815c35487f60a206f909429fa2e63f7514837e8721df45642fd906217d35886f0a0a1cfd1732be22a63ed250437c85205fc1642f692c637e25442fe6a195f89610bfa2c41bc419037884205f4d421dea18857d05907de6590dfc9432bfa28217d158c2eea2a1df51420bfa2c637f535027c8a90dfc5642bf9a881f741906fa6ba17dcc521be92e87dd438c6fa0ba15b14940bfa2c617e5110fb86a885f51640bf8ac61ef42082fa4ba07790f30bb8ac657c25c42f86b90df4d641bfa2a41ec42082fe6b20fbd4943ef218637f25906ee2b215fd4540fd98261be41507b86a905fc5430bfa2a217e35487de42907750e32be1ae21f910042fca020df91630bf92821dd310c6fa2ba1db09510bfa2a637f15d0afa4a20dfcd740f612a217f05102fa8a995f41721bf92e217f454c3bc6518dfcd521fa108217c45c42fe6a20fb88120be8ae41f7318c6fa8b985fcd431bf22c21f521c43de8590ef91520be92c877f25082fa8b1077cd440ef21a617f05842fa8b20d7cd440bea8083f850486fa8b187b48421bea2e63fb40cc37e81205fd41419f22a617f35d07ee2a105fcd520ef18261de324cbf280204f11521de214837f5250fee43085f54031f7a10657d35486f88b18df8d620fa8ac657d45c82be6ba17dc8621fb908217f35882fa8a18df41632bf82c43dd351037a8720f70ca31fb8a843be43903e8a29077cd742f792c83ed21482f8a2907d14530b792c837f524c37a8b98dfcd410be1ac21dc430c2fc8b90df51430ef21c657f050c2fea098f78d521bf22e637d15902fe2b2077d0e43fda00617c45882fa0ba1ef10c40be28265be45486fe0b205fd1621bf92c217d458c6fa8b21dbd4940be1ac41f441842fa2a107bc8621bfa8a85fb308c2fa8a087bc9420bea88857e50087be87185fcd643be22e43f441886fe2b107d4c431bf8ae61bc42106fa4b887bc9442bf1a8417d15882fe2b20df11432f710c41be4350feea2985f91632be22c43f4410c6fe4b205f8d710bea2c21de430cbde4a087bd0942f6210657451483ea2a107ec8010be29a83de314c6fea2905fd1710ef9a8617f058c67e8a187b0c921bf928617f05906fa6a107dd0410de20881f421842e8a2a05f54043
  | 1 => 0xc5050fee83085f14930bf1ae437f2590efe8b905b14943df21483bf45102fa6a216f50f40be9ac637f05ccafea6a15bc9410fa8ac856e25442fc8b105f8d621be1a84377514c3d842104f51732be228217c454c2fa8a10fdd0431dfa18857f1590ff0a0a1d78d521be92c217f35c82fe4a215f91720ae1aa41ef20882fa0ba0fed0140ef194617e500caf88a885fd1532dfa1e817d35902fc8a185fc5440bea2c43f5210877c86207dd4543ef21c637d250c3f260185fcd710bf8ae817d35842f88b185fc1743fb8ac85f431843de6490df8d520af1aa41ef42ccbee6208774d741af1aa217d25cc37e8a21df94042bf29087f710843da40105f41631bea2c65ef52503da4b20efd1442fb10e21df3510efa8b90dfcd421bea8085be42106f0a090fd145439ea28616f524c3e88290dfc5621be28a81f751502fa6b186f90140be92c837d25cc7b865185f45740bf9ae437e35087de4a10dfc9731fd82841df350cbf240107dcc531be92a217f058c37a8a185d14530bea2c857d35442bea6a0778c430f629261fb50487ee6310fd10731bf82e85be41102fe8a21df11532bfa2e43bc454c3e882087dd0521bfa2881ef328cbbc6418d74d742ba28a877f45cc6fc8b18fe10030ef1aa416f5250fe8a2a07dd0541be92e83dd434c2fa4a205fd1732bfa82857c5350bd864107b88420ae1aa217e5010f7e8720df14131be1a8417c52506f86b10df49620bf22e217e25c42ee2a10778c630dea1085fb05042fe8a20fb4c832bf9ac817d15102fa6b195f91732fa90a217f25d07f040085fd1632f610c417d25043da84215fcd430bf22a43bf450c2f88a10df4d6429f22a417f514c2fe4b985fc9510af9ae83751590afe4a20f7cd431fa18a43bd41106f88b98df41732bf28865ec42487f081984f91510b692c637f35442fc6a085fc14109e22a41bf4390bbe86a1df11730fa88021bf45107f620885fc9632bf8a8437f35d0bbe6ba0f750f30ba8a8417e35842fe8a107b89510be92c617d158cb7887206f11520df22a217f45842fe0b105f14532dfa18837f258c6fe8a90fb14940bf228657d35042fe6b087b0cb21be82c85f7150c6fa6a20dfc5631f792c637f4510afa0b98df8d720ee1aa43dd300c2788a985f51521bf22a617d15cc3f681205fc1731bf92c85ec42ccafe0b21dfc9740bf128217c45486faa221df45742fb10a217f52506fa8a905dd4540be29a817f15ccbba86197710e30bea2e657f258c2fe8b9877d0c30bea88656d25042fe2a18dfd4d41bf8a8217d35482fa4b206f90840ef99465dd430c77e85215f45732bea2e217e5110af8a4a1df11430fb98c217d35c86fe2a105fd4132f2908437d35c43de85217dc5441be28a616c524c3788a90df91531be82c43de320c2fe0a107bcca20bea80657c524c77c83206f50040f799
  | 2 => 0x3b1b9000000597d00257000000000000130000000000217c005065a00000000fd62465000000000000400194000000000000000ab0028b000002cc00002550bc000001800000844b6002a400000001d5000000000000c0054d5b00400664000000000000634005494900000000007a4000023700000000000018d0000020400a49ec000000000029800000007a000000007849a002930000013c007d5ca1d40081400000001c0005e8460017f0000036c5b0000000224001860000081400000000001500000000a800083000006e0000000000000000000000000000000da29c00000000026c0000004800000000040016d59002346dc0044802005b3000000000000000000000016b001bc000006140000000000000000020000000000000000000000000000000000000000000000261000001243e000007d4004c40000002001d4000000049a176720c41184c006240000283000b00000000400001ad00000000ea00000001fc1fc06000008d400281a40000000000000001a4000000094d4e00000000e2000000025ea34000000000000005c7000c1000000c0006e800000dc000004be0a0017f000009b8000000000000000003ac00074000023e0000000000000009e8fa00000002a6000000080097c003c4ae88185000005dce10000000095000000000000001a3e4ba14010000000000a84000000000000001a961034000000000000001000000040000000000000000c000000000000000840000026900000000000000000000000015c000000000016d00105000002e40000000001db610120011fa1400000000b00067800000000000000000000000000000000000007a80014400000000013d00241001605558494c000000000000000000013a6280000000002230000000000000000000042c003b4000000000082001f64980000000001164d800000e8000000027d9740000000724007600000000000b1000bf34800000005f40001000000000000064c2d00143000008000000000000000000000000001a7001970069d384000010e9580000000790003080020800002a87a3bea6a077cc230bf8ae87bd431077a8b995f14543bf28063dc53502fc8a18fec8220dea1887dc318c33a8621dfc1721bf22a657f450c3ba8621efd1731fb8ac657f058cbf60a187bd0921be28285bf43502fea090fed4143be1a8217d45442fa8a98fb0ca20fb90a437f35887f621085f91730be228637f250c6fe2a20df14121bf22a41dc320c7b864187bc8720bf9a8417d50086fa2b087b10b21be22c65f741886f86a90fbc9432be92c63ef524c2fea2a1df91421bfa28437d351027a8b98df91410ae9a881dc310c2b8a6a05f454309e22a217f25086fea2995f91510dfa2e657c45083d885105f11732bda8243bc42902eea2905f11520bea28657
  | 3 => 0xc70006611c0000000001eda240008435666a8a38000000088d380000031e684e4000162484800000000200081000649b40000001000000000000000400000001240000000000000000000000000004d0007b8000040000000000000040052985000000000000002008e6568a900000815c0000000006f00054000b10019300cd20000000000000000008347901000000011800000000000000052000899c40000000000000d1000006b0000003b0000000000000c200000000000000000000268000028b00000000005d000000310005f0000000195000a80016b001b700137000006b232069f40000083c0000141001f70000000000000007e400000000019a00000000066180028400000520000000000000006bd4c0000000c00000002dc0000000000000000036c010000000000000000000600197000000013e0000000000000007c000000005edc64fc000025710c020000000000328000000000297a7400a8e09000005a4613c40000000000006780100004830008f13a030014b8000000000000000003580200000000003300000286000d6774000019d921510018489c000000000000230dc0087a85c0000000001e4a50000005b0015a0021600000000000000000400000000004c004000010a0322b000000000000000001fd0000046926002a70012d4cdab6a00000000000000055400000001b80000000000001f20000006400000001b00100000000610019700000000000000316c03000f80001a0000000000530000000037da0590cd94c009e8000000000003382988c8007f0000000000000000020040265c000000000c022cc00064d055c00000450000082800664000000000000460004c8000000079c04000000013d000040000000222000000019a002360026c000de29c000080084400000000000033c0000000000004c00000000002a23a4000000067800000000e800820008580000000000003f800000f8000000022e00000050000054465c0000027000000080000000000009e80f000d5000000900000000000008e40000a701e5bd54800000007a8eb961c300125000000017f00000000dd000000e4007c000618007fc000040037400001b3000000000200000004000000108c0000000898000000000187000000027f000000000001400000000016c00000000000c0000000000000790148600534c000000000000000f000000000000000900000004007ca47000000000000000748000000000000000410023400000000000000000000000a197000000000000a71800000008c80000
  | _ => 0

def s1K4 : Nat → Nat
  | 0 => 0x9150826c6251432d9d0915083376151430cd50f1590b1f43cd7408f51b354865d36d1720dc0c4504876621c97109b49a250434e3509510b61814310f6521d1421c74c1450c2786051532978d9254423e4654021c7517350c26f6251530d909610443543510521c7116304c32f4314940d9d4851502d86050c31d30d44248675168d7209ed81454c27516916309718d450c3645214540abc9a411025d3611610d9096214434c3589510d9487350871e43d17308f119354427b6051531978d95008677614d520d9cc9158cb5636456428fd5a454832c45881209e181354875453d45409b18935842e82644010c79163544336464542097d5a35442746151732c7115434c2b746cc610b5cdb414869d46cd432a74db45106776550441d949715043642548510974d845886d736d04108fd1b350c63e46540318f119258c23c4645630cdd0c515032c45c8520b545a320c71c6351430d68d4504871c458d521d9c8715c837351d41439bc98450429d46cd4319e41b454867716d1520d5d8535d074e3649410978d9159025d36d1532d5d8535102d86050c32978d9250434c35095108fd1a258433a45d412197d5a354826f6251430c750f3590a3f460d621d38d625442776154043974db454c65f36c9510cd11751482af46cca209b189351023c464d521d958425442f061480209bc9b15d03e321c80108fd1b254425c3654041cb119258c758604d440f10d9210863c4649631d9105250427b6049510a751b328ca6f624d7418f51b354423e464d520b3cdb424865d3611620ce117304c32e45109219b189454c67b65500409bd5b32486e46048421b9c9b414866f26c5730cb119259065f36d1521b5c5a320c32c625173297d8d454426f654c832d3d8935102b86050c439ec1b454863f56115108f919158c25f3689610d9d05250431e450d5219dd85500ca3f5611520b3c9a310c23c46494108fd5b4350277168d4209b189454c3643245420ad45a421066d26d15308f119150827b6051521978d9259025f36d15109d18535d0b9b6050c43ae18143d031c3151430cd114514c25d36d142197d8d454c25c36540429bd58254429f6550c43c750f359071c4391630c7905351027b6051532d9cc5258c67756d0521d3d8935d0a746151430c71053510357614d7428f51b35c826d268d410d3d4c525036b4214121978d91590b2d26915218f919354871c450d5109dc5b25cc23e4649410d9d091590b543584110da1085048677614d4409b49a458c7686049410d50d7514823f46114309d45a450827716917309dd85454c2cf268c630974d8450433645d4520add8543106d86050e3297d95320ca5f36d1432970d9250426f56d09219dc5a458c26f62540439e41b354875543c5632c70c9450c25d3689710ae1814310be36048421ce90c5050ecc6250c31
  | 1 => 0x76b60494108f51b254436451c85209b498458c7674149641b64d840cc3645214530b54db41cc69d46cc6319b189458423d5690c40b9d9521086d863500409b49a5110e7b0691631c714d43503704114121f8084200431f6351430c750f458cb1c4590d30cb14a40502f11608310da0c850486746548510974d845c865f36d14319d458458cb376151731c750e5110eb8464c030ce91450487a64648421ae181431063f65500409dd8535883676548421cd914514c31f6550c43a751b3510e6d26c5740cb18945cc6ac4648020dc1475050e776151532d9481150836720454208fd5a454871c424d440cd185450c23f5691530970d9500871e464d4408f51a35c825f560d520b6181434c278605143097cdb450871e450d510b949b15107345190140cbd8945cca6f26917309bd95200831e424d4408f919500ca7461540429d458450826c624d420e51854310f6452145439bc9b354432f6251731d30d7214829d36d1442d6d0c5050eb86050e41b5c5a328c25f63515208f119158cbc4320c521ced81450c25f36d1520a74db419072c4649410974d845082d4614c030e6d0f400c36752d4543b9185200832e45d4930f8181210871e31514309b18935d077051141439bc9a350426f26916308fd18358823d46cd431974db454865f3611430974db454431c434d4408f51b350867461516209b899501071d6311530b5185430ca5f5690d30cd50c515025c3649641b3d89430cae516c94429e18145487652154021b54db410c78f6250c439b189354426f56c8520e650f40cc2d86050f30d3d8935d067461515209dd5b314874c3649641d9441250425f361161097d58354863d460d621974da45c427b65440109d185450434c36494109bd954210a751691432bc181210863e4649631b34db420cae526c54319dc5b25d036b32141219d185354825e3654041b30d920083642149410cb914254426f2691410b8181210863f468d720d914b5150e9c63500409d45a5210f4c5314940978d95010b344548510b9c5b424866d26c5730b5185438ca5f568d521970d915902b44644010bc18121c423d460d4108f51b354827461540329d45a458ca3f65504418f51a450c2af46cc9218fd1b350873461517318fd58454c35835141219718d45482b46150c42d58d7314863e4649510d9d4b514c2b71690a408fd954310f1c53d0d40dad4b5050e9c464c030ad1854390a5d36d15208fd1835042e86048520cd917514c2e86048720d390c524c2b746cc621ae181435034d268d5218fd1a25c425e36454209dc5a450827461494109b189450c27b06cd521dc14720482ac6250c41d9085150825f654c431d91462048274614d4409ed81354865f36d1710d50d621442e716cc921d914b514c34d43c9631c791635486776151520abd894310a5c3645420d50d
  | 2 => 0x36897109bc98350426f26d15309d45a350807d56c1410ad185401036b5214143b34db42cca77160d420d58d4514832d43c96418f119254423c464d520cb116254436731494109dc5a450ca5f36116209dc5a450865d3689610c78c9450c35635d45209dd854544365210d421cd117314863f46cd720d9484450865f361142097cdb45c82771691720d314a304c23e4645420d50d5214425e3649641cb11732487706045420b50d9100427516c9740e690c40cc27461514319bc9a450c66d2691630d30d5214831e458d520cd919158caf06048510ba181210867761515319b49a45c431d4394843e350c420cb986050c439dd8545cca77654842197d8d454871c458d5109b899500c7c63648421cd1161044367521454397195434c34f53d4940e550c410c6cc624c0308f51835c87e121c83109b099501076825c4110c750d5010f2c45095109dc5b354827516d1530ce117504875453145408fd1a35c423d46cd7109dd85450c3344588510b9099100434c3649631cd117514c2771611632b3cdb42c866f2694443d590c514c35543145309755b430c26f268d4218f11950087344645632d5185351032e45149309d55b210425c36456428f51a258426f62515329dc5a35c826c26540319dd8535d0a5f36116219bc9a458c76a2114121add1b314876442454209d45a45cc27716d15309dd852544275160d420cb189450c2b746cc4108fd1b354423f46cd5209b49a450437341141218fd954210a6c6251510d318935d074c35d09219ed95200823f460d721d68d7504876521097109bd8935482d76150c318f51a35c431d43d16319d45b354834d4314930c7914354826f5689510adc5a421027906916329dc5a5210e5d36c951097cd845c869c6050c439b498450433445145209d45b25cc35835d41219dd85354432e4649410cdd8545ccacf36d08208fd1b350ca7b06916329bd89458433743c5642974da45c827860494109b49a45cc2e526c5421c750c450c65f36917109e181454c756350c5219dd855010a6f624d510cd91441486d736d0610d30d6204825f36917208fd1b354863d46897108f518358426f260941097d954310f2c45d4930d90c525043976150c43c714e40502d736d06219e41a458c72d4314940cb919258c734450c521b6181438c74e43c9631d9185250432f62514309d185454c35435d05219bd8935842e516c9432c7114354874c624d440dccc4504877351141439b49b454427716094109d45a45c831c4351430d590f158ca746151532d5146304c31c450d5209d185358827761516208f919354436732454209dd95100426f6251520d614f405025c63515109b18945083575314540cb114524c36852d4143cd11915083984310030c7d01351031d43114329bc9b454426d268d710d38d925907364514520ab189439
  | 3 => 0x15938000000007740000000001650000100000000000000000000001b900000008003093b4bc00001c8000000002d001940000053800000880000093800ab000000005680000000000000000000000000000000062c000000098800000008cc0007c00000000000000000000000020d000000003f6b800a88b30cc000000000000000000022d00000002c0000007485788d1b2ec00304006ce0e08ea40027a00000000006f8000008b001ab000000005b0016c9e40000000140000000000000000004bc00001cb0004a31c7200000000000002d0000043400146820000000060b6cee0000000400000000000000001000000023d00000a00000000000299000000015a00191004020b80076c00b14004240000400000b1632a100000000000023a001029f400001380000000000794007c800268008bc00000002529d0028b91400000008d400000006ec00000006d00081c0000000470a700000000009600003c0039c009900079c000004c0026500014001be000000000000159000000001400000000000000400000a3ea70000000250000008f8000004f00000000002fc000003000000000440010b1a80000000ac40000400000000000000280000001dc010016429000000000000000254001940000000000000a891c000020a45c00000000000000000001f6aa40035581a31990ec00000030000000045000c91dc003a00000000000c67ac00a6800099c34f0007d40025e602780100000001c3000d8000009e28600000000009f800a245400291000e70000000000001a30000000000000002b00000000000000000000000458000000000000a30006f00000000001bd00000001dc00000000acd9086258435636454208f119500caaf46ccb2197d58354435753d4540cb115214823f460d420ab189401026d5688420b9c9b314867461540439b498350434c53d49409dc5a458cacc6250e31d9d85250426f624d440ae1814390b6626454209bc9a45c423e4649630970d9254423c46540319bc9a4508674614d41097d95300c23f5691510d518535d0a7516d15209b18945cc677654c431f888420c4373211412197cd8450433860514309ed95300c26f2611631d9d4b515036452d4540cbd0f259074e350c921cb91625442986050c438f919158cacf36d0a20d50d91590a6c62540439bd89454c7543514520abc9a41903346151732c7116354825c36496409bd8945443a44210521cd45a454863d46cd4329dc5a35087384514121c750c45cc32c450c921e9119210863f56115218f518350823d460d6209dd5a21443645148520c7501351026f6251731d545a354878c6250c438fd18358425d36d1710d9d48514c26d26cd5109bc9a35c426f65484219b49a450c6af46cc8209dc58450836852141438fd1b35c429d36d0a429718d454865f
  | 4 => 0x7a00000800000003b400001b50000074400000f8b41b0001700000000000af00000000001a07440000400001f918e6d1b8000000057c000000000000000000000000000a4800000dd01d9c868008cc0000000002c3000000000000000000007d4003940000000000003bced00000000007c80013c000000000000000000f40000293791e70000000000008000000000070000000044c81202000000003bae80148800000000180000000000000000000800000007f0004000097c00000003440074a46001e70c8001fd99000001d40000227000000000028c008a40000146ac400000000000000800090007c9d9ab9e4000000000000000000009521600000002ac00000000006840000000000f60000040c00000000000000000000000000033400000007c400ac800000000029a000000000019c0242000000000000000000002b560000714000000000000000000020f0000000000000000020e00000000008a000002c800000000003fc00000000000004000000000010b99a64000008512c00000001a50017c0018f001dc0000000000000000000090a3400000000000000000000000000000000000004000000000000000001f4000001a01887568a81d400000004c4000000000000004de2d00100000001260000300000000006b40000000679a0000007a5e88700037400000016b400000000000000000a859319c015680090400000c400000002c0001e00000000002a1e35ab00000000000000015f00c0300000895f500000868000000000000001f5000830000000000000260000013402000000b4007a4de00055115a7a3d19000005fa56b300000000815c1000000000063000a2400000b240400454000000000000000a9002080028100000000008284000000000000b800000008f400001a6400000002f000000000000000000000000040c00000be0000063800000000024600000465ac6ba66356970004900000aa00000000000000000000000000000000000000000600011b000009424d0009b00000002270019b002940680060400000000016b000000007d37001000002cec20004024800000000000031822a211a0000000000002c600000211bc000008503b0bc000000000093000000022d0000000000000000000039400000002b8006f80500000000000008a0000a000010000000000000001d0000002c000de000000016f4f80000000932260000000000188000022f000000026a00000000e0258009e40000000000005780082c27000000000300000121ff001c900000000000026377c0327a22002bb70c00000005f000b54000016629400aa00000000000001b6a3000000014f00000548ee378000a400001f81cc0000000000004900000000650006283100000002380000000000078dc0040004c0000
  | 5 => 0x3222900405000000040300c00006aaacc008840079291226397a8002ec0000c00000002926b000000029848400000409c0ff0000086c00904000000000000430000005400000504000000000002aa80000076000000000068c005725391c0000000001d90000031400002630000000c000005200064000009c40057c0000000000000028e69400000001e80000000001a6000000fc000000000000000003cc000020b00000000000000000000000000080467400000000000
  | _ => 0

def s1K3 : Nat → Nat
  | 0 => 0xb0000d0000000000800014d14401e005c000000002cae0000d00000520000049ca000000000000980000000b40000c0003eb00000000000009c3801c00000000000016000001f00000620002345013f3008a00000000a00c0178037000000000030016e3e1560025b540002900760004eba00031914da0010dc049016ede5b2180070000002000088000485ab00000000000000c4000001e00000c20298000000000188000000001f000002f2800018000000078025c54da81186048421e088a1906290d0c724c1450c28c382879ac8551cdf4149410a966fa10a090d487050c524c28cabe87a0061910d92154021ac0e09086a10e486218135103821a88420a43641c14310431d08c430a8621e244648550086a99be82282434ad1f3214121d20c23028621e1843181450c23233a2092821851183645420a30e0a1e8b195187050c450ca70b3c4210621861146050d30e4084208a090d287050f259060fbb28622e614c1c14314540a30e0a1e8b18d6317cc850486b0382439a84345c5e3251430ac62fa10a090e2862181450c345b10c0a188758c9f3114121a8e6fa122a1063061181450c233bb24212e21920d86049410a488e8824a08514715013510330ab8c090843510dd1049410c32ae3028621d607048445087241a8c090a415855f21c8010a30e0a188b98630461811508293a3e648a841b00d86048421c2a878b4a421d507050c514c3062306c928218c1146048510932cf21881985287050c52503281a8c090a214c1c143c5642d26c23028621d507050f158cb611b0c090843981846049410a18e4a026a2052747cc52504306a18c4a80874911d2045420c1a87934a221e2521d1b350868793c829a881980846049410b10e0a188419617651854310e8793c62a2861611c54310832a28e29828a185187050f359070c318c0a28614cd1f3114121e8064188a090e4462185351030aa18c2a808758c9f4114121d088c1b24210e2462185450c2a43828792c63461c14311431ac0e09084b886506118135102a21ba408a8410719d3051430cc04a3024288628461812504344310c0a18879148736d1421ca06c3022a105187050e5210e8b8bc849a881461c14394443d448c3024210d60704874508714228c090a41611c94310431
  | _ => 0

def s1K2 : Nat → Nat
  | 0 => 0x6000001010d28a204855c6048421a108050f1694843a408048736d1421a108155c6050c43a403855c6048421a208048746cd421a088255c6050c43a088050f2694443
  | _ => 0

def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 732
  | 3 => 105
  | 2 => 8
  | _ => 0

def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0

def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/81+packedAt s1K6 (640+(h % 81)*6) 6) % 40)
  | 5 => 2*((h/1365+packedAt s1K5 (18414+(h % 1365)*10) 10) % 682)
  | 4 => 2*((h/1465+packedAt s1K4 (27816+(h % 1465)*10) 10) % 732)
  | 3 => 2*((h/211+packedAt s1K3 (5145+(h % 211)*7) 7) % 105)
  | 2 => 2*((h/17+packedAt s1K2 (480+(h % 17)*3) 3) % 8)
  | _ => 0

def s1Pos : Nat → Bits
  | 0 => 0xffffffddbefffffeffffddffb4ffffff0fffff
  | 2 => 0x7af77ffafb53f7cffb33bbffff03f03ff3c7c7
  | 3 => 0xedabd36747beacbfcdfdf7fa7ffc0fc0fcf8f8
  | 4 => 0xa3ec77fa7fa3dcdfc3ee3e577f000fffff00ff
  | 5 => 0x5d13ba6ffb7db7b3bed3ffeccffff000ffff00
  | _ => 0

def s1Neg : Nat → Bits
  | 0 => 0xd85043010702181509506b0c83249249055b5b
  | 2 => 0x18c92532a2bac888a252ca0115d75d772c5c5
  | 3 => 0x250d05885a59a60be40205268d9e79e7b8e8e8
  | 4 => 0x3e023c004890732481f7060262ebaebadf00b6
  | 5 => 0x89c2504821f545005122909b26f3cf3cefb600
  | _ => 0

def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000faa0aaa0aaa00000, s1N, s1R, (fun _ _ => 0), s1I⟩


def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s2K5 : Nat → Nat
  | 0 => 0xb0000181000000000d558002600000002188000024001a020000b4a02e02e0000009c0000011000040580000c000000005807c000500000000702d9c0025000000a00003800000023000000bd43fc20fd42bf41fe30fc30ff30fc21fe41fc41ff43be42fd41ff21be40ff20ff31fd32bd41fe31ff10fd30bf43fe21fc42fc32dc32fd43fd31ff32fc40ff41ff42fe43fc43bc42fe32fd20fd21de32fd10fe42bc40fc10ff40fd40fe20fe10fe40fc31
  | _ => 0

def s2K4 : Nat → Nat
  | 0 => 0x1780000000208006800008400000004d80250000000017400640035f80000f000000000cc0000000001d8000000000000028c05ec0000000001480002280130000008023c04000401fc0000003c00008400740000000000000000000000000000000000000184000244d800000000000001667658ac24017a6520025c38500000014801bc0000020e5c001000041000340000240001846401fc000244c400000229b80000000000000000000000000000000000000000000000020c00017000000000019130012000013c027c00003c000000000000000001fc0001a00001500010ac000084000400000001c80000000000d0000000800000bd9c004e7c01f8000000015c0220000401980000e400001e3401c40000000000040000000000000001b8011000000008a5880001705478000018000000fd528c00013c6c54000000000000000000000002867e8a98c74d440af92c653d3510b3a87984fd17329ea28653f25102788a90e7916329e22a655f35d0a7a6b204f544429f22c659e420ca78a0a0cf517319e22a616d258c67a8a0863108329fa2c413d450867a8b984f51631ae9ac415c35442788b08574d621cf2146574514833a87194f91532cfa9a873d35102788a104f51643cfa1c652c5250ef6a090cf14143b7a92613f25d06be6a20574d741cea1c635e354873e8a194f454409f82881af4290ad8a4a1cf4d642dba8a833d45907760a20730c820af1aa213f458c678a4a1e7116329ea28631d35d075e4a214fd1710ae29a856e25442de4a084f915109f22c61cc32c867a8a18570d521cea28653c458ca7e8b9073d08329f22a616c524c33a8618cfc9743e7928653d159027a8b8857d4d429f228413e458427e8b10ddd4520e6194419c428ca7c8a904fc9642ba28a61cc420ca7e0b214f11520cea18653f450427a6ba0e74d440b7a92873d1590b5885994fd14319f92c815f350427e8a184fc1640af1aa419e32102788b184f149419f928859c325073c6520670cb41ce190819f430cb3e6a204f517209f82e833e5010af0a090e78c941ce194813f45cc6be6b10574d4409f82e873f5150f38841957cd741ae1aa413d458867a8b99678cb41ae9a8213f4510f58a4a1cfd14329fa28833f45086ba6ba15b49410cea1a619d35d067c8b90f30c9219fa2e613d15d0eeea2984f91521cf9ae833d45882d84a884f515319e22a215f358867ea6a0dbc96319e22e435f250cb5ea4a1eb10832
  | _ => 0

def s2K3 : Nat → Nat
  | 0 => 0x1d8c0015040c403b2000000000000000000000000bc00400008860111800002c02c0000000300000bc09a19f200000000024002300000000a3c00006000000009800090003b2000025000000000e6400000000018001d180022002a3c9a458ca2c624d741878d91590b0d4314930a3189430c61c624d7418b189351028d61108328d45845082951611632a311b250ca1d36d17208e181454c62c6251531c3d89351030f624d741c38d85250f483214121a3189351021d3611420878db25d070f5314943874db454c70c3211721a3c98458cb0c520c941874db45c430d43c96318318935d068c6250f30c3189351030c450c9218bc9a458c20c624d440a3c9a420ca3516116328759432d070c624d741874db0590a8c6251432a3189438c61d3611610878db251021d36117218b189450ca4c624d440a318935d061d36d142187189351030c32d1620c550c514c24c624d74187195434c30c32c9640874d8505068e6010832a3189434c21e364564087594321030c3211420
  | _ => 0

def s2K2 : Nat → Nat
  | 0 => 0x140001c000040001022428b88d92865411c94314530818e49b08b0840c724d845082838bc6c29287031c936d1710818e49b0a0a0c0c724db45087021922c2284103c9e3645640
  | _ => 0

def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 166
  | 3 => 60
  | 2 => 10
  | _ => 0

def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0

def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/101+packedAt s2K5 (800+(h % 101)*6) 6) % 50)
  | 4 => 2*((h/333+packedAt s2K4 (4482+(h % 333)*8) 8) % 166)
  | 3 => 2*((h/121+packedAt s2K3 (2280+(h % 121)*6) 6) % 60)
  | 2 => 2*((h/21+packedAt s2K2 (490+(h % 21)*4) 4) % 10)
  | _ => 0

def s2Pos : Nat → Bits
  | 0 => 0xffeffffdfffffdbffffff7badfff83fe3ff1ff
  | 1 => 0xfbdaeff7fededb76bbffbef7bfd07c3fce3e3f
  | 3 => 0xffbd7fcb1d2326fbcd9aef7d79bfffc1f3cfcc
  | 4 => 0xf2ffdb5bd7a66ec7571b8fcf26187fc1fc0ff0
  | 5 => 0xaed61152a875d5cf865c721cf2378001fff000
  | _ => 0

def s2Neg : Nat → Bits
  | 0 => 0x800161c440b25510190084508201148a14d0d5
  | 1 => 0x3440a0022482825200e218e6972a954ca262a
  | 3 => 0x426c0701a88d64c641b97a81a404ce67634b4c
  | 4 => 0x7910bc698c029b1806754420174f73b9bc0db0
  | 5 => 0x97cee68502220b6176511bc4501ffbfdffb000
  | _ => 0

def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xee88aa88ee888888ee88aa88ee888888ee88aa88ee888888ee88aa88ee888888ee88aa88ee888888ee88aa88ee888888ee88aa88ee888888ee88aa88ee888888, s2N, s2R, (fun _ _ => 0), s2I⟩


def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s3K5 : Nat → Nat
  | 0 => 0x16000000000000000000b80000000000000000000000000019014000aeca80000000000000000000000380000000000000000000800000000980000000000000000000000000000000000000000000a800004c0000029000000b4000000000000000001200000000000000000000000010000000000000000000000000000000000000000002700002900700000000000000000000000000000000000000000b00000000000000000002d2c0000000000000000006000840000001000ac000000d0080000000000000003000000000000000000000000000000000200000000000000000000000000000002e70010300000000aa000000000000000000000000000640000000000000000000513000000000000000000000000000000000000022000000030000000000000fd40fe43fd42ff41de30fd43ff21fc42fd21de32fe41fc43fc30be42ff30fe30fe31fc10fe21fe32dc32fc40ff10bc42df31fc41fd32fd41dd31dc30ff43fe42fe10fc32ff42ff31fc20fd10ff40fe20de43fd31ff20fc31ff32fe40dd43fc21fd30fd20
  | _ => 0

def s3K4 : Nat → Nat
  | 0 => 0x2000000000000044821c503401fc000000000000980000000000000000c80004028d30000264000000009c002008024c00013c00024e840c0000009c000000000001e000a00001980000004c7000003a0c0000018c00018000000120000000000c0030dc01a402380000000268000000142c0000000044381a10009c080000000009000000014d5c6d78000270000000000000018c00040040f00008000264f40000000400000400700000024ca80160000001f40002098c000001c1b0000001b00000006800015c0000080000000001dd2800000000000000dc00000001b00098f86c00ec00ec40000000000000000000000000022c0098000c0401d591e400f40094000110000001080000017c012400000000010c02280004d8100000fc00000000013402480005e00001e001e00000000000005800025401a28800000000000000011800013c00007c02b8a498d7cd641ba28a415d351033c87214fd1621af928615f35c42be6a10db149409f22a65cf420ca7a8a0867d1430cea1a815e450cabe4b98cf51731ae9a8435f058caeea2a05751430ce1ac855f350c73c86214fd1620ae1aa419e3590b98841957cd4419e22a219e42cc6ba6a20eb10921af92c875e35c86be6b904751430af22a635c35442bc8b98e790832af928659e428cb1884194f91520cfaa2879f3510abca0196b10b32b7a92875e450c2d84a885ed4121cf21461ac42c86bea2a1d791632ce216635e358427e4b2157cd440ae9ae815d35d06be6b10cf51732ae9ac419c420ca788a90d7c1731af1a8415f0590ebe4b195d14540af9ae839e420c2ba6b18cf51621af1aa415d150c3388518574d742cf212635e35442ba2b1857c1430ae9ae215f35d02de4b20d74d621af92c613f45ccaba6b20e74d442aea2a635c35c86b8a6a15e14121a6292873f2510ab86b0873d49439e22a419c420c2da4a086b10a20b7928215f3588358841073149439f22a213d450c358841967d1731af9a8875d450cbaea298d791630e7928655c5250edea4a04fd1430cea2e633f45042b8a6a04f91521afa9a855d45cc6be6a2157cd4109e22a65db050c33885195b14943d7928859d4310aba2b195751643cea1e816e25442da4b20ddd45209fa2e635d1590e7a8b1057544328ea2e635c350833a8620d7cd742aea2c65b541106be0b186750e42ae282639d450c2ba6a08574d720aea2c615c35486bea6a06710931cea1c835e35486ba6a215714143
  | _ => 0

def s3K3 : Nat → Nat
  | 0 => 0x440000000000000d4038000f00040002dd000300005800000004000001c4000e9eb050b80000d90c000005658003400501c0280000000000000003000000286da00e640b8002000000030000002d338980000000040dc002300093c9a458c30c42c9630c3d89450c28c6250d40c39185250e1d46cd720a3189431068c6250e41a3189450c2586051531c318945cc70c625143087919158cb0c3510921c350c5250315431454093189450ca55160d420c3108350824c62517318718945cc60c6251430c310b358821d6510b3187919158c30f6251731a3c983590b0f54149438b18945cc61d4614131c310a450ca1d46cd421a318945cc68f269083287594420c21d46cd71087518358430c4254432a318943d022c62514308751a450c20c6251731a3c9a3590a1e46c94308751835c861d460d4208751b058cb0c42149319545a450ca1c62514308751b350c61e46c9731a54583590b0c420d721c350f25907284214121c3594420ca4c6251430c310a500ca4c6251531
  | _ => 0

def s3K2 : Nat → Nat
  | 0 => 0xc04c001c000044c0060793c8c8ac61031c9460d420c08848b06a1040c7251b35086838bc8c29287031c946cd710818e4a30a098c0c7251835842823928628a81811091691432
  | _ => 0

def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 166
  | 3 => 60
  | 2 => 10
  | _ => 0

def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0

def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/401+packedAt s3K5 (800+(h % 401)*6) 6) % 50)
  | 4 => 2*((h/333+packedAt s3K4 (4482+(h % 333)*8) 8) % 166)
  | 3 => 2*((h/121+packedAt s3K3 (2280+(h % 121)*6) 6) % 60)
  | 2 => 2*((h/21+packedAt s3K2 (490+(h % 21)*4) 4) % 10)
  | _ => 0

def s3Pos : Nat → Bits
  | 0 => 0xffffbfdfdfff73ddefffeeff7fb83ffe3c7fff
  | 1 => 0xfbbccfffefccdfff9feeff7dc77fc03fcf8e3f
  | 2 => 0x7cebf7f53233bf2f7635dbbabef7ffc1f3f3cc
  | 4 => 0xb47ae322d7cbca2c6d16c97f20d803c1fc03f0
  | 5 => 0x3d43fee67677edefdd4d31e8bbeffc01fffc00
  | _ => 0

def s3Neg : Nat → Bits
  | 0 => 0x42001142a5a50a40840c0240071488a1434d5
  | 1 => 0x8917a6210500035a252108804b829554c98a2a
  | 2 => 0x85887cc29000c408930464467d2ce66762d34c
  | 4 => 0xa3224089cd8307fecf0f830096cfbffdfc03b0
  | 5 => 0x4835813f81c52b200634312920873bb9bf6c00
  | _ => 0

def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xe8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888e8e8e8e8a8a88888, s3N, s3R, (fun _ _ => 0), s3I⟩


def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s4K5 : Nat → Nat
  | 0 => 0x41f00000d0000000000210c0800a800000200000110009801c001e0000000000190236814800014400003807807cc00001c00000000c000b4090f5400000003c001d00200001b140000000fd41ff31ff20df32fd40fc10fe42ff30fd42fd20dd32dc30ff10ff21ff41ef42ff43fd31ff40fd32fd30fc40ff32fe43fe10dd31fc32fe40df43fc30fc43fe21fe31fc42fd43fd10df31fd21ff42fc21de30fc20fe30fc41dc43ec42fe32fc31fe41fe20
  | _ => 0

def s4K4 : Nat → Nat
  | 0 => 0xcf30000000006eba00000001491400d07716ae012a98000000200a00140000000000000000060401008c7a1200000010000000000000ea6e0000000000002c006c00000200e650cc000000009e00748a000000000000009c009a007c000000002c820000013c01000000d200000000f93a5a7800008a0000012e00002e003a00000002000200000045222600000200a10f1a0000008a000000f2000062000048053400000000000b080000012c00b800007cf60000005ec600000000000a0000000000e0000000002a000036000000000130be00000000007a00f8fa00000008001740000000000000000000000000300000000000000000000000000000de00013888010e0800547d4a009c2c000000c29600000000000039120138033116009042820002c88c00000000000000001200ca000000260000ea00007e000000c4000000780000007c7400235c454cb5884a0f310c42e6216635d3590ab86b084f91510cfa1c876d25042be6a10ddd4540e7a12655f350439e862167d1443ae9a821ac42d06be6a10734cb20e6990436d250c39e6a2157d4931e69a885e5210869a4a18574d720afa28615f35886ba6a10d7cd720af9ac85ac4210398849957d1531af828615f458c2b86a90574d721ae9ac835c45ccb9e4a184f115209ea28216f2590aba6a20f310830b7a92835f350c6d8a4a0e710e429e22a213c454caba2b185711531ae228615c5350a7a8b10f34c920af82e65cd328875886215749731afa28876f25907388a9957d4d40af9a8658c4310abe6b8875d4531ae9ac816e25443986ba15ed4141af9aa435d3510ab8a098d7c1743ae282655c45cc6ba2ba1dbc9410bc282836f5250eda4b21d74d632aea90875c35882be0b98dbc94309fa2821cf25cc6e8a2a06791532b7a28855e358839e87a15b14940e692861cc424c6ba4a184fd1621af82c615f514cabe6b90d711630ae92e87cf424c6d84a887349731ae9a841af4510b58852057cd643b7a92815e35442ba6b885b14943af9ac815f5350aba6b10d78d610ba28a415c53502bea6a0f3d0a30b792c81db050c2baa221cf91532bba8a411c454cabe8b9973d4932ae92c61cc43d0aba2b9957cd442afa2a655d150c338862173d0830afa2e636d25cc6da4b20db49640b792c875f35d02de4b98f38d7429f22a415d354879885995349731ae29a835d358c6b86a8857cd441af1aa41cf42ccabca021f310a30e7a1663ae4310abe6b20d74d740
  | _ => 0

def s4K3 : Nat → Nat
  | 0 => 0xa1c000a7c088b540000e8000b6400000000de7c0000c40080000005000000000000d570000000000334404800004c00003c0e80000c40000d40000000000a00000000407d0000f0000004700005406c070001c00000001d01b880c311532482c5160d742c3117524ca8f3690c428b11925cc64c654c920ca108505070e464973195458450c30c4649731a311925cc64c46494309349b35c424e264563087119250c24d26c174393498504c61c46497319311925cc70c421173296181354868c464c82187119354864d260d61087d1a358824d2611430c34cb458870f6211532c310b458c24f4649430c310b359028e6010c42d14c8514824d6510b319349b35d020c46494309389915d0e4f464973187d5a454ca8d6110c42a311932c830c45d0932a3119250c28c464ca218311925cc70c45109329545845cca4d26cd44193594420c28c464c920c3108450c24d26cd521c3119250c30c4510931c310845cc70f42d1732c314c425070e46494308b119250c24d2611731
  | _ => 0

def s4K2 : Nat → Nat
  | 0 => 0xc001156001000c28223a6428a4141c5f62115328188e9366a90c0c4749835843022122c228610311d26141318188e9366b8840c471953248207a3c4c8ac61811091611732
  | _ => 0

def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 167
  | 3 => 60
  | 2 => 10
  | _ => 0

def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0

def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/101+packedAt s4K5 (800+(h % 101)*6) 6) % 50)
  | 4 => 2*((h/335+packedAt s4K4 (4509+(h % 335)*8) 8) % 167)
  | 3 => 2*((h/121+packedAt s4K3 (2280+(h % 121)*6) 6) % 60)
  | 2 => 2*((h/21+packedAt s4K2 (490+(h % 21)*4) 4) % 10)
  | _ => 0

def s4Pos : Nat → Bits
  | 0 => 0x9bffff7f7f7fff7fffffffe53fff83fe3f1fff
  | 1 => 0x6d9ee7f6bfbd7ffd73ffbbffffd87c3fc8e3ff
  | 2 => 0xe6cc56adb7f75c8fd4fe61dbf3007fc1f0fccc
  | 3 => 0x1b2b9b3d4f0ef15cac387f5b78278001ff00f0
  | 5 => 0xf761ffbbfee3dea6af5b4f1ed43fffc1ffff00
  | _ => 0

def s4Neg : Nat → Bits
  | 0 => 0x1cd8851001038c010600529000944a130d55
  | 1 => 0xb4307680a6c00612861e08466832994c862aa
  | 2 => 0xc321480227da5f0844415c0ea8bdcee770b4cc
  | 3 => 0x44b255e2e3176a335b5079474a47eff7fd00f0
  | 5 => 0x280ea421b914901414188aa90b2e7339aedb00
  | _ => 0

def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae888888888eae8eae888888888eae8eae888888888eae8eae888888888eae8eae888888888eae8eae888888888eae8eae888888888eae8eae888888888, s4N, s4R, (fun _ _ => 0), s4I⟩


def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def s5K5 : Nat → Nat
  | 0 => 0x540c4001f6300003800000003c00000000004800000150000005644c000000000000000000000600008001d00000000000000000000020900002104001b00030028000001b0000000000017801c0021000000000200994000000000000000000000000000000000000007000000380980ff41fd10df43fd21ff40ec20fd30fe32fc30fe30fc40ee32fe43fe31fc43ff20fc41ef42fd31ff42ff31dc43ff10ed21fe40ec42fc20fe21fd41ed32fd40ee20fd20fe10ff32fc42ef21fd32fd42ff43fe41fe20fc21fc32ff21fd43fc10fc31fe42ff30
  | _ => 0

def s5K4 : Nat → Nat
  | 0 => 0x4600001a8000000080002700000000000000000009000000004f8000004d0000003590800000000b830388808081000000000000110000000028801eaa80384c000000162f0000000000000080000acc800000002400388000000026c1b9802600000000490000000043000008800100000000000000000e8049b8411a2d3680800000000980001480000800004c800000000bd00000003e2412001e800000028007c680000000000000358880438000328000000000002d000040000000052dcb8000000000004d800000480f00000051000dae2e00000e00000039850000001c0000003e5012af800000108000008000002e8000002d80169a000012800049000006910000002b800000000000260000001e001e80460000000010000000003a800000003b802c000000000000000000001a8034000000468000004f8000003180000000068000200038734d7219f22a6574514c2de4b205b8d521b7280853c454433887215dd4530b792e216f52506da6a90f34cb30b6282656f524c2da4b985b49640b612c21cc43486de4a20d7cd721e7a9a65cc438cada4ba04f91510e621e856d25cc6be6a104b11532b792e81cf35c873e8a21d7d1443d6218859c4310ab8a6a05b45632b792c856f25086de4a085b49430b69ae43cc43083988699574d410e7a18858c4310b9e8790dbc9432b792e613e454c2da4b20dbd1721b6a88856d258c6d84a887310e20b6928214d35c86bea6a0dbd4940e6a90877b50506da6b106b90c42b629261cf43486d8a090db49431b622c65cf438cb9a6a104f51631b622c416f05c86de8a215e14141b7928636f05882da6b19578d510b622e436f45882de8a90f34ca31ae9ac836f05082da6a1073d0f42e621e436d5210e788a985714d42e7a1a65cd320c73887206710d41b7a8a655f3590ee8a2a05bd1532b6292875d35082dea4a1dbd1632b71ac415c354427e8a084f11532e7a1c414d35082dc4a8879d4521b7a28416f05d0ade4b98db89610af9ac83cf43082d88a105b14940e621885ce25d0ede4b20e710f419fa2c635f5350a7a8a085bc9643b69a8856f258c6de4a185b8d721e6992616c45486da4b21db45742b692e215d3590bd60a105b4d742e7290875f35902bea6a05dd4540b71a841ae454caba6b90dbc1632b68ac416d15083588a996710c40d7a28856d25886be6b215714d41b622a65cc25d0f9e6a105b49441af9a8216e5210ed8a4a0d74d640
  | _ => 0

def s5K3 : Nat → Nat
  | 0 => 0x26038000000000d8000000034008000000000700004000000000008003a000000024c00000000005000000c4000c01d8400008e4000002000ac0440000e40022ec001800160002a040501000df40000000000050410049b6040000c391935c864d36c1742c610c50506651611632c310c45c870c43c96409359443c870c4311632a311935c870c439404293119350824f464d721938d9158830c431494199458450830c45d0d32a311932cc24e3645742a3119324c22c464d72183119350828c464ca31934d8450824d3614121934db25d030f6311532c3d0f458ca8c464d4208311935c870c4311420c3117534ca4d3611721c3919350824d36c9421934db251061c464d7219a181354864f464d4208bd1a358822c464d420d14c8514c30d32d16319311935c870c454c9308b119354862f5691532c310c454868c464c831c310d5110a4d6510c20c3119350828f3690c42c311935c86c51609743c310f458824d36c9710c3114434ca4d368d42087119350824d3609610
  | _ => 0

def s5K2 : Nat → Nat
  | 0 => 0x200000000000000000040800001c030221a2c2284103d1e3645620c08868b08b1940c474d8258420623a6c282430311d36c94218188e9b64b88504474c8514c207b3c8c9a84141c5f6311532
  | _ => 0

def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0

def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0

def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/151+packedAt s5K5 (800+(h % 151)*6) 6) % 50)
  | 4 => 2*((h/331+packedAt s5K4 (4455+(h % 331)*8) 8) % 165)
  | 3 => 2*((h/121+packedAt s5K3 (2280+(h % 121)*6) 6) % 60)
  | 2 => 2*((h/31+packedAt s5K2 (490+(h % 31)*4) 4) % 10)
  | _ => 0

def s5Pos : Nat → Bits
  | 0 => 0xfeb7ffbffdffafffdfdefebfbfd83ffe31ffff
  | 1 => 0xdfdebdee6ef27f7976ffdfff56f7c03fce23ff
  | 2 => 0x517ebf5cf1afbb16aebbb30eada803c1f03ccc
  | 3 => 0xe969e05deeea58bcf1f9f9fb76affc01ffc0f0
  | 4 => 0x256f57519f7dddceeff735f7fdffffc1ffff00
  | _ => 0

def s5Neg : Nat → Bits
  | 0 => 0x5044018282042430d02031c76e1444a10cd55
  | 1 => 0xc8091284860e290042ec248081029994c622aa
  | 2 => 0x95a07395a809763866d670410e4efff7f034cc
  | 3 => 0x64613c4a80919325189681600584eee77b40f0
  | 4 => 0xa9c014254f2ac98c0016a0290373339adbb00
  | _ => 0

def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888eea88888, s5N, s5R, (fun _ _ => 0), s5I⟩


def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x740db33c570701630c180d3325a2485f382300ff1801ff90c03fa6403ff3105ffa9017f9480ffe6407fe5300fea100ff14403faa003fe4100fea9007f4800bfc6403ff5101fe20807f50c17fea601fd5401ff9080ff94403fc8005fc3200fe9800ff8c417fea809fc4004ffa1817f9080bfe4003fd3101fea080ff88407faa205fc5204ff2a027f15013fe8407fc4305ffa8007f54c07fa4203fc1001fe1880ffd0403fca007fc5300ff1000ff8400bf88405fc2003fe18007f50007f8420bfc5003ff98027fd0007fa2003ff10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xcc6403fff98553009f9592006ffc9a503fff8855306ff8812006bf85a4006ff85a4000bfd915006ff5022045df1495403ffd0d3006bf0da400cff5462006ff05a2003ff94d3205bf1592005bfd59401cbfd814024ff94d5036ff14d5206ff0da4000ff5513202ff9494200bf8d92003fecc23000bfd895300df959320cffc862006ff4da4003ff90d5337ff1015206ffd5a4040ffc815306ff1422023ff1495025ffd0d5006ff91a2003ff90d3210ff0c53006ffc1a5000ff50d2002fe0812006ff1022000ff9193006ff8412000ff5895404ffd015444ffc415403bf18d5206ff0412006bf05a3002ffd09201bff14d4000ff501202bff1853211ff1493005ff141520eff10e2003ef90d4306ff9415033bfd894214ffd593006bf85a5004ff1514305ff1415324ff98d5006bf95a2007ffc852006ff0424019ffc854007ff1852003ff50e3000ff50e5019bf5854000f7d8d4010ffd05300aff1512035ff1855202ffd494200ffd8d5402ff5092006ffc823013ff1193003f7cc93006ffd5a2015ff8863002ef1094202ff109520eff94e2003ff14e3006ff8c12022ff8c55000ff8d92007ff9052010ff8c53001bf9855300bf9593006ffc5a3004ff9514322ff5055000ff541200bffd512005ffd415004bf9915210ffd453004fed024006ffd023020ffcca4023ff8c95006ff9412006fbc822006ff9414025ff9515006ff0c13005ff551533fff905532dffd41320aff1192011ff9893019ef5054046ff94d540cff0c6200eff90e2006ffc824004ffd514210ff1053020ff14e4006ff1015000ff5915000ff4d92006ff5423006bf05a2002fec812006bf85a200affd0d2001bfc5a5006ffc822006ff0422006ff55a2002ffcc95210ff9453006ff8da5034bfd914200ff5192027bf45a5006ff9413000fb4c9203aff0c54307fb4852007ff1452006bf15a3006bf1813207ff0c52000bf49a301effd464006ffcda4000ff9192041ff1015346ff98d540fffd0e2000ff50e2015ff9063017f7d0e3004ffd094027ff9065007bfd852005bfd592013ff1513013ffd013002bf1893003fbcc93206ff1012006ff8c13006ff95a3000bf5192007ff0852006ff0c12000bf9193015ff5063006ff1023029ff90e5000bf55a2002bf9894044ffd055406ff9012006bf11a5006f78c13006bfc1a3006ff89a3009ff10d2004ffd0a4004ff5524006ffc5a4006ff8422006ff4da2036ff18d5215ff0863006ff85a2019ffcc54002ff4c92006ff4c22010ffcc53007ff8852035ff945523aff5854304bfd1a5004bfd1a2006ff0414007ff4852006ffd1a2036ff0c15206ffd5a3006ff8423007ff5052007ffd452006ff081201aff9094006bf09a3015ffd463007ff5852007ffcc52006ffcda200cff486201affc814003fe0c13002ff0c92006ff0da20
  | 1 => 0x7bf5852004ff1515422ff1455015ff0c63002bf9894306ff0da5002ffd093204ffd514000ff4ca5037ff9515211ff8c9300bff1592035ff5855222ff4c55032ffd4d4235ff9055206ff91a3003ffcca3004ff1014344ffd455422ff5855024ff90d5006ff85a5006ff05a5006ff0814000ef9193206ff8425000ff58d4210ffc853015ff8c63006f7cc2303cffd594306ff91a5006ff4424019ff9454005ffd4d5202bf1895002fb1495235ff0415202ff909423bff0814300bf9193202df9495202ff1094200ffd815202f70c93200ff1815306ff141202bff4413241ff9515300bf4d92006ff45a3022dfd455006ff15a202ebfd893200bfd894030ff4854203b718d5406ff49a5007ff985201fff8ca4044bf585543abf5854306bf05a5019ffd454005bfd594306ff09a3037ffd015204bfd1a3006ffc5a5030ff5454206ff1414010ff5853019bf51a4000ff181422bbf5853200bfd813206ff9424006ff1014000ff9592004ef1515400f7d8d541bff10d4005f7d4d5300ff5895000ff9814306bf05a4028ff94a5000ff5592006ff0423027ffd465005ffd515003ff0c1432bff5853235ff1055223ff1095000ff5193006ff05a402affd0e5040ff9095306bf8da2007ffc41200aff9512000f74c9302bffd453204ff9514001bfc5a2006ff8415024ff14d5002fec822027ffcc6503fbf5855304bfd193222ff54550059f1593206ff9422006ff85a3000bf4da5031ff94d4230ffd054202ff8c92029ff10e5001bf9855228ff0ca5016ff8ca3012bfd813004ffd01421eff8864002ff9093222bf5855002fb14a2045ff9095410ff905301aff0c94015ffc863003ff0c1320cff1462000bfd915310bfd853003f710d3222ff0c55002ff9092002ffd493206ff0c14030ffcc54230ff5054237ffd0d5200ffd915002bf9893000bfd8d5203ffd4d3030ff0414206ff0415044ff0c55400ffd81530bffd592000bf5193006ff45a2000bf4da400cffd062001bfc5a3035ffcc55205ff54a5005bfd5a3010ff1853000ff5594002ff54a2006ffcc2200cff4c62006ef1014020ef10e4006bf95a4004bf1915304af1193037ff1915204bf1193001bf9854006fec1a4000ff9594027ff0c65025ffd015030ffd454206ff95a4006ff8424001bf185521fff14a4002bfc9a3030ff9054205dfd515000bf51a3020ff94e4025ff9915006ff0823022ff185501bff98d4000bf51a2044bfd855400ff5095002ff0c93203ff90d4300fb1895403bf18d401fff10a4010f74c53006ff1413001bf9855400bf5593000ff4ca4006dfd425000bf51a503fffd055300bf9192000ff5813201bfc5a4027ff8c65003ffd0d3214ffd493006fec1a2005bfd59422bff9453206ff05a3001bf1854002ff8c9523fff4c55300ff5893027ff4c65006ff142301eff
  | 2 => 0xbc81322bff8853218ffd52303fffc41533affc414302bf189432bff505323fff1855327ff5065011ff0c93002ff8c93206f70c13003bf98d5405ffd4d5011ff1893007ffd05202bff1453206ffd024022ff885503dbfd8d4319ff8854004bf9915306ffd424004ff1014204ffd515403bf98d5026bfd815004ef9514002fb8c9201eff9464041ff9915306ff9014035bf5855223ff909502bffd053204ff1524044ff8c55403bf98d5202ff5492006ffcc2502bff4c5323fff5455311ff9093019ff5854002ff4ca203fffd855303ef10d4300fbd895400af9193246ef90d541bffcc14003bfcda400bffd4d2002ff1495244ff8415402df1495204f7d0d4319ffc414000ff5894045ff1095406bf09a501eff506403fff0c55306ff8413006ff8da2045ff9895410ff1453010ff8853038bfd895239bfd955203ffcc13021ffd4a401aff1894044ff5455400bf5594004ff5514006ffd025040ff1095306ff15a3010ff4c5302aff1525006ff4422000ff5493000bf959201aff9894006ffd022001bf1855302ff8c9422dffd593215ff9463006ff11a5044ff9855404ff50e4047bfd915406ff9023000ff589433fff0415309ff90d2010ffc413003ff14d4303ff14d533fff4855300ff54d2005ffd495405fbd495203ff54d323fbfd85531bff90d4000bfd815302fb1094206ffd1a50009f9593206ffc9a3010f7cc53004ff951422bffd853206ff542403aff4414346ef10d5404ff9524003ff10d3207ff4412003ffd0e3046ff18d5404ffd094306ff1424022ff9055000df551503aff8414304bf1915019ff4414002ff1493222ff485501eff9064030ff5854205ffd4a5007ff8c52037ff1515206ffc42201eff0c6403fff5855327ff4865006bf1815415ffcc63045ff1495400ffd893006ffc1a3003ffcc93001bf1855006ff0813005bfd5a2002ff0813202bf1895406fb8812000bf5193203ffd0d5303ff10d5330ff4414200ff50d5005bf1594006ff45a4002ff1492001bf9852006bf91a301fff94a4006ff51a3004bf1193206ff4423006ffc1a2006ffcda5004af119321aff1094030ff8854200df9592004efd015427ff1065002ff9095222ff4415005bf1594303ffd4d5300ff5093000bfd893032ffd594219ff1454000ff5414030ff4c54206ff4425040ff9495306ff5422021ffd4e400cffd462024ff10d5000ffd894303bf0d92032ff1594211ff109301fff90a401fff0ca4020ef90e400cff9062030ff0c54203ff4c93003ff14d3044ff5855406bf1815206ff55a3035ff5055200ff4c12004bf1192006ff0413019ff1854000ff5013003ff0c15310ff485302cffd013205bfd593035ff1455206ffcc2302bff9853241ffd015304ffd014344ff5055435ff4c55213ffd093006ffc423006ff15a4045ff0815428ff90a5
  | 3 => 0x501dffd4d4000ff9814200ff5413005bf159423fff1055325ff1915006bf0da5006ffc42400cff9462006ff49a4006ff51a5000b7d8d5402ef9094200ff5522003ffcc95300bf9594300ffd8d5001bf1855400bf5594206ffc5a2027ff1465003ff94d4305ffd495002ff9495227ffd065004ff50d400cff0862000ff5895310ff085303cff1414303ff14d3236ff10d5200ff1814300f718d54059f1592044ff945543fff8c55302ff0814222ffc855004ff5514302ff0c9523aff1854310bf4da3000ff54e4000ff5512003bfcda5014ffd513007ff1052000bf559432bff1053206bfc1a2044ffcc55405ffd495304ff1514000ef5514010ff4413015bf45a3006bf15a4003fecc13045ff0c95400bf49a4000df1592009ff94d203aff9454303bf18d5035ffc415202ffd492025ff1515007ffd85201bff94d402bbfd853200ff5915300ff5594302bf9895318ffd4a3029ffcca503fff1455348bfd955400bf4da2037ff991520affd012044ff0855446ff90d5444ff4c5543aff885433aff485432cff1013200bf9594200ffd915236ff98d5231ffcc14206ff0c2402fbfd8d3203ff50d3202ffcca2002ff8ca2000ff5814208bfd812022ff985503fffcc55324ff18d5005fed42501effc86401bffcc9402bff5453202ffcc94200bfd81423affcc54307bf49a2006ff0c22003ff10d4327ff0865000bfd8d5402ff1494227ff886502aff9525000bf55a3003ff4ca3003bfcda203fffd455306ff9423005ff54e5028ff10a503aff1054314ff1593000ff981322cffd193200ff54e201eff8c6403affd454303ff94d3000bbd895424ffcc95000ff50a3044ff1455400ffd813210bf5853017ff9523044ff8855410ff985301eff0864016ff94a3002fb1493203ff54d3006ff0815045ff189540cff8c62006ff11a3007ff9452004df9515400ff9815202ff9492045ff8c95405ff5515231ff0c14200ffd8d5202ff9493202ff14a2022ff9455000ff54a3006ff1013013ffd193046ff14d5400bf49a502bff0413206bf11a2006bf181531aff9494000bfd8d402dff1413240ff1895317ff1523023ff989500fff952201dffd414022ff1055004ffd514300ff581541eff5464035bfd855235ffd055200ff5915203bf18d5444ffd855406ff1415019bfd854002ffcc9322affd0a5000ffd915306ff9013044ffc855402ff10a2031ff10d4229ff14e503bff0c9432bffcc5322bff0c5321aff8c94001bf1854306bf09a400eff14e2002ffc814203ffd4e3022ff085503affd054306ff55a4003ff54d432bffc413231ff98d4202fb0c93211ff9493003ffcc15305ff54d5200ff50d5206bf1814301bf1852002ffd0a2000bfd895400ff54d4246ffcc95430ff0854227ff9465030ff1054228ff8ca5014ffd41300dffd522006efd024002f
  | 4 => 0xff151533affc854315ff1463011ffc813006ff09a4000ff5593000ff5594215ffd063032ff1414203f7cc13203bf98d4205ff1415406bfc1a4025ffd095005ffd4e5006ffc1a4001bf1854201bf9854202ff0815203bf18d4230ff9854210ff5453019ff0c5400dffd4e2000ffd895040ff8c9533bff1894306ff0c25000bf9594019ffd054003df14d5331ff90d4205ff5515005fe141501eff106403bff8c9431eff4864000bf9593222df545503aff9854301bf1853004ff50d4222ffd455001bf1853202f78c93201bf9854300ff9593204ff1015400ff959432dffd513228df94a5005bf1593005ffd4d5402ff90a2001bf9853202bfc9a4005ffd52500dfbd4a2000ff5815206ff4da5004ffd524005ffd51533bff949431dff1594002ff94a2016ff90a3043bfd955306ff8414006bf11a3022bf55a5023ff1895005ff5525002bfc9a5003ff10e3000ffd8d4222ffd055000ffd895303bf98d403fff5055306ff102501ebf45a403aff5054330ff8c5420affd192006bf0da2000ef9193005ff5495042bfd8d5303f714d531dffd594030ff8414206bf91a2000af9193044ff1055402ff5494204bfd193004ff9515435ff9855228ff14a5003ff90e3016ff14a3040ff081530bffd41203ebfd914303ff54e3044ff9055435ff085522cff1513204ffd01403cffd414300ffd89403bff9094319ff5454006ff95a2035ff4415206df1415004ffd0d5406ffd422030ffd85423aff4c54304ff50a4000ff58d520cff1062006ffc9a4035ffd855207fbc852003f710e3006ffc42502cff1193202ff509322cf7d0d3202bb1895036ff90d5229ff94e5000bbd895003ffcc14335ff8855201bf9855000ffd814345df9495403ff94d5304ff5094006ff49a3000ef1193002ffd094204ffd0e4027ff5465016ff10a300cff5062006ff11a2005ffd515200ff50a5000df1593202ffd495206bf1814205ff54d5020ff10e4006ff09a5000ff5513024ffcc15002bf1895346ff0c15402bf9895000b7d8d403cff1594302ffd4a203fff0855306ff902203aff0854300bfd91523abfd85433bffc814315ff4863015ff5463004bf1915206bfd8d3010ff5053006bfd95503fff4415300ff9593040ff1495303ffd4d4317ffd0a3010ffd853023ffc815006ff0425000bfd895000bfd894336ff94d5200ff58d5000ff4c95009ffcd92000ff181521eff1464000bf55a400cffcc62031ff18d4200ff581433bff1494328df14a500cbf45a2006fec1a3002ff0ca201effd064006ff89a5005ffd415306ff502302bff0853213ff9513046ffcc15404bfd192032ffd414200ff1813206bfd892019ff0854000ef1193206ff0824006ffcc24006bfd914003ffd4d321eff4c64015ff4c63022ffc415005bf1593200bf5593204ff1514202bb1895405fed41
  | 5 => 0x36c27e6c8002d431a0000000022858c5609695d1326f07074e600003c33200a25980034942948ce098c4a90c928502001c180000129d680a41ac4393046613e47e719aca0c68de5a1c2a1231b00007450f4530118140a0fb000878d75c0a2725e000000003c63b88c21b000c782b22734b028004557349440000023cb0cdb0003c2001214c515f395164f6908da5ed8002a9285fd8000011d037c0d91a0005941317cb48f381a8e027e2b80017a000000110e63de53233736001ae46a144c040009b76099d93c0846a001268a461108a3f34b156000df931000981bc14b3dd174f61ee000000000002cd294c644b0c53a61680789c8ac83b5720a001069440011ea84800014c5e188006c6900a295a3069d1fa44e75a000000007a40024bc6b000000003135580028300004df1515406ff0c15000ff981543bff9894346ff10d5403ffcc94302ffc815215ff106303affd85432bff8413206ff89a4000bfd8d4209ffcc12020ff90e4002bf9895403ffcc13207ff4c52002ff5493227ffc865019ff4c54035ff8c55200ff5494006bfc1a5041ff1915335ff4855204ff5514200fbd895019ff5054022bfd855035ff5455204fed01402cff9513203f710d4344ff0415435ff0c5522bff9053200ffd814240ff9895300ff1815406ff45a5002bf1894002ffd09523fffc855306df9415001bf9853005bfd5a403aff8c54330ffc85422dfbd493206fec1a5003b718d4045ffc815419ff1054030ff9454244ff4415405dfd415400ff5523006ef9014000ffd8d403fff8415300bfd814306ffd425044ff4855404ffd0d4209ff0d9203bff1094330bfd854204ffd0d4005efd515404ffd095402ffcc9200fff1522000ff58d403aff041433cffd494300ff9815323ff0c95000ff9594200ff5815305bfd593202ff0c94200bfd815202ff50a2030bf5854235ff8415200bf5592000ff54d403aff1454300f718d4035ffd455200ff9193222ffd855006ffd1a3004fe1014041ffd09532bffc853219ff9854006ffd42302bff8c53200bfd8d5006bf95a3035ffc85522dff1593203bfcd9203aff5454306ff0825000ffd81541aff1494000ff58d5403ff50d3002ff1092002ff1093230ff1854206ff8c22004bf9915030ff1454206ff8da4000ff5193203df94d5300ffd895400ff54a4000ff5593206bf15a2002ffc812004fbd094202ffc813205ffd415223ff9495016ff0ca303aff905430cff8862045ff9495409ff14d2031ff14d421dffd494000fb189501bff18d4019ffd854003ff94e3000ff4c94006fb0812000bfd81543fff945532bff4853219ff9054007ff5452019ff8c54005ffd415419ff4854003ff10d3003ff90d3036ffcc15222ffcc55040ff0c95319efd054044ff1855403ffd0d4330ffc414206bf85a3006ffc825006ff51a2041
  | 6 => 0x5052ce3ed3c0ea9641958b9619487f8002c5000e20731fe4668dccd0341b4822310005870a5e700b9787a576881000bed2711d41425834ba93bc53ddba31000818002cb0010ce7a40e688b3e3b93c1bcec577ca800061217b0e37a000d523d1669418c22e71713a70bd733e47e801ac73d2ec7f29d366f500000b380169a924e2aa0008c38183637a5dadd44c0dc2347c08c93c5806287142009ce6932d200029f56c000b6bda59c371e031d1b60c85847b30f43d819c314040d960ff1188b4c92680000396e9269940013c1d021c0020a0003980008b4fb9480027ba6d40f04da09ee370000004b86d4809343940543c426b064929245f88d0fc320971599fa0012b0003234124099200000055c620000d08b21d6d1371851b91c09e5daca87f2fe235c363e20c60e98774c0000047e162d4c001876770d5611a163cc8c002c52f0aa400000000d4941c3966cee43623705a0026ec1a00000078b4354029c000bd636011ab8002ee000eb354028d48001292860020da3d098b714a0610010c0379d7000001891591b87d40029b01e4acd19a6128001dc00046cfa5a5192494e04090005be408b09ff7dab71ff368000219d90821db27cbc848001244000ec8f319442a6c4f6fe44b8002a445c001b97bc588c5ab785e002268008768789a4405b02200011a55e67a4ba740000023cb6f2c924e7f8005b8885f62fb0000002eb0e466001ac9d47ca0000002267a3b1544a76ed2459db7b46d3a115800386001763f22594040f00087e8609d1df176d5c2b21a00013cf78006deab80000042a000000d3a180003cac4994000002ab044e64953b959e0899e346672f7165800000000348000001ec3e10772cb2c004910000006aab210aa90540005a93284d4ef0f8000001b8410f0ccda042cac18000917f050dc700054634c390003406845028992a4c48dade71e4d4f8847000000002330124ac854f60000021c4581c0000002c07c2001f7297426001fd0009f89c40030c5a123a84c2c546fd40038d91b18e4c800000a880049a0003a417495001074608003684f969a7a4b0fa8000380b0f40e7b496cc33575437000ea812b3c25a5040037c0000000002d00102800211588001d933a000cac4a4e685af605b00077400000000144255700001e2005234150006f800401504b2cc93858dcd06828007e0d7c001fa8f000009acb3047199483c000731e0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x35021b3ea14ac990067e569193200dde65b12a001bb58762550a33f93cac904375e329593200cfe872b24001bbd0926940033e2b28c90034ff078d92000d7e212326401af186464c95b3fb00ac90014ff67d895300d7c2f23264553fdd556501af6f83ec6a0006df635494000cfe212b240013f85f635090376292ac99004fd7151930009fee8ab440013f5c546880027e3b2a4a0006de32d8d4000beee2ab280019f94a5650caefa38ac099006bc474da5000dda4293480033f05f645481a7f83c8c90004fe5749a40399f84f2b240519f086564805f6fa16c6a0006ec41d8950049fceca8280013f95d46480835e18c8c980067c619593257edc412b240016f91d624c0033e23cac90007cd324c12031dbcc7b1a84013f45f604c81a7f13cac90006ef7255a3003db86c9824005b71d9324c1d77783ec4a804ddc735192000d7c8ca02400d3f9c1568c01a7e3b28710006dd314da20009faaea34402fb711f635001a7f1bcac9802cff57919207cbf6e0b22a00b3fd5e464c11a7eabcaca1826bf4655230019fe2fb22a601eb11d32480036e31ec4a008eec524da2000dde6fb12a0019f94d56882273f184ac9902cfc578d9208dddaafb12a801b7984635011b6f21ec6aa0067e319592000bbee6a32410d9f10a564c81b6e1826d101467d5295920029fecfb12801bbbd4f62540a33f194ac90006bc561193006cf8a0ab440033fc5f625000e7eabec0a9b0f9c301193086cfc652b264357b1c950500973eaa2ad2001ddc735013000cf82f2b24035bb14b625001a7e03cac90015ec725012046b7a8fb1aa8013f85f624c027e621a649030f9e301193011bd8e4a826001afdd146480067f38aac98004fd379192014cf8a52b260019f8de56480035eaa28d180079d5418d40009fee2ab260073f9cd46880167e2bc8c9014cff755593004978e8ab2602fb741f63500067e38a8c98024fc7455930009fae2a3240017bdc950500027fbb2a498025bc474ca4000d78af23260073f1d9404c0023f2ba8c90005ef725413061dbec831a80013f55e46480035f9048c98014ff67d8954019f8e29348001af584464c00af6392a71000cfc715592003bb8e6a8260057b1c9544c8067e38aad1835ede10d8d40049f88e9b240019f55256480023f2ba6c9007ebc4351a2004d788ca02609f7bdcd32480b2dfa3cc099004fe179192000d7c8e9b24009af119404800fe7b926498007ac7255140009f8cea1aa4015f95d32940033f9bcac90024fc479593000cfcaca8280019f0d856480533e2b2609008cfd764c12000ddee4ab240013f45e56480037618ec4a8034fd47959400dcfea8ab440013fdcd468802f3e28cac90144ff7555920059feaf1b24005fad8132480173e2b2a69014e7d5395930009f8eca1a405bbbd59324815f3f104ac90007eb704c920
  | 1 => 0x17d894000dbac3b1aa83b9f159565000a7e3928d28006dd5618d4000ddc6fb12a90d9f882564c8036fb9a6c90007d8704c930019fce29b4a0b3b7d8063500377729ec4a8034fc0791920009fae2ab260093fd1d36480036f83ec6aa1467c3295920069fceca9c4013b70d936480027f0bec6a8036bc4051a3000bbee6aa46063b710d464c8035ea0c8c993febc2791932568fecf2b2405b9fd5a564c8ba7e1bec498417af32919321dcfea12b28041af50e464c237762bec4aa01cfc379594006d7ee8a34602fb750f63501bf9e292a8a0006ed37d895000cfe832b24001eb91d324804777196c498006df57d8d400bcfea12b240519f49e56480067f8bcaca0034fd57d8d5000bbee6b12a8013fdd156480067f38aaca1007af52919321dcf8aca0240957edc146480067f38aad18024fc47d815261f3c8031a800b1f15d464811b6e18ec6aa004ff7051932029f8ec98240053f09f63500127fa3a6d1008cff724d92000e7cacaa2801dbb4cb624c08e7fb92ac90034fd2795920059f8afb028537b714763550027fb8a8d180076e574c920599feeca026001be58060550067f38aaca1834ff7055a20499fa4fb026401bed8260548036fb9aaca10067e54959205ff9ea49926001b7c8763500067e38a8d1000cfc17d8930009fecea1aa0093f11f624c0027eabc8c980bedf4351a3011f9e4099260d3f610063500027fb8aac904dedf51d8d5419be8e2b1280299f146564c0027eb8aaca001cdf67d8d5400beee29b240ebbb95f62541cfb7aa0c4a80067f755592000cfec32b240013f45f6254c96de23a64a80067e5654120059feae93480033f05f625515a7fb3cac90006ef43d895028cfa852b2400d3fc1e464c9267fb826c90014fe765412000cf8acb026401af909468c0035f232a09816eec564c9202dedea52b264017bdc9504811b5f21ec6aa02e7c565512068bf6e0b128001af546464c0036e98ec6a001cfd47d814300cfe2f2b26437771cd62500035f10c8c98004ff765512000ebee6aa2a001af90a464c1267fbb260900076e564c92006cfea0a34a00d3fdc1268c02b5e2328c90006be465893055edc402b240c7af942464c0027e83ec4aa056bf409192000cfcaca82600b1f15d26900035fab48c98106dc534da405cbbae299260013fdc5565081a7f23caca0005df735513000dbc4fb1a80013f55f624c003760bec4a801cfe7355a2000cfaa72b240015f95d604ca377623ec4aa44f6f32959321fdd8a493480973fdd9504801adf382a8a0004fd379594273edea2312a00b3f15d468c15777b28c4a8004fe575193000edaa9b12a0093fd1e36480027eaba4d20026bc4650930409fee4ab26401af90646480067f38a8c900a67f569593000dba629b48001bb98c62550b35fa0c8c9900cff17d8953049fecfb22a001e75536
  | 2 => 0x19f551568818f5f1bc8c981deee32d894300e7cac23264c52fd9e464c00e7e39aad100067f419593200d784f23260853f15f63540037623ec4a8014fe7255a3046d7a8fb1aa8013f91d36480036e30ec6aa3febd529193200cfeeaab264019fdd556508035e0bc8c98314ff679193000dd8c6312a8053f09e565002ebe2ba6c90004fd37d915046dbcc7b1aa8019fd86564c9afce206c6a0006ed6318954039fe6fb02842fb71536350003e71b26490004fd17d8930009fae2ab24007771cd544c0067f8bec0a1056bf4691920029faafb1aa4073f0df60508036f886c6aa19cfc47d894000cfc212b2640d3fc1e56480a76f29a6d28006df51d8d40009fa4fb02a801bbc43625401a7e03c6c90036de304da4002bd8e4aa2413beb15062550036fb9a8c9003df4714d92000cfca72b284013f85f604c8027fb8a6c903ffaf209193213b788eb1260053f9c9468c0027fb8a6d10006df63d894000df021b026401f318f62551d776086c4a81679f43919328e9feecab28401af01e464ca0b5f98c8c9901cfc765413000f388e9926105af14e464c96afdb82ac98006df634c940539fe4f2324001bbd4926900027e93ec6a030f9c4018d40019f8e29b440013f51d3648002bf2bac4a19467f219592000cf80f2b264c17edc1624c00377086c4aa0c67f5155a3092bdee4b1aa4016fdd16254c03af296c6aa0367e5055a2000bdee4b1aa01bbb947625400377b926c90004ff7654a4000beee2b22a08bbb0cb62550027f2bc6c9001cff67d8d406fe7ca4aa2803f3fdd1464808e7e83ec4a80bedd41d8d40009fee2ab280b37edc1464c0027f2ba6c9031ebc5091930069fce09b4410d3f49e564c8067e0bcac98005df7350a3010be8e2b1260013f45f63548ef77316c4a1804ff6750950019f8e29b480af9fc1e56480067e0bec6a00dcfd765013000dba649b4a0017ddc5604c803778bec4a82cefa30d814303db8c699280019f95946480b35e2a48c99006ef30d89507fdba6f232640d3f8de464c2377621ec4aa004ff724da4000bdee4a9c40b5be8c36054c1a7e3828d180075e5218d54009fee29b4a0013f95f624c17aefb92649802f3f745515000ebe872b26401b7987635001b6fb9a6d1008eee62d893000ddc63b12a823f3149324c0027e8bc8c90024fe7455a2023dd8a4ab44001b7dcd46880033f2ba8c90006be46509301bdb865b1a80019f984564c8035eb0c8c98034fd7051a207fd784123264013fdc52690003af2ba64981457f6715920459fee4ab28401af11d364800a7f93cac98016ec624c9500adda84934804b3fdd1565015f3e084ac90005be474c120409faafb12a60d3fdc13688016be2ba6528036ec2049a505dbbee29926001bb48526940db6e31ac6a90067e574d920049faafb02a8053f1d94048117b7296c4aa004fd
  | 3 => 0xaa4367e279593200cfca52b2600dbbdc926940067f38a6d2005eed5249a5020d78869b480ffafd4a464c8033eb08ac90034fd278d920019fe2fb12a001bb98c62540127e23cac990063e561193206b78e0aa280019f44256480027fbb2a69022cfd47d8954009feeca9460fbe78c8464c8036fb18c0aa0067e479592028cfe852b240477bd9f6254117b7abec4aa0077b705515096dbea9b1aa80dfa081504820bcf9bc8c99034fe7051a3011dd843b126001bb58f6255016be2ba64a8256fa20d8142069fc4f1b24129bbd4362551f7ce3988c99004fd3795940029d8e4ab46001af90b6454c027ea3ec099005be4758132009fee6ab284073f9cd56509173e292aca14376f27959328eddec8312a8013f4df62550037730ec4aa004ff715593200cfcad1b240013fd9d32540036ea9ec6a0206ef21d8953009fa0fb22a51b7bd9c625505f6e20ec6a004ddc73551200ad788723240013fdc5369006f6e29ec6a04257f679593246d7cc6aa280011f95d26900167faba8d10006bc7455930a0f38a831aa8016fdd163540033f2b28c99034fe7051a50019f82fb0264013f45f6350802f7b92aca0004ff7255a4000bdee4a024041e7cca464c10377196c4a98067c569193246d7c86ab28729ebd5362550036fa1ec6a90debf4351a3028cfc852b24001af98a464c01a7e3824d204375c3295932009fc2f1b240019f0da564801a7f3824d28004ff7650e50009fa4fb1aa137a751f635504ede3a2ac98006fb705192011dd8c4b12600b3fd5f625000e7e1bec8a90079f735514010be8e2ab2600d3fdc1468801a7f13c8c90007b8705514000cfcac98240873f0de564c0b6be2bac099005ef725915394ddaa1b12a8cd3fd9e564c00377b92ac981b6dc43d8d522dcf8a32b264016f91d36482273ea1cac99006bf7451930009eee29b240017bdc96054cdf5e21ec8a90063e569193217dbe81b1a80659f14e565088ef6392c6a811eef57d89509bdbaa3b1aa801de1c1545403777a92ad1000cff179193200ddec6312a0013fdc9564c0033f21cac90024fc4749a5009bb8e6a02400b3f15d464c0163e2ba8c99055bc474c12056ede422b240053f51f605081a5e3b2a8a000cf47155940039f8e6a34410d9f886564c8067e0bc8c904367e42959321bdbe8fb1a807d3f0de464c0033f8bcac90004fd17d8142029fce49b480016fdd1505000a6e9bc8c99006fb705594000bdee4ab260092f11d3648002bf2ba6c900076c574c92000d7cc323260013f5c556900027f0bcac902d4fd37d815328cf8a4934a0013f5c5369400a7f93ec6a0006ef62d815482dbe6f23264519f486564819e7fbb2a0a0004be474d920019f8e2ab2604bafd0364540c6ee39aaca10bedf41d8d4000bdee4ab286013f4df62541af6f286c6a00bede07d8d40009fee2a34400
  | 4 => 0x9b22a03bcfd4154500027e93ec8a80067d5455a3000db843b1a80457d1c5635401a7e382ad1046eed41d89543ccf8aca1a4001bbd8462540139fbaaa8a00067e5195920009faae9b44001af41e464ca273e984ac99006dc6218d5400cf8ad3026451dec8256480037bb8aac983fcff745193257cfc612b240033fc5f63540067a38a8c9018edc6358d422cd388c99261013fdd9464ca273f98cac99006ec7255a300dbdece312a007371cd565080377b1264a8004fd715593297dbec831aa801bb0c76255016be2ba85283a6fa50d8152a0f3e8031aa853b7cc936940037631ec4a8126de53d8d5086cfe4f2b264019f51e56480ef7631286a808edd324da20009fa2fb1aa905af4c2464c906de3a2c0a9b1ebc1091930019fe2fb22a035bbc8362500163e2ba6c9022e6f57d89541dcf8a32b280519f9492694037f5a86c4a8006fb7055920009fa2f2b260013f5c52690066fa38aaca03af6c50d895013d788323260fbeb148464c88f76216c4a8006bd5451a2020d7e6523260017ddc5564c0033fbaaac98004fe674c94000dbe87b1aa0013f85f6054d467f93c6c90006ec07d895413d7ca923260013fdc95650c127fa3ec0a9c376c3295932458faafb12a80d3f9d9548821b3e93cac99024fe745593082d7aa72326441af14e464c1667fb828c981467c42959209a9fecf2b286af9f89e564811b4e31aa8a0005be474c94000cfaa2ab48001bbd0362540a3b7194ac90004fe6750d5249df441b0264013f91e36481cff4280c4a8004fe5751a20069f8e0ab48001cfd91545416a7fbb2a0982ae7f6215920069f8e0ab2871bbbd5362550036ea8ec6a00367f7555a20009fee0ab28637b798f635025b6ea16c6aa006dc6218d40009faae9b24001bb18a60550035f234c0994276c321593200d7ec223264013fdc9464c00377b1284a8234fd57d8d5406cfca0ab46001b798763550027fb92aca00067c41959201add843b12811bbbd0362550a73fa9cac98006be4391920019f8e2a324001e7119324c0b35e20c8c99315bf679193000dbee6ab2600d9f9415690002dfba2ac980a67c565593002f9ee699240019fcc65648002efb9aa89042f5f301593200eb8ae992603b5f15d625000377b928c9935ede40d8d40019fce2a3264013fdc9568c2273ea9cac99024bc7455932029fe4f2b286019f5065648003edb826498014fc27d815400ddc43b1280013f51e564c0035f236c49809ebf469193084cfec62b264093f1d1568821b3f1bcac99034fc765523000bbee6ab2800daf901468825e7fbb2aca1806dc17d8d4006dd8409346001af90f64548067e0bec4a9b3dfb7055940059feaea326001bb584625406f5ea1a8d18006ef10d895400dbc631b240ffaf086464c8035fba28c99006fb6098142649fe6f23260019f15d464c80e7f9bec4
  | 5 => 0x6e206c6aa034fc705594255ed8402b24001bb85f62541eebfba2a8a8004fe57d894000b7ee8a9c80019f102564c802efb9a809822eee52d8954009fcae9b480cfbe903605511b6e196c6aa02cff5751a30009fa0f2b28447bb0cb62540036e83ec6aa006ef42d89501bdbe61b1a8001af958464c8033f28cac992bf6c209592028ddc64934a0cf3f51f60550a37790a4d280dede43d8d40009faafb0286d7b791f63500033e2b28c9944e7e439593200d7c8e9b4a1319fd4e5650c027e83ec6aa235df3798154069fcecaa4602fb7dcd468c01a7f83ec4aa006fb609813216ddc6493460af9f082564820b5e18c8c99106bc32919305bdbec0992610d9f082564c81b6e9824d18004fc7650930019fe2f2b24015af106464811b6fa3ec6aa005be474c950589fe4f2b24059b7119324c116f6392c6aa007af725514094dd8a3b12a87b3f11f63501d777186c4a84dedc50d8d5400dd887b12a0937edc13648002dfba2ac990feee3249a4040bd8e4b22a60d3f1d942940773e2928d282be7f6598152029fe4fb22a6596f11d604ca5b6f2bec6aa004ff705593200d7ec3232613f5fd5f62550027e3b2a49808edf324da20009fc2fb1a8001b714763500033e308ac99156bf4151a50409faaf2b26401bbcc762552575eaa6c8a9035ec704c920049fe8e9346001af906464c8027e33a64a00076c564c920019fce2934a08bbbd1f625525e7fba2aca1806bf745594302bd8e4a8241319f54e5650c03f43826490474fd27d915200dbec6b12a81bbbdc956881dafdb82c6a8004fe5791930049fe8fb02a437b7ccb63500167fabec0993febd4291932069f8eca9460013f85f6454c027eaba8c9804edc438d920019f82fb22a66db794f63548027eb8aaca1034fc765522006bb8ec9926027afd0a464c01aee3826498025bc474c940039f86fb12a801bbdc9564c803761bec4aa014ff279193017fb081b1a80013ddc5564c0035f2b08c98006df50d8d4045edcae312a8556f11d32940035eab48c980067e619592000d7a4f23260817b1c96054c8f77906c4a8006bf579193000cfe0f2b264073f0de5650837762a6c4a80067e179592000dbe21b1a80013f55f6350802fbb8ac0a1034fd7049a3045dd8c4b12a81fbb50b625023b5fa16c8a9006f4714d9201bdbece31a8001b7d0d268c15f3e184ac90034ff07d89538dddca9b12a82db74ca36481a7eda00c6a0106df314da40039fceca8260353f5d940480027fbb2a89801edc6354d4020f388699480ff2fd9c464ca433faa4aca1006de17d8d54249fee6ab26041e7cc6464c0036fb1ac4a001cfc37d91504a9feeca02407f7d1c56054c1b5e2028d2803df47151920009fee6ab240073fcde56500127fa3ec4a8385bf7555140069fa6f2326001b7d8d6055237d7a06c4aa004fd574da4025d7ca
  | 6 => 0xcfc832b24001af984464c8067f8bec6a1006bc519193200d7ea523260073f0df62501af6fb1cc0a1baf6e50d895082d7ca72326401bbc5f62550035f3108c98466dd43d8d4216dbe651b24001af90d56900037783ec4aa006dc635895428cfc0f2b240019f4de56480036e30ec6a000cfc17d814332af8aeb02840d3f1d943940033f23cac99126dc6358d5000dbcafb1a80f5cf10d545408afa38ac8a830e9f6418d400ddd8afb12a0019f042564ca627f1bcaca1814fd37919328ddda8fb12a801b7887635525baf2a6c6aa004ff7355a4002bba6f23264053fc9f605506a7fb928c9012cfd765414000df2c030284053f1c936940873fa8aad2006eed07d895025b78e8b1aa105e7cc2464c80277b92aca02379c43552307ff5865232640b3f15f604c81a7fb3ec0a9024ff479592000cfeeaab2808bbbd9c625500a7e13ec6aa3fcfd27919321fdde4293480053f4df604c8036e03ec6aa01ded2795932009fa6fb02840b3f15d36480127e23ec0991467f2095920069f8e0ab26401bbd8c625500a7e13ec0a18076d541895000bbee6b128001eedc154500033fa04ac9025cfd27d815200bbee6b22a51fbbd94625501a7fb3ec0aa006ef725594000deee29b24001bbd8f62550036fb9aaca02369f47d8d541bdb863b1a80ffaf8de464ca0b5fa9c8c9901edf364ca5089cf8632b264013f85e564c00377320c4a8424ff67d8d5275dd861b12a083afd076454c1a7e3826d10004ff6750d5275ddec5302a4013f51e5648002bf2bac6a14367c329593200dda43b12a601b709f63550035faa48c98036bf7451a50019f8e2934a00137dcd56500ee7fb928c9944e7c43959328dddc87b12a801b3d8f62550033fa30ac99004fc674c95000dd8c3b12a0093fd1f6354a53b7a86c4aa004fd7155a208e9fee8ab28401af946464c8027fb9aad1001cfc735594200d7a8323260053fd9f62540027f2ba8d180b4ff734d920019fce2ab2640d3b1d932480037710ec4a84b6dc57d8d5445bdecfb12a8559fd5256500b73fa8cac99034dc764c93013dba869b480db6f5c5545002f3e29cac900bddf6718d40009fa2fb1a808bbb8cb62550027f33a86a800cff17d814386cfaa52b26401bddc5464801b771024d280d6ee62d8940029fc6f2b264019f94946940035e232c4981b6de63d8d52049f88fb12a0033f1c5565000a77b3ec4aa235dc735815428ede432b2400d3f5c156880037db04c0aa014fd57d91520dddc0fb12a02d7b1c9548c01abe382a8a8014fc7251a3000eda422b2408b9f98954540036e308c6aa004fe17d895006d7c80a3460abdb14062540b73e2a4ac990067f611592000dbea7b1a84093fd1f624c1fedfb388c99034ff67d815313d788ca326001bb1c956502277693cac99006de07d8d5400d7eac2326129bb143625525b
  | 7 => 0x624c1874fb188c9846eee40d8954009feecaa2652db7953635500a7f392ac9831f9e3091930009faaf232648bbb087625518bcf9908c98006ef47d895041b78e8b12a6d7b7083635008f77296c4a8006f4715593000cfe8f2b26441afcde464c2273fa9cac9902cff579193296dba83b1aa8af9f902564818fce1848c98006ef621815424db8c6a828001bb887624c0027e9bec8a9075dc735522089eda4f2b26459afd1a464c80e7fb3ec6a800cfc715594287bbee6ab264053f9c9369403f5fa0a8d10004ff7455a307fd7e4f23264013fdc55650c1a7e3b2a7201deec52d8943049f8e8ab264033fc5f6054a77b62a0c4aa00cfe7155a4006db8609b4a00d3f1d9329000b7631284a8406df32d8d4245cfca4ab284013f41f6250c1a7e3b285183febf209193223dd8c4b12a00b9f159505022ef7b92c6a101cfc37d8950019f82fb128001af11a604c803771bec4a80367c5055a3025e78c8aa2a001bbcdf62550033f2b2c099034fc7051a50009faafb1286cb3fcde564c0036f296c6a01467e2195920029f84fb22a6c5e7cc4464c0027bb8a8c900079e464c93000ddec7b12a001af95e464c8033e2ba8c90004fc765512017f3ca9b1a8001af89e464c26fcea3ec6aa004fd1795940069f8eca9c4001b71cd464821b3f904ac9916eef5295932039da4f2b26463771cd60508027fbb2a6a03fcfe2791932009fa2fb22a6093f1d950502273f18cac99006ed07d895400dbc43b1a80fbafd8c464c81a7e3824d18024ff47d8d5000cfac22b26401af142464ca27ae21cac99004fd57d8940029fe4f2b280013f51d36941ff5f2948c99107bb30919307fd7e432326401b749f63500127e3a2ac90005be474ca50239faeca8240019f0de5648116beabec4aa0dddf67d8d40019f82fb1aa8073fd9f635501b5f2028d2800cff178d92000cf88d2b240013f85f6050c027fbb28528006be46d813200ddcc9b12a001bb45f62550036fb08c6a00bedd42d8d4000db8e6ab280ffaf89e464c803b6a88c4a84b75c54d8d54009fa8fb02a4655f15d63508033e230ac99006fb10d815400dbec7b02a941d795063550db6e31aa4a00ee7c5295940879fa4fb1aa407bbcd932480027f0bec6a946f6e54d89544a9fa4fb0284013f1d9534820b5f9bc8c99006be4191930029f8e4ab2604bcfd0154540033f2b4c0990a67f50959308df5887b12a80dbbdc926901ff5f1948c9944e7f379593269f3e8231a80013f95d36880b73fa84ac99006ed61d895014dbaa69b4a001bbd4b6250c027f0bec8a902cfc574da20069fe0f2b28601afc1e464c8037698ec4a80067d0795932009fa4fb1aa807f6d81324c0033ea8caca1034fc705193214af8aeb1260053f09e564c237d62a6c4aa39feb5018950069fa4f23240053b1c9564c0037721ec4a8024ff474da5
  | 8 => 0xc5218d54009fee2a32648b3f55f625501a7f83ec8a9806fb10d8132039f8e6a3240013bdc95650c0277b92ad184a6ed51d89547fd786523264156f11d364825377286c4aa004fd3795920039f86fb02a8179fd46564812a7fb828c90006ef725192086cfa432b2640d3f9c136940133e3b2a8a8034fe704da40059f8ae9348077bb1896250c5f6faa6c6a0006f7715594000d7ea323260013f51d36880067e0bcaca18067e519594046f3886aa264237b1c9544c11777216c4aa22f6c525522000bda4f302a8013bdc9564c0033fbaaaca1befaf2011932059feafb12600177dcd5488236f7b92aca1004fe1795932919fecf2b2840d3f4de564c01b5fa02ad20004fc7655130009fece992809b7b5c5324826f6e296c6aa0dedc6358d401bdbca7b1a80015f95d6050a377723ec4aa01cff379592006bdce0992400b3fd5f605080376a1ec4a8006dd21d8d54069fe0fb1aa801e71cd545004776296c498004ff7149a5037d7cc9b22a5117bdc9564c9d777286c4a84df5c52d8d5400afcaeb12800db70c136902273fa1cac992af6e5018950069faafb12a0013f45f60550037630ec4aa185f47158142009fa2fb028737b7d4363550ab5f2a28d2802cff5751920059f8afb1a84d1be903605098f5fb24c0a1824ff4749a50069fe0f2b28539af5536454c036f310c6aa4367f21959320dddca9b12a0017bdc96355003e6318c4aa004fd37d815404cf8c8aa2a001b7958635000e7f39a8d2800cff17d815428cfe652b2412d77d9c6355003d7218c4aa004fd47d893031db8a7b1a8401f3d8f62550027ea3ec4a9ba5fb705895000b7c8e99480053f9c9565000e7f23caca186eed51d895000ddc43b12a8c5afd80464c0067f8bec8a94247f679593245dde41b12a8011f95d464c8037798ec4a84366f279593220f706123260033fc5f635503b6f98a6d1011eee42d8950029f8e4ab480013f91d369401a7f3824d18006ed41d895000db8c7b12a801bed826054c027fbb28710036de304da5044be8e2b02a8fb2fd9e464c80b6e3126498006df735594300ddcc7b12a0013f85f63550167fabec0a19a4fc2791920009bee6a324001b794763500035fab08c99004fd279594382d7e8723264477b1c9645404f5fb388c9800cfc178d920019fe2f2b2871bbb107625500a7eabec0a9006df534da40009fc8e9b441353fd9f6454c027f0bec8a822e7e52d8954009fae293460f5cf90d545400376b08c4aa1476c524ca506bdbc41b1a806faf1916454916f6392c0aa024fe745593281bdee4a326401b7d4f635025b6f216c6aa014ff27d8d5400d7ec223260013f99d42540135fa32a9100067e561813200d7c8ca026051bb10926940027e83ec6a90057d5798132009fa8e934a0013f41e464c8373fa8aad10004fd179594200cfe8d2b2400d3fc1f
  | 9 => 0x12fdd1564c8036f310c6a0236df31d8d5400cf8ae93480033f9c5568801a7fb3ec0a1806dd17d8d5400df2c0302650d9f4de564c91bce238c6aa4275c321593200db821b1aa8dd6fdc554500ee7ea3c8c99006ef52d894087dd8a5b1aa40d3fc1f6354a273693cac99006ef32d895400cf88d2b264013f55d46480975e21aad2020ebe54d915300cfaa32b24059afd02464c8035f30c8c99006f9601815300dbc21b1aa801bb45f625400a7e83c8c90004fd37d8152009fc2f2b280093f41e56500035ea0ec8a9a06ec20d8953009fa8fb1aa4013fdcd4648277d7a00c4aa0057e575192098d7c872b286f35fdc554540035f0848c99006dd314da50059feafb128649771cd64540035fab48c99004fe57919322097ece23260013f45f645401a7e9bec498024fc479592000cfca72b240013f41e5650c035f232c0990067f3095920059f8aea324001bb984625401b7d300c0a9007cf631895405d78acaa28077bb90b6250c0e7f9bec4a82be7f651815200cf88c2b2400bded81545400a7fb3ec498004fd07d915305d7eacaa2805b9fd9c564c82f3faa4ac90004ff7155a40029f84f2b286c7afd906050e1a7fbaaac99004fc7654d4200ddc2fb12a8ab9bd88564801b3ea828d282a4ff679192000d7c0f2326401db48656480936e21ec6a801cfd479594300cf8ac9b240073f41e564c05f5f2a28d180067e564d92000db8e6a3440013f41f6254c035ea8c8c99106bd3191930049fce8ab24001bb487625400377b26c4a80bf9f41d8d40009bee6ab284019f952564c81abf382a8a831ebc07919306bdb8a1b1a8035afd0946880067f8bcac98006ec6318950009fa2fb12a8d5be9036050c033ea1cac903febe2191932029fa0f2b240019f95940480036eb08c6a02be7c079592003bb8e6aa264019f552564c8036f2b6c6a000cfc17d8943009fa2fb12a001b7d0e36481027e9bec4a9806ee611895445ddeafb12a8013f51f62541af6e086c6a0006bf1791930019fce29346051de08256480167faba6d10006dc5618d409bbbee6b22a729bb54f625501b771024d2006eec51d8950069f8ec994a0073fcde46482027e93ec6a125eef6018950009fc2f2b2860d5f1d954540027fb926d2800cfc1795942009fc2fb12a937b754363550027e9bec4a000cfe715592006dbee69b4a097be88360548035eabc8c98004ff7151a50039f86f232403fbb90926900035e236c0993aeef6218152009fa2f2326001afd52464c80376316c0aa006de31d8d508dddc83b12a801bb44362540035f2b48c98007af521193200dba43b1a80033f05e565015abfb3cac90004fd27d8153019f82fb02a4013fdd1564c8127e23ec4a9ca6ee51d895400dde85b12a601b758463550027eaba4d18006dc62d8d40059f8af232640d9fdd5569000a7e3926d2050f5
  | 10 => 0x9906eed52d89504ebdee2992400b9fd5954880027eb8a6d1022eee62d895446f3c87b1aa88b3f55e5650a0b5f9848c9922e7c625515000cf8ac302648bbbc8762550033fa04ac990079d4118d4097b7ee8ab28601dbdc95454003afa18ac99006de27d8d5400de8e2ab2808db7d9c635525377a8ec4aa024fc474da5006d7ee8a3440013f95d464c8c76f98ec6a1006be4618132049788e9b4a037b7cc7635001aef382649800cfe714da2000d784323260ab9bd946254013ddb02a8a0006ef524da208ddda87b12a801af505469408f77b38c4a800cfc17d815400cfa2f2b26441af4de464c00e7e1bcac9006eef50d8950009fee2a32610d9f086564c8027e93caca016e7f549593200d7e212326127bbd4b6354a537729ec4aa4a5ef725915296dba8fb1aa91d9f94b64548167e2bec0a182cfc5791930009fc2f23264033fc5f6350217b7b90ac99006df61d8d4096f38a9b1aa8013f91d26940036e93ec6aa0eebd5451a50039f8e6a34a0053f8de464c9a7cf2a0c6a00067e5691920019fe2f23260013f49f6050c835f98c8c981bebc465493023cfaa4ab4403bcf15954500036e0bec6aa00cfe7151930049f88e9b4400dbbc8136880039f2b48c993ecff6791932009fa4fb22a6973fdc15648002f7b9260900079d319193082d786123264015f95d32500127e23ec6a83febe209193246bb8e6b12a801b7c5f63500035e2b48c9835edf631814300cf8ad2324103b710f6250c0377986c4aa0347c765515032cfea32b28401b7d8d50500f2be2bac4a1834fe7055a407fd7a6f23264013fdd9424c01b7d300c0a98067e61159207fd7a43232646faf9536454a273e98cac9944e7f309593225d7883b22a001bb1c9564c217b7990ac993f7af321193200bbee6a8260053f9c956900027fb82aca14367f329593200dbea5b1a80ebbb84362540033fa30ac90166be54919327fd7e652326435bb90b62500036fb0ec6aa006dd10d8d5400d7e432326001b318c625521e7fb9aac99007cf624c930019f8e2ab440ffeb14a464c8067e38a8c99034ff67d814200d7ea1232641b3bdc956480067f8bec0a98b6ef2149a3000dda6fb12a8659f15956508173e2b2a09000cff179192000cfe8d2b264033d1c5564c11a7fb9aaca1805f77158d50009faafb0264373f41f63500035eab08c9900cfc179193200cfe8f2b2412fafd0f6454dafcf206c6a0004fd715193200afcaea14a0017bdc954880a23fb38ac90006df735193011bd8e4ab26099bbd813248002f7b92a8993ff9c3291932019f8e2a3460013f45f63540835f1948c9801cfe7650130019fe2f2b28459af102464c81a7f382ad10005f77158930009f8cea12a0013f55d468c0036f316c6a0106be079193000dda43b12a8019f0c65648027769924d18004fe17d8142019fce2ab280
  | 11 => 0x2fb22a0013f49e464c0ab3eaa4aca041ddf379193200f5c87b12a80dbbdc9268c0037631ec4aa3c57d71551502cb78e8ab264179f1525648003b6a8ec4a8014fc7255a3000ddac9b12a0013f85f6254c0e7e1ba4d20006df27d8d5484ede402b2652db790763550037720ec4a805e7f539592000d782f23264053f09e464c0835f9848c98006bd109193200dda64934800177dcd60550067e38aaca1cdede51d8d5445cd8c4aa2a12db7d0b635500a7f3928c98005ef7255120019fce2a34410177dcd464c81b6f1826d1011eec21d895000cf8ad1b240013f4dd269023776a06c4aa004fe4749a307fd7a4f2326443af553645411bcf238c6aa1e67c529594309dbe6d1b24001b708363550036f93ec6a02b77820159209bdbca5b1aa8175f15d464815f3e204ac90005dd379815400cf8832b264053f9d9404800e7f9bec8a9006df434da5098d78872b28601afdd1565000377b0ec4a8014ec7255943989feeaab286013fdcd56500037c086c0aa004fd079593200d7ee8ab284019f906564c8033e0bcac990c6dd53d8d50019f82fb12a059b7d0d464ca3e7fbaaaca1034ff07d8d4263d7c41232600daf50156900035e28c8c98317bb301193000e7aa8a8280033fc5f63549ff5e9048c9948cff67d915228cf84f2b240073fcdd26900027e3b2a89902e7c565513200bbee6b22a0053f41e36480037723ec4a8004ff765494000dbe41b1a80013fdc556880027fba2ac98006ed10d8954969bee6ab286016fdd163549f75fb108c99006bd219193000de8e2a32402fb790b63500036e31ac4a0006ed2149a3029dbe629b4a01faf95146880027eb8a6d2004edf308d92082d7a6323264033f1c556900036f8bec6aa004ff7650a30009fcafb1a800d3fc1e564c8035e8bc8c9900cfc17d8d42599fa6fb028601b708763550035f21ec8a8006be17919307df3ee62326483af10b6454c027f2bec6a10bedd54d8d4000dd8c2312a8fbe70c8464c803769924d284376f209593263d7861232608b7bc9e605511b6e186c6aa02e7c565413000d7ca523260033f05f6054cbe7e13c6c900067e179593261d7ec62326001afc9e464c0035e0848c9900cfc17d814200d7ea12326001af55a464c8036f316c6aa036df3049a3028cfa652b240019f442564c8027eb8aaca1806bd4151a3000ed8e4aa2a0e53fd9e56500033f28cac984347f671593200d7aa92326001b745f635011bcfa3ec6aa44e7c3095932039f8e6ab480016f51e604c80e6e39a8c9001cff3749a50019f82f2b26449b798f63540036fb9a8c99006dd31d8d4200df2c0302860d3f9d9438812efdb82ac90006bc465813200b7ee8b02a601af184464c00e7e39aac90006dc7355942009fa8fb1aa001b715b63500027f0bec4a000cff17d8132009feec99480addec8056480033f2b6c
  | 12 => 0xa7fb3ec09912e7f5455a40849fecf2b26401bbdc956508027e8bc6c9002cff574d92000db84fb1a80053fc9f6054c037db04c0a198ede43d8d424697a8fb1aa80d7b1d932480a33e83cac9004fcf304c92006f7080a0260013f5c5568c0035f20ec8a8006ed63189506abf6e0b1a812de7d0363550033ea8cac9900cfc7151a5000cfa2f2b2404baf19164540b777a92ac9922e7f57d8954019fe2fb12611bbb1036255002f7b92a91801eec364c9201fd7e852324001bedc1364823777a1ec4aa036fa601814217d7e82a346001b7d84635502f3fab4ac90026bc465513200d7aa92326401af442464c0036fb9aac9920ebc64591531b9fee6a3260499f54d568c01a7e3826d20006ed63d895000cfa8f2b2651b9b55f62550a3772924d28005df735513245dd841b12a905af50e464ca5b6fa06c6aa4df5f50d8d5477cfec0aa2a06f6f1d1635481a7ea3ec4a031ebe109193000d7eaf232651f3f49e56508b35e2328c99006dc62d8d54029d8e4ab280013f85f60548027e83ec6a116e7c50959328f9fc4f2b284edbe9436054c035eab08c9801cff37d9150009fee6a34a049b7cc36354003760bec4aa404ff735193200db8c6b02a92db715363550835e83c8c98034fc7049a50029fa8f2b28441afd0e464c0027eb8a8d284ce7d549594300df6e0a32611f9f54a565080e6fb3ec6a001ddc7350a30019f82fb1aa4093f9d1568c00e7e39aaca00067c574d920009fee4a3460013f5c5364801b7d300c0994367c279593221af8ae9948027afd06464c0173fab2a918004ff7650d20009fa4f2b260013f45f6250c027eabc6c90006bc6211930009fc8fb12610fb7ccb63548036e296c6a0006dd61d8d4000cfcc32b2643b9fd5a56500035e2bc8c990367f7555a30119fa0fb12600b3fd5f635080376326c4a8004ff7654d4200ddec3b12a909d78c8564c83777a8ec4a800cfe7149a40879feecab264019f10e56480027f0bc8c98006bf61919328abde4f2b264013fdd9548805f5e2128d180067f361592075dd8a1b12a00b3f15f62500036f0bec6a0006bf745593000beee2b02a6053f9d9304800b6f312649812ebe64d915017fb681b1a812db7d0763550036fab0c6a0106df324da4000d7c8ca9261219f5525650a2f6fa1ec4a1806cf6318954069fce093480073f0df60549d77603ec4a80073c561193200afcaea32652db791f63551b35fb02a8a0244fc479594002bd8e498240053f4de564c802efb9ac0a102cfc5751a209bdbaa5b1aa8053f09f63540033e30cac90006bc569193220d7aa7232612f3f4df6454d5f3f084ac900bede54d8d40029f8e4a326001af118604c86af6392aca046f6d57d89543bbd8e4ab2860b3f15f63500035e3148c98014ef67d895000dbc65b1aa801af586464c88f77196c4a816e6c564c920019f8
  | 13 => 0x5000dd8c2312a001be580605480376186c4aa0067d319592000afcae992a00dbb481368800a7e392aca011e7f5255a20059feae9b480013f85f60550035f8bc8c9900cfc714da5011f98c49926001b78c763550036fab6c6a0014fe7255943a1ebea031aa8099f991545400377a96c49802cfc5751932049f8e8ab460fb6fd9e464c80376a3ec4a81dcfd37d8943009fc2fb128641af0de464c0127e23ec0a9806bf745593200bdee4b02a92db711f63550127e23a4d184767c52d915200d78ac232640daf101468820b4f9bc8c993ecff67d8d427ff3c65232641bbbd5362540027fb928d2802cfc57d8930029f84fb22a0019f545568c06b5ea128d10236dc6358d5428cfea52b2410bd710c564c803cf23a64983febc379193220d7a652326001bbd90625400376312c0aa006dd56d8d407fd3a6f23264013f51e36480036631ec4aa124fd07d8d5000dbe41b1aa827af10a464c0027f2bc8c9001cff37d894082d7c612326401b744363500033f9b4ac90034fc7051a2013d7e812326001b7984635500376b20c4a80d4fd07d8940039fa0f2326137e7d53635504777906c498416be319193200cfec22b2641bbb54f6254002efb9aaca14b6dd40d8d5402bd8e4aa440073fcdf60550975e232a0980079d41d8d40049f88f1b240018f15a464c9837d186c099024ff47d81320dedea9b12a0096f1d1539023f3fa94aca11dcfd47d8943049fe8f2b26541d715063550067e0bc8c984367c3795932009fae2a34600b3fd5f63500167e2bec4a181ddc7355230009fa8f2b264033f1c5564c803ce9888c98104ff7451930009fa2fb02a4073f9cd56480033f2ba4d2022f6c571895400d7a2f232600db7dcd369011e7e2bec8a8006df63d8954009fa8e934608db7d5f63550377629ec4a8004ff7655230009fa2f2b286013f99d32540025f23a6d2846eef41d895499cfea92b2860b3f15d268c0027e33a86a82d4ff705593075ddc81b12a0033f9c5364801a7e03ec498024ff47d89530dcf8a6ab440053f91e5650a3677b92aca1006df639815400ddc63b12a0799f1595650dff5fa148c9949edd53d8d5204b78e8a828001af505468800a7f3928d28004fe1795942019fe2f2b26401afd46464c8835f21a6d20006ee63d895475dd881b12a13bdb95062550027fb8a8c90014fc27d81538ddd8a9b12a801af55e464c8033eb0cac9901cfe7355a40009fa6e934a0073f9cd464825b6f206c6aa317b8301193046dbca7b1aa8013f51f6054df37d286c0aa2b76e32159207df5864232653debd50625500377b12c0aa0bcdf735193000dda63b12a8013f8dd26940036f18ec6a000cfc714d920529fecf1b240179f15956480167faba8c994a6ef53d895440dd8c4b12a65b9f159564ca37b62a6c4aa20ebc40d9153069fae09b4410d3f89e564c81
  | 14 => 0x126900035e236c498006fb705593000db8afb1a80033fc5f625500a7e3b2a0900067e5295940019f8e2934612db710b6355227af984ac99006ec725594300d7c86a344001b718e60550f33fab4aca1806bc529193025d7887b22a059afd9c464c8036f90ec6aa11eef21d89500dddaa9b12a10d9fd4a564ca627e9bcaca1834fc7055a307ff3a6f23264fde7cc0464c8835f18c8c9801cfd57d9153009feeca9c40013f45e464c8067e0bcac90006be611193000dba649b4800d9f14156900027e3b2a6a0006dc6118d4000d7ac223264013f8dd26900cb3fab4aca106f6f51d895020d7ea72326137b794363550067a38a6c904c6df6518d54009bee6a34400d6f1d954500033f884ac990bedc42d8d401bdb886a346001af95a464c80a7ea3ec6a10c67c5255a30049f88fb1aa441af94e464c0039e2b48c99034fd57d9150009eee2ab2805b5f15d464c80a7fb3ec4a18067e5255a3006ddc40934608bdb149544c81a7e3b2a52001cfe735594000ddcc3b12a08d3f51f635511b6f996c6aa0dddc735594000dd8c4302a801b718c60550633faa2ad18004fd7149a5086cfe852b265456fd1f63550967e83ec8a84357f6715932059f8ae9b480493f5d9504c0031e2b08c99004ff7654e4029db8869b4a00b3fd5d268c27bb7a80c4aa206ee52d895350f9e8699240033f05f63540836f21a6d20005ef725513046d7886ab28601bbdc95650cc76e186c6a10057e575893000cf88f2b26427af152464c002f7b92c8a8206ee62d8953a1f3ea831aa8033f9c5468c0daee39ac8a938cff4795940029f8e4ab28729bb14f62550067f8bec4a186fe850d89502cdbe8c9926001af95e464c25b6e20ec6aa475bf745594205d78ecaa2800d3f1c1369400f763b26490014ff27d814300ddec5302a8659f1425650a1b3e904ac99166df4391932009feec994a007371cd565001b7d300c0a1b3cff705594024db863b1aa0017ddc5605506b76312c4a0004fd5751932019fce2a34a0012fdd1564c25b6eabec6aa01cff37d815200ddec2312a801bb0df62540033e308ac90006de364c12046bbecfb1aa847bb98b625401a7f83ec4a1804fd17d815309db886934608dafd1f63550033f03cac9901cdc7351a2046d78c6aa280017ddc56250002fbb8a8c90236df30d8d54029fe4fb1aa001bb04362550035f28c8c98004ff7149a3006df4c0302a8c7afc1e464c18f5f1848c984267f6215932009fcae9346001b74c7635500b779326520436ef2795932069fa8fb1a80053fc9f6454213b6390ac9905e7f671592063d78412326001d71cd54540b6bfabcc0990067e575193241d7cc9b22a6013f45e564c80376320c4a8005df7350120009fee2ab46137b7d4b63550033ea0cac990067c56d813204d788caa26081bb10b6254c0e7e1ba4d281c4fc57d89
  | 15 => 0x95d56e168b0006e716603d0000009554f091e00000085b09e5260c03707eb19c00066193ea537be496935358000050a007060006fb3eb0000005ce2784d336e3787f05a800077f50c6b900063b2ac0006e57765a86dc0008601766737b80420007852ea31b00030873d70b9897de00000045e1cb6be4e62d177b65c7dd3062099cb73c91905828000096b5ed0007ca00056330b9fc0000000003ec5376c93d30003560004b2a156e230b8e8000764a2c8576675230008035610006ed0000450007f245b5856987fb29e3a282763d47662e9890004f828e0cf0003d308379e2a279002469700033398d75500000000064503e7e30006240ab11429117c32900054a2180446090006cc0003073e80003952b60009f964042462760953073235764c0009f83c702f8c670812510c0518bc2c88808e66677ed10855a00000033b6780006d85c40000005107e41323c50a700000019d6e217556659e7b594826e00003d5332054177316d000100000028a1d496e53b0000008015b800096a82255700079d99d9698eaa1200012a5db9ba0000005681030004d60000000000d81493da02f23584d4317d2a130008616955db80f0e183f8cb96a00000038e0000009c04985890000004ff4730009f075f4e15599f423717200099379119d47b6df6633090007a77a82d87006ee34216294e6999a26b0a0464f0b63589ed26328a0009d701022a8a70e06681e498090634f4eb0000006b348852c79c1843640000009300008fb00096d7e14b848b5aa0000009544d30004a2000000a0a3d65d0600101245a2f8750000f200016f0996f42dc2b588c7863a36f82b48e300024786c36344c02e0186e36e38063cc5dd3d48a937d139a306ef4311e7131a482d387d1c68180002fd76846d5a86d98a671c1155673112677c91893d02169298894244f10000195c128402300005939200053166200071771237188d62392b3051a43238b4000946a3c8f44fa9e500000026976f78a75621f89e2b708400000000062c6e50007cc6867691b47a01cd8067b800030f8136d216d00083737a60e9efa1a2bd9885d900097f4eb00000072aa375c38070001a86d43c60002ef25f7ea2d80001ce42465d3ab00000088922a9eb8ac0176ff70f4893e10000505b500040b17dbc83b1a80073fcde5650a5aefb9aaca1806dc63d8154009fa2fb22a53beb10c62550027eabec6a0034fe7051a2000d78e8ab264d7b710363501af6e03ec6a001edf364ca4000dde83b12a001af186464c0033eb0cac9046eee57d895400cfaa2ab440ffaf14a464c80b7793265281267f5355a3009f986c992403faf50a46480276e18c6c90006dd57d8d40049fe8f2b260416fd9c464c0035e3088c990ed7c574c940009faafb02848b9f55f62550037703ec4aa034ff07d915200afcae994800dbb08
  | 16 => 0x29400008983c41544f28c00033e6500003490003992d11e823f0982c13340fe0009603f15fc2398be6b665123673f8b27d21bb0002d8748000000274a451ed0005209a60007084b14966104725240009be0000000001d200013c5765851d90009be989375698a2834a0430005a300032ea5100046930599c1180007b43457b70dc5f838a5760d49e97ac42634000075c92534374e2a354b91443d45d0003b85753fb371a4c0003bb1690640000006347721e23d700048411e0d49ce45f1079e12216fe0000490000000b84a9749000a4e05e865a5058d04c66f00074d0000002f32ed9d44c63412410a76e200081b00091409500055a0330001a43f52ca00046b9b70005b309e5156897ff0002eb0d00a9a062b84ff94d75a33801e00095b00042428a6eb16d41b36e9fe3341016359400001253469782a097612d00033f6fc29170e00000f48678947424b0006b861190d9cd00026e7123650530005331456e98ef35103527f60c33000084900087476f22586d02068700028a00091b34d00062c000313a0d61b0005ad4218d30822e68da4a66118050455e00f80003d34047793144a445b9ee6353eb6e57355d30005af3478928f327a0000801df2125e6254000000a3c1c99d60001c69ca08c9327313a44ea1ba00000000095c89631f7380002909930009138c380c2e90cf0002305a246501f81305d53d0318fe6684b900007412803b00000000001d0a63f736b00096b85a13774897305e0da1571329152e742f5a4a28000a249de43833435c5490003f43428203018c16941ae73850070b8fd2130210000000000009f47bc6638040639655ef0396628b60009f19e97ec21b1181c07290007ca0004550000000000da33a2535858950009030003767d67de9870003ff9433a65cc47a75f532a5615c23a3cd7ab00080b9006985e94286e46a42ab0006da94893600009799f0b94c760c05676e99f15509a93a1ab1026382fe5b125252100033b3fc4eb26b3f200025e00025169d0ce09965696866f1cc0001be29300065b8bb2950005084431f58291684d36e82f500005d8864da0003df00067970c7ec4d95329269560004bf00004f00043e0fc7e90a04c85318de0000000002e682256712b8041c50000008438e85163114469710009c66067f90008be1d555075a17c0005283ba3dd13344119004433972a0000009fe0009000000000004d35c106e3e12a84ba21329e0006942d74d67b50004531740805c592990314d7080000004632d70005652e22a844949e75c3d50000c02d500000f6aa3cf90f10a82692b0002ec52b3d672c00012155d00007e4cf0540000003d83248ba07800000049d3276dc3df25e0007748d271d6917440120588b566c9ce9d84bb81a44d2fc21f8df60766f9b9271713976a4600000023e8c38545102d900000054
  | 17 => 0x4f10000df98d0000636cf50f96b4ae0008068df0003fd00019946c0000000f79bd6621335077af1cb000888328a249bfa1214a00054f5970000000008f939598276b7be9902176560002b69325080286992235c409c5d00bc2b145d577569000a1d3db9c07094a5581a440462ba3dd83739a8e61864d8307a3c2b80006a93dd0006f65257673c92ea4265f80e448869c0b400088c00000016f43069e00073938c0000004e161c19100000038028c546a333aba379a40d31f33661a24b450930b0008430009ea39102945b3368d875d7d940549a8483b696f18a5ca68e9049445e70004407f10ef4650004e696a000a010000002052543db1d30000272ef9e16e47b75c24ba8d13b000057080a0005f31260001ce00070c2d190962000034a000012772000a2b0003100008483c7a2798c8193bc6551eb0000000c403c4e91280006165ce0000000000004cc0f3a417663c673914d0001857b01e05b47cf3fe0000007d05590003c479e7ee0a800019816e06a08165d6673354e497c1296bd9652599caa4a89d9019e02fe7bd2d00004511317603690001682b80000002c58aa00025899583a78c4792000002a39e360075378d7fc0004110002a03060007ee5361bc00040673c00077f3523248d860d8766bd00097b81b2f120f4940007ec31934f0009639c931a1df0001e09ed6203c99e20004d22390007a58de71b0180000184b30000000fb6929d0a4261b7d092a26275763e1290bc2720009eb00000000062e0000faa360009275b700092607a0008f20003374138be2c795b41c2b68904431ae00000090e2081e96b56ee3210be7a500003a00010c90d908000a561e43311db7cc123a0a8d30000001303433cd00017c1e40007642c900028c5eb00090d4b30000000007fc95a6e81251c82e000072e0000000004900fc0000ff5a46d60000000000007552b78032e50fc81b6b30ca22082a9cd3463680008fb00051042d0007f07273c66680b52976e847b0008b214d0004cb5570195bc0e392c9a6a16
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x25500327dd0735594200a5f5888763500032b1d3725593000c7657dc53648002ab4a2579193000a5e584c936940033518f715894000a6d58887625500297961314da5000acc825846350002970e16115920b8e2d2895a464c803331c86358154008bf845c5464815f1b1da564c92000a5f38906564800327ce2474da5000c5c7395940480028f121611592000aaf28946464c00a37de3634c940038dc835c5464800237e0d715594261a9e864c4464c0033318f725414000c6c72959504c0063d205575193000c76571c5464826ea752027d8d54018f778dc5565000297d6227d8d400687c875515688002b9205631895055a6c8654462541571b1d8564c92000a3c58586464c0023b4a2574da408da6d5805f625501a3b21d3249a5000c3c5691d30480031b14b7251a5000a3f8454556900028fd62619193200a5e3858656480029be0961159200587c585c546480033518f7158154068dc874c5368800735c5d31d8d54008df835c5364800e3720d5751920018f48155d46480029bd6221d894082cac7691d3248186a72194118d4000a6d289465648283171d8735515000c6c57dc946480122fd237355a20018f778dc5564c0029e56010d8154008ed7898462551fea74e00791932018ef8748762540022f921379592000a6d58d0b6254c023ee1d601814320a9f3805e464c1863720c674c940a6c6c574852690003174dc379592000ce472dc5564c1d63be09578d920038dc835c55650002a74e3549193200cd4731c54648002a752353d8d420087f7815d46480122f121714d92000aad48d4b62500023de05474d920028ec8255d464c00339d8b715815400c9c46dcd504c0031d15f7151920018bf87506464c0032b1d0725593055a6e8648456480023be09574d920008ef78d8960551ae37e0d474da20068ef68dc930480061fe1d51959200087f7815936480161f1613749a4000a6d28d1856480023be09714d92061b988050463500029b4a3361592000cb774dc5564c0022fe11715594000abb80586464c9563bde37255a3000acc8255b63500032ddd0715593000c5c571cd464800333dcc725594000c3c4795936480063dde3714d92000a3e4858456480032ddd071519200087f855c5564c0161fde2574d9207faaf2895e464c81a3721d324da4001cb47150546880022fe11574d920008dd3891d26940031d95b71519200587c585c536480032711f734d9200687f7894d568800335dcf715192028a6f2805e564800335dcc714d920048bf48dd9524c05f2711b735013000ab78155a464c00e37de3735594062a9f68919324c0031d15f714d92000aac82584464c00335dcc715192000a3d488c656480034b15c474c92000acf8255863501561fda2574d920008df835c55688002ab2096191930048bf7891d3648002ab4a25191930
  | 1 => 0x6191932008ef8255d464c0023ee017155940008fb805c5464c8030fd1e4795920558ec8219d325400e37de3735594282c9c6391d3250002a75226218d400087f78959464c80237e0d7151a209ba9d4889f635501a7321d324c12000a5d5804363550033318b735895400c6e57d893254186a72193111930008f7781c5564c0029bca2519593000acd28947635020aab4a0079193200cb71785e464c803991852195920048bc845c5564c8029b4a251959320087e87042564c8032d1d3715593000cd471d8d62500031d95f71519208dc6c76dc954540061fe1d519593200a6d2898456480022fde0465813200a6d5898c62540023ba1c30d895400acc8358462540028fd626111932008f78155d36480021f961715193000c3c57119624c25aa7d2010d8d54028ec8255f6350082a7ce2579193000a3d48c1e564ca0aa7ce05791932008de870436355002a7ce241d9150008bf78119624c29e9bd60611895000a6d58ccb62551862fde2474da5089c5f6794b63550161f1617149a40048bc485c52694003391c76258154008ef8255f635000e37ce25791920008ed8704362550032d1c646581327ecac7611d32480023be095751920028ef78dc95650c023dde0714d920038df3891d2694003a51854118d4000aad488c762542931bd9d51d89508da6d580df6255002a74e2621193000ce4721c5565000a3bca2574da4000e4c36959324821a9bca010959320587c5851d36480022fe1d561193200aac8458f62540023ee1d601813200cb471119624c2cf0fd9e56119325787c6895d36481571b9d8564c920038dc835c546880030fd5e469813261c9c76119324c2cb8b4a2561193200e6761544625400297e0d5455a3000a3f58c1e464c802b3ce2611895485a6c8615d324800237e0d57519320dc6c56dc9504828f271cd4151a20008dd7898463500029720d5495920008dd7898463550031d15b715813200c5f5355f6350aaea74e2611193200c5e534de5648002b3ce307d895400aad28042464c8022f5e3561193089a5f3891e564c8030f1594798132068bf7890d4688002a74e26111930acc5f3715a464c802374e2579192000aac8458762540029bda2574c92056a6f6895932480031bdd472559430687c87551568c0031d95c714d92000c6c56dc93048002a7121324da5000a5d38946564c002ba20161d895400e4c568d932482ab1bdc8565813200cb471919624c0033c1c7704d92000ae481590625400366dcc7055140018f48151d36480031755c57d8d406badb835806050c023b5e2611895000c9c431d9544c802b3e0d64d8950038ed2885e564c81a2f21d5451a3096c5c76dcd54540031bc9d179593246a9c681cd54500031794d3795942028dc8351f624c01a3b21d2149a5000a9f845846350002ab209569193096c5d57d8f6
  | 2 => 0xf78959604c8032bdd3725593000c5f7394d568821a9bca2479593200a9d48d4f63500023be1d631895496c9f46dcd548c00237de063581548da6d5885f62550023be0971519200087d58d9d325000e37ce3765494061c9f3701e464c8030f1195798132008bd87042464c8023be097155920068f8805c556508029b1613249a4000cf071dc156500023761c20d8d5400a6d28952564c8028fd62219193056c6c2715a36480033318f7258d54008ef825c5564c33393d5f63d895400a3e48586564c802b3e0d47d895098a9e84158635022697ce21795932068f8805c5464c802abe1163d895000e4e52d8f6255002b320957d8d4000ab481558464c00237e0d474d92000a5c5858463502529bd6017d895400acd389846255002b3e0956d8d40008ef825c55650802aee01611193200ccc7318960550028fd22611593206acc864c930480072d1c54151a3000a9f3890646480371b15f624c95084c5c7615d324c003271ce46501208987e5849f6454c023be097155a30ace1f73158464c8028f96127919300087f7815d36481171b1c95455a3045c6f6755362540030f55c579193200c9c4391d268c082a7ce0279193000acf8258463502269b4a2479593261a9e86504635031fa3523631895400cb4741c5564c0031d45c1795932b6c5f67d0e564c8161fd63674c940058df8754f635025a9756217d8d5400acc8358762540022f523765493000cb646dc5604ca1a1f1a257581327dc9c7611d324c003351c4635894000a9d48d586350002b34e261d895400acf8258763500028fd22319592000c6f5785f62551aea721941d8d407faaf28946464c80317dcc5651920c1e4e5718c62550b32711d324da508ea6f5819062540032d91f714d92000a6d5898462540030f959479813255c6f27c1e564c80237e0d47d895000ccf378df62540028fd60109193200a3c58584464c0021f9617151920008ed7898c625400333dcf7255942008fb87580605085f2711f634c940008df835c55650e5aa7d2217d8d5406bc8804c93048002b32095618d4082aaf68d4a464c8021f961715193200aeb8058762550030f91e564d92000c74571c546481f6a7218474c93000ab880584464c802abe11611895086a5d3801e564c80a3b2097155a3000acf83587625400339dcb715594000ccf63dc9505026ea752217d8d5462c9f674c6464c01a374e2579193000a5d588876350002ab1213249a5000c6f751c9564c2372b11b7255132aec3f67158464c802ab2095451a30028dd3895e464c80335d8f71581547faaf28042464ca531bd5b725522000c747115946480161fd637650d2000c747195936480022fe1d561193006a3c8655150500022fa1c509193201cd4714c53694002b620161d8d540087e5851d36482b78bcc8561193200a9d48d4d36900028f161
  | 3 => 0x32d1c44658132018df874c763508030f51c47959208daaf4885f62550162f52217d8d540487d5885f63550021fe157155932008fb875806054e52ab52217d895400e2c5611d32480032bdd0725593000aaf488df62542531b15b725513286a5d3885e564c802b3ca010d8d5400c5e56dcd504c0032bdd07255943038dc8355d46882269b4a0479593200ce471189605515a9bca0611592000cb646dc5624c21b171da574c930068f8805c55650c0237e1d6118d400087f7895936480023be1d61189508da6d5881f625500393188735515000aaf82558464c003391cb715594000a9f83584464c0028f96161919307daac82158464c8030f91e565813200af081580604c803331cf725594294aad4801f62550028fd22619593200d9a471c1324c307939506318954058bf87552464c8021fde0575193200c3f4715a604c802a75226118d409ba5f5885f635528f27d9d41d8d4000ce772dc5564c00333dcf725594000acf28c1f63550039918551d895055a6c86550625418637de37351a2055c6f57c1f62550023be0957519320487d5885f62550028f121379592000c3e57dd1464c9af275237351a200687c87545568c0063be1d21d895300c3e5791d36482121f160674c95061c9f37c1e464c8021f61c109593200ccc63dc960550030f11e564c12000a5e5858763500029b4a25355a2000a5c8355156880032d11b715813294c6c56dc95448002b3ce261d895400d6b721c154540123bde3625095000acf28984635500a374e2179593200c5c56dcd40480023b5e26318954048bc484de5648002b320961d8d4055a6c8648456480031795c735192089c5f3695d329418ea74e2579193061c9f4701f63550032d11c714d92082c9f3691d329015e9b21921959209eaaf6890c62550038b19154d895000ccf63dc960550023be1d631895000cd773dc556500022fe11715592000ccf731c95650c028f5626191932028ef2895e464c00237e0d5751a208da6d5801f6255002b3e0961d8d5400a9c83551468818ea74e0279193089c6c7695d32482b28fda2561193200a9f488c636480161f1612791930b6c5f73159464c9aea752227d8d4000c5c57d8d62500029b56342d8950008bf845c5564c002b9e056418950038df3895e464c0028f1216115932018f48155d36480031bc9e179593200a6f8558462540031d95b714d92000c3f4795a604c9fea74e0579193282a9f3895e464c802ba20161189547d8bc4819d3250002b3e0d61d895400c3f5455e464c236abd2010d8954008ef87590625400333cdf6298154028ec8255d468c0029ee01619593200ae48158f62542a32711d314da50068dc874c936942271718e574c94055c6f5701f62550032b11f624c95000e2c5691d32480028f12161959205787f7815d26900032718f74541400087
  | 4 => 0x154068bc875054694002bc2056018154018df874c76355282c7d225218d549ba5f580436355003879595418d40008ef825c5464c0029796131d8d54008df8758463550028f9614151a5000c3e4715936480031b15b725012000ccc73d89605501a3b21d2149a308dcaf46dc9548800317dd4735594200c6c57dc93648323a3d2363d8954008fb805c5564ca5aa7d2017d8d5400c747115936480031b15f725193200a5f835525648003a311b624c93000a6f8255256481af9694350d8d4000cac74dc9564ca1a9bca2179593200ce7721c5564c00335dcc715594028a6f280de56480022f5e35611932008bf845c5564ca532b1db725514000ce7721c5364818e2f9213795940008f78155d464c2b38b0c8561193200c3e5451e56480028f161279193000acf38043625500339dc87155940008df7818d6255003351cf715594061c9f47c1f63551d69b56047d8950008df835c546481feabca2179193200ce4721c5564c00333dcc6258154028bf78919424c2b787cc0561193250d8c474c9304800237e0d715193082a9f3805e464cb0f9355c63d89546ba9d4805f6350002b5e0556d8d4063e3a50d42464c2bf8bca2561193200c3f751d1564cb06b3ce26318954008df78d8d6250002374e3765494000aac8458462540029b4a253959200087f7815946480031715f7351932bec6f75189605518ea7219319193000c7471159604c8121fe1d549593275a6c865476254003a5d854118d40ace1c73158464c8031bd4957d8943018ef87487625511a371a37358154038dc835c556880023dde07151920028ec8255e364801a3b21d2149a4000a6f68dc95454307a31506318954cce8d48d8f62550021fde056519320087d87102564c802b34a307d8d54a1c9c761cd54500021fe1d611592000c7471959464825ac7d2252d8d547dcaf67d4a464c802b34e241d89506fd2c72551505021717d5c63d895400aaf8255a464c2269b4a007959329dc6c761c95454002abe096111930028ec825c5464c0023ee01715594200c6e56dc95048003331cb635414000ae78159362540021fde05658132aee1d3715a464c802b34a26118d540087e584dd269030f33d9c63189549ba5f5888763550022fe1d611193000c6f751c956500023be097151a3000a9f6891d324c26e37e0d47d895300c3f75dd1564c8122fd23674c95000a3d58984464ca6f1715b735512000c7456dc54648002b34a010d8d540087e5849e464c313a3d23631895457c6d2895d2690002b920564d89500687c8754556900023ee1d601815400c5e57dcd4648003a5d85311193000a6d58d092694002b3ca261d8d54008ed2895e464c0062fe1d419193263a9d3805e464c003a518541d8d4000aad28946464c8031bca25749a4089a5f38042564c8021f961714da40008fb805c55650c
  | 5 => 0x1b624c002b320961d8d54638bc6891d624c00a3bca2579192000ccf3718a6055002a7da37355140c1e8c4818c62550031ddd47155930008df78d8d605500317dce565192063abb845806050c02ab211631895000a9d38d58464c0029b4a01095932c5aaf8458c62550029716161d8d400087d7898456480022fe11715193200acf825846355002abe0954919307fcaf6790f62552ef0fdd7745594200aac82552464c0028f563079193204c3f47552564800387118574c9307fcaf2691d32902cf874de569193200cb446dc5624c1fae3ce3521193261a9c865506350003271d3735593200a5f83546564c803631cc725514000c3c471593648003531cc725515000ad78155863500023be097155940068bc87505468820aab4a25791932018f778dc5464801a3721d314da4000acc83593625415e9b4a0379592003acf38d89325401a3b21d3249a4000a5f83552564cb36a75226118d5400c9f48dcd46880022fe1171519307fa9d3881e464c8039318b73551500087d58dd943480062fe1d41d91530587f58dc9468c01a2f21d4151a3028c6c7295950480161f161715193057a7b855806054a831755c63d895457a6d2891e5648002b6e0161d8d54b3e2f2895a464c8031d15b714d920c2e8f5418c62551fe2f1a2475813200acc8258463550122f1213749a5017a9f4805f6350002ae52010d815400c3f5455e464c80237e1d5618d4000cac46dc9504c0023be1d611895456c6f6748656480161f161714da40c2e4f5018c62551ae371a37358940008bf87584464ca6f1715b7355132038dc835c556509d69b56017d8950058bf87552464c00333dcf6258154c0a6d589846255003331cc7255940008de8708363552269b4a0179593200acc8359062542e69b4a2611593200acf8358462552eb17dd7735593246c9f6755363501aea721954d8d4000a6f2894656500033918b715815400c9f4745f635517f93159324c12085c6c7615d32480023b61c30d89540487f8755256480031ddd4715594000e676148456482c2abe09561193262a9f38184464c2d333dcf725193200c3e57119624c0038711b431593200c3c5711d36480030f95e465813294aad488df62550031b148765513286c6f2695d32941d71b5637255a3000c765145e564c8028fd201095932048bc845c5564c0028f9213795920618bf6891d624c0022fde0474d92000e1c4695d324c00e3b4a2579193200aaf2895e464c25a9756227d8d540693c8755150502369b56237d8954a4c6c72545568c0031d15c714d920038df78dcd46482b3870c8561193200c7656dc5604c8030f11a575193200a6f58887624c2363be0957d8d42008ed7899062540028f56241d9150988bc484de5650213174dc569193200a5e3858456480023b4a26750d50a9c9f73119604c8033318d2798
  | 6 => 0xd2231d8954ace2f20158464c80333dcf725594394a6f580df62550022f9217149a50068bc8755146881d69b56237d895094a6f5885f6255307a3d00631895400aad488c7625520ae3ce3529193200c3c47959604c803171cc5651920c8ccf67d8c6255002b52055618d4000c9f3745e464c9569ba19541895000cb7741c556500022fa1c109193200ad8805846355002b320d61d8954008fb875806054b07931506318954b8e1f3795a464c802b9e0563d8950a5a9f48184635032b17dd4635895400a3d58042464c9d6bae0960181520087e585c5269031a9be15631895417a9f4815f635000335c5e17d8d5400a5d3890656480028f921619592000c3c5791d36482df87cdc569193289a6d2885e564c803351c7635815400c3e5451e564c81a3e201715593200c5c57d8d325000297e0d5155a30bfc9f7418d60550021fe15715592000cac72919504c00e3720d47d8950008bf78919624c3239355f63d895400cb6471c536481163b1a3725815400cb447dc536481d69b21954d895000a7880584564ca0aab4a21791932008bd48dcd56880022f61c509193200e8c631c954503079315c6318954028ef78dc9564c0031715c6358940008bd78984464c0031bd637255a3000e8c6390c625500e3b4a2179193246c9c7355146880023bde0625815400a5f3891e564825a9756007d8d5400ad938043604c8028fd230795932028ec825c5468c0023de055751920c4acf6818c62550034715c474c930008be485c53648186a7a195418d4000ae78158c6254002ae20161919322dc6c574c9269021b174de56919327fa9d3895e464c80333c9f639815400c5e5718d6250002a7d2231d8d5000c3d5715e464c0031b95f5249a4000c5e57d4d369000a3b2097155930008be485c53694002b34e010d895400a5e5858463500122f121714da50bcc5f75dcd5650c0637e1d31d8d4000c3c57dd1464c80317d4d57d8d4000c3e47959304801a1f21d5155a2000c9f741cd56500039318a5218d5486c6c6295d325401ace201545414000aad480436255002ba4a010d8132048bc8455d364800a3b209715594000a6c82551568c0028f522611593200e1f4395a464c8030f95b7454140c9c9f7418d62550a29bca2479592000a5d3891e56480029b56010d895463c9d3891d36940162f52217d895400c9f4785f635500a3b209715594300a3e48584564c8030f95c465813200a7880586564c8023761c10d8d547fc9c7691d324c0021fe1d611593200ccc73dc95650003271d37355930008bd48d9d32540030f11c565813200a5d588876355002b34e307d895400ccc72d8d605521a9bca047959326ba9d4815f635025b2711b735513000aaf488c762540022fe11575193000cae47d893254002974e2529593000a3c58584464c8030f15e465813262c9c371
  | 7 => 0x48bf78dd1564c0032711e364c12000acf8359062540021f5e261159327fa9d3885e464ca269b4a207959320da6f5805f6254003a5185319193000c5e57d8d32502b78be0856119320087f7895946480022fde2465813255c6f2701e564c80327cde179193200a5d58d0f63540022f5e261119328dcac46dc9544c083271ce465013000ccf624de605520aa7ce0109193200c3c57119604c802b3e0957d8d4094aaf6890f62550031d1c6565813200a3d4894656500122fde374559320587f7895d464826ea752007d8d5400a3e58586464c80335d8f715894000a6d5899062540030f51c479593200c5c57dcd46481eb8718d5454140028ef78dc95650002974e241959327daac4818c62550028f961611193200e8c62119324c32f93d5c63d895400c3e4655e604c802b320d47d895063c9c76919324c00297161324da400da6f5811f62540035a95c704c92000a5d588c7635426f17d5b735523000a9d4804363550021fa1c409593200acf8358462540028f5226195932008df835c5564c00237e0d715592000acc835846255002375e35618d40008df835c556500023ee01714d92000aaf845876254003351cf71519200587f7895d464c802abe09619193000e1c56550635025b2711b7355132038ef78d8932540031795f6358940028dd3885e464ca3a1f16127d91509ba9d4805f635500237de06358940c2e8e4818c62550031bdca5255a3000c5f73959404800e3720d715592000a9d38042464c8032b91b725413000c6c7295950502b38b208561193200a5d38042564ca6ea752207d8d5400a3d48042564c802ab52237d895000acf2894763500029756227d8d40bdc3f75dd15650c02b34a261d8d54ace1e32158464ca529bd6010d895400ccf2718e6055003a318f725514000c3e47159604c8021f961714d920068ed2895e46482be8fda056119325587f7895d269000333d8d279815400aac82558464c2c6a7e0d561193245a6c681c954540030fd5c469813200cd7731c5564c0072dc5d419193200aaf8458c62540030f15e465893000a3e58584464c00333189379815400aeb80584625520aa7ce2179193200a7b80584564c8021f5637251a3000e2e56d4a464c9aee620141d8d4000c5c739594648187279d8464c9307fcac6291d325400327dd0735192000ad48155b635021a9bca0179593289a5f38906564c8022f9213749a5000cd47118d605500a3bca26750d5000c6f5745f625500339dc8715192000c3c56dd1564ca5aa7d2027d8d540187f875465650802ad205569193000acf389076254002970e1619592001cd4714c5369015e9b4a0179592000c6e5249e5650e6f271db735514000e94614c4464c21a974e24795932068dc874c536941569ba19511895000ab781558464c00237e0d57519300387f8754e5648236ab
  | 8 => 0x919e601b0000010790d2b84d52dbc6754e1c260008591b1353064ea00095c464cd10c08c310bcdf86a000716a2539934000f39d2b6d180f78002a85b2458000005846ac6c3384ae569420006e4ac474c000000020828329097c120b833b1d0003ba020001fb83163219c230826f101c0002638a0007d8e10000020584c8308e00008b56c379678850b8eb030ba12c24d8004171e47880000054000cf1b2e5cb18d98ae07a70b9cd21f4d48adada1425457cbe2bf490000b98e40001663a101000d1cd0000660a75068004e07c4968002580004a1bf68292a3aae982c4380036786e0022fb2683d008b5bc80ee0002780070cfbccd0bb4e1010afb67000228da000249065d824a5c0000e8aea00106cc68003dc27d90bce0005e0001ee000781b206021ace00015a6224c5dc4595d80012e19274871a190000000000033d88e86ceeaaf0dc001683c21ae5bd623386111201abb120a001d44671b502e2a18831c870e690664a1d0ae00081644a088006b045030800000958000be000bb54e00010e9ed1b921644704f09d7000b91a00ba88e15a120ec6f80020e860000ce5e389401aa1ddf96b52d0d4dd8bd0000008a47c000b59880001debbd3ab9d280000cf8a31e2001ea1817eb1702f96d4a2a45270003a24dd010b53ca4949811b2ac000000401127c50100016825c088002a8000b7118000239a8b611c8001ae180072001c73551620000429d03853c00224604000082646f469c45420016f3566421150250d70008c60006d800000001fc9604eb17c509e4412948002676f4a3879800000225798731f0e50bb000509205a78130000ac4643b00084a169e01cf1c0003b30006e4a28e04a7088ab80000030c313608cc6a8c619314272a041092dc5c0019ad7eed6c000000109759d1834ba0001f8958951050f41d67461c0008e7f01440036b78ac9d53825000ae46525d57e32d66b2370e2ae153bb50400000324080a611da4432d1c80026a7150986f2dc11a2ec5ab174bef14a284c722fc0342102fcd4cc7c431d0591353e20006853fb386489e9fe087000ac0c4a1a6be40c72a2649cb816680085f1d40009b400001700002be001c4000542a911b3126f4ea8002967d0fdc508f1000002008004d4001221980928058e00000054517147000ce1363e7008ef825c55650c0237de3635895400e2f6455062540021fe157155940008f7781c556500161f161715193200cd4731c556500122f21171559209ecac761c9545000237e0d57519207fa9d3805e464c8028f562219193000a3c48586564c8023ba1c10d895400a6d5888762540030f95c474d920758ec68dc96354002b6e016118d547f8be484de56508029b4a25395942b5c6f72159464c8023be095751a30008bf8455d464c8030f95e46589307eaaf68d48464c8038b15b52119320
  | 9 => 0x4241a90596201aba608800206ac21430616436dd2b32569094f9800136594001eb37ab9913800900d88b4be65a8c0507ad80f600063ba00008b400000000119e6800000f3c0000023a000593c436055c003a76d274149bb0876cca342cb6210c137b5b378001571f043c0bdf18040580018487f22b0e0000000003a6193755aa825ff0003a0001598e715a39a0f13c832a600014b70600161ad61fe000488bb544af00000033ed05f80505c042c0000040c6e48d0871a22d1edaeb00030a11a0723b0f91fbb600
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x6708b60081fcc28e23cac9060e131a0731c954541568d6d3b90e0aa2a183a0f4818a5218d54cea163c8ac23a64900070310c521d9544cab30390c2b88e99260c349b6991c704c930add079c0ada908c9930d26da7731c1545030a918f2318e4aa280ab46b6995c704c920
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x1
  | 7 => 0x98a
  | 8 => 0x150a
  | 9 => 0x98c
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x128a
  | 13 => 0x128e
  | 14 => 0x128c
  | 15 => 0x128d
  | 16 => 0x9ca
  | 17 => 0x9cb
  | 18 => 0x168a
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0x12ca
  | 22 => 0x12cb
  | 23 => 0x12cd
  | 24 => 0x12ce
  | 25 => 0xa0a
  | 26 => 0xa0b
  | 27 => 0xa0c
  | 28 => 0x180a
  | 29 => 0xa0e
  | 30 => 0x130a
  | 31 => 0x130b
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0xa4a
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0xa4d
  | 38 => 0x198a
  | 39 => 0x134a
  | 40 => 0x134b
  | 41 => 0x134c
  | 42 => 0x134d
  | 43 => 0xcca
  | 44 => 0xccd
  | 45 => 0xcce
  | 46 => 0x170a
  | 47 => 0x15ca
  | 48 => 0xd0a
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x188a
  | 52 => 0x160a
  | 53 => 0xd4a
  | 54 => 0xd4c
  | 55 => 0xd4d
  | 56 => 0x1a0a
  | 57 => 0x164a
  | 58 => 0xe8a
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x18ca
  | 62 => 0x178a
  | 63 => 0xeca
  | 64 => 0xecb
  | 65 => 0xecd
  | 66 => 0x1a4a
  | 67 => 0x17ca
  | 68 => 0x104a
  | 69 => 0x104b
  | 70 => 0x104c
  | 71 => 0x1a8a
  | 72 => 0x194a
  | 73 => 0x168b
  | 74 => 0x180b
  | 75 => 0x198b
  | 76 => 0xcd512
  | 77 => 0xcc992
  | 78 => 0x98cd2
  | 79 => 0x995d2
  | 80 => 0xcc995
  | 81 => 0x3ca
  | 82 => 0xcb
  | 83 => 0x40a
  | 84 => 0x10b
  | 85 => 0x449
  | 86 => 0x14b
  | 87 => 0x1649
  | 88 => 0x44a
  | 89 => 0x180c
  | 90 => 0x198c
  | 91 => 0xcd692
  | 92 => 0xcc9d2
  | 93 => 0x9ccd2
  | 94 => 0x9d712
  | 95 => 0xcc9d6
  | 96 => 0x150c
  | 97 => 0x589
  | 98 => 0x10c
  | 99 => 0x1789
  | 100 => 0x58a
  | 101 => 0x5ca
  | 102 => 0x14c
  | 103 => 0x198d
  | 104 => 0x150d
  | 105 => 0xcd
  | 106 => 0x168d
  | 107 => 0x18c9
  | 108 => 0x105812
  | 109 => 0x104a12
  | 110 => 0xa1052
  | 111 => 0x104a13
  | 112 => 0xa1952
  | 113 => 0x74a
  | 114 => 0x14d
  | 115 => 0x8e
  | 116 => 0x150e
  | 117 => 0x1a09
  | 118 => 0x168e
  | 119 => 0x105992
  | 120 => 0x104a52
  | 121 => 0xa5052
  | 122 => 0x104a54
  | 123 => 0xa5a92
  | 124 => 0x180e
  | 125 => 0x58b
  | 126 => 0x40c
  | 127 => 0x178b
  | 128 => 0x18cb
  | 129 => 0x188c
  | 130 => 0x160c
  | 131 => 0xcc592
  | 132 => 0x5cb
  | 133 => 0x44c
  | 134 => 0x17cb
  | 135 => 0x1a4b
  | 136 => 0x1a0c
  | 137 => 0x164c
  | 138 => 0xcc452
  | 139 => 0x170d
  | 140 => 0x15cd
  | 141 => 0x1a0d
  | 142 => 0x1a8b
  | 143 => 0x194b
  | 144 => 0x164d
  | 145 => 0x74b
  | 146 => 0x170e
  | 147 => 0x15ce
  | 148 => 0x188e
  | 149 => 0x160e
  | 150 => 0x1a4d
  | 151 => 0x1a8c
  | 152 => 0x194c
  | 153 => 0x17cd
  | 154 => 0x74c
  | 155 => 0x18ce
  | 156 => 0x178e
  | 157 => 0x44d
  | 158 => 0x40e
  | 159 => 0x104452
  | 160 => 0x5cd
  | 161 => 0x58e
  | 162 => 0x104592
  | 163 => 0xb8c
  | 164 => 0xbcb
  | 165 => 0x184c
  | 166 => 0xb0e
  | 167 => 0x19cb
  | 168 => 0xb4d
  | 169 => 0x592d3
  | 170 => 0x45294
  | 171 => 0x58b53
  | 172 => 0x5c593
  | 173 => 0x44414
  | 174 => 0x5d793
  | 175 => 0x597d3
  | 176 => 0x41a14
  | 177 => 0x59a53
  | 178 => 0x41654
  | 179 => 0x1797d3
  | 180 => 0x1715d5
  | 181 => 0x45894
  | 182 => 0x5d8d3
  | 183 => 0x45614
  | 184 => 0x161654
  | 185 => 0x44b14
  | 186 => 0x1a57d3
  | 187 => 0x1a9953
  | 188 => 0x1a57d5
  | 189 => 0x1a9954
  | 190 => 0x45355
  | 191 => 0x59316
  | 192 => 0xbc455
  | 193 => 0x5c455
  | 194 => 0x58416
  | 195 => 0x5da15
  | 196 => 0x45a55
  | 197 => 0x41796
  | 198 => 0x457d5
  | 199 => 0x418d6
  | 200 => 0x1a1a55
  | 201 => 0x59616
  | 202 => 0x5d655
  | 203 => 0x59896
  | 204 => 0x1898d6
  | 205 => 0xb8596
  | 206 => 0x40454
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1299
  | 6 => 2648
  | 5 => 1156
  | 4 => 12
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*14) 6
  | 8 => packedAt gbK8 (i*25) 17
  | 7 => packedAt gbK7 (i*36) 28
  | 6 => packedAt gbK6 (i*47) 39
  | 5 => packedAt gbK5 (i*58) 50
  | 4 => packedAt gbK4 (i*69) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*14+6) 8)
  | 8 => gbHint (packedAt gbK8 (i*25+17) 8)
  | 7 => gbHint (packedAt gbK7 (i*36+28) 8)
  | 6 => gbHint (packedAt gbK6 (i*47+39) 8)
  | 5 => gbHint (packedAt gbK5 (i*58+50) 8)
  | 4 => gbHint (packedAt gbK4 (i*69+61) 8)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (14+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/24+packedAt gbK8 (1500+(h % 24)*6) 6) % 60)
  | 7 => 2*((h/849+packedAt gbK7 (46764+(h % 849)*11) 11) % 1299)
  | 6 => 2*((h/1726+packedAt gbK6 (124456+(h % 1726)*12) 12) % 2648)
  | 5 => 2*((h/752+packedAt gbK5 (67048+(h % 752)*11) 11) % 1156)
  | 4 => 2*((h/6+packedAt gbK4 (828+(h % 6)*4) 4) % 12)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03ff803ffffffffffffc063c7e3e31ffff
  | 1 => 0x3fffc0fffc07c03fffffffc39cf91c7ce23ff
  | 2 => 0xfc0ffff000007ffc0f81f803c1f3e1f9f03ccc
  | 3 => 0xfffffffff80000ffe0003fe03fe01ffc0f0
  | 4 => 0xffffffffffffff0000003fffc0001ffff00
  | 5 => 0xfff000000000000000000003fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x951100b28012951512924aa80214261a10cd55
  | 1 => 0x2a62c0535402842a565955018c990c4c622aa
  | 2 => 0x580f55500d0a4ed889b1e019c162e169f034cc
  | 3 => 0x508b9a69d9ab00900e78c062ec03fa017b40f0
  | 4 => 0x830ce38e6e3c73e3c001018377fc0001adbb00
  | 5 => 0xe3c000007030030300400603bfbf5db6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888, gbN, gbR, gbH, gbI⟩


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs0_3_0 : Interval s0Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
lemma alls0_3 : Interval s0Atlas 3 0 11 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs0_4_0 : Interval s0Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
lemma alls0_4 : Interval s0Atlas 4 0 10 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
lemma alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_2_0 : Interval s1Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
lemma alls1_2 : Interval s1Atlas 2 0 8 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_3_0 : Interval s1Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_3_96 : Interval s1Atlas 3 96 9 := block_range (n:=9) (by decide +kernel)
lemma alls1_3 : Interval s1Atlas 3 0 105 := (concat bs1_3_0 bs1_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_96 : Interval s1Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_192 : Interval s1Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_288 : Interval s1Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_384 : Interval s1Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_480 : Interval s1Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_576 : Interval s1Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_4_672 : Interval s1Atlas 4 672 60 := block_range (n:=60) (by decide +kernel)
lemma alls1_4 : Interval s1Atlas 4 0 732 := (concat (concat (concat bs1_4_0 bs1_4_96) (concat bs1_4_192 bs1_4_288)) (concat (concat bs1_4_384 bs1_4_480) (concat bs1_4_576 bs1_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_0 : Interval s1Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_96 : Interval s1Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_192 : Interval s1Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_288 : Interval s1Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_384 : Interval s1Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_480 : Interval s1Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_576 : Interval s1Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_5_672 : Interval s1Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
lemma alls1_5 : Interval s1Atlas 5 0 682 := (concat (concat (concat bs1_5_0 bs1_5_96) (concat bs1_5_192 bs1_5_288)) (concat (concat bs1_5_384 bs1_5_480) (concat bs1_5_576 bs1_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_6_0 : Interval s1Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
lemma alls1_6 : Interval s1Atlas 6 0 40 := bs1_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
lemma alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
lemma alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_3_0 : Interval s2Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
lemma alls2_3 : Interval s2Atlas 3 0 60 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_4_96 : Interval s2Atlas 4 96 70 := block_range (n:=70) (by decide +kernel)
lemma alls2_4 : Interval s2Atlas 4 0 166 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_5_0 : Interval s2Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
lemma alls2_5 : Interval s2Atlas 5 0 50 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
lemma alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
lemma alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_3_0 : Interval s3Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
lemma alls3_3 : Interval s3Atlas 3 0 60 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_4_96 : Interval s3Atlas 4 96 70 := block_range (n:=70) (by decide +kernel)
lemma alls3_4 : Interval s3Atlas 4 0 166 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_5_0 : Interval s3Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
lemma alls3_5 : Interval s3Atlas 5 0 50 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
lemma alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
lemma alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_3_0 : Interval s4Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
lemma alls4_3 : Interval s4Atlas 3 0 60 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_4_96 : Interval s4Atlas 4 96 71 := block_range (n:=71) (by decide +kernel)
lemma alls4_4 : Interval s4Atlas 4 0 167 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_5_0 : Interval s4Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
lemma alls4_5 : Interval s4Atlas 5 0 50 := bs4_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
lemma alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
lemma alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_3_0 : Interval s5Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
lemma alls5_3 : Interval s5Atlas 3 0 60 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_4_96 : Interval s5Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
lemma alls5_4 : Interval s5Atlas 4 0 165 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_5_0 : Interval s5Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
lemma alls5_5 : Interval s5Atlas 5 0 50 := bs5_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
lemma alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
lemma alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 12 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1156 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 56 := block_range (n:=56) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2648 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)) (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 bgb_6_1248)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)) (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920))) (concat (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208)) (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 51 := block_range (n:=51) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1299 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi


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


lemma bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 34, 38),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


lemma bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


lemma bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


lemma bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


lemma bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


lemma bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)


theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888fee8eae8eea88888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677352 * 2 ^ 32 + 4004022408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_43022.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[6,0]⟩,⟨.or,[1,7]⟩,⟨.and,[2,0]⟩,⟨.and,[8,3]⟩,⟨.and,[5,0]⟩,⟨.or,[11,4]⟩,⟨.or,[10,9]⟩,⟨.and,[7,1]⟩,⟨.and,[12,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4004022408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4004022408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_43022

open PEqualNP.Outside.L_meta_43022 in
theorem PEqualNP.Outside.L_meta_43022 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4004022408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4004022408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
