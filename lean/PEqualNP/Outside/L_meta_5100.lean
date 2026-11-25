import Mathlib
import PEqualNP.Defs

-- Adapted from Daniel Gallups, L_meta_3156 (Apache-2.0).
-- Certificate words are listed as 16-bit words, most significant first.
-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_5100
open PEqualNP.CircuitLowerBounds
def fromLimbs (xs : List Nat) : Nat := xs.foldl (fun acc x => (acc <<< 16) + x) 0
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

def inputs : List Sig := [(BitVec.ofNat 512 (fromLimbs [0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa,
        0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa, 0xaaaa])),(BitVec.ofNat 512 (fromLimbs [0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc,
        0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc, 0xcccc])),(BitVec.ofNat 512 (fromLimbs [0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0,
        0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0, 0xf0f0])),(BitVec.ofNat 512 (fromLimbs [0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00,
        0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00, 0xff00])),(BitVec.ofNat 512 (fromLimbs [0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0,
        0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0])),(BitVec.ofNat 512 (fromLimbs [0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0,
        0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0, 0xffff, 0xffff, 0x0, 0x0])),(BitVec.ofNat 512 (fromLimbs [0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0, 0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0,
        0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0, 0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0])),(BitVec.ofNat 512 (fromLimbs [0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),(BitVec.ofNat 512 (fromLimbs [0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]))]
def graph : Sig := (BitVec.ofNat 512 (fromLimbs [0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xfffa, 0xfff8, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffea, 0xffc8,
        0xffff, 0xffff, 0xfffe, 0xfcfc, 0xffff, 0xffff, 0xfffa, 0xf8f8, 0xffee, 0xfeee, 0xffee, 0xfccc, 0xffea, 0xfaea, 0xffea, 0xf8c8]))
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

theorem first_bits : (zero :: inputs).all (fun v => !(bit 0 v)) = true := by decide +kernel
theorem first_all : ∀ v ∈ zero :: inputs, neg v ≠ seed := by
  intro v hv e
  have h := List.all_eq_true.mp first_bits v hv
  have s : bit 0 seed = false := by decide +kernel
  rw [←e,bit_neg] at s
  rw [s] at h
  exact Bool.noConfusion h
theorem getD_mem {α} (w : List α) (i : Nat) (z : α) : w.getD i z ∈ z :: w := by
  rw [List.getD_eq_getElem?_getD]
  cases e : w[i]? with
  | none => simp
  | some a => exact List.mem_cons_of_mem _ (List.mem_of_getElem? e)
theorem first_not (g : Gate) (h : g.op = GateOp.not) : gv inputs g ≠ seed := by
  have e : gv inputs g = neg ((g.inputs.map (fun i => inputs.getD i zero)).headD zero) := by
    obtain ⟨o,l⟩ := g
    subst h
    rfl
  rw [e]
  apply first_all
  cases g.inputs with
  | nil => exact List.mem_cons_self
  | cons i l => exact getD_mem inputs i zero

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (someNot : ∃ g ∈ C.gates, g.op = GateOp.not) (small : C.size ≤ 15) :
    ∃ k S, k ≤ 13 ∧ Live true graph k S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
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
    have count : gs.countP (fun g => !isNot g) ≤ 13 := by
      obtain ⟨n,hn,hx⟩ := someNot
      rw [hgs] at hn
      have isn : isNot n = true := by simp [isNot,hx]
      have mem : n ∈ gs := by
        rcases List.mem_cons.mp hn with e | e
        · subst e
          exact absurd eq0 (first_not n hx)
        · exact e
      have lt : gs.countP (fun g => !isNot g) < gs.length := by
        rcases Nat.lt_or_ge (gs.countP (fun g => !isNot g)) gs.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) n mem
          simp [isn] at eq
      omega
    have mono : true=false → ∀ g ∈ gs, isNot g=false := by simp
    have out := get_rep (u:=true) (execute gs (inputs++[seed])) C.output
    rw [goalEq] at out
    unfold Repr at out
    have pg : bit 0 graph=false := by decide +kernel
    rw [nrm_id pg] at out
    have targetIn := out.resolve_right (fun hn => hn graph_proper)
    obtain ⟨k,S,hk,run,hs⟩ := extract gs _ tailLegal mono graph_proper targetIn
    have ns : (inputs++[seed]).all plainWord=true := by decide +kernel
    rw [nrm_map ns] at hs
    exact ⟨k,S,by omega,run,hs⟩

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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
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
  | 0 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0,
        0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1])
  | 1 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1])
  | 2 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x1, 0x0, 0x0, 0x0, 0x1])
  | 3 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x1])
  | 4 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x1])
  | 5 => (fromLimbs [0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1])
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

def supportPairs (w : Bool) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if w && i==0 then 4 else if w && i==2 then 1 else 0
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
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
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
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
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

def rootB (m : Nat) : List Sig := vars m ++ [seed]

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

def splitPairs (l : List (Nat × Nat)) : List (Sig × Row × Row) :=
  l.map fun (i,r) => (inputs.getD i zero,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def splitOK (m : Nat) (l : List (Nat × Nat)) : Bool :=
  let xs := splitPairs l
  checkEssential (graphGoal m) (rootB m) xs && (xs.map Prod.fst == vars m) && properB (graphGoal m)

theorem strong_split {u} {m l} (ok : splitOK m l = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  by_cases hs : seed ∈ S
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

theorem strong_low {u} {m l cap} (ok : splitOK m l = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset)
    (b : Impossible u (graphGoal m) cap (rootB m).toFinset) :
    Lower u (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.2) (essential_plain ok'.1.1).1 (essential_plain ok'.1.1).2 hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e
  · exact a k (by omega) (e ▸ run)
  · exact b k (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower true (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def known3 := extendKnown [] 1 [(12,[49,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known true known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0xefe, 0x47cf, 0xaf79, 0xfcbe, 0x2267, 0xeff8, 0x2033, 0xcfbe, 0xeb8f, 0xfe97, 0x7f4f, 0x9cbd, 0xc18a, 0xcec7, 0xfcf7, 0x5aaf,
        0xdffd, 0xd73e, 0xf57c, 0xeff7, 0x7f9f, 0x3c69, 0xfef3, 0xaba8, 0xbc60, 0xe65b, 0xaef3, 0x608e, 0x7d15, 0x5c29, 0x5bd6, 0x4db,
        0x7a7, 0xfa33, 0xff1d, 0xa267, 0xd7fa, 0xf155, 0xd5d3, 0xb284, 0xe7df, 0x8b57, 0xed3e, 0xbf3d, 0x93ee, 0x7ca6, 0xf3c4, 0x7473])),(BitVec.ofNat 768 (fromLimbs [0x362, 0x118a, 0xc459, 0x16a9, 0xd022, 0x2229, 0x2091, 0x25e, 0x293, 0x11c0, 0x8210, 0x147f, 0xaa44, 0xc85b, 0xd94a, 0x89bf,
        0xc029, 0xb302, 0x3630, 0xad42, 0x68a5, 0x51db, 0x8a04, 0x2603, 0xe6, 0xa101, 0x419c, 0x90, 0x7c94, 0x7095, 0x80b2, 0x44a2,
        0x21a3, 0x2941, 0xf500, 0x200, 0x46b1, 0x2be0, 0xc10, 0x22a2, 0x825, 0xc080, 0x9, 0xd60c, 0xc9, 0x9dd6, 0xa537, 0x3652]))),((BitVec.ofNat 768 (fromLimbs [0xffdb, 0xfbff, 0xffb9, 0xfdac, 0xebfb, 0xfeff, 0xffbe, 0xb7fe, 0x5f7d, 0xeee7, 0x7ebf, 0xfa7f, 0x9e57, 0xed23, 0x6c3f, 0xfedb,
        0xefff, 0xf77e, 0xf65d, 0x33fc, 0xefdd, 0x1fff, 0xeb7f, 0xff7f, 0x9f0b, 0x7b4f, 0xa1eb, 0x7f7a, 0xf7af, 0x7ef7, 0xf24f, 0x35ff,
        0xde5d, 0x9979, 0x7b9d, 0xa1fe, 0xda7b, 0xbde3, 0xc25a, 0xff45, 0x77f6, 0xcf7f, 0xf577, 0x6f3f, 0xd8da, 0x5dae, 0xe9e9, 0x7a7f])),(BitVec.ofNat 768 (fromLimbs [0xb890, 0xec00, 0x1102, 0xe910, 0x2c41, 0x4c82, 0x8844, 0xb900, 0xb844, 0x8020, 0x501, 0x2280, 0xa3, 0x1580, 0x2011, 0x2240,
        0x5c0, 0x849, 0x4008, 0x8, 0x9102, 0x2c00, 0x4552, 0x74, 0x6b09, 0x10ee, 0x2421, 0x209, 0x308, 0x340, 0x504, 0xba04,
        0x4810, 0x480, 0xe, 0x41fb, 0x200a, 0xf, 0x21a4, 0x85c, 0xb098, 0x651, 0xe396, 0x20d1, 0x3112, 0x9, 0x1888, 0xc829]))),((BitVec.ofNat 768 (fromLimbs [0xf7a5, 0xfe75, 0xd0ee, 0xf75b, 0xdffe, 0x135f, 0xffef, 0xfac3, 0xfdff, 0x157a, 0xebf8, 0xffcf, 0xffff, 0x7fff, 0xbfdd, 0xf5f5,
        0xbcc6, 0xfef3, 0x1fa7, 0xff9f, 0x977f, 0xffb6, 0xd5ac, 0x56d7, 0x67ff, 0x9ffd, 0x5f1d, 0xdff7, 0xaafb, 0xffdf, 0xbff9, 0xfb64,
        0xfffb, 0xfffe, 0x9eee, 0xdf9d, 0x7dbd, 0xdebe, 0xbfbf, 0xcdfb, 0xfeeb, 0xfdff, 0x1fed, 0xf3e3, 0x6f77, 0xf77b, 0x7eff, 0x8f9c])),(BitVec.ofNat 768 (fromLimbs [0x420, 0xb, 0x6080, 0x8b, 0x1002, 0x8125, 0x293, 0x238, 0x4439, 0x102, 0xb8, 0x4008, 0x8c40, 0x4824, 0xcda6, 0x4432,
        0x8204, 0x610, 0x2184, 0x4047, 0x6821, 0x4190, 0x8a00, 0xea09, 0x8014, 0x8401, 0x8106, 0xf042, 0x40c4, 0x5011, 0x9882, 0x44d2,
        0x8004, 0x2801, 0x1180, 0x8604, 0x380, 0xa60, 0xe11, 0x403, 0x205, 0x82, 0x68, 0x4420, 0x0, 0x9700, 0x4122, 0x1714]))),((BitVec.ofNat 768 (fromLimbs [0x1034, 0xb7f7, 0xc546, 0x37fb, 0xbf9d, 0xf36a, 0xbcd7, 0xcdaf, 0xbbbe, 0x77df, 0xf940, 0x4583, 0x6dfe, 0x73fc, 0xdff3, 0xe726,
        0xdd34, 0x7ddf, 0xebbe, 0xffeb, 0x77f2, 0xf673, 0xbcad, 0xb491, 0x6efe, 0xd7fc, 0xdf5e, 0xefcd, 0x8d56, 0x93fd, 0xeff6, 0xeffa,
        0xfff6, 0xeedf, 0xefe3, 0xdf1d, 0x759c, 0xc23c, 0xbfff, 0x64ff, 0xcb1d, 0x7ba0, 0x6fba, 0xfdcb, 0x776d, 0xb2d9, 0x77d6, 0x8de0])),(BitVec.ofNat 768 (fromLimbs [0xe98f, 0x99f4, 0x1031, 0x7a04, 0x6ed9, 0x22ca, 0xbd20, 0x9580, 0x8b84, 0x2221, 0xec47, 0xb152, 0x42be, 0x242, 0x1241, 0x88c8,
        0x55ba, 0xb162, 0xa23, 0xb880, 0x8090, 0xc22, 0x107e, 0x1592, 0x2841, 0x688c, 0x74e9, 0x59c, 0x8c39, 0xa886, 0x4264, 0x210d,
        0x3af0, 0x3ea, 0x604c, 0x79f0, 0x246b, 0x405, 0xb026, 0xfb8c, 0xa8c2, 0xdd69, 0xb103, 0x1955, 0xe4f5, 0x20d9, 0x2e1d, 0xe8e0]))),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore known3) = true := by
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
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound known3 valid3) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown known3 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) valid3 low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := (fromLimbs [0x30, 0xbe67, 0x208, 0x0, 0x6500, 0x16, 0x3575, 0x400, 0x4755, 0xc084])
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x4cd4, 0x35b1, 0xcff8, 0x9bfc, 0xf340, 0x3d6f, 0xfb5e, 0x7b6f, 0xb6f0, 0xa252, 0x750d, 0x8f3e, 0x775f, 0x7a4b, 0x35bf, 0x17ff,
        0xc1f1, 0xf68f, 0x49af, 0xf3f9, 0x7ef5, 0xdcbf, 0xfcec, 0xfb8b, 0x347f, 0xdad1, 0xb97e, 0xe9ea, 0xb1fe, 0xf35b, 0xbda9, 0x3bde,
        0xfe31, 0xd48e, 0x2e2a, 0x2dee, 0xce0b, 0x7743, 0x3265, 0xab9, 0x592b, 0x7ca4, 0xc3cc, 0xe372, 0x38ad, 0x15d1, 0x6630, 0xb273])),(BitVec.ofNat 768 (fromLimbs [0x641, 0x2e45, 0x4180, 0x3680, 0x9b01, 0x888a, 0xcb04, 0x1289, 0x8282, 0x4834, 0x415c, 0x3040, 0x5900, 0x32d, 0x4100, 0x9c80,
        0xd020, 0x218, 0xb02, 0x200, 0x4306, 0x120, 0x1640, 0x641a, 0x1dc0, 0x651, 0x80e1, 0x100, 0x2a04, 0x900, 0x2630, 0xc78,
        0x4004, 0x1c50, 0x204, 0x8000, 0x1612, 0xa04d, 0x9391, 0x6092, 0x80, 0x2d00, 0x8345, 0x200, 0x101, 0x1525, 0xc6a1, 0x2412]))),((BitVec.ofNat 768 (fromLimbs [0x73bc, 0x6673, 0xe6f7, 0xfb12, 0x7e7e, 0xdfbb, 0x35af, 0xbc3c, 0x7aef, 0xfeff, 0xb7b3, 0x6ea1, 0x5203, 0xb3fb, 0xb23, 0xd71a,
        0xe729, 0x3cfd, 0x7c6b, 0x76af, 0xff7f, 0x9f42, 0xce52, 0x4641, 0xef74, 0xbc77, 0x75f5, 0xb7be, 0xeca9, 0xfab6, 0x4d8d, 0x2f05,
        0x7df7, 0x5fd7, 0xb06e, 0xffad, 0xf147, 0x5668, 0x65d7, 0x76d6, 0x7ddf, 0x9c9e, 0xb9cb, 0x59bc, 0xc3fa, 0x90c2, 0x8646, 0x4e7f])),(BitVec.ofNat 768 (fromLimbs [0x4806, 0x818a, 0x3a13, 0x32, 0x401c, 0x244, 0x21, 0x2c06, 0x5450, 0xb142, 0x1883, 0x380, 0x207b, 0x40c0, 0x1250, 0x6139,
        0x8c5, 0xd427, 0x7099, 0x91c0, 0x28a8, 0x485c, 0xe128, 0x381, 0x2224, 0x884, 0x6004, 0x38f1, 0x480, 0xe460, 0x4004, 0x7002,
        0x3480, 0xc0a0, 0x7020, 0x2090, 0x8860, 0x1130, 0x66, 0x8240, 0x3032, 0xd0b1, 0x68a0, 0x10b8, 0x406, 0xc2d0, 0x952, 0x4869]))),((BitVec.ofNat 768 (fromLimbs [0xeffc, 0xdbd0, 0xce5f, 0xec73, 0xcdbe, 0xfbd7, 0xdef1, 0xb1c3, 0x790e, 0x5bae, 0x99df, 0xf1cd, 0x23a5, 0xcdbe, 0x62c5, 0xeb05,
        0x8a46, 0x5b7e, 0xeb5a, 0xddf6, 0xc9be, 0xf153, 0xe11a, 0x35ff, 0x6fd5, 0xcffe, 0x7baf, 0xe6b6, 0x139b, 0x5cef, 0xe3db, 0x14c7,
        0x95e5, 0x8371, 0xdbcb, 0xcdf5, 0x7fd9, 0xef3c, 0x55f2, 0xf346, 0x4a77, 0xdfd9, 0x7475, 0x3609, 0xf3f5, 0x8c06, 0xd986, 0xcd9c])),(BitVec.ofNat 768 (fromLimbs [0x4b0, 0x1000, 0xc040, 0x800, 0x621, 0x253b, 0x644c, 0x50e8, 0x9a0, 0x699, 0x20c, 0xd813, 0x1084, 0x993e, 0xad06, 0x8806,
        0x811a, 0x1c8, 0x8424, 0x4431, 0x9502, 0x300, 0xa81, 0x9002, 0x900, 0x540a, 0xb5a, 0x4408, 0x7379, 0x101, 0x110, 0x44,
        0x8054, 0x3053, 0x884a, 0x8000, 0x6402, 0x26cc, 0x4c08, 0x818, 0xcecc, 0x800, 0xc, 0x6144, 0x3029, 0x2906, 0x6205, 0x8794]))),((BitVec.ofNat 768 (fromLimbs [0xfefb, 0xbd6e, 0xfc55, 0x4e65, 0xd6d3, 0x2e9e, 0x9fc8, 0xc5f7, 0xfb2b, 0xc7bd, 0x6e78, 0xffd4, 0xc9b6, 0xfe5f, 0xece4, 0x7b85,
        0xfeef, 0xcd40, 0xdf76, 0xeb99, 0xe3fb, 0x3fd3, 0xcb11, 0x7c3c, 0xbbc9, 0x27b8, 0xbed5, 0x9f45, 0xff18, 0x4d50, 0x9bdf, 0xf7bf,
        0x9d8f, 0xfb22, 0x4ff7, 0x161a, 0xd1bf, 0xbf9e, 0x9d09, 0xef7e, 0xa6dc, 0xdb5f, 0xcfb7, 0x6f87, 0x7dce, 0x7e6c, 0x59e9, 0x980])),(BitVec.ofNat 768 (fromLimbs [0x5802, 0x8e42, 0xd9b, 0x642, 0x152, 0x4880, 0x82b0, 0x8603, 0x244, 0x920, 0xc440, 0x10c, 0xa452, 0x40, 0x4030, 0x21,
        0x5020, 0x2, 0x90a, 0x9288, 0x845, 0x42a, 0x2014, 0x600, 0x9402, 0x100, 0x2080, 0x8305, 0x402, 0x8c00, 0xa685, 0xd1a,
        0x3023, 0xca20, 0x55a0, 0x669, 0x40, 0xd902, 0x8207, 0xc282, 0x1022, 0x2598, 0x2420, 0xc0a, 0x8056, 0x1669, 0x95b0, 0x4820]))),((BitVec.ofNat 768 (fromLimbs [0xb18f, 0x7a8e, 0x312b, 0x6eee, 0x7925, 0xdbdd, 0xcc1f, 0xee96, 0xcd7f, 0xc4dd, 0x4f7d, 0xdebe, 0xfdfa, 0x8c25, 0xbff9, 0x86e3,
        0xb4d8, 0xe33b, 0x16ac, 0xabff, 0x13c4, 0x46ed, 0xb2bd, 0xfdc6, 0xfb8f, 0xfc18, 0x8e9a, 0xd961, 0x5cc7, 0x6daf, 0x377c, 0xf7ff,
        0x5a7f, 0xaa5f, 0x85f4, 0x37c6, 0x3e34, 0xeadb, 0xee7b, 0x7fed, 0xaced, 0xbfe7, 0xafda, 0xcfc6, 0x2f3f, 0xebbb, 0x2079, 0xb000])),(BitVec.ofNat 768 (fromLimbs [0xa03c, 0x4000, 0xa020, 0x101, 0x84, 0x1645, 0x1441, 0x2920, 0x2908, 0x3208, 0x3a82, 0x4402, 0x24, 0xb000, 0x9ac3, 0x6004,
        0x598, 0x9c25, 0xc054, 0xd23, 0x10a0, 0xa051, 0x8923, 0x11c5, 0x39, 0x502e, 0x4518, 0x3000, 0x4091, 0x52a0, 0x5940, 0x3084,
        0x798, 0x200c, 0x18, 0x2012, 0x602d, 0x480, 0x6c60, 0xd6c, 0x8959, 0x1267, 0x92, 0xf175, 0x2200, 0xe892, 0x284e, 0x92c0]))),(0,0),(0,0),(0,0),(0,0)]
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
def known47 := extendKnown known31 5 [(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64]),(339,[131,50,114,82,99,66]),(440,[129,50,83,48,114,97,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(95,[101,66,16]),(175,[116,100,83,32]),(183,[115,84,99]),(231,[83,82,114,99,66,16]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(423,[133,80,116,96,48,32,16]),(441,[84,133,80,66,114,96,16]),(462,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x9da8, 0x3de5, 0xfe85, 0xdcb1, 0xfb13, 0x1acd, 0xa7cb, 0x7fa6, 0xfdff, 0xf53f, 0xfdd1, 0xe39f, 0x470e, 0xdae9, 0x8ffa, 0x779f,
        0xed3d, 0x49cf, 0xd7ff, 0x65f3, 0x91fe, 0x43c4, 0xc2da, 0x557b, 0x3d0f, 0x9d8b, 0xe4df, 0x9a25, 0xabff, 0xffe0, 0x6fcb, 0xe9b6,
        0xb53b, 0xd976, 0x6e67, 0x796e, 0x1eea, 0xf292, 0xd828, 0xfb3a, 0xdaf0, 0x6cf9, 0xf65f, 0x62d5, 0x6dc, 0x8c69, 0x2839, 0xf653])),(BitVec.ofNat 768 (fromLimbs [0x9952, 0x888, 0xbc44, 0x1a08, 0x8081, 0x8840, 0xf90, 0x6aa, 0x3802, 0x7780, 0x8041, 0x8a4, 0x2161, 0x4804, 0x4a0, 0x8592,
        0x84, 0x8c26, 0x34, 0x4300, 0x1128, 0x1a00, 0x10, 0x4010, 0x2808, 0x900, 0x28e0, 0x4844, 0x8151, 0x4130, 0x3849, 0x4402,
        0xef02, 0x8285, 0x9485, 0xe014, 0x1280, 0x40a0, 0x31e0, 0x8189, 0xc024, 0x2002, 0x180c, 0xb0f0, 0x4d19, 0xd48, 0x2811, 0x2652]))),((BitVec.ofNat 768 (fromLimbs [0x6f53, 0xeedf, 0x3e34, 0xf5ed, 0x54d6, 0xbf7e, 0x1fff, 0xf7d, 0x43ff, 0x9f66, 0x7beb, 0x1928, 0xff77, 0xd9f5, 0xed55, 0xffb6,
        0x7fdc, 0xbbdd, 0xf3e7, 0xbdff, 0xfefa, 0xea5d, 0x6eb4, 0xa6e7, 0xe6a7, 0xcf77, 0xd8cd, 0x6f9e, 0x6efa, 0xfc7f, 0xdfde, 0xb6fd,
        0xcfbf, 0x3ddb, 0x8fe9, 0xff16, 0xe7f6, 0xfde5, 0xb7df, 0x4e2b, 0x3f7a, 0xb38d, 0xeae8, 0x71aa, 0x3b7e, 0x5391, 0x7e26, 0x487f])),(BitVec.ofNat 768 (fromLimbs [0x481, 0x211, 0xa0, 0x10, 0x108, 0x1017, 0x8040, 0x4041, 0x28, 0x848, 0xc08, 0xa002, 0x2, 0x124a, 0x342, 0x6800,
        0x1400, 0x0, 0x8440, 0x23, 0x2a01, 0x4408, 0x3100, 0x2404, 0x4121, 0x22, 0xb, 0x438, 0x8, 0xa81, 0x6, 0x894,
        0x24, 0x5000, 0x4058, 0x863, 0x2028, 0x100, 0xc, 0x800, 0x1541, 0x10, 0x300, 0xa, 0x2a6, 0x2010, 0x422, 0x4829]))),((BitVec.ofNat 768 (fromLimbs [0x74d5, 0xebbd, 0xd9eb, 0x9a5f, 0xb6bd, 0x77df, 0xeba4, 0xbccb, 0x17df, 0x28cb, 0x12ed, 0x7fee, 0x19f5, 0x6f97, 0xfa51, 0x9e4b,
        0xf2d7, 0x5c34, 0xe8c4, 0x9b07, 0x66e7, 0xbdba, 0xf577, 0x997b, 0x977e, 0x76cf, 0x6b3e, 0xcf79, 0xf39a, 0x2c5e, 0x5037, 0x6d1f,
        0x6d65, 0xbbd3, 0x7535, 0x3bfb, 0x16bf, 0x97bf, 0x67b9, 0xf1c7, 0xfb85, 0xb75e, 0xbbe5, 0xdd44, 0xc503, 0x731e, 0xb1c3, 0x8f9c])),(BitVec.ofNat 768 (fromLimbs [0xb120, 0x68, 0x454, 0xa1c0, 0xc087, 0xa960, 0x6d15, 0x36a4, 0x604, 0x1301, 0x126, 0x5045, 0x5d30, 0x20a5, 0x2438, 0x21a,
        0x8344, 0x900a, 0x6029, 0x8a04, 0xc004, 0x2310, 0xf1, 0x1012, 0xa80, 0x2b50, 0xac00, 0x881, 0x5607, 0x500a, 0x1111, 0x1069,
        0x408, 0x8181, 0x2883, 0x6100, 0x5301, 0x8610, 0x81a1, 0xa010, 0xa20c, 0xc180, 0x5418, 0x4144, 0x9d09, 0xc605, 0x3181, 0x8514]))),((BitVec.ofNat 768 (fromLimbs [0x1dd5, 0x6f61, 0x45df, 0x333f, 0x162d, 0xd2d7, 0x7f55, 0xf59b, 0x1cd7, 0xa7e5, 0x40f, 0x75cd, 0x4be0, 0x664b, 0xd92e, 0xbe4d,
        0xeb3, 0x27fb, 0xca83, 0x265c, 0x648d, 0x75ab, 0xbbad, 0x8eb3, 0x91fb, 0x79d7, 0x77e6, 0x6057, 0x3e79, 0x23c2, 0x37a7, 0x79d,
        0x28f5, 0xbf28, 0x1f3d, 0x5dfd, 0xb599, 0x30b, 0xc872, 0x2dc5, 0x6dad, 0x83fb, 0xabc5, 0xbed8, 0xc223, 0x200e, 0xc1fc, 0xfc0])),(BitVec.ofNat 768 (fromLimbs [0x40da, 0xb592, 0x1b2b, 0x1c0c, 0x3c00, 0x4217, 0x9068, 0x4018, 0x9039, 0x604c, 0x20d1, 0x8490, 0x28e, 0x8748, 0x1c4, 0x2925,
        0x13, 0x4540, 0x102, 0x344b, 0x150, 0x84ad, 0xb40e, 0x8244, 0x603e, 0x4027, 0x3f8, 0xf54a, 0x8800, 0xd1, 0xa286, 0x4a06,
        0x8a7, 0x1c78, 0x724, 0x94ae, 0xa884, 0x79a4, 0x385c, 0x1666, 0x462, 0x2654, 0x2807, 0x36bb, 0x62f6, 0x391a, 0xc07c, 0xac0]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xf12e, 0x51fe, 0x9df1, 0x5d5a, 0xfdd0, 0x233c, 0xf761, 0xe695, 0xb8e9, 0x777f, 0xaf7c, 0xe3fb, 0x672f, 0x3679, 0x82ef, 0x85f5,
        0xe529, 0xcf3e, 0xeeb8, 0x47a7, 0x6de6, 0xddb3, 0x265a, 0x731c, 0xacb7, 0xa2ab, 0xf493, 0xf368, 0x8135, 0xa382, 0x6951, 0xfc8a,
        0x3ee7, 0xcdae, 0xef72, 0x3df5, 0xec7c, 0xad13, 0xa8e4, 0xdf56, 0xa826, 0x4f25, 0xfdbb, 0xc71d, 0x482, 0xcce0, 0x1ff, 0xf020])),(BitVec.ofNat 768 (fromLimbs [0x62d, 0x3466, 0x4091, 0x6534, 0x6f58, 0x72bf, 0x3026, 0x7001, 0x4248, 0x8812, 0x448c, 0x6140, 0x860a, 0x29, 0xfa5d, 0x7040,
        0x8079, 0x4390, 0x78c0, 0x388e, 0x8447, 0x21ae, 0x8762, 0x8427, 0x536, 0xd4f5, 0x1410, 0x100a, 0x66a4, 0xa8c2, 0x326, 0x809d,
        0x1000, 0x3048, 0x687a, 0xb01, 0x4d0c, 0x2b1c, 0xc808, 0x210, 0x1402, 0x82d5, 0x42c0, 0xf0f, 0xb0c6, 0xf2b1, 0x81ee, 0xd020]))),((BitVec.ofNat 768 (fromLimbs [0xf7c3, 0x26c3, 0xfabb, 0x7b07, 0x65ec, 0x93ba, 0x313d, 0xac9b, 0x402a, 0x6356, 0xd93b, 0x6b34, 0xb738, 0x9b77, 0x43e, 0x973c,
        0x1898, 0xab9d, 0x236f, 0x96cd, 0x5df8, 0xf8cd, 0xcb4, 0x36c7, 0x74f0, 0xb8fe, 0xdc80, 0x23ff, 0x72e, 0xe8d5, 0xe4af, 0xb670,
        0xfcc, 0xc679, 0x8ab9, 0x9e23, 0xe7c6, 0xa9e2, 0x92ee, 0x6cbd, 0xcefb, 0x92e6, 0xf289, 0xf7fe, 0x3c20, 0xee, 0x7f04, 0x20])),(BitVec.ofNat 768 (fromLimbs [0x9064, 0xad20, 0xc501, 0x83c0, 0x9a17, 0x400, 0x1d14, 0x8a08, 0xa192, 0x93a2, 0x73a4, 0x47c8, 0xf1ac, 0xda0, 0x9c0d, 0x828d,
        0x8ad3, 0x6b89, 0x68a6, 0xa59c, 0x512, 0x1bd7, 0x8a4a, 0x9808, 0xb68c, 0xdd91, 0xa9f0, 0xe843, 0xe431, 0x7020, 0xe8a8, 0x7202,
        0x230b, 0x20b0, 0xa706, 0x3600, 0x1ec2, 0xc82, 0xb60, 0x63c8, 0x421e, 0x718a, 0xf411, 0xcff5, 0xfd59, 0x9fef, 0xfb04, 0x0]))),(0,0),(0,0)]
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
def known111 := extendKnown known63 7 [(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(413,[134,117,33,32,65,48]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := (fromLimbs [0x42, 0xf9f2, 0x8c08, 0x1400, 0x0, 0x20, 0xf801, 0x630c, 0xd0])
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0xb1dc, 0x1ff7, 0x132a, 0x7ff6, 0xe795, 0x4acd, 0xad6b, 0xfbbb, 0x4172, 0x275f, 0x57d4, 0x85ef, 0xe917, 0xeeb7, 0x1c7f, 0xf77e,
        0xf27, 0x10ed, 0xeec0, 0x9b15, 0x4b6e, 0x1e5d, 0x7bf5, 0x4df3, 0xf4dd, 0x5c7d, 0xd493, 0x8def, 0xdfcc, 0xf59e, 0xee87, 0x375e,
        0xf555, 0x2cb6, 0xbdff, 0x87f9, 0xe5f8, 0x848f, 0x3787, 0x7351, 0xffeb, 0xb95f, 0xb54e, 0x1da6, 0x4108, 0x12b, 0xd832, 0xf47c])),(BitVec.ofNat 768 (fromLimbs [0x68, 0x874, 0x2300, 0xa3a, 0x31, 0x12a0, 0x8, 0x2c31, 0x4400, 0x2014, 0x6209, 0xe00a, 0x2443, 0xb088, 0x26a2, 0xc783,
        0xc22a, 0x2018, 0x806d, 0x94, 0x2af, 0x4218, 0x9033, 0x1400, 0xc10, 0x8040, 0x96c6, 0x4039, 0x5c, 0x4080, 0x4a80, 0x1120,
        0x2bd0, 0x30a1, 0x649, 0x2006, 0x4111, 0x3e22, 0x4050, 0x50, 0x4017, 0x804, 0x503a, 0x1d85, 0x9600, 0x2119, 0x9906, 0xa42c]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xeb6f, 0x6506, 0xf1e2, 0xaa6d, 0xee22, 0x6de1, 0x56dd, 0xffe9, 0x4e5, 0x7bee, 0xad59, 0x7045, 0x13e2, 0xe966, 0xffdb, 0x64a3,
        0xf7b8, 0xdb55, 0xbb1f, 0x1a9e, 0x751d, 0x7de3, 0x3b4c, 0x6bc3, 0x92f4, 0x2ec3, 0x74ec, 0xbbaf, 0x3654, 0xc836, 0x729b, 0xe4ba,
        0xa8a1, 0xb074, 0x3f34, 0x7b7a, 0xfe53, 0x6de5, 0xff5b, 0x1928, 0x9bf0, 0xa963, 0x347b, 0xac45, 0x8a97, 0x5004, 0x2f2d, 0xc84f])),(BitVec.ofNat 768 (fromLimbs [0x8c00, 0x1201, 0xc00c, 0xc140, 0x602, 0x117d, 0x4102, 0x4270, 0x2011, 0x1440, 0x481, 0x2242, 0x1e2, 0x4010, 0x1800, 0x1002,
        0x2d20, 0x8a08, 0x699a, 0x4082, 0x1070, 0x1c62, 0x4230, 0x1589, 0x98b1, 0x4904, 0x1665, 0x2250, 0x4000, 0x409, 0xa4, 0x4c62,
        0x94a0, 0x8030, 0x4188, 0xc2f2, 0x8062, 0x10c, 0x4680, 0x8321, 0x10, 0xd400, 0x810, 0x4c6, 0x1e45, 0x4406, 0x1425, 0xc84a]))),((BitVec.ofNat 768 (fromLimbs [0xf66b, 0xc486, 0xedbf, 0x6752, 0x992c, 0xfed2, 0x569e, 0x9459, 0xbf37, 0xbdf6, 0x868a, 0x4b58, 0x1370, 0x516e, 0x1540, 0x8dc4,
        0xead6, 0xb1da, 0x975d, 0xc462, 0xfef7, 0x25ca, 0x8dda, 0x991e, 0xbd30, 0xaea, 0x7845, 0x6370, 0xee84, 0x4f97, 0x9859, 0xbc9f,
        0x5dea, 0xfd42, 0xe238, 0x7048, 0xee48, 0xd79c, 0x7ef3, 0xf0ec, 0x5855, 0x64e6, 0x4ffb, 0x9958, 0xe417, 0xa600, 0x21ce, 0xf8f])),(BitVec.ofNat 768 (fromLimbs [0x141, 0x86c, 0x2342, 0x24, 0x210c, 0x2e02, 0x90d8, 0x8c82, 0x820a, 0xc202, 0x680c, 0xd018, 0x1404, 0x8805, 0x6065, 0xc915,
        0x9259, 0x51, 0x9600, 0x91c, 0x4b00, 0xc089, 0xb40a, 0x22, 0x400a, 0xa272, 0xc090, 0x48ab, 0x84ed, 0xc290, 0x42, 0x1199,
        0x610c, 0x4d05, 0x463, 0x2501, 0x3709, 0x1683, 0x78, 0x3810, 0xa165, 0x947, 0xc0cd, 0x1909, 0xe00a, 0x3a18, 0xe18a, 0x685]))),((BitVec.ofNat 768 (fromLimbs [0x1be0, 0xdbb4, 0x733b, 0x3fde, 0xa539, 0xdb5d, 0xc1e4, 0xd61, 0xba39, 0x7321, 0xdeab, 0xaa5c, 0x9e79, 0xb42d, 0x6566, 0xbd39,
        0x6bf5, 0x1599, 0x6fe7, 0xf579, 0x83f5, 0x1a71, 0xa1c9, 0xbade, 0xffcf, 0x76fe, 0x2399, 0x4df, 0xfc78, 0x9ed5, 0x7f5, 0x4ab9,
        0x755f, 0xcbae, 0x7d5a, 0xee82, 0x615d, 0x191e, 0xf434, 0x8fdd, 0x8cad, 0x469f, 0xbbb1, 0xe778, 0x400, 0xa62f, 0x50f1, 0xf70])),(BitVec.ofNat 768 (fromLimbs [0xf886, 0x4002, 0x809, 0x9000, 0xc642, 0xc109, 0x6206, 0x0, 0x38a4, 0x9a0, 0x9502, 0x580, 0xa30, 0x270, 0x8108, 0x8,
        0x880, 0x8286, 0x2810, 0xe023, 0x8410, 0x3420, 0x4100, 0xe145, 0x80a5, 0x5185, 0x8, 0x9440, 0x5100, 0x45, 0x2509, 0xea42,
        0x1003, 0x212, 0x5980, 0xd258, 0xa6, 0x4140, 0x3680, 0x4386, 0x1e08, 0x5288, 0x700, 0xe272, 0x1f4, 0xc426, 0x71, 0x950]))),((BitVec.ofNat 768 (fromLimbs [0x759, 0x515f, 0x9d7e, 0xe0bf, 0x78df, 0x1fe7, 0xad5a, 0xfa9e, 0xeb6e, 0x9dbe, 0x6bad, 0x8fb7, 0x6e9e, 0x7bd4, 0x1f89, 0x6f6f,
        0x2536, 0x247e, 0xcf38, 0x2b95, 0xe96b, 0xd25e, 0x7fbf, 0x1eff, 0xa33e, 0xd91b, 0x9f56, 0xce60, 0x9f3, 0x7fe8, 0xfd2f, 0xbfef,
        0xc6ee, 0x8f4d, 0xccf1, 0xe8bf, 0x40ae, 0xa3c1, 0x97b6, 0xfe1a, 0xee12, 0x9e4e, 0xcf84, 0xd2c2, 0x7969, 0x9d0, 0x80fb, 0xf080])),(BitVec.ofNat 768 (fromLimbs [0xe680, 0xc603, 0x5803, 0x3181, 0x540c, 0x8009, 0x3916, 0x9140, 0x1c, 0xc040, 0xdc0, 0xa4, 0x4980, 0x201, 0x1850, 0x3844,
        0x2c40, 0x8c0, 0x182, 0x4242, 0x1950, 0x9c40, 0x4608, 0x205, 0xb1a3, 0x722e, 0x801, 0x1b40, 0x6820, 0xa01, 0x9120, 0xc05,
        0x9000, 0xb46, 0x3000, 0x1261, 0xb08c, 0x188, 0x68a, 0xa2ac, 0x820, 0x5289, 0x8240, 0xc042, 0x684f, 0x5e82, 0x40f9, 0x5000]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xfc3e, 0x2eb8, 0x6c64, 0xe5fb, 0xbe73, 0x79bb, 0x3583, 0x650f, 0x2e89, 0xc5fe, 0xbf79, 0xf8f9, 0x8fbf, 0x1cf7, 0xeff5, 0x3fb3,
        0xdbe9, 0xffcb, 0xe6ff, 0xec89, 0xecb8, 0xcf31, 0xf5e3, 0xfad6, 0xef7b, 0xf308, 0xcfab, 0xf802, 0x587f, 0xcdf1, 0x87b9, 0x49b9,
        0x272c, 0xda3b, 0x7845, 0x2b96, 0xbae7, 0xffe5, 0xcf4d, 0xdef2, 0x9ee, 0x4bce, 0xe6cd, 0xfb3d, 0xbae0, 0x59d5, 0x2e01, 0x80])),(BitVec.ofNat 768 (fromLimbs [0x1100, 0xac, 0x2680, 0xe3e, 0xa1d1, 0x6e02, 0x8420, 0x2c86, 0xdf22, 0x182, 0xb028, 0x5010, 0x9605, 0xb582, 0x4228, 0x8018,
        0xd292, 0x6115, 0x1240, 0x9401, 0x8005, 0x428c, 0x8886, 0x10, 0x424c, 0x8080, 0xe09a, 0x42f, 0xc, 0x3124, 0xa4b, 0x3300,
        0x91d, 0x481, 0x8606, 0x250c, 0x11, 0x1e23, 0x2900, 0x402, 0x254b, 0x26, 0x4109, 0x3b39, 0x81b0, 0xa179, 0xab00, 0x80]))),(0,0)]
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
def known127 := extendKnown known189 9 [(127,[]),(381,[129,82,113,48]),(499,[98,99,81,131,114,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := (fromLimbs [0x9909, 0x0, 0xb500, 0x0, 0x1a1, 0x52f0, 0x5d5c, 0xe, 0x4006, 0x800, 0x1574, 0x9fa6, 0x141, 0xc738, 0x2b0, 0xa681,
        0x3797, 0x6081, 0xbca1, 0x99ea, 0xaa3d, 0x9613, 0x88c0, 0xf3a0, 0x23, 0x28c0, 0x84, 0xa050, 0x8, 0x9c2a])
def g191d9 (i : Nat) : Nat := (fromLimbs [0x288, 0x6161, 0x80c4, 0x8a11, 0x66c0, 0x8c8, 0x1858, 0x8a2e, 0x4e, 0x68c2, 0xc214, 0x19c, 0xe185, 0x88b2, 0x4101, 0x294,
        0x4c30, 0x431, 0xc508, 0x9360, 0x1813, 0x8408, 0x512, 0x18b0, 0xc032, 0x8614, 0xb0a0, 0x3013, 0x9610, 0xc080, 0x3944, 0x862a,
        0x8614, 0x8887, 0x403, 0x8c28, 0x4240, 0x1827, 0x8d60, 0x745, 0xa25b, 0x53e4, 0x3cce, 0x27c5, 0xe0bc, 0xff, 0x483f, 0xe30f,
        0xf4c3, 0xfd10, 0xff54, 0xffe1, 0xff9, 0x3fe, 0x20ff, 0x4c7f, 0xc20f, 0xf58f, 0xfd40])
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := (fromLimbs [0x1, 0x4000, 0x0, 0x0, 0x19, 0x8cb0, 0xa, 0x4e0, 0x8a52, 0x1, 0xa51c, 0x2000, 0x531, 0xe80b, 0x6438, 0x8d00,
        0x789, 0x63d8, 0xa75, 0x2480, 0x343, 0xb41a, 0x6708, 0x0, 0x7a7c, 0xc632, 0xd752, 0x3950, 0x2d60, 0x7286, 0x4000, 0x0,
        0x60, 0x8400, 0x0, 0x2a10, 0x28, 0xa67e, 0x35db, 0xbd50, 0x1a, 0x6c31, 0x5cd7, 0xa0d1, 0x13ac, 0x2700, 0x121, 0x8000,
        0x5256, 0x8158, 0x594e, 0xc000, 0x682a, 0xf900, 0xf6, 0x8800, 0x1, 0xb6f, 0xab80, 0x321, 0xac31, 0x374a, 0x97c0, 0x180,
        0x6824, 0x3a2b, 0x9f0, 0x6ef8, 0xc800, 0xc98, 0x4c7f, 0xad80, 0x73, 0x2e29, 0xd36f, 0xd3c9, 0xba46, 0x6000, 0x3, 0xc50a,
        0x43a2, 0xe72f, 0x0, 0x37c, 0x5c48, 0x4413, 0x0, 0x6096, 0x6343, 0xd567, 0x81f, 0xd240, 0x16, 0x1fd8, 0xfb85, 0x7db1,
        0x616c, 0x2d70, 0xbc00, 0x1da, 0x5049, 0x81c0, 0xa8, 0xcb68, 0x709b, 0xaa54, 0x3933, 0x5015, 0x3817, 0xe93b, 0x2ee0, 0x8a0b,
        0x35c9, 0x71e4, 0x8126, 0x48c4, 0xcf0, 0xc890, 0x74a, 0x5b90, 0x1b85, 0xc19b, 0x60f, 0xf30, 0xf9c6, 0xd46f, 0x8229, 0x9e4,
        0x68ae, 0x58b6, 0x1, 0x460, 0x7b, 0x14, 0x2a8d, 0xc0d2, 0xc800, 0x31c, 0x6000, 0x5ad2, 0x8d4a, 0x6000, 0x0, 0x0,
        0x4, 0x6100, 0x0, 0x0, 0x0, 0x59, 0x7800, 0x750, 0xc07f, 0xc419, 0xa5a3, 0x3000, 0x612d, 0xc384, 0x51b0, 0x4000,
        0x33f, 0xe570, 0x0, 0x2d7, 0x6000, 0x244c, 0x429f, 0x180a, 0x5d34, 0xb0ba, 0x1360, 0x1a, 0x731a, 0xfd48, 0xa565, 0xb2f8,
        0x6006, 0x14, 0xb1d8, 0x111a, 0xaaac, 0x6000, 0x56d8, 0x0, 0x0, 0x26c, 0x2da6, 0x8678, 0xcd5b, 0x803a, 0xe000, 0x10d9,
        0x1906, 0xc600, 0x0, 0x173e, 0xc82c, 0x4200, 0x58c, 0x8000, 0x0, 0x1b, 0x509c, 0x9847, 0xce37, 0xe900, 0x1c4, 0x66a9,
        0xe954, 0x0, 0xc9, 0x9484, 0xd7ca, 0x82a8, 0xf9, 0x3447, 0x1820, 0x24f8, 0x0, 0xc48d, 0xc000, 0x5960, 0x3008, 0x3ad0,
        0x5a1c, 0x7500, 0x6c10, 0x8174, 0x1081, 0x4060, 0x62c, 0x3582, 0x51, 0x841c, 0x80, 0x1071, 0xc964, 0x60c2, 0x0, 0x20c,
        0x70c0, 0x1c90, 0x8b0c, 0x0, 0x800, 0x4, 0x1016])
def g191d8 (i : Nat) : Nat := (if i<1 then (fromLimbs [0x50b3, 0xa06, 0x2068, 0x860c, 0x1071, 0x6208, 0x2818, 0x8001, 0x141c, 0x8803, 0x8918, 0xb140, 0xc61c, 0x40b1, 0xa082, 0x1c49,
        0x40b, 0x10a1, 0x8885, 0xa129, 0xe2, 0x4686, 0x10b1, 0x4406, 0x3043, 0x8589, 0x8b1, 0x4312, 0x2d10, 0xc2a2, 0xe20, 0x5960,
        0x4618, 0x2c82, 0xc608, 0x3221, 0x60c8, 0x2460, 0x8807, 0x1094, 0x4385, 0x9050, 0x3146, 0x400c, 0x68a0, 0xc1a, 0x1022, 0xc630,
        0x5831, 0xc016, 0x3064, 0x389, 0x2811, 0x60c8, 0x2460, 0x8407, 0x10c1, 0x40c6, 0x900, 0x90e4, 0x480, 0x3892, 0x100e, 0x1864,
        0x386, 0x18c1, 0x6240, 0x1c48, 0xc60b, 0x1601, 0x80d1, 0x1110, 0x3182, 0x838b, 0x1239, 0x143, 0x214, 0x1c48, 0xb3a5, 0x181c,
        0x5091, 0x7083, 0x2050, 0x7124, 0xc195, 0x160c, 0x3163, 0x1438, 0x9160, 0xc904, 0x48d1, 0x8712, 0xc61, 0x1089, 0xe34, 0x5144,
        0x8180, 0x2c80, 0x858c, 0x1c10, 0x41c4, 0x8b28, 0x1142, 0xc624, 0x7080, 0x8212, 0x2c82, 0x4689, 0x2c61, 0x458c, 0x2b06, 0x10e2,
        0xc48e, 0x44a0, 0xc1c5, 0xa206, 0x5c02, 0xc60d, 0x3011, 0x6309, 0x48, 0x7244, 0x228, 0x58c1, 0x714, 0x3100, 0x4002, 0xe2c,
        0xc1c4, 0x8849, 0x30e0, 0xc81c, 0x48b2, 0x80ca, 0x8848, 0xb18a, 0x620, 0x243, 0x8c50, 0xb10c, 0x1620, 0xe247, 0xc62, 0x6160,
        0x4487, 0x1e70, 0xa1c0, 0x8a22, 0x50e2, 0xc542, 0x1260, 0xc1d0, 0x8b26, 0x2102, 0xc626, 0x1020, 0x2285, 0x9800, 0xf123, 0x830,
        0x1250, 0x228a, 0x48, 0xb18c, 0x1621, 0x8984, 0x8702, 0x210, 0xb405, 0x1306, 0x221, 0x61ce, 0x1858, 0xa193, 0xe0c, 0x61c0,
        0xd16, 0xca0, 0x458a, 0x1c11, 0x21c1, 0x9208, 0x90e0, 0xc808, 0x3a11, 0x22ca, 0x500, 0xb062, 0x4a0a, 0x72, 0x4418, 0x1c48,
        0x2424, 0x459c, 0x6071, 0x22c8, 0x2c08, 0x7120, 0xcb00, 0x71, 0x6414, 0xc48, 0x60a, 0x1240, 0xe251, 0x16, 0x28c3, 0x6c5,
        0x4c09, 0x413, 0x820f, 0x449, 0x187, 0x1630, 0xc3c3, 0x8c24, 0x58d8, 0x3090, 0x30a1, 0xa245, 0x9716, 0x142, 0xc9ba, 0xdb87,
        0xb53b, 0x11ae, 0xbaa9, 0xa75a, 0x41a0, 0xd9cb, 0x9a59, 0x5592, 0x18df, 0x8b98, 0x9385, 0xf82b, 0x7db7, 0x9977, 0x3731, 0x70b6,
        0xe56a, 0x367d, 0x6496, 0x155e, 0x15ad, 0x5795, 0x5351, 0x14eb, 0x4c54, 0x9144, 0xf40d, 0x3d93, 0xa537, 0xf34b, 0x3252, 0xe326,
        0x91fd, 0x1831, 0x330e, 0x30a1, 0x6d0, 0x2afd, 0xaf98, 0xf64f, 0x14ee, 0xeba, 0xe78e, 0x52e2, 0xcd96, 0xd46d, 0x12cd, 0xc8e,
        0xc5ac, 0x26bc, 0x8ba2, 0xb60b, 0x10ad, 0xcab6, 0xa82a, 0x5ca3, 0x6a02, 0x9969, 0x548f, 0x68b4, 0x8808, 0x227e, 0x790, 0x75c7,
        0x366b, 0xc650, 0x61c5, 0xe859, 0x8564, 0x5224, 0xe049, 0x440, 0x3fe3, 0x9235, 0x300, 0x2be2, 0x9825, 0x61f8, 0x18c1, 0x4a11,
        0x60d4, 0x920, 0x4200, 0x1ff5, 0x4930, 0xffaa, 0xa07, 0xfd71, 0x483f, 0xeb1c, 0x21ff, 0x5012, 0xffc, 0xc520, 0x7fd5, 0x2503,
        0xfe98, 0x221f, 0xf58e, 0x20ff, 0xac09, 0x87fd, 0x1058, 0xffeb, 0x9a41, 0xff58, 0x640f, 0xfa60, 0x907f, 0xd724, 0x43fe, 0x882a,
        0x7ff5, 0x910, 0xffee, 0x2907, 0xfd20, 0x58ff, 0xe98c, 0x41ff, 0x5413, 0x1ffa, 0x2090, 0x7fd2, 0x1903, 0xfeb1, 0x281f, 0xf481,
        0x53ff, 0xa42a, 0x7fe, 0x7244, 0x3fe9, 0xc41, 0xffdc, 0xd20f, 0xfa65, 0x87f, 0xd328, 0x83fe, 0xb0c6, 0x1ff8, 0xca10, 0xffa4,
        0x3187, 0xfd21, 0x58ff, 0xeb9a, 0x21ff, 0x5493, 0x1ffa, 0xc098, 0xffd6, 0x2903, 0xfeb1, 0x461f, 0xf589, 0x31ff, 0xac0a, 0x7fd,
        0x204c, 0x7fa3, 0x8a41, 0x7f5c, 0x520b, 0xfae5, 0x107f, 0x9208, 0x42ff, 0xb928, 0x1fdd, 0xc520, 0xff22, 0x1105, 0xfd75, 0x902f,
        0xeb88, 0x417f, 0xdd11, 0xfba, 0x60b1, 0xfdd3, 0x24c6, 0xfeb9, 0x4617, 0xf5ce, 0x10bf, 0xee0a, 0x9dfd, 0x7054, 0xefeb, 0xac61,
        0xfdc8, 0x610b, 0xfee2, 0x907f, 0x9104, 0x82ff, 0xb926, 0x3fd4, 0x8531, 0xbfee, 0x2b1f, 0xbf74, 0x4c2f, 0xfbb2, 0x617f, 0x5c16,
        0x3bfa, 0xed18, 0x5ff7, 0x1502, 0xffb9, 0x2217, 0xf5c5, 0x53bf, 0xae91, 0x5fd, 0x7690, 0x2feb, 0x9c41, 0x7f5c, 0xc20b, 0xfee2,
        0xa9df, 0xf704, 0xc7de, 0xa148, 0x17f5, 0xca10, 0xff26, 0x905, 0xff72, 0x58fe, 0xe982, 0x637f, 0xdd53, 0x1fea, 0x6308, 0x7dd3,
        0x54e, 0xfeb9, 0x2637, 0xf5c1, 0x31bf, 0xae2b, 0x1dff, 0x724c, 0x2ffb, 0xb281, 0x7fdc, 0xd10f, 0xf261, 0x105f, 0xd718, 0xc2fe,
        0xb8c8, 0x17fd, 0xcd20, 0xbfee, 0xaa05, 0xff70, 0x58ef, 0xeb9a, 0x41fe, 0x4823, 0xbfa, 0xe310, 0x7dd3, 0x258e, 0xfeba, 0x4217,
        0xfdd5, 0x30bf, 0xee29, 0x87f5, 0x514c, 0x6feb, 0x9481, 0x7f5c, 0x963b, 0xfeec, 0x98df, 0x7714, 0x82ee, 0xb9c4, 0x16fd, 0xd130]) else 0x10410e24)
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := (fromLimbs [0x38, 0xd505, 0x5793, 0xc367, 0x9268, 0x754b, 0xc618, 0x8000, 0x1b, 0xef92, 0x589, 0xc626, 0xa650, 0x70, 0x140c, 0x8d5d,
        0xe5f1, 0xd7a2, 0x1d03, 0x44d9, 0x8ee8, 0x18, 0x3ee4, 0x8800, 0x1, 0x1197, 0x1a1, 0x89f7, 0xac18, 0xd073, 0xc41c, 0x5a46,
        0xf2f, 0x6dbb, 0xd3e, 0x90a0, 0x6b82, 0xf5bc, 0xc029, 0x28e3, 0xaa85, 0x2e88, 0x0, 0x109c, 0x3461, 0x6429, 0x775d, 0x57a0,
        0x841, 0xde89, 0x68c7, 0x53cd, 0x4f77, 0x7943, 0x6ba6, 0x25de, 0x8998, 0x9907, 0x1c11, 0x166c, 0x728, 0x5d41, 0x58b1, 0xc40c,
        0xba38, 0x1970, 0x1ff1, 0xed4e, 0x0, 0x1d, 0x75e3, 0x8654, 0x5f25, 0xc03c, 0x4e3c, 0xcfe7, 0x905e, 0x2217, 0x7700, 0x0,
        0xa10, 0x5, 0x11f, 0x8991, 0x186d, 0x8000, 0x14, 0x4100, 0x8f, 0x3130, 0x25a4, 0x33c0, 0xcd88, 0xdae6, 0x60be, 0x9400,
        0x121, 0xc000, 0x2, 0xc880, 0x0, 0x655, 0xb0af, 0x5234, 0x2fd8, 0xc3fb, 0xe11d, 0x390, 0x49a5, 0xa1e7, 0x3251, 0x8000,
        0x4d4e, 0x9a30, 0x8f4f, 0x4000, 0xe, 0xf180, 0x2b07, 0xe014, 0xcea1, 0x70ac, 0xb800, 0x0, 0x9b4, 0xc400, 0x8e61, 0xbc79,
        0xa059, 0xa0f7, 0xfcc, 0xb137, 0xf85b, 0x2554, 0xdc00, 0x0, 0xf21, 0xe93d, 0x1260, 0x12, 0x5800, 0x3490, 0x0, 0x0,
        0x283, 0xab34, 0x0, 0xb, 0x1c00, 0x0, 0x3, 0x1850, 0x23a5, 0x3196, 0x8aa, 0x1, 0x9134, 0x7800, 0x0, 0x0,
        0x0, 0x46, 0x6214, 0x0, 0x0, 0x0, 0x5b0, 0xdc8e, 0x0, 0x42, 0x6e6c, 0x726f, 0x99d4, 0x15a6, 0xc304, 0x5000,
        0x1270, 0x23e0, 0x70c8, 0xd80b, 0x8894, 0x363, 0x1ef9, 0x64fd, 0xd219, 0x6b35, 0x879c, 0xa860, 0xc065, 0x6093, 0xc9b6, 0x6e60,
        0x4e1a, 0x8c2, 0x3, 0xc849, 0x4d72, 0x2896, 0x4094, 0xcaf5, 0x9a81, 0x39a1, 0x49ac, 0xc, 0x1510, 0x5044, 0x2, 0xc010,
        0x242, 0x821, 0x1104, 0x7148, 0x2078, 0x8109, 0x5147, 0x800, 0x4204, 0x7000, 0x20, 0x10, 0x1c0, 0x2830, 0xc504, 0x1,
        0x400, 0x8004, 0x540, 0x402, 0x400, 0xc0, 0x80, 0x708, 0xc1, 0x0, 0xd00, 0x4015, 0x1000, 0xc004, 0x141, 0x1880,
        0x0, 0x4000])
def g191d7 (i : Nat) : Nat := (fromLimbs [0x230, 0x4242, 0x1610, 0x2c, 0x2161, 0x208, 0x83, 0x8410, 0x0, 0x58, 0x4883, 0x400, 0x2080, 0x8400, 0x4181, 0x815,
        0x880, 0x8200, 0xa811, 0x584, 0x2c34, 0x108, 0x818, 0x82c4, 0x1, 0x401, 0x6100, 0x6040, 0x4, 0x1288, 0x0, 0x6508,
        0x8242, 0x2, 0x8421, 0x4100, 0xc0, 0x1624, 0x1080, 0x7, 0x850, 0x6042, 0x4a10, 0x0, 0x220d, 0x42, 0xc200, 0x2c,
        0x2041, 0x18, 0x4082, 0x10b0, 0xd084, 0x0, 0x3840, 0x82c4, 0x1210, 0x9080, 0x61, 0x902, 0x848, 0xe842, 0x50, 0x8408,
        0x2000, 0x0, 0x601, 0x881c, 0x2121, 0x0, 0x8bf, 0x14a2, 0x2c38, 0x8670, 0xba10, 0xc148, 0xf00, 0x9fab, 0xe87c, 0x6f79,
        0xecbd, 0x479e, 0xf09d, 0x6ba8, 0x736e, 0x39c4, 0xb7c6, 0xded6, 0x9a6b, 0x4866, 0x6c99, 0x8cb0, 0xc5fe, 0xbe97, 0x2ae0, 0x5b6b,
        0x3964, 0xabc5, 0x6eaa, 0x952a, 0xa053, 0x6a19, 0x40a7, 0xc4ee, 0x9892, 0xaa50, 0x4969, 0x191c, 0xa2c4, 0x4e88, 0x90ea, 0x83f,
        0x67d8, 0xf89e, 0xc3be, 0x748e, 0x29b8, 0x3666, 0xb8d4, 0x9a43, 0x2e62, 0x8be9, 0x782e, 0x65b8, 0xb095, 0x429e, 0x5089, 0xe930,
        0x2464, 0x5888, 0x90c2, 0xe3e, 0x8728, 0xd819, 0x6318, 0x608b, 0xc15e, 0x2484, 0x2880, 0xf61, 0xb830, 0x85c0, 0xae14, 0x8268,
        0x4808, 0x60b8, 0x1081, 0x401e, 0x280, 0x2800, 0xdf48, 0x15ca, 0x209f, 0xd879, 0xc910, 0x9fd8, 0x2dc1, 0x63df, 0x5215, 0xc620,
        0xaff8, 0x6549, 0x31ff, 0x3814, 0x8230, 0xfe92, 0x549, 0x30df, 0x7715, 0xc520, 0x9fd8, 0x2dd5, 0x30b7, 0xf855, 0x8140, 0xbf78,
        0x15c5, 0x20bb, 0xf844, 0xc120, 0x9ff8, 0x15c1, 0x63df, 0x7715, 0x120, 0x9ff8, 0x15c1, 0x539f, 0xd81d, 0xc163, 0xfe92, 0x486,
        0x30df, 0x920d, 0xc530, 0xff21, 0xdc5, 0x209f, 0xd825, 0xc640, 0xf755, 0x1541, 0x31bf, 0x7814, 0x8131, 0xdf78, 0x15ca, 0x10df,
        0x7815, 0xca40, 0xddf7, 0x14c1, 0x63bf, 0x7815, 0xcd20, 0x9fd8, 0x798a, 0x409f, 0xf815, 0xca20, 0xfd55, 0x14c1, 0x31df, 0x9724,
        0x4220, 0xbf98, 0x9c9, 0x10db, 0xf745, 0x4930, 0x9ff8, 0x5c5, 0x639f, 0xd81d, 0xd930, 0xded2, 0xdc9, 0x63cf, 0xd764, 0xc620,
        0xdf48, 0x15ca, 0x40bf, 0x9808, 0xca10, 0xb7f8, 0x5581, 0x319f, 0xd82d, 0xc530, 0xdf92, 0x5c6, 0x30ff, 0x2104, 0x8131, 0x9fd8,
        0xdc5, 0x539f, 0xd81d, 0xd530, 0xbbd8, 0x49c9, 0x10bf, 0x5815, 0x8e10, 0x9ff8, 0x5c9, 0x63af, 0xf865, 0x4940, 0xddf7, 0x14c9,
        0x63df, 0x7715, 0xcd20, 0x9fd8, 0xdd9, 0x319f, 0xd82d, 0xc563, 0xdf55, 0x1dc1, 0x31dd, 0xd215, 0xce20, 0xdf77, 0x14c1, 0x20fe,
        0x9205, 0x910, 0xdf53, 0x15ca, 0x10df, 0x783d, 0xc520, 0x9fd8, 0x25c6, 0x30de, 0xd52d, 0xc931, 0xdbd4, 0x25d6, 0x40df, 0x610d,
        0xd931, 0x9ff8, 0x15cd, 0x20bf, 0x7814, 0x8163, 0xdf55, 0x15c1, 0x319f, 0xd82d, 0xc540, 0xddf7, 0x64c1, 0x319f, 0xd878, 0xca10,
        0x9fd8, 0x1dcd, 0x209f, 0xd80d, 0xc563, 0x9ff8, 0x15ca, 0x40db, 0xd54d, 0xc940, 0xff11, 0xdc5, 0x20db, 0xf745, 0x8130, 0xded2,
        0x15ca, 0x30df, 0x5615, 0xd210, 0xbbf8, 0x44c1, 0x10ff, 0x814, 0x8230, 0x9fd8, 0x2dd1, 0x109f, 0xd82d, 0xd540, 0xdf47, 0x1dcd,
        0x20df, 0x7714, 0x4120, 0xbbf8, 0x45cd, 0x20db, 0xd425, 0xc640, 0xbf78, 0x14ca, 0x10ff, 0x3714, 0xc120, 0xbdf8, 0x3509, 0x10bf,
        0x7814, 0x8153, 0xdf72, 0x15d2, 0x10bf, 0x7815, 0x8131, 0xfe52, 0x485, 0x31bf, 0x7815, 0x4131, 0xded7, 0x2486, 0x40cf, 0xd764,
        0xca20, 0x9ff8, 0x15c9, 0x63bb, 0xf845, 0xcd10, 0xdf58, 0x3dc5, 0x20ed, 0xd635, 0x8130, 0xdf47, 0x15cd, 0x20df, 0x771d, 0xcd20,
        0xddf7, 0x14c1, 0x53ff, 0x714, 0xc120, 0xfd53, 0x14ca, 0x109f, 0x7815, 0xc520, 0x9f78, 0x15cd, 0x209b, 0xf845, 0xc153, 0x9ef8,
        0x25c5, 0x639b, 0xf845, 0xc163, 0x9bf8, 0x45ce, 0x10fe, 0x120c, 0x8610, 0x97f8, 0x55da, 0x408f, 0xd86d, 0xd531, 0x9bf8, 0x45cd,
        0x209b, 0xf845, 0xc131, 0x9f78, 0x15ca, 0x409f, 0x581d, 0xc163])
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := (fromLimbs [0x30, 0x450a, 0xc641, 0xc006, 0x2400, 0xb2c0, 0xa0c, 0x8100, 0x0, 0x1c5, 0x0, 0x42a, 0x883a])
def g191d6 (i : Nat) : Nat := (fromLimbs [0xdf2, 0xb688, 0xde65, 0x43ca, 0x1408, 0xfb4c, 0x102b, 0x9441, 0x93f8, 0x5dd1, 0x604c, 0x23ef, 0x22c1, 0x6eaa, 0x62f, 0xe1b7,
        0x4549, 0x30cd, 0xbc26, 0xe298, 0x2411, 0xf791, 0x61e6, 0x2903, 0x36f0, 0x838a, 0xe690, 0x56de, 0x5183, 0xdc52, 0x8fb, 0x4c0e,
        0x2b9a, 0x419b, 0x784d, 0xc573, 0x4823, 0xef22, 0xc16e, 0xa984, 0x7de4, 0x582d, 0xd110])
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0xbfd3, 0x5797, 0x40f8, 0x2be9, 0xfbed, 0x9f2b, 0xf55b, 0xe3fa, 0xfcb6, 0x662d, 0x6f7f, 0x3cf1, 0x4bf0, 0x8eab, 0xb46d, 0xef1e,
        0x662a, 0xe1c9, 0xf751, 0x2026, 0xffb6, 0xce8c, 0x845e, 0x43cb, 0x1e95, 0xbbd3, 0xca3, 0x7d5f, 0xfae2, 0x7f26, 0x9e36, 0x47fb,
        0xee97, 0xe07f, 0xf865, 0xdd73, 0x12da, 0x8e80, 0xefa3, 0x1334, 0xf8b7, 0x7110, 0xa294, 0xfa2c, 0x1401, 0x1247, 0x6e21, 0x7263])),(BitVec.ofNat 768 (fromLimbs [0x2080, 0xc480, 0x1a91, 0x8000, 0x7, 0x8898, 0x1094, 0x1021, 0x82e0, 0x6420, 0x41, 0xa20e, 0x181, 0x1088, 0x600a, 0x0,
        0xa04, 0x1020, 0x509, 0xa028, 0x8714, 0x10, 0x5234, 0x5290, 0x2400, 0x2326, 0x1b00, 0x8, 0x4008, 0x208, 0x2230, 0x2e04,
        0x2000, 0x42, 0x200, 0x840, 0x1a, 0x8204, 0xe622, 0x10a, 0x1082, 0x3154, 0x4240, 0x618, 0x1028, 0x9, 0x21, 0x2202]))),((BitVec.ofNat 768 (fromLimbs [0xb379, 0x4ce, 0x7ff5, 0x6953, 0xde81, 0xac71, 0x7d90, 0xa710, 0x34d3, 0xd5d4, 0xa6fc, 0x75cc, 0xcee0, 0x9986, 0x647d, 0x661c,
        0x9fc7, 0xe222, 0x4bfa, 0xdc35, 0x9caa, 0xf065, 0x6b39, 0x11ff, 0xba9b, 0xe216, 0xf65f, 0xa1c4, 0x9dbf, 0x8998, 0x74be, 0xe9c7,
        0xf5c5, 0x64fa, 0xfbf6, 0x49e0, 0xe6a5, 0x5061, 0x3dee, 0x46b1, 0x71e5, 0x184, 0x200e, 0x1300, 0x163, 0xa237, 0xccc4, 0x483f])),(BitVec.ofNat 768 (fromLimbs [0x865e, 0x2104, 0x50a, 0x7230, 0x8a50, 0x404, 0x2641, 0xc980, 0x102, 0x8304, 0x4b20, 0x40e1, 0x2412, 0x6c53, 0x1835, 0x55,
        0x19, 0x8c1a, 0xba02, 0x1811, 0x40ab, 0xc567, 0x8c01, 0x8946, 0x8338, 0xd498, 0x8062, 0x7890, 0x8b53, 0x21e7, 0xc4c8, 0x8102,
        0x41a8, 0xc138, 0x49d5, 0x9586, 0x8125, 0x50c0, 0x11dc, 0x2291, 0x6965, 0xcaaa, 0x243f, 0x59e4, 0xc1d3, 0xe726, 0xbcc4, 0x4879]))),((BitVec.ofNat 768 (fromLimbs [0x7656, 0xb9ff, 0xaf7f, 0xbcd6, 0x9696, 0xb5df, 0x89fd, 0x9fd9, 0xae65, 0x5747, 0xdd1d, 0xde16, 0xff5d, 0x7744, 0xcf53, 0x57c7,
        0x8b75, 0x72e, 0x3bbc, 0xb52b, 0xd544, 0x54f9, 0xbc65, 0x746e, 0x7a9e, 0xd839, 0x7e00, 0x9281, 0x9879, 0x95e6, 0x5ee4, 0xa7ee,
        0x5d3, 0x26f4, 0xf397, 0x16d7, 0x5fcb, 0x8767, 0x821a, 0xd46b, 0x8448, 0x825, 0x8e2a, 0x3253, 0xcf6e, 0xa138, 0x8104, 0xd8c])),(BitVec.ofNat 768 (fromLimbs [0x1881, 0x31, 0x1060, 0x8104, 0x24, 0x3a01, 0x2a, 0x49, 0x200, 0x1000, 0x80, 0x412, 0x8824, 0x4, 0x2788, 0x6820,
        0xc422, 0x50e0, 0x5, 0x8040, 0x304, 0x810, 0x6142, 0x2208, 0x30c2, 0x0, 0x101, 0x662, 0x102c, 0xc08, 0x1004, 0x7041,
        0x44, 0x0, 0xb020, 0x40, 0x2002, 0x8721, 0x8002, 0x942c, 0x9618, 0x1045, 0x8040, 0x8003, 0x1c00, 0x1098, 0x4100, 0x8504]))),((BitVec.ofNat 768 (fromLimbs [0x9e7e, 0xcfa1, 0xb663, 0xbe28, 0x9e4e, 0x66e8, 0x5ebe, 0x769c, 0xf03a, 0x281c, 0x40ae, 0xc59a, 0x531a, 0x89bd, 0xc291, 0x7cd7,
        0x5aa4, 0x958, 0xeacf, 0xfcda, 0x90ff, 0xe713, 0x7ad9, 0xbff7, 0xc173, 0xac63, 0xed6d, 0x16fa, 0xf510, 0xb9fc, 0x3b7, 0xf5f2,
        0xd538, 0xed59, 0x2be8, 0x3d12, 0x9d66, 0x69d0, 0x7e8c, 0x8ca, 0x7a9, 0x8c10, 0x1ac0, 0x24d2, 0xc280, 0x4ca4, 0x11f9, 0x9a0])),(BitVec.ofNat 768 (fromLimbs [0x2020, 0xb0c6, 0xa91, 0x6043, 0x1882, 0xc064, 0xa005, 0x310, 0x90c4, 0x2e02, 0x6a, 0xe00c, 0x2440, 0x711a, 0x4040, 0x518,
        0x1394, 0xa05, 0x1c50, 0x1630, 0x12, 0x4107, 0x8600, 0x5480, 0xc0c, 0x2f44, 0xea48, 0x411c, 0xc000, 0xb182, 0x21, 0x8c84,
        0x512, 0xa, 0xe08, 0x838a, 0x4064, 0x28c0, 0x5eec, 0xa42, 0x1a4, 0x2438, 0x5293, 0x645c, 0x4328, 0xc327, 0x10b1, 0xae0]))),((BitVec.ofNat 768 (fromLimbs [0x48af, 0xe352, 0x529d, 0x9f71, 0xe7ba, 0x56c3, 0xdf94, 0x55f8, 0x6aec, 0x7ed2, 0x31a4, 0x182f, 0x1e83, 0x909b, 0x5b57, 0xf4f8,
        0x538a, 0xbddc, 0x7c7b, 0xd3f1, 0xe1b9, 0xb703, 0xaf06, 0x97bd, 0x7a20, 0x6ddf, 0x91ce, 0xbd2d, 0x1fe4, 0x5a97, 0xaba9, 0xde04,
        0x33ff, 0xdbc8, 0x9b85, 0x911b, 0xb195, 0x5413, 0x9111, 0xeda5, 0xcf49, 0xd492, 0x89dc, 0x9481, 0x80, 0x4cc0, 0x31fe, 0x5240])),(BitVec.ofNat 768 (fromLimbs [0x25d, 0x110, 0xc02e, 0x120, 0xe328, 0x1003, 0x64a, 0x8886, 0x6903, 0x819d, 0x1380, 0x1580, 0x523a, 0x664, 0x1510, 0x4801,
        0x4020, 0x8540, 0xc080, 0xc1, 0x5820, 0x3660, 0xc9, 0xa90d, 0x301, 0xd081, 0x436, 0x8a01, 0x1412, 0x4404, 0x884a, 0x4003,
        0x8061, 0xe094, 0x101, 0x2025, 0x3d81, 0x5413, 0x111, 0xe4b5, 0xce49, 0xca82, 0xad2c, 0x98a3, 0x8c92, 0x3cd0, 0x654e, 0xd000]))),((BitVec.ofNat 768 (fromLimbs [0xbb71, 0xfaf6, 0xe605, 0xe9fb, 0x6977, 0x4f3f, 0x236a, 0xffde, 0xc5b0, 0xf6fc, 0x6eeb, 0x31aa, 0xab97, 0x9ba, 0x5982, 0x5f28,
        0xb5e1, 0xb4c9, 0xa929, 0xee60, 0xce31, 0x3e28, 0x61ba, 0x59e0, 0x8d7b, 0x943c, 0xc731, 0xde5f, 0x7b3f, 0x26db, 0x622d, 0x793b,
        0x8c1a, 0xbc51, 0x7578, 0xe539, 0x38e5, 0x3ba8, 0x4144, 0xb4c4, 0xe12, 0x26ca, 0xd101, 0x69ac, 0x3410, 0x1864, 0x8a03, 0xa410])),(BitVec.ofNat 768 (fromLimbs [0x9053, 0x85a, 0xe008, 0x1828, 0x2a70, 0x3443, 0xc76b, 0x2b0c, 0x1000, 0x189e, 0x6488, 0xd00, 0xa862, 0x4210, 0x1085, 0x8634,
        0x438, 0x45cc, 0x4, 0x4bd6, 0x4840, 0x5185, 0x148, 0x1, 0x4980, 0x401, 0x64a5, 0x6321, 0x2414, 0x422, 0xc100, 0x4141,
        0x52de, 0xbe81, 0x912c, 0x5304, 0x10e5, 0x9e8, 0x1140, 0x94c4, 0xae18, 0x468a, 0x9400, 0xa0a6, 0xcc00, 0xbdf6, 0xde02, 0x8450]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0x541b, 0xb2ba, 0x83ee, 0x7937, 0x935c, 0x70de, 0xcb49, 0x594d, 0x47a4, 0xa4bb, 0xdac0, 0xcf1b, 0xb6df, 0xf7e7, 0x5f8a, 0x6af2,
        0x5530, 0x74ec, 0x29c3, 0x3f1a, 0xc9df, 0xa1d5, 0xd1c5, 0x9a7c, 0xfbcf, 0x815d, 0xa96, 0xbfd0, 0xe7b6, 0xf0ad, 0x684c, 0x6c94,
        0x8490, 0x37d4, 0x150c, 0xbe2d, 0x31f8, 0xf01e, 0x2cfd, 0xe810, 0x4146, 0x83fb, 0x5729, 0x1309, 0x2a5d, 0x108, 0x3, 0x8410])),(BitVec.ofNat 768 (fromLimbs [0x440c, 0xb000, 0x903, 0x2480, 0xd081, 0xbc, 0x3804, 0x412, 0x60f2, 0x2640, 0x8034, 0x7221, 0x689, 0x108b, 0x60, 0x0,
        0x1905, 0x2801, 0xae42, 0x2029, 0xa0ab, 0x248, 0x631, 0xd020, 0x22d, 0xa000, 0x985a, 0x8898, 0xcbc3, 0xc101, 0xc68, 0x8bc,
        0x20, 0x11c, 0x841, 0x8480, 0xcb18, 0x7016, 0x2cbd, 0x6811, 0x4126, 0xa930, 0x633d, 0x5f58, 0x23ff, 0x4201, 0x2001, 0x200]))),(0,0)]
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
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(254,[117,67,32]),(471,[115,83,133,99,50,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := (fromLimbs [0x2, 0xe190, 0xe, 0x4402, 0x8954, 0xb001, 0x2971, 0x3b90, 0x21c, 0x5c40, 0xa24, 0xa286, 0xe030, 0x0, 0x0, 0xd80,
        0x6, 0x7900, 0x0, 0x5048, 0xcec0, 0xc584, 0xc000, 0x294, 0x1000, 0x109])
def g383d11 (i : Nat) : Nat := (fromLimbs [0x1, 0xc180, 0xc08, 0x840, 0xa80c, 0x1608, 0x8085, 0xc16, 0x428, 0x7044, 0x440, 0x70d0, 0xe042, 0x8210, 0x2a03, 0x50f,
        0x610, 0x4307, 0xd0a, 0x850, 0x8680, 0x3613, 0x65e1, 0x7803, 0xfe08, 0x7fc3, 0xffa, 0x61ff, 0x443f, 0xf187, 0xfe10])
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := (fromLimbs [0x605e, 0xc8c0, 0x0, 0x111, 0x7d3d, 0x8e63, 0x2bfc, 0x4341, 0x26a5, 0x60a0, 0xc97c, 0xd1c2, 0xe000, 0x6879, 0xdce0, 0x1300,
        0x202, 0x9832, 0x241d, 0x31f8, 0x9848, 0xe708, 0x0, 0x0, 0x19d, 0xd990, 0xa81d, 0x8340, 0x1050, 0x198b, 0x41ca, 0x520a,
        0x2f40, 0xadba, 0xda29, 0x270, 0x22, 0x1200, 0xf02, 0x4055, 0x5b3c, 0x62d0, 0xc010, 0xb446, 0x40b0, 0x0, 0x0, 0xa02,
        0x0, 0x27, 0x4e00, 0x193, 0x1, 0x40ac, 0xe19, 0x5908, 0x54ad, 0x6249, 0xde0, 0x2102, 0xd21d, 0x6156, 0x1429, 0x4400,
        0xd8a, 0x4082, 0xdc48, 0x5500, 0x7f7, 0x9444, 0x1, 0x4100, 0x142, 0x2051, 0x3068, 0x0, 0x5800, 0x991, 0x2818, 0x7538,
        0xf66, 0x1504, 0x984e, 0xda4b, 0x2e78, 0x7cc3, 0x9625, 0x232a, 0x26, 0x53d2, 0x4506, 0x1c2f, 0xea20, 0x0, 0x680, 0x4000,
        0x2, 0x4e94, 0xb185, 0xb1a, 0xd217, 0x101, 0x60, 0xb00, 0x170, 0x5030, 0x1c05, 0x70, 0xe260, 0x4044, 0x5140, 0x410])
def g383d10 (i : Nat) : Nat := (fromLimbs [0x2e, 0x1d81, 0x8587, 0x821e, 0x2216, 0x14a1, 0x30f0, 0x9114, 0x6478, 0x584c, 0xc3c, 0x2c10, 0xb0a7, 0x885, 0x6160, 0x8c04,
        0x207, 0xa04c, 0x4428, 0x6021, 0x1d1a, 0x1611, 0x2300, 0xa100, 0x82e1, 0xc613, 0x1185, 0xb0a, 0x4746, 0xc2c1, 0x584, 0x5898,
        0x8a30, 0x2822, 0x3838, 0x785a, 0x5041, 0xd141, 0x4184, 0x42a1, 0x2d2, 0x88a, 0xa12, 0x2254, 0x60ac, 0x2c10, 0x8050, 0x40f4,
        0x583, 0xc282, 0x820b, 0xa1c, 0x4c45, 0x191c, 0x1c48, 0x24e2, 0x30c8, 0xc098, 0x20a9, 0x1e8, 0xc307, 0x504, 0xd0e, 0x3618,
        0x2228, 0x7851, 0x4342, 0xc181, 0xc144, 0x4281, 0x482, 0x548c, 0x140e, 0xb08, 0x1664, 0x2058, 0x4040, 0xb0a3, 0x885, 0xc282,
        0xa303, 0x203, 0xe08a, 0x72c, 0x1610, 0x1024, 0x28b8, 0x60a1, 0x1821, 0xe146, 0x4106, 0x587, 0x711, 0xb38, 0x2838, 0x9849,
        0x2d1, 0xc1d1, 0x8284, 0x824e, 0x230c, 0x8c0e, 0x201c, 0x1670, 0x9470, 0x7464, 0x2040, 0xa0f0, 0xb4e1, 0x83a3, 0x222, 0x8687,
        0x1d08, 0x3210, 0x102c, 0x28c8, 0x61e0, 0xf818, 0x4098, 0x21c1, 0x4906, 0x1607, 0xc10a, 0xc211, 0x440, 0x306e, 0xe10, 0x2e1e,
        0x58, 0x5261, 0xc181, 0x7070, 0x8242, 0xc110, 0xc14, 0xa08, 0x4060, 0x50d0, 0xac10, 0x8043, 0x8303, 0x8485, 0x8282, 0x1818,
        0x242f, 0x420, 0x10c0, 0xf840, 0xa238, 0x2140, 0x8711, 0xc206, 0x407, 0xc3c0, 0xc10a, 0xf50, 0x3606, 0x183e, 0x820, 0x6e10,
        0x5872, 0x91c1, 0x8143, 0x70b0, 0x4281, 0x108e, 0xd87, 0x8209, 0x840b, 0x8014, 0x12a0, 0x7050, 0x4188, 0x402, 0xc56, 0x1f04,
        0x1080, 0x80a2, 0x504, 0x121e, 0x3e, 0x1608, 0x21ac, 0x3aa6, 0x6952, 0x81e7, 0x4a5d, 0x64a2, 0x36e2, 0xba1a, 0x60b1, 0xfbde,
        0xa9dd, 0x5d21, 0xbcda, 0xf9a2, 0x58b1, 0x7fd7, 0x2963, 0x55a1, 0x4ad3, 0xb928, 0x5191, 0xbcf, 0x88e7, 0x4d40, 0xc2cb, 0x98aa,
        0x49d0, 0x8fc8, 0x86b, 0x4560, 0x44c2, 0xf828, 0x4210, 0x17c1, 0x280d, 0x4003, 0xff5c, 0x530f, 0xfd73, 0x443f, 0xf5c1, 0x30ff,
        0xd730, 0x43ff, 0x1cc1, 0xffd, 0x7384, 0x3ffa, 0xd10, 0xffd7, 0x18c3, 0xff9c, 0x430f, 0xfd30, 0x443f, 0xf1ce, 0x10ff, 0xc834,
        0x43ff, 0xcc11, 0xfff, 0x814c, 0x3ffa, 0x530, 0xffe7, 0x18c3, 0xff4c, 0x610f, 0xfd31, 0x8c3f, 0xf9ce, 0x10ff, 0xe318, 0xc3ff,
        0x6053, 0xffd, 0x710c, 0x3ff1, 0xc430, 0xfff8, 0x3443, 0xffcc, 0x610f, 0xfd83, 0x443f, 0xf205, 0x30ff, 0xf718, 0xc3ef, 0xe113,
        0xff9, 0x708c, 0x2ff6, 0xd10, 0xbfd8, 0x18c2, 0xff60, 0xc10b, 0xfd83, 0x8c2f, 0xf606, 0x10bf, 0xd810, 0xc2ff, 0x61e3, 0xff9,
        0x704c, 0x2ffe, 0x530, 0xbfd8, 0x3842, 0xffe0, 0xd10b, 0xde83, 0x42b, 0xf618, 0x30be, 0xd828, 0xc2fb, 0x6081, 0xbdd, 0x8304,
        0x2efe, 0x1130])
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := (fromLimbs [0x711, 0x9811, 0x5833, 0x604b, 0x1a0, 0x6, 0x6e8, 0x8fc0, 0x24, 0x2d7c, 0x1fb0, 0xfaad, 0x2800, 0x0, 0x907, 0x2000,
        0x0, 0x0, 0x0, 0x1, 0x1a60, 0xc, 0x95e, 0x7a0, 0x3c80, 0x0, 0x20, 0x7200, 0xb000, 0xf03, 0x7421, 0x8000,
        0x83d, 0x7434, 0x0, 0x0, 0x1, 0xfe0, 0x19, 0x1d80, 0x38, 0xc800, 0x0, 0x0, 0x5000, 0x1a19, 0xc000, 0x0,
        0xf0d8, 0x2, 0x4171, 0x5f0, 0x10, 0x2bc, 0x8ec, 0x1b00, 0x1e1, 0x2c00, 0x0, 0xf0e, 0x7e92, 0xd81a, 0x6801, 0x0,
        0x81e2, 0x997c, 0x7b6, 0x460, 0x2f, 0x86e0, 0x47b0, 0x9359, 0x1c0b, 0x4286, 0x3642, 0x440b, 0x4814, 0xa409, 0x0, 0x1,
        0x167, 0x1f8, 0x992, 0xcbb0, 0x3080, 0xc1, 0xb41, 0x6439, 0xd943, 0xb147, 0xaae0, 0x0, 0x14, 0x0, 0x0, 0x51cc,
        0x437e, 0x4b46, 0x4d4, 0x3368, 0x1200, 0x51, 0x6302, 0xb9f1, 0x0, 0x406, 0x7d0c, 0x8043, 0x0, 0x61b5, 0x6b10, 0x0,
        0xc580, 0x0, 0x78, 0x3f10, 0x4c00, 0x3fb, 0xb800, 0x907, 0xd07, 0x382c, 0x4f54, 0x0, 0x1, 0x4a41, 0x460, 0x17,
        0x1508, 0xea8, 0x7408, 0x33a5, 0x8800, 0x240, 0x4721, 0xa41d, 0x7010, 0xe870, 0xe0a6, 0x0, 0x41e7, 0x802d, 0x68a0, 0x0,
        0x0, 0x0, 0x166, 0x5c3, 0x2d93, 0x3682, 0x3a9a, 0xd, 0x7e20, 0xd86d, 0x416e, 0x10a4, 0x82, 0x8f54, 0x40c8, 0x13b8,
        0x3e60, 0xa220, 0xd8fa, 0x1581, 0x20e, 0x4099, 0xe819, 0x7842, 0x3012, 0x10c9, 0xaa80, 0x8357, 0x404e, 0x1fd, 0x3040, 0x41e1,
        0x23c, 0x6482, 0xe6b2, 0xcf06, 0x3e21, 0xe71a, 0x6056, 0x370a, 0x32, 0x182, 0x5400, 0x56b, 0x139c, 0x293c, 0x35f0, 0xf831,
        0x1d90, 0x3113, 0x2ca7, 0x7211, 0x5827, 0xb062, 0x18a0, 0x2035, 0x61cf, 0x8691, 0xf5a, 0x5f4b, 0x8b23, 0x3b38, 0x2b58, 0xee49,
        0xdec3, 0x300d, 0x7802, 0xd8c0, 0x502f, 0xd101, 0x9b0, 0xc0a9, 0x7ee, 0xa0f, 0xc274, 0x22d, 0x3a10, 0xd506, 0xb10, 0x8505,
        0xd001, 0xd3c3, 0x1732, 0x3018, 0x38cc, 0xa179, 0x204, 0x714, 0x80aa, 0xd97c, 0x1b80, 0x50, 0x9cd0, 0xa402, 0xa948, 0x2901,
        0xe317, 0x1c30, 0x0, 0x64ac, 0x78e8, 0x4, 0x854e, 0x40d, 0xdec8, 0x4110, 0x6f32, 0xa042, 0xd71, 0x5820, 0xcb28, 0x1009,
        0x2535, 0x383b, 0x24a5, 0x5e, 0x8321, 0x8280, 0x109e, 0xcf40, 0x6a, 0x47e0, 0x5400, 0x3c1, 0xd6c1, 0x7800, 0xc84f, 0x7001,
        0xb077, 0xb090, 0x1, 0xc268, 0xe, 0x880, 0x14, 0x3b22, 0x1e2f, 0x0, 0x390d, 0x4, 0xc17, 0x3408, 0x21, 0x1f04,
        0xc, 0x3852, 0x5c, 0x82b, 0x403, 0x102, 0x8802, 0x102, 0x4c3d, 0xe17, 0xf, 0x511, 0x4101, 0x57, 0x3e04, 0x12,
        0x7, 0x500, 0x164, 0x4, 0xb01, 0x407, 0xd, 0x1, 0x204, 0x100, 0x400, 0xa01, 0xe07, 0x0, 0x0, 0x3720])
def g383d9 (i : Nat) : Nat := (if i<1 then (fromLimbs [0xb102, 0xc382, 0xe181, 0x41e0, 0xb051, 0x5081, 0xb058, 0x4481, 0x3238, 0x441e, 0xb28, 0x448e, 0x13e0, 0x8641, 0xe683, 0x82b0,
        0x80b2, 0x5c2, 0xc0a1, 0x8143, 0x20a1, 0xf082, 0x20f1, 0x8170, 0x80b0, 0x5100, 0xa170, 0x58c0, 0x81a0, 0xc8c1, 0x60a1, 0x2102,
        0xb0, 0x8902, 0x20a1, 0x4101, 0xe2a3, 0x128, 0xa0e2, 0x30b8, 0x20f0, 0x5102, 0x40a0, 0x48f8, 0x1c10, 0x782c, 0x145e, 0x83b,
        0xa0a, 0x214, 0x100f, 0xe082, 0x8085, 0x92d4, 0x90e4, 0x231f, 0x18e4, 0x46c6, 0x3231, 0x688a, 0x8c4e, 0xa223, 0xfa8, 0x71c3,
        0x3216, 0xb09e, 0x843c, 0x1560, 0x6b00, 0x37f6, 0x3ee9, 0xf46f, 0x8c7b, 0x63d0, 0xde34, 0xef17, 0x68ba, 0xa1d1, 0xe68, 0x71fb,
        0x8a1c, 0x10dd, 0xf6df, 0xb6a1, 0xafed, 0x5f6a, 0x4347, 0xd9fe, 0xcd66, 0x5b32, 0x7d8f, 0xec68, 0x61fb, 0xa18, 0x22bf, 0x15e8,
        0xaee9, 0x710b, 0x685a, 0x8ac7, 0xd5fe, 0xad65, 0x5faa, 0x354c, 0x8a29, 0x4fba, 0x75d3, 0x5c98, 0xe4bb, 0xa539, 0x26e9, 0x2048,
        0x4a35, 0xd15c, 0x8974, 0x3721, 0x3905, 0xc7fc, 0x3ee1, 0xf14f, 0x1476, 0x139c, 0x1bd0, 0xda86, 0xb434, 0xa196, 0x4c84, 0x6102,
        0xf397, 0x40b4, 0xe590, 0x2b39, 0x540a, 0x6051, 0x927c, 0x9340, 0x9604, 0x9023, 0x390f, 0x883c, 0x3e31, 0xe60e, 0xb072, 0xa37e,
        0x1af0, 0xd1c6, 0x602f, 0xe16a, 0x8a8c, 0x4d02, 0x3f10, 0xf87f, 0xc3be, 0x1b60, 0xcb05, 0xd82b, 0xe136, 0x8f8, 0x4201, 0xbe0b,
        0x604b, 0x190, 0x640, 0xdf, 0xeb8b, 0x718, 0x6ff6, 0x573, 0x843f, 0x7f08, 0xb8a6, 0x1bfc, 0x7360, 0x610b, 0xfecb, 0x9029,
        0x86ff, 0x6067, 0x3843, 0x7fb0, 0xfc1a, 0x21bf, 0xf874, 0xc110, 0xbffc, 0xbb06, 0x885f, 0xfe5d, 0x3044, 0x37fb, 0xe98, 0xc217,
        0xfd97, 0x20d1, 0xbff, 0xcba6, 0x3085, 0xff65, 0xf304, 0x42ff, 0xb2fc, 0x1a21, 0x7fd9, 0x7a0d, 0x10bf, 0xecbe, 0x6308, 0x4ff6,
        0x6173, 0x443b, 0xf2e1, 0xb8c6, 0x13fd, 0x981c, 0xc109, 0xfe4c, 0x2e68, 0x84ff, 0xe617, 0x3042, 0x7fb3, 0x388, 0x613f, 0xc985,
        0xc530, 0xddfc, 0xa307, 0x184f, 0xfe45, 0x878c, 0x27fb, 0x30b9, 0x821b, 0xed82, 0x8c63, 0x9ff, 0xcbb0, 0x6085, 0xfbe4, 0x9834,
        0x42ef, 0xb2a4, 0xa61, 0xfd93, 0x15c1, 0x30de, 0xec1a, 0x6308, 0x5fe6, 0x4073, 0x842d, 0xff2c, 0xb886, 0x13fd, 0x985c, 0x130d,
        0xfb38, 0xb021, 0x87de, 0xe557, 0x8c2, 0x7fb2, 0xfc0a, 0x61bf, 0x581e, 0x530, 0xdef4, 0x1f06, 0x884f, 0xf661, 0x7384, 0x2f7f,
        0x28c0, 0xa61b, 0xf571, 0x6043, 0xbde, 0xca50, 0x2986, 0xf7e0, 0xf304, 0x427f, 0xb303, 0x9c21, 0xafd9, 0x1618, 0x309f, 0xecc6,
        0xe318, 0x5fee, 0x4131, 0x8c27, 0xff2e, 0xc1a2, 0x1bee, 0x7360, 0x810d, 0xdfca, 0x3070, 0x85fe, 0xe413, 0x1843, 0x7bb2, 0xec18,
        0x217d, 0xf935, 0xc130, 0x9ffc, 0xbb07, 0x86e, 0xf247, 0x844c, 0x37bb, 0x7c1, 0xa217, 0x7d95, 0x9c43, 0xbfc, 0xc846, 0x3186,
        0xfb60, 0xa718, 0xc27f, 0xb313, 0x8c61, 0xbdd8, 0x35cc, 0x10bf, 0xcc80, 0xe608, 0x4ffa, 0x6173, 0x4427, 0xfd30, 0xb8a6, 0x13ff,
        0x9760, 0x630d, 0xf6cb, 0xb051, 0x85bf, 0x65b3, 0x1843, 0x7dd2, 0x2c14, 0x61fd, 0x8935, 0xc130, 0xdf6c, 0x8b05, 0x186f, 0x725d,
        0x8304, 0x37da, 0xe6c1, 0x213, 0xff98, 0x5c63, 0xdf6, 0xc10e, 0x6086, 0xfbdc, 0xd820, 0x42fe, 0xb239, 0x8221, 0xbed8, 0x25c6,
        0x30dd, 0xf48f, 0x898, 0x6efe, 0x4784, 0x4c37, 0x7f08, 0xc0a6, 0x17f5, 0x911c, 0xe10f, 0xddc2, 0x2e09, 0x86ef, 0xe117, 0x4c3,
        0x5fb0, 0xcb88, 0x61be, 0xd936, 0xa30, 0xbdec, 0xa0e2, 0x186e, 0xfe11, 0x714c, 0x37f7, 0x30b8, 0x4616, 0xff96, 0x5c63, 0xdf6,
        0xc16e, 0x3186, 0xfda0, 0x7814, 0xc35f, 0xb0d3, 0x8861, 0xbdf9, 0x760c, 0x10bf, 0x7c93, 0x298, 0x6f76, 0xc83, 0x4427, 0xfb31,
        0x3886, 0x1bf5, 0x8120, 0x5309, 0xfecc, 0x4e70, 0x84ff, 0x65d8, 0x10c2, 0x7ff3, 0xb9c, 0x217f, 0x990d, 0xc630, 0xdfcc, 0x1ae1,
        0x186f, 0xd605, 0x318c, 0x27ff, 0x2ec0, 0x8617, 0xbf94, 0x4c11, 0xddf, 0xc270, 0x2985, 0xfee4, 0x1834, 0x427f, 0xb319, 0x8c21,
        0xbdd8, 0x3cc6, 0x10dd, 0xfc25, 0x298, 0x5fe6, 0x4331, 0x8435, 0xfd22, 0xc306, 0x1bef, 0x9260, 0xd109, 0xfecc, 0x2e31, 0x85df,
        0x6568, 0x3442, 0xefb2, 0xb982, 0x217e, 0xf924, 0xc610, 0xdef4, 0xbb06, 0x86f, 0xb609, 0x318c, 0x3fb6, 0x62b8, 0x2617, 0xef92,
        0x4c63, 0x9ff, 0xcc2e, 0x2186, 0xfba5, 0xd828, 0xc3fa, 0xa63c, 0xa61, 0x9fd8, 0x75c6, 0x309f, 0xecbf, 0x688, 0x6f7e, 0xd30,
        0x4437, 0x7f08, 0x40a6, 0x1bbd, 0x91e1, 0x1309, 0xfecc, 0x4631, 0x84fb, 0xe498, 0x3442, 0x77f2, 0x8c1c, 0x213b, 0xf946, 0xe30]) else (fromLimbs [0x73, 0x608, 0x1105, 0x1426, 0xa15, 0x41e, 0x8407, 0x28a, 0xf11, 0x82c7, 0xc305, 0x5c2, 0x2403, 0x8284, 0x1342, 0xa106,
        0xe05, 0x4102, 0x2404, 0x82c4, 0x1105, 0xa0a, 0x840b, 0x448, 0xb04, 0x881e, 0x410, 0x2416, 0x2058, 0x2440, 0x9058, 0x81e0,
        0x4103, 0xc0a0, 0x4058, 0x28a0, 0xb050, 0x5860, 0x5040, 0x102e, 0xe28, 0x4c12, 0x2028, 0x2808, 0x2509, 0x9426, 0x910, 0x5c1c,
        0x2020, 0x3814, 0x3058, 0x142c, 0xa20, 0x3c16, 0x1105, 0x1108, 0x404, 0x8288, 0x405, 0x447, 0x4705, 0x3c1, 0x64e1, 0x8381,
        0xe3e0, 0x83c1, 0x4342, 0x101, 0x60a2, 0x3c2, 0xc2c2, 0x441, 0x6308, 0x8101, 0x40f2, 0x1141, 0x2111, 0x8443, 0x42e1, 0x902,
        0x20f2, 0x101, 0x60a1, 0x8241, 0x6208, 0x8101, 0x40f2, 0x104, 0x20a1, 0xc100, 0x8110, 0x5900, 0x8210, 0x50c1, 0x60f1, 0x1c1,
        0xc0f1, 0x8241, 0x6202, 0x8581, 0x60a2, 0x2c1, 0x4208, 0x8284, 0xc607, 0x646, 0x407, 0x3c6, 0xa05, 0x8a0b, 0x40e, 0x581,
        0x4502, 0x3c1, 0x4305, 0x384, 0x705, 0x118, 0xa0e2, 0x8101, 0x60a1, 0x9140, 0xa090, 0x8901, 0x20a1, 0x2c1, 0x4041, 0x1864,
        0xa090, 0x8828, 0x2444, 0x2a10, 0x81c, 0xb02, 0x8c0a, 0xc02, 0x2e0, 0xf284, 0x4140, 0x9183, 0xc0a0, 0xb071, 0x121, 0x1090,
        0xc141, 0x9104, 0x70c0, 0xe059, 0x162, 0x2104, 0x41e2, 0x902, 0xc505, 0x201, 0x42c0, 0xa2c1, 0x422, 0x829, 0x161, 0xc101,
        0x4080, 0xe0b9, 0x18e1, 0xa0b8, 0xc230, 0x4058, 0xe821, 0x9420, 0x2816, 0x5628, 0x3c14, 0x3078, 0x5041, 0xfa17, 0x68a, 0xf05,
        0x188c, 0x607, 0x2c9, 0xc103, 0x8281, 0xe4e1, 0x7040, 0xe0aa, 0x2810, 0x1e70, 0x805c, 0x1630, 0x4050, 0x1430, 0x284c, 0x123e,
        0x708, 0x1dc1, 0x782, 0x8c13, 0x88a, 0xc05, 0x8e1, 0x165, 0xad6, 0x140, 0xb202, 0x81e2, 0x211, 0x4121, 0x1202, 0x81c2,
        0xe1f0, 0x41e0, 0xa211, 0xc162, 0x484, 0x4243, 0x503, 0xc404, 0x702, 0x8704, 0xd84, 0x4164, 0xf04, 0xc1e3, 0x4202, 0xc143,
        0xe081, 0xc140, 0xf221, 0x80, 0xb051, 0x121, 0x1090, 0xf85c, 0x18e8, 0x1014, 0xf30, 0x3c28, 0x2020, 0x6416, 0x3078, 0x5040,
        0xf0a0, 0xa8a0, 0xf050, 0xc1e0]))
def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)
def g383h9 (i : Nat) : Nat := (fromLimbs [0xa16, 0xf054, 0x972c, 0x2800, 0x915, 0x83d, 0x9e, 0xb00, 0x184, 0xb4aa, 0x7, 0xdf9, 0xa000, 0x0, 0x1038, 0x0,
        0x0, 0x408, 0x95c7, 0xd1f4, 0x3045, 0x2c83, 0xb410, 0x0, 0x66, 0xc401, 0xa931, 0x4035, 0x8900, 0x181, 0x590e, 0x60c4,
        0x6e, 0x9707, 0x3987, 0x8c26, 0x8f43, 0x19a8, 0xa1e8, 0xa227, 0x410f, 0x8051, 0x5a00, 0x677, 0x8002, 0x2f0, 0x2991, 0x5b90,
        0x7440, 0xe6c7, 0xf8b0, 0x8b06, 0x8a9c, 0x4164, 0x8c8, 0x4be1, 0xfb32, 0xf040, 0x14, 0x3200, 0x0, 0x0, 0x0, 0x0,
        0x1d, 0xaa09, 0x90d5, 0x8b48, 0xe1, 0xd917, 0xe016, 0x4058, 0x1811, 0x7209, 0x91cb, 0x65f6, 0x5399, 0x9ed0, 0x240c, 0xf0c8,
        0x400, 0x4d, 0x8a6, 0x6108, 0x2008, 0x4081, 0x540, 0x40, 0x10, 0xa, 0x4210, 0x804])
def g383d8 (i : Nat) : Nat := (fromLimbs [0xa102, 0x0, 0xe08, 0x5840, 0x8185, 0x82e, 0x1044, 0xa10, 0xc, 0x8400, 0x16, 0x1001, 0xe103, 0xa10, 0x0, 0x0,
        0x504, 0x0, 0x0, 0x141, 0x1e, 0x1010, 0x8102, 0x8191, 0x2081, 0x282, 0x28, 0x20c8, 0x4000, 0x1e1, 0x283, 0xe0ed,
        0xf5ba, 0x3ccd, 0xeebb, 0x539a, 0xc5dc, 0xadb6, 0x8acd, 0x529f, 0x4a9d, 0xcda4, 0xf228, 0x9c3a, 0x1304, 0x7fbe, 0x9eaf, 0x70b,
        0x71ae, 0xd266, 0xb218, 0x6be5, 0x7aa9, 0x3696, 0x439b, 0x8be5, 0x258, 0xf05a, 0x2811, 0x8781, 0xe00d, 0xafe5, 0xb845, 0xc530,
        0xcefe, 0x1f94, 0x4c11, 0xaef, 0x69c9, 0x1e11, 0x30af, 0xb68f, 0x7360, 0x810c, 0xefe1, 0x1972, 0x530, 0xcef5, 0xc794, 0x60e3,
        0xcfb, 0x61f9, 0x24c6, 0x10ad, 0xfe95, 0x87e0, 0xd10c, 0xef5c, 0x7946, 0xe10, 0xcdb6, 0x5582, 0x1cc1, 0xf74, 0x5c53, 0x15c1,
        0x308f, 0xdea5, 0x8120, 0x5308, 0xefe9, 0x1985, 0xc130, 0x8fb6, 0x8998, 0x1cc1, 0xcaf, 0x6199, 0x41c4, 0x308f, 0xbe89, 0x985c,
        0xd108, 0xbf69, 0xa985, 0xc530, 0xafa6, 0x8297, 0x60a3, 0xcaf, 0xe5b8, 0x45c5, 0x30cc, 0xfe11, 0x9520, 0x530c, 0xdb65, 0x5829,
        0xc630, 0xcfa6, 0x990, 0x1cc1, 0xceb, 0xe539, 0x260d, 0x10ae, 0xbe89, 0x91e1, 0x130a, 0xf668, 0x976, 0xc10, 0xcbbe, 0x5982,
        0x5c63, 0x8fb, 0x68b9, 0x161e, 0x308e, 0xfe91, 0x989c, 0xe108, 0xbfe9, 0x9976, 0x430, 0xaf36, 0x8897, 0x60c1, 0xceb, 0x6518,
        0x28c6, 0x308e, 0xfe91, 0x985c, 0xe108, 0xfb6a, 0x582d, 0xc630, 0x8bfe, 0x9b98, 0x5c43, 0x8bf, 0xe999, 0x85c6, 0x30c9, 0xf655,
        0x869c, 0x430c, 0xebe1, 0x3926, 0x530, 0xad76, 0x9497, 0x60c1, 0x8bf, 0x6a39, 0x65c4, 0x30ac, 0xf694, 0x91e1, 0x1308, 0xf7ea,
        0x5832, 0xd10, 0xcfa6, 0x990, 0x8c63, 0xaf9, 0xa869, 0x760a, 0x30ad, 0xd696, 0x7160, 0x430a, 0xeb69, 0x2976, 0xa30, 0xaf96,
        0x8697, 0x60a3, 0x8ef, 0x6a78, 0x4a05, 0x30ce, 0xb651, 0x821c, 0xc108, 0xdfe9, 0x597e, 0x530, 0xaebe, 0x9193, 0x60a3, 0xccf,
        0xe578, 0x45c1, 0x30ce, 0xe611, 0x901c, 0xc108, 0xfb6a, 0x3924, 0xc630])
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := (fromLimbs [0xa, 0x295f, 0xdb2e, 0x3ca3, 0x708, 0x52bf, 0xb65c, 0x7946, 0xe30])
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x7bf3, 0xda45, 0xaf3f, 0x8c08, 0x5a5c, 0xb987, 0x177b, 0x9950, 0x7674, 0xf4c9, 0x37c6, 0x357f, 0xf7c7, 0xe09c, 0xe49b, 0xeeec,
        0xbf77, 0x77c8, 0x78be, 0xa111, 0xfaf6, 0xda32, 0x6b91, 0xbcf4, 0xee73, 0xcf4, 0x458d, 0x3f72, 0x79c9, 0x98d, 0xb863, 0x83f5,
        0x41a1, 0x4f4a, 0x486b, 0x2153, 0xac6c, 0xc220, 0xd9a4, 0xc042, 0x8821, 0x4440, 0x812, 0xc1a0, 0x3824, 0x14a, 0x3e21, 0xf653])),(BitVec.ofNat 768 (fromLimbs [0x6c0c, 0x908, 0x8454, 0x1000, 0x4000, 0x8100, 0x1004, 0x5710, 0x111, 0x1584, 0xccc2, 0x500, 0x8218, 0x1, 0xa002, 0x4,
        0x8800, 0x1000, 0x114, 0x810, 0x8143, 0x4024, 0x2a00, 0x8400, 0x0, 0x1e41, 0xa680, 0x4200, 0x4101, 0x4411, 0x8003, 0x8350,
        0x41a0, 0xc802, 0x27c, 0x33, 0x6160, 0x1060, 0x6901, 0x3446, 0xc20, 0x9508, 0x1041, 0x902, 0x2004, 0x8a, 0x2421, 0x2652]))),((BitVec.ofNat 768 (fromLimbs [0xda7e, 0x816f, 0x3feb, 0xb785, 0x9eb6, 0x9321, 0xadfa, 0x95cb, 0x2d74, 0xd81a, 0x38e8, 0xc299, 0x3ff7, 0xc9dd, 0x4f4f, 0xdcfc,
        0x37ab, 0xafbf, 0xbba5, 0x4cf8, 0xbb0b, 0xabce, 0x157e, 0x577a, 0xab0a, 0x9e25, 0x6f1e, 0xae7c, 0xb247, 0xb98d, 0x969c, 0x798b,
        0x2d38, 0xf019, 0xccd9, 0x55a0, 0x208a, 0x2083, 0xda20, 0x8001, 0x20c0, 0x10a1, 0xd545, 0x6e25, 0xc86f, 0x4208, 0xc8c6, 0x481f])),(BitVec.ofNat 768 (fromLimbs [0x2, 0x34, 0x281, 0x601, 0x204, 0x5a20, 0x2820, 0x8088, 0xa028, 0x4041, 0x100, 0x4082, 0x104, 0x7144, 0x221, 0xa340,
        0x22cc, 0x8684, 0x0, 0x4202, 0x84, 0x493, 0x8, 0x4018, 0xb12, 0x28, 0x0, 0xb804, 0x8000, 0x922, 0x403c, 0x2883,
        0x2805, 0x3019, 0x8883, 0x108, 0x1491, 0x48f, 0x8080, 0xc081, 0x10c3, 0x2d0, 0xc884, 0x1400, 0x8862, 0x4405, 0x88c4, 0x4809]))),((BitVec.ofNat 768 (fromLimbs [0x52ad, 0xe7ca, 0x8472, 0xa7a2, 0xb56b, 0x45b2, 0x8960, 0xa5c8, 0x855d, 0x7bfc, 0x7237, 0x4bde, 0x836b, 0x42eb, 0xf256, 0xbce2,
        0xc89e, 0x322, 0x188a, 0xf5a9, 0x6fcb, 0x796f, 0xb735, 0xd57e, 0x3a90, 0x5ea1, 0xa259, 0x30bb, 0x344d, 0x1496, 0x6b67, 0xf704,
        0x8292, 0x8ec6, 0x8648, 0x92a7, 0x808c, 0x5443, 0x410, 0x300, 0x306, 0xa901, 0xd5cd, 0x2044, 0x308, 0xa310, 0xf107, 0x8f9c])),(BitVec.ofNat 768 (fromLimbs [0xa3a4, 0x450a, 0x514a, 0x89fc, 0x8820, 0x18, 0x43cd, 0x6905, 0x1c0, 0xeb4, 0x1e05, 0x930, 0x160a, 0x86a8, 0x71d8, 0x4419,
        0x5d20, 0x280b, 0x9693, 0x90c9, 0xc938, 0xd200, 0x4495, 0x22e2, 0x1481, 0xab52, 0xf260, 0x44d0, 0x5d2a, 0xc050, 0xb183, 0xd704,
        0x8210, 0x8ec6, 0x35c, 0xd2a7, 0xca2c, 0x5360, 0x6153, 0x706, 0xa304, 0xa029, 0x342b, 0x6866, 0x288, 0xa318, 0x7103, 0x8514]))),((BitVec.ofNat 768 (fromLimbs [0xcf2b, 0x445e, 0x2c8f, 0x92ea, 0x37f6, 0x9711, 0x935d, 0xc32d, 0x8ac9, 0xfba7, 0x5f0b, 0x2f7f, 0xbdac, 0xff60, 0x2b76, 0xc313,
        0x7a97, 0x7e4a, 0x5b3a, 0x7afe, 0x6df0, 0xf64b, 0xb381, 0x9165, 0x489d, 0x455d, 0x3f7e, 0x2631, 0x53db, 0x4ef0, 0xe6c8, 0xa73,
        0x5fca, 0x4439, 0xb2e3, 0x869d, 0x9110, 0x9444, 0x667, 0x1424, 0x1006, 0xab06, 0x2288, 0x5b, 0x3d0, 0x9cb6, 0x1f8, 0xf80])),(BitVec.ofNat 768 (fromLimbs [0x1011, 0x2284, 0x8c00, 0x2000, 0x400, 0x2802, 0x810, 0x12c0, 0xc02, 0x114a, 0x8010, 0x1082, 0x8021, 0x1, 0xa00, 0x9002,
        0x18, 0x0, 0x2104, 0x430, 0x1201, 0x13, 0x2800, 0xc, 0x208, 0x1029, 0x98d, 0x105, 0x240, 0x3024, 0x68, 0x3b,
        0x598a, 0x4030, 0xa023, 0x550, 0x1141, 0x2c96, 0x1ea4, 0x3020, 0x1c00, 0x5944, 0x140, 0x9011, 0x950, 0x10a2, 0xb0, 0xa80]))),((BitVec.ofNat 768 (fromLimbs [0xfbaa, 0x4318, 0xbaa5, 0x7959, 0x542a, 0x280e, 0x640d, 0xf397, 0x78b4, 0xd46b, 0x1f3c, 0x151b, 0xf3f0, 0x993b, 0xd0fe, 0x3df9,
        0xe94e, 0x9542, 0x8bc4, 0x37eb, 0x34b1, 0x1ff9, 0x2c19, 0xff03, 0xe6ba, 0x72ca, 0x35ff, 0x1343, 0xff1f, 0x7fc, 0xbab6, 0x7c86,
        0xb441, 0x25c7, 0xc20, 0xa80c, 0xbc7e, 0xc004, 0x2, 0xc06, 0xc005, 0x4640, 0x210, 0x5c, 0xf480, 0xfbe0, 0x1ff, 0xf020])),(BitVec.ofNat 768 (fromLimbs [0x8040, 0xd470, 0x6129, 0xc441, 0xb047, 0x5088, 0xa0e8, 0x8807, 0x1200, 0xa820, 0x1328, 0x86d, 0x4886, 0xb9f0, 0x588, 0x42e0,
        0x763, 0x2e16, 0x4441, 0x220f, 0x2c88, 0xaa48, 0x85ca, 0x32b2, 0xc0c7, 0x6084, 0x0, 0xbc88, 0x10be, 0x988, 0x7194, 0x7c84,
        0xa441, 0x25c5, 0xd00, 0xa80c, 0x8e1e, 0xc308, 0x8042, 0x4881, 0xe007, 0x22b1, 0x6ebe, 0x406c, 0xd4a0, 0xef45, 0x14e, 0xd020]))),((BitVec.ofNat 768 (fromLimbs [0x7ef3, 0x9cf8, 0x1d5e, 0xbfdc, 0x6993, 0xb54f, 0xc7da, 0x86b, 0xed31, 0x6d3d, 0xbd7f, 0x9d6c, 0xe832, 0xaf68, 0x5e8f, 0xd1cd,
        0x19ce, 0x79fa, 0xca95, 0xb97a, 0xc8e7, 0xc4c0, 0x5d5e, 0x67a5, 0x74ec, 0xf577, 0xefc3, 0xe709, 0x5e97, 0xadf7, 0x8198, 0x3c3a,
        0xb81e, 0x2a64, 0x8807, 0xc2c2, 0x206, 0xa24, 0x5bc, 0x4000, 0x4ff8, 0x18, 0xa32, 0xb780, 0x410, 0x9b53, 0xfe00, 0x20])),(BitVec.ofNat 768 (fromLimbs [0x3b1, 0x16c1, 0x6a20, 0x2824, 0xb0cc, 0x2203, 0x8f08, 0x8041, 0x884a, 0x8a18, 0x1200, 0x9a5c, 0x2c81, 0x29c8, 0x4ec8, 0x54a2,
        0x661c, 0x6038, 0xac4b, 0x7a9, 0x2e08, 0x8c80, 0xc12a, 0x2036, 0x2704, 0x4020, 0x4832, 0x491, 0x462, 0x9848, 0x2c58, 0x382a,
        0xb81e, 0x264, 0x8903, 0xc2c0, 0x1207, 0x2c96, 0x14fe, 0x40a0, 0xd291, 0x6af0, 0x796, 0xb6a0, 0xc30, 0x9b74, 0xda00, 0x0]))),((BitVec.ofNat 768 (fromLimbs [0x8293, 0x6fa0, 0xd663, 0xc33f, 0x77e4, 0x58ec, 0x25db, 0x297e, 0xcc37, 0x24c6, 0xa282, 0xd566, 0xf829, 0xf79a, 0x33da, 0x631a,
        0xf6fe, 0xbbbd, 0x2c61, 0xacfd, 0xfc64, 0x37c6, 0x9f10, 0x522c, 0xfb1a, 0xe989, 0x2941, 0x91c6, 0x906f, 0x6062, 0xfd1, 0x9338,
        0x998a, 0x1ec2, 0x3330, 0xce50, 0x600f, 0x6198, 0x2218, 0x3bd9, 0x2000, 0x10a0, 0x210, 0x2fdd, 0xf75f, 0x6000, 0x0, 0x40])),(BitVec.ofNat 768 (fromLimbs [0x92e0, 0xcc00, 0xec44, 0x8804, 0x44e0, 0x8402, 0x744, 0x1f20, 0x1096, 0x61c, 0xea13, 0x905c, 0xbc41, 0x8810, 0x4106, 0x826,
        0xd531, 0x928, 0xed2f, 0x1538, 0x2008, 0x8808, 0x2860, 0x242, 0x484, 0x2842, 0xa113, 0x4180, 0x46b6, 0x20c4, 0x8481, 0x1338,
        0x919a, 0xe42, 0x3320, 0xc650, 0x636e, 0x7810, 0x1b5b, 0x3e70, 0x8c00, 0x7928, 0x753, 0xabfc, 0x771d, 0x20a8, 0x0, 0x0]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xce92, 0x7de0, 0xdc24, 0xecd0, 0x970d, 0xe7df, 0x73d2, 0xffaa, 0x3a7f, 0xb3c3, 0x9ffc, 0x6327, 0xe8d1, 0x4647, 0x987a, 0xf226,
        0x3360, 0x9618, 0x9d5d, 0x227d, 0xd00d, 0x2c64, 0xc7fe, 0x7699, 0xf3e7, 0x77df, 0xda82, 0xd597, 0xd5b7, 0xda7e, 0xbf6f, 0xc4c4,
        0xe664, 0x31b5, 0x758c, 0x1c33, 0x4315, 0x959, 0x2059, 0xbbf8, 0x57fc, 0x41e, 0xa020, 0x1002, 0x410, 0x6405, 0x0, 0x60])),(BitVec.ofNat 768 (fromLimbs [0x440c, 0x20, 0x1190, 0x401, 0x911, 0x51a0, 0x1080, 0x401e, 0x220, 0x80, 0x520, 0x4020, 0x4210, 0x5224, 0x1031, 0x308,
        0x880, 0x443, 0x210, 0x2802, 0x80d2, 0x140, 0x1000, 0x1501, 0x42, 0x500, 0x1200, 0x8a48, 0x1108, 0x4410, 0x1106, 0xc4c4,
        0x660, 0x3181, 0x449c, 0x382f, 0xc90, 0x368, 0xe000, 0x810f, 0x216e, 0x8403, 0xf828, 0x4002, 0x80, 0x4401, 0x0, 0x60])))]
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
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx29 : Lower true (varsX 541) (graphGoal 541) 4 :=
  strong_low (m:=541) (cap:=3) (l:=[(0,20),(2,9),(3,4),(4,1)]) (by decide +kernel) (plainA (q:=29) (prior:=boundsBefore known383) (before_sound known383 valid383) (by decide +kernel))
    (cut_root (prior:=boundsBefore known383) (before_sound known383 valid383) (512,1,12,16,2) (by decide +kernel) (by decide +kernel))
def knownx29 := extendKnown known383 4 [(677,[115,67,100,83])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx29 : Known true knownx29 := extendKnown_ok (m:=541) valid383 lowx29 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x2207fd10
def x189l7 : Packing := (1,1,2,0,0,0,0,x189d7)
def x189h7 (i : Nat) : Nat := (fromLimbs [0x3c, 0x2003, 0xf12, 0x847b, 0x400, 0x0, 0xb100, 0xc672, 0x8e0, 0x130c, 0xb0f4, 0x5c35, 0xc9f1, 0x3048])
def x189d6 (i : Nat) : Nat := (fromLimbs [0x104, 0x20b, 0xb8a0, 0xfe88, 0x110b, 0xf589, 0x10fe, 0x4811, 0xbfd, 0x8910])
def x189l6 : Packing := (4,2,2,0,0,5,0,x189d6)
def x189h6 (i : Nat) : Nat := 0x140
def x189d5 (i : Nat) : Nat := 0x4df7358910
def x189l5 : Packing := (1,3,2,0,0,0,0,x189d5)
def x189samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x56ab, 0x85b, 0x1e98, 0xfc17, 0x86f, 0xdc76, 0x35af, 0x2f36, 0x5755, 0x9387, 0xaa8f, 0xf592, 0xb233, 0xf3f4, 0x980f, 0xfa40,
        0xa7d3, 0xdf4f, 0x78cc, 0x6fc7, 0xb07e, 0xecf6, 0xf62f, 0x3ffe, 0x5696, 0xfc5b, 0xbb06, 0x7c63, 0xd434, 0x7079, 0x2cd7, 0xfd9,
        0xd564, 0xf9a5, 0x6746, 0x106d, 0x68b7, 0xffbc, 0x364d, 0xaf4f, 0xbdd2, 0x4d97, 0x7ec2, 0xf4a7, 0x21c1, 0x4117, 0xd813, 0x3474])),(BitVec.ofNat 768 (fromLimbs [0x10, 0x304a, 0x7e4b, 0x8724, 0x582, 0x2a16, 0x2c0, 0x2571, 0x202b, 0x4250, 0x1280, 0x2a1e, 0x40, 0xb10c, 0x410, 0x8002,
        0x824, 0x1015, 0x2400, 0xb023, 0x5, 0x5709, 0x5620, 0x8044, 0x8084, 0x51e, 0x3a95, 0x9304, 0xc612, 0x9a55, 0x4863, 0xcc8,
        0xa225, 0x9190, 0xbb81, 0xc, 0x8487, 0x2a, 0x9231, 0xa21, 0x180, 0x4802, 0x82e1, 0x54a0, 0x2745, 0x12d, 0x1902, 0xa4a4]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xbd48, 0xd95f, 0x1cd5, 0x47f9, 0xeea5, 0xc177, 0xd7c, 0xe53b, 0xfeec, 0xb4fe, 0x997f, 0xbbf4, 0x6725, 0x3e0a, 0x4fa3, 0xc387,
        0x12f6, 0x38b6, 0x9a7d, 0x37f7, 0xbebb, 0xfbc3, 0x2fcd, 0x6f3e, 0xecf9, 0x9b87, 0x9938, 0x92fe, 0x519c, 0x79bf, 0xe6b3, 0x53bd,
        0xa99e, 0xf4cf, 0x4df0, 0x99ef, 0xecad, 0x17fb, 0x2baa, 0xedd3, 0xef20, 0xf723, 0xa309, 0x7ca8, 0x503e, 0xc108, 0x372c, 0x884b])),(BitVec.ofNat 768 (fromLimbs [0x4309, 0xe05, 0x4180, 0x200a, 0xe10, 0x45a4, 0x2050, 0x2302, 0x9045, 0x30c0, 0x4856, 0xc48, 0x8598, 0xb2b, 0x300a, 0x480d,
        0xd0c1, 0x5b82, 0x1312, 0xa94, 0x14, 0x1458, 0x6041, 0xe9, 0xef11, 0x284, 0x1300, 0x446d, 0xa82, 0x8043, 0x1384, 0x4000,
        0x4166, 0x6, 0x5001, 0x906c, 0x5878, 0xccc6, 0x42, 0x8154, 0xcb4, 0x4004, 0x106, 0xe8a6, 0xc489, 0xc228, 0x1c28, 0x884a]))),((BitVec.ofNat 768 (fromLimbs [0x9a64, 0xf6d8, 0xf7d7, 0x2ca, 0x467d, 0x7fb8, 0xd774, 0xc4db, 0xbdbe, 0x1c2d, 0x19ff, 0xa7a5, 0xcba5, 0xbf2d, 0x91f8, 0x1eff,
        0x38f5, 0x64ec, 0xf9cd, 0x3c93, 0x9f86, 0xcbc8, 0x6c75, 0xc663, 0x73ef, 0xf757, 0x7b8b, 0x82dc, 0xfb6b, 0x3984, 0x7f01, 0xa846,
        0x27dd, 0xbfff, 0x3c7b, 0xb971, 0x9ffd, 0x19ab, 0xfa32, 0x5f6a, 0x56b5, 0x8a58, 0xedb7, 0x9360, 0x291a, 0x2720, 0x21ef, 0x8f83])),(BitVec.ofNat 768 (fromLimbs [0x1030, 0x9062, 0x167b, 0x340, 0xd1c8, 0x851, 0x78a, 0x8c58, 0x2622, 0x423d, 0x2480, 0x9206, 0x4205, 0xe094, 0x610, 0x590,
        0xa12, 0x2431, 0x888, 0x9162, 0x400b, 0x382, 0x1abe, 0xc200, 0x86, 0x8022, 0x48d, 0x9010, 0x40c, 0x210, 0xc479, 0x888a,
        0x3a08, 0x5800, 0xa614, 0x4901, 0x8484, 0x231, 0x2289, 0x1821, 0x9, 0x2888, 0x9c71, 0x1301, 0x3b46, 0x1504, 0x6187, 0x681]))),((BitVec.ofNat 768 (fromLimbs [0xd3f7, 0x76f3, 0xf73e, 0xd837, 0x177b, 0x7fa2, 0xfbdb, 0xcff4, 0xde58, 0x3775, 0xe282, 0x60e7, 0x7e9b, 0xac66, 0xba5d, 0xeefb,
        0xc1a2, 0xdc59, 0x4f08, 0x4bc3, 0x47f6, 0x3835, 0xd2f0, 0xd353, 0x5360, 0x79ec, 0x669b, 0x4764, 0xe44f, 0x58db, 0x364e, 0x8aec,
        0xbefa, 0x2ec9, 0x712f, 0xa4a4, 0xbbde, 0xec4d, 0xbd5b, 0xd1f5, 0x4955, 0x894d, 0x5ffb, 0xea5c, 0x988, 0xa235, 0xc8d0, 0x4ff0])),(BitVec.ofNat 768 (fromLimbs [0x6200, 0x4215, 0x4, 0x581a, 0x21, 0x520, 0x5835, 0x1204, 0xc850, 0xb402, 0x95d, 0x161, 0x9002, 0xa23, 0xc0c4, 0x302c,
        0x91c8, 0x4b48, 0x8172, 0x4214, 0x9f40, 0x8054, 0x140, 0x3d00, 0x4b29, 0x1881, 0x4002, 0x60ca, 0x8c0, 0x2522, 0x2284, 0x5301,
        0x4400, 0x627, 0x6a, 0xa0d0, 0x128, 0xb5c0, 0xc40, 0xa4c0, 0xfc30, 0x65, 0x6004, 0xa85e, 0xc0b8, 0xaa12, 0x8070, 0x4950]))),((BitVec.ofNat 768 (fromLimbs [0x16de, 0x1570, 0x66a7, 0xeae5, 0xb952, 0x15de, 0xbd07, 0xf185, 0x593f, 0x78cf, 0x4f84, 0xa4dc, 0xd64a, 0x6fd1, 0x2ebe, 0x908f,
        0x6e5b, 0x5796, 0x64eb, 0xb31b, 0xe169, 0x54b, 0x200e, 0x33bc, 0x75f, 0xadb0, 0xee45, 0x797b, 0xaefc, 0xb679, 0x9f2c, 0xff33,
        0xe11d, 0x63f0, 0xf330, 0xd6b0, 0xb7ad, 0x86c3, 0xe55e, 0x52ae, 0x7cee, 0xdab7, 0x5f9e, 0xa197, 0xa649, 0xdcc2, 0xdf, 0x700c])),(BitVec.ofNat 768 (fromLimbs [0x341, 0x204, 0x100, 0x2800, 0x4014, 0x5c8, 0x3002, 0x200, 0x8604, 0x9081, 0x8824, 0x8080, 0x8ea2, 0x832, 0xa24e, 0x2960,
        0x9451, 0x2820, 0x204, 0x4c44, 0xb700, 0x880, 0xa841, 0x4989, 0x4a31, 0xc200, 0xc40a, 0x4439, 0xac, 0x2122, 0x3004, 0x216,
        0x15c2, 0x6022, 0x8, 0x8020, 0x928, 0xb480, 0x608a, 0x10, 0x9c74, 0x1601, 0x3114, 0xa107, 0xd88a, 0xd280, 0x40fd, 0x5008]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xa1fb, 0x9be, 0x99b4, 0x6f6a, 0xb19c, 0xea5f, 0x4942, 0xbd81, 0xae7e, 0xfb57, 0xceff, 0x9ad8, 0xc46a, 0xc2ab, 0x6e30, 0x59f1,
        0xcc4a, 0x6275, 0x863b, 0xfd2e, 0x7c8f, 0xbd59, 0xe5d7, 0x5aaa, 0xffbb, 0x17ac, 0x7df0, 0xd372, 0xee8e, 0xdffb, 0xc3fa, 0xf1aa,
        0x5d03, 0x865c, 0xd5b7, 0x77de, 0x7ad1, 0x99f0, 0xefca, 0xb6b7, 0xfe79, 0x3c26, 0xb99c, 0x1f58, 0xf724, 0x9cc9, 0xb600, 0x400c])),(BitVec.ofNat 768 (fromLimbs [0x10, 0x10ea, 0x3433, 0xd115, 0x80ea, 0x1012, 0x425, 0x4471, 0x40b0, 0x71a, 0x2009, 0x3134, 0x2005, 0xe404, 0xc20, 0x9480,
        0x900, 0x8005, 0x809, 0x912b, 0x48ea, 0x2227, 0x594, 0x3202, 0x82, 0xd02, 0x2081, 0xb182, 0x1401, 0xc9c, 0xc84b, 0xb9c1,
        0x818, 0x8e08, 0x2a26, 0x2d81, 0x8281, 0x101, 0x9c01, 0x4e03, 0x201, 0xa87a, 0x4260, 0x1658, 0x2374, 0x2c57, 0xa300, 0x84]))),(0,0)]
def x189columns : List ColumnInfo := [(644,0,57,0,4),(545,0,156,0,4),(24,0,677,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 8 23 3 10 2 4 x189h7
  | 6 => lookupWord 1 3 1 9 1 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨701,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore knownx29) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_0 : block x189 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 1=true := sx189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_6 : block x189 6 0 4=true := sx189_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_5_0 : block x189 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_5 : block x189 5 0 1=true := sx189_5_0
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
theorem lowx189 : Lower true (varsX 701) (graphGoal 701) 8 :=
  strong_low (m:=701) (cap:=7) (l:=[(0,20),(2,9),(3,4),(4,1),(5,1),(7,4)]) (by decide +kernel) (plainA (q:=189) (prior:=boundsBefore knownx29) (before_sound knownx29 validx29) (by decide +kernel))
    (index_root (g:=x189) (i:=0) rfl rfl (before_sound knownx29 validx29) geomx189 tablesx189 (by decide +kernel))
def knownx189 := extendKnown knownx29 8 [(701,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx189 : Known true knownx189 := extendKnown_ok (m:=701) validx29 lowx189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx349 : Lower true (varsX 861) (graphGoal 861) 7 :=
  strong_low (m:=861) (cap:=6) (l:=[(0,20),(2,9),(3,4),(4,1),(6,256),(8,8)]) (by decide +kernel) (plainA (q:=349) (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (512,1,332,16,5) (by decide +kernel) (by decide +kernel))
def knownx349 := extendKnown knownx189 7 [(997,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx349 : Known true knownx349 := extendKnown_ok (m:=861) validx189 lowx349 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx413 : Lower true (varsX 925) (graphGoal 925) 7 :=
  strong_low (m:=925) (cap:=6) (l:=[(0,20),(2,9),(3,4),(4,1),(7,4),(8,8)]) (by decide +kernel) (plainA (q:=413) (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (512,1,396,16,5) (by decide +kernel) (by decide +kernel))
def knownx413 := extendKnown knownx349 7 [(949,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx413 : Known true knownx413 := extendKnown_ok (m:=925) validx349 lowx413 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx381 : Lower true (varsX 893) (graphGoal 893) 9 :=
  strong_low (m:=893) (cap:=8) (l:=[(0,20),(2,9),(3,4),(4,1),(5,1),(6,256),(8,8)]) (by decide +kernel) (plainA (q:=381) (prior:=boundsBefore knownx413) (before_sound knownx413 validx413) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx413) (before_sound knownx413 validx413) (516,0,377,0,8) (by decide +kernel) (by decide +kernel))
def knownx381 := extendKnown knownx413 9 [(893,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx381 : Known true knownx381 := extendKnown_ok (m:=893) validx413 lowx381 (by decide +kernel)
def x471d7 (i : Nat) : Nat := 0x440ffd20
def x471l7 : Packing := (1,1,2,0,0,0,0,x471d7)
def x471samples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x53a, 0xe61f, 0x4d1f, 0x4e5a, 0x6af6, 0x7e8e, 0x797e, 0xffe1, 0xa5dc, 0x7cae, 0xcacf, 0x2f9f, 0x6b95, 0xc93f, 0xf5ab, 0x6c2f,
        0xf65d, 0xc93, 0x1dc3, 0xf372, 0x789e, 0x3064, 0x7fed, 0x730e, 0x7775, 0xcc06, 0xcd2f, 0x7c8e, 0xde4b, 0x1cf6, 0x31be, 0x3d87,
        0x2fb8, 0x7ca5, 0xfd7b, 0xdf1, 0xd7b3, 0x7827, 0x7fff, 0x4200, 0x1066, 0x81be, 0x58b9, 0x1063, 0xfcc, 0x3c83, 0xb367, 0x43f3])),(BitVec.ofNat 768 (fromLimbs [0x6a82, 0x6824, 0x8413, 0xc40, 0x5888, 0xd005, 0x8014, 0x5022, 0x5d5c, 0x6a01, 0x11b4, 0x4e40, 0x825a, 0x104c, 0xa08, 0xe40,
        0x5c40, 0x5c00, 0x32c, 0x2009, 0xc891, 0x986, 0xc0da, 0x444, 0x41c2, 0x9311, 0x8684, 0x104, 0x8c00, 0x1b8, 0x9c12, 0x400c,
        0xa06, 0x11, 0x8405, 0x8606, 0x1061, 0x4700, 0xe5b1, 0xe292, 0xaa32, 0xaaaa, 0x1813, 0x2063, 0x948, 0x6c81, 0x3245, 0x4252]))),((BitVec.ofNat 768 (fromLimbs [0x97c6, 0x2473, 0x4718, 0x7bd5, 0xc1b3, 0xee57, 0x7ed6, 0x16b4, 0x1d59, 0x1333, 0x3c75, 0xcbfe, 0x5ff5, 0x3335, 0x7b37, 0xaebd,
        0xe478, 0x8462, 0x96e4, 0xf0b7, 0x4ff0, 0x7143, 0xcc7f, 0x3fe, 0x3d79, 0x7f63, 0x6b2b, 0xccdf, 0xd9c8, 0x8bb3, 0xbf7b, 0xe461,
        0x95ef, 0xe8e4, 0x767d, 0xe4fd, 0xfe7c, 0xdc37, 0x7e9c, 0x21, 0xec01, 0xffff, 0x2124, 0x3204, 0x367c, 0xc0f2, 0x4399, 0xfc9f])),(BitVec.ofNat 768 (fromLimbs [0x1161, 0x8408, 0x20c4, 0x9282, 0xa004, 0x2908, 0x6202, 0x1, 0x8022, 0x42, 0x202, 0x1004, 0x4004, 0x221, 0x44c4, 0x8188,
        0x822c, 0x5, 0x4450, 0x5002, 0x268, 0x2240, 0x501, 0x8000, 0x8008, 0x44, 0x1051, 0x6a, 0x42c9, 0xc00, 0x6160, 0x10e1,
        0x440, 0x9802, 0x4128, 0x118, 0x980, 0x22, 0x1208, 0x921, 0x1, 0x100, 0x6124, 0x1204, 0x2224, 0x8052, 0x4110, 0x2889]))),((BitVec.ofNat 768 (fromLimbs [0xdfd9, 0x11b7, 0xd2ce, 0xf2e3, 0x94bd, 0x93fc, 0x3279, 0xe27f, 0xd8e7, 0xe7d9, 0xfad2, 0xb526, 0xae69, 0x25ee, 0x47f9, 0xf681,
        0x8ba0, 0xb295, 0x753b, 0x38fa, 0x77e9, 0x3ffc, 0x299a, 0xbbf3, 0xaf86, 0x9a7e, 0xf763, 0x8a93, 0x9df4, 0xfa47, 0xfc37, 0xbff1,
        0x6d6e, 0xc975, 0xad5f, 0x55e5, 0x6def, 0xb9f6, 0xb9e0, 0x3c8, 0x129b, 0x7e00, 0x146, 0xec78, 0x3873, 0xf1c, 0x7ce1, 0x8f1c])),(BitVec.ofNat 768 (fromLimbs [0x8210, 0x10c0, 0x4b01, 0x901, 0x543, 0x211, 0x15c8, 0x887e, 0x2658, 0x9288, 0xa104, 0xa468, 0x81c1, 0x84, 0x8a30, 0x7203,
        0x12, 0xcc98, 0x388, 0x85bc, 0x4100, 0x5583, 0x30c6, 0x205, 0x60, 0xa603, 0xc400, 0x980, 0x8022, 0x4350, 0x100c, 0x8000,
        0x905, 0x2150, 0x81, 0x2c3, 0x420, 0x690, 0x4012, 0x244e, 0x766e, 0x6626, 0x3, 0x8c78, 0x1c52, 0x4a08, 0x28e1, 0x8714]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0x46b4, 0xfe8c, 0x7177, 0x555f, 0xea0f, 0x9cbb, 0x43fe, 0x83c5, 0x375e, 0x4f0d, 0x182f, 0x34cf, 0x46e8, 0x3888, 0xa784, 0xdf6e,
        0x4d1d, 0xaa1, 0x1dcd, 0xcb79, 0x60b6, 0x1903, 0x86ff, 0x58dc, 0x2347, 0xe360, 0xd473, 0x6a40, 0xd637, 0x6ad3, 0xaf9d, 0xcb57,
        0x26a8, 0xa439, 0xd04b, 0x8b39, 0x56ed, 0x571e, 0x4167, 0x28, 0x1164, 0x1, 0xd1f9, 0xf80, 0x3b83, 0xb01f, 0x80fe, 0xfe0])),(BitVec.ofNat 768 (fromLimbs [0x8140, 0x1253, 0x1240, 0x1017, 0x552, 0x2a88, 0x2b23, 0x851d, 0x203, 0x14fc, 0x60a, 0x110c, 0x5c00, 0xecb2, 0xb4d4, 0xd026,
        0x1b4, 0x2d1, 0x3402, 0x4ef6, 0x106e, 0x5630, 0x3f00, 0xa101, 0x1618, 0x4cac, 0x3832, 0x3c21, 0x40ba, 0x4647, 0x6269, 0x990,
        0x9141, 0x758e, 0x589a, 0x79e1, 0x211e, 0x80d6, 0x242, 0x1d6d, 0x55cd, 0x5555, 0xc1e8, 0xf80, 0x3683, 0x901e, 0x80ba, 0xda0]))),(0,0),((BitVec.ofNat 768 (fromLimbs [0xaa97, 0x4e57, 0x7bfe, 0xf19e, 0xb5c7, 0x4baf, 0xffcb, 0x698b, 0xc708, 0xefec, 0xe7e2, 0xe6c6, 0xbea3, 0xfff3, 0xea6, 0x535a,
        0xb1f7, 0xfbfb, 0xa20e, 0x2e25, 0x80a5, 0xf7a3, 0x9ed1, 0xc4cd, 0xcf0c, 0xf795, 0xaad7, 0x3361, 0xae43, 0xd7ef, 0xd241, 0x7e3f,
        0xb11f, 0xb23a, 0x7fc2, 0xf68f, 0x8903, 0x7f6a, 0xa71e, 0xfc37, 0xed00, 0x41, 0xae00, 0xfff, 0xc003, 0xffe0, 0xff, 0xf000])),(BitVec.ofNat 768 (fromLimbs [0x840a, 0x6004, 0x3, 0xd21, 0x1803, 0x4021, 0x8109, 0x800, 0x4a95, 0x6808, 0x48, 0x2512, 0x820, 0x7450, 0x3001, 0x42,
        0x1d92, 0x8848, 0x2001, 0x621, 0x1091, 0x4517, 0x8a10, 0x942, 0x60, 0x602, 0x4200, 0x4005, 0x906, 0xa06d, 0x16, 0x2814,
        0x6835, 0x180, 0x8000, 0x261, 0xb24b, 0x4b54, 0x2872, 0x5016, 0xd9c, 0x1e5f, 0x493, 0x952, 0x8003, 0x7fa0, 0xef, 0xd000]))),((BitVec.ofNat 768 (fromLimbs [0xdb0f, 0x93cf, 0xd300, 0x8134, 0xb589, 0xab06, 0x6eef, 0x4e25, 0x95fa, 0xf1f0, 0xea7e, 0x78c6, 0xbfc8, 0xb398, 0x187f, 0xf2da,
        0x9b2e, 0x2777, 0xe03e, 0x389b, 0xb289, 0x291d, 0xfdfb, 0xea2d, 0xa9d7, 0x7f3b, 0x1077, 0xc939, 0x1af6, 0xa46e, 0x667, 0xa3ab,
        0xdace, 0x4799, 0xc9ef, 0x8728, 0x4ee8, 0xdfce, 0xb88d, 0x43e8, 0x39a, 0x8001, 0xaf6e, 0xd000, 0x3, 0xbfff, 0xff00, 0x0])),(BitVec.ofNat 768 (fromLimbs [0x4502, 0x2610, 0xb0b6, 0x828a, 0xe884, 0x758e, 0x4823, 0x5480, 0x91a3, 0x507, 0x40da, 0x4305, 0x5e3e, 0x4808, 0x502, 0x830,
        0x1940, 0x7, 0xd036, 0x3a43, 0x69c, 0xa004, 0xc701, 0x1ce8, 0x6103, 0x5838, 0x2335, 0xc07a, 0x6d01, 0x2880, 0xcc01, 0x4e8c,
        0x140a, 0xda27, 0x466, 0xf418, 0xda5f, 0x5943, 0x821, 0xdbb1, 0x8991, 0x99d9, 0xfffc, 0x7000, 0x1, 0xb5f7, 0xd700, 0x0]))),((BitVec.ofNat 768 (fromLimbs [0xad70, 0xbec, 0x7aec, 0x618a, 0x22f2, 0x223a, 0xa1a5, 0xfbaf, 0x5f60, 0xf48a, 0x65c5, 0x2cf6, 0x4013, 0xedfb, 0x48ca, 0xbb49,
        0x36ba, 0xf799, 0xbf0, 0xbd36, 0xac7e, 0xcfef, 0xbea8, 0x675c, 0x4e65, 0x959f, 0x62fd, 0xdba3, 0x73b6, 0xfda9, 0x5c09, 0xd8df,
        0x407c, 0x927e, 0x79c8, 0xbe8b, 0xb72a, 0x73cf, 0x41ad, 0xfe3e, 0x1102, 0x8000, 0xaf6c, 0xdfff, 0xfbfc, 0x0, 0x0, 0x0])),(BitVec.ofNat 768 (fromLimbs [0x6af4, 0x9d10, 0xa290, 0xf200, 0xe10c, 0x154, 0x2f4, 0x87e1, 0x102, 0x561, 0x9f02, 0x10cd, 0x1399, 0x8a21, 0x8b14, 0xbf0c,
        0x21, 0x2515, 0x85fe, 0x6092, 0x8e64, 0xa8, 0x642d, 0xc4b1, 0x398e, 0x50e5, 0x1d63, 0xaf6a, 0x94c0, 0x1f90, 0x5d89, 0x9642,
        0x140, 0xd86e, 0x767d, 0x3510, 0x4520, 0x1023, 0x4401, 0xafe9, 0xf263, 0xe1a0, 0xfb6c, 0xf6ad, 0x7ffc, 0x0, 0x0, 0x0])))]
def x471columns : List ColumnInfo := [(660,0,323,0,4),(641,16,326,0,4),(516,128,339,0,5)]
def x471autos : List (List Nat) := [[],[98,135],[32,116],[32,96,116,132],[96,32,132,116],[96,132]]
def x471levels : Nat → Packing
  | 7 => x471l7
  | _ => emptyPacking
def x471index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x471 : Forest := ⟨983,7,fun j => x471samples[j]?.getD (0,0),x471columns,x471autos,x471levels,x471index⟩
set_option maxHeartbeats 0 in
theorem geomx471 : graphValid x471 (boundsBefore knownx381) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx471_7_0 : block x471 7 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx471_7 : block x471 7 0 1=true := sx471_7_0
theorem tablesx471 : checkedTables x471 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x471 0 0 0 = true)
  · exact (rfl : block x471 1 0 0 = true)
  · exact (rfl : block x471 2 0 0 = true)
  · exact (rfl : block x471 3 0 0 = true)
  · exact (rfl : block x471 4 0 0 = true)
  · exact (rfl : block x471 5 0 0 = true)
  · exact (rfl : block x471 6 0 0 = true)
  · exact allx471_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx471 : Lower true (varsX 983) (graphGoal 983) 8 :=
  strong_low (m:=983) (cap:=7) (l:=[(0,20),(1,1),(2,129),(4,1),(6,2),(7,4),(8,64)]) (by decide +kernel) (plainA (q:=471) (prior:=boundsBefore knownx381) (before_sound knownx381 validx381) (by decide +kernel))
    (index_root (g:=x471) (i:=0) rfl rfl (before_sound knownx381 validx381) geomx471 tablesx471 (by decide +kernel))
def knownx471 := extendKnown knownx381 8 [(983,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx471 : Known true knownx471 := extendKnown_ok (m:=983) validx381 lowx471 (by decide +kernel)
def xmd13 (i : Nat) : Nat := (fromLimbs [0x1, 0xd0b, 0x907, 0x402, 0x7f, 0xfd20])
def xml13 : Packing := (1,1,7,0,0,0,0,xmd13)
def xmh13 (i : Nat) : Nat := (fromLimbs [0x82c, 0x12, 0x11a4, 0xba2, 0xc815, 0x2031, 0x782, 0x3380, 0x802, 0x41, 0x2180, 0x100, 0x6502, 0x8000, 0x0, 0x0,
        0x4a3, 0xb107, 0xc04f, 0x47e8, 0x710, 0x100d, 0x6, 0x1cc, 0x1921, 0x0, 0x3, 0xc1c0, 0xa0, 0x4800, 0x0, 0x740,
        0x9408, 0x105, 0x8018])
def xmd12 (i : Nat) : Nat := (fromLimbs [0x62, 0xc0f8, 0x30cc, 0x50b, 0x8280, 0x2182, 0x4a0a, 0x8530, 0xa854, 0x5e1a, 0x209, 0x8002, 0xeb, 0xc04, 0x8278, 0x4c32,
        0x1a01, 0x8303, 0xe0a0, 0x2850, 0x7b42, 0xe07c, 0x3059, 0xa09, 0x80c0, 0x1061, 0x2520, 0xf0b0, 0x5c30, 0x1e03, 0x4, 0xa003,
        0x83c3, 0x6081, 0x4850, 0x39f0, 0xc110, 0x3c19, 0xc10, 0x4a1, 0x6028, 0xb800, 0x2198, 0x4c2a, 0x170c, 0x8603, 0x83e0, 0x2838,
        0x21, 0x7864, 0x3614, 0x1c0a, 0x6a0, 0xc0e8, 0xc283, 0x30c8, 0xb050, 0x2600, 0x803, 0xa40f, 0x85c3, 0x260, 0x3004, 0x59c2,
        0x983c, 0x2e18, 0xe00, 0x80a2, 0xd009, 0xc2e1, 0x80f0, 0x141c, 0xf8, 0x5c30, 0x2507, 0x180, 0x1801, 0x8209, 0xe1b1, 0x7838,
        0xa15, 0x154, 0x201f, 0xb86, 0x8002, 0x6021, 0x4484, 0xf098, 0x3c32, 0x1603, 0x8280, 0x493, 0x8304, 0xc030, 0xd820, 0x3c05,
        0xa8b, 0x494f, 0x2614, 0x6382, 0xcf49, 0xb0af, 0x9558, 0x9590, 0x91c5, 0x3025, 0x187c, 0x8a30, 0x9a00, 0x3ffa, 0xa690, 0x7ff6,
        0x4520, 0xffec, 0x9a41, 0xffd8, 0x3483, 0xffb0, 0x2907, 0xffe4, 0xd20f, 0xfe98, 0xa41f, 0xfd98, 0x483f, 0xff30, 0x907f, 0xfe45,
        0x20bf, 0xfc8a, 0x41ff, 0x9104, 0x82ff, 0xf309, 0x5ff, 0x6612, 0xffc, 0x9824, 0x17fd, 0x9148, 0x2ffb, 0x2690, 0x5ffe, 0x4d20])
def xml12 : Packing := (18,2,7,0,0,11,0,xmd12)
def xmh12 (i : Nat) : Nat := (fromLimbs [0x180, 0x8881, 0x9881, 0x3e40, 0xd000, 0x381, 0xc082, 0x3ed1, 0xbf01, 0xec10, 0xf940, 0xcbc1, 0x6fc1, 0x71d1, 0xd251, 0xea80,
        0xde42, 0x4a04, 0xd681, 0xc4c2, 0xbd1, 0xe500, 0x1fc0, 0xf2c1, 0x6951, 0x7c84, 0x8581, 0x1be5, 0x4bc1, 0x7951, 0x28dc, 0xd000,
        0x3c01, 0xd5c0, 0x1951, 0xcc91, 0xd921, 0x3301, 0x3791, 0x1041, 0x16e1, 0x7f00, 0x7c11, 0x4a81, 0x4341, 0x9d2, 0x400, 0x0,
        0x141, 0xa8d1, 0x86d1, 0xec02, 0x2c91, 0xa3d5, 0xafc1, 0xacc2, 0x1640, 0xb654, 0xb451, 0x3a00, 0x9600, 0x3500, 0xb2d0, 0x7181,
        0x7400, 0x0, 0x140, 0x6dc0, 0x4400, 0x0, 0x0, 0x18d, 0xa400, 0x241, 0xb681, 0x3900, 0x7151, 0x18d1, 0x2280, 0xbb58,
        0xf000, 0x0, 0x380, 0x7400, 0xd800, 0x35e, 0x8c0, 0xcc00, 0x59, 0x5f40, 0x2311, 0xa45d, 0x6800, 0x0, 0x81, 0x1fc2,
        0x3614, 0xc00, 0x390, 0x9082, 0x1900, 0x9a01, 0x9000, 0x0, 0x0, 0x110, 0x5591, 0xfb52, 0x1111, 0x8201, 0x4991, 0xb919,
        0x3182, 0x4e80, 0xeac1, 0x601, 0x2442, 0x4142, 0xd42, 0x2210, 0xcc01, 0xe151, 0x925e, 0x2d81, 0xff41, 0x4f10, 0x2641, 0x8f02,
        0x1e01, 0xe5c0, 0x4d12, 0x38c2, 0x4481, 0xca40, 0xfb91, 0xf180, 0xaad1, 0x8881, 0xe900, 0x5800, 0xd452, 0x1981, 0x5ac1, 0x2240,
        0x5300, 0xe781, 0x4440, 0xffc2, 0x280, 0x8400, 0x3c1, 0x2a44, 0xec1, 0xa000, 0x280, 0xa681, 0x8680, 0x541, 0xb941, 0x0,
        0x0, 0x1c0, 0x8000, 0x3d9, 0x7c00, 0x0, 0x0, 0x181, 0x12d2, 0x1c00, 0x0, 0x1d, 0x800, 0x0, 0x3c2, 0x400,
        0x0, 0x1d1, 0x2540, 0xec00, 0x0, 0x118, 0x9000, 0x380, 0xf6de, 0x3ec0, 0x5f12, 0x3300, 0x4381, 0xd000, 0x0, 0x0,
        0x0, 0x290, 0x7681, 0x6680, 0x1340, 0xaf91, 0xe1c0, 0xf10, 0x1f41, 0xc41, 0xfbd0, 0x1000, 0x0, 0x3d1, 0xdd1, 0x8f00,
        0x5640, 0xc1c1, 0x9e40, 0x25d1, 0x3041, 0x2cc1, 0x9591, 0x3e91, 0x5c91, 0xc000, 0x280, 0x8e19, 0xb800, 0x0, 0x110, 0x7c00,
        0x100, 0x2c00, 0x19d, 0x4a19, 0xe800, 0xbf41, 0x7c00, 0x1590, 0xed81, 0x5585, 0xaf00, 0x6782, 0x2404, 0xb701, 0x8345, 0xb9c0,
        0xc7d0, 0xf400, 0x9f00, 0xb50, 0x4081, 0xdd00, 0x6181, 0x3000, 0x241, 0x5f80, 0x4800, 0x2c1, 0xbc00, 0x3c1, 0x6101, 0xf750,
        0x6f00, 0xa302, 0x3800, 0x6991, 0x4440, 0x9181, 0xf000, 0x282, 0x334c, 0x78c1, 0x8800, 0x304, 0x3902, 0x1352, 0x2400, 0x2c0,
        0x2950, 0x2e98, 0xe400, 0x0, 0x1, 0x5141, 0xccd1, 0x9481, 0xd801, 0xa554, 0x3800, 0x0, 0x0, 0x218, 0x5802, 0x28c0,
        0xe341, 0xb000, 0x2c0, 0x3114, 0xd400, 0x394, 0x8600, 0x180, 0x7900, 0x395d, 0xd71c, 0x9400, 0x200, 0x7041, 0x1400, 0x1b00,
        0x1004, 0x520, 0x4000, 0x1000, 0xb0, 0xc00, 0x4000, 0x400, 0x208, 0x2cc, 0x9d81, 0x0, 0xc0, 0x0, 0x0, 0x0,
        0x0, 0x0, 0x0, 0x3d92, 0x4104, 0x100, 0x400, 0x608, 0x0, 0x520, 0x410, 0x1, 0x10, 0x8208, 0x0, 0x10,
        0x900, 0x1081, 0x10, 0x0, 0x1, 0x0, 0x10, 0x2000, 0x0, 0xc, 0x1, 0x8, 0x204, 0x1000, 0x5c0, 0x0,
        0x141, 0x0, 0x500, 0x0, 0x12, 0x4008, 0x0, 0x0, 0x100, 0x4000, 0x0, 0x400, 0x0, 0x800, 0x8000, 0x0,
        0x410, 0x8108, 0x0, 0x0, 0x108, 0x0, 0x0, 0x0, 0x0, 0x10, 0x708, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x4204, 0x84, 0x0, 0x0, 0x0])
def xmd11 (i : Nat) : Nat := (if i<1 then (fromLimbs [0x65f8, 0x96de, 0x5809, 0x54e5, 0x1293, 0x6e4a, 0x491b, 0x6436, 0x8ffe, 0x3828, 0xd063, 0x148b, 0x762b, 0x899, 0x6238, 0x8766,
        0x1a28, 0x5d61, 0x2a83, 0x5609, 0xe814, 0xdfd6, 0x7ecd, 0xf5e7, 0xc75e, 0xe67a, 0xbde6, 0x478d, 0xde0a, 0x7725, 0xd927, 0x545d,
        0x1a73, 0x65ca, 0xc71d, 0x5c3e, 0x6ff5, 0xbb26, 0xd75b, 0x306b, 0xbdaa, 0x469d, 0xda54, 0x689d, 0x9fa6, 0x70d9, 0x7864, 0xb58f,
        0x662f, 0xd87e, 0x60f5, 0x7de5, 0xe757, 0x665c, 0xbd70, 0x25b5, 0x5694, 0x594d, 0x6125, 0x67d5, 0x6854, 0x9d4b, 0xe51f, 0x5414,
        0x4efd, 0x36a4, 0xc7d2, 0xe84a, 0xc527, 0xa48e, 0x5202, 0x46dd, 0x18a4, 0x5c51, 0x3a43, 0xe50c, 0x2425, 0x5022, 0x3f34, 0xf8c3,
        0xd04f, 0x143b, 0x74e6, 0xa380, 0x4dac, 0x3534, 0xcee3, 0x2b4c, 0x582f, 0xe4ba, 0xe2db, 0x4b22, 0x2ae4, 0xa642, 0x88c9, 0xd825,
        0xe491, 0x22c, 0x4870, 0x2044, 0x7bc1, 0xdc47, 0x261b, 0x9469, 0x193, 0xc60e, 0x170c, 0x5821, 0x43c4, 0xba11, 0x9444, 0x2100,
        0x43ac, 0xd84, 0x3160, 0xadc2, 0x5807, 0xe41a, 0xe058, 0xc118, 0x334, 0x780, 0x1040, 0xff, 0xf54f, 0x9848, 0x3ffd, 0x5360,
        0x520f, 0xff6a, 0x5534, 0x83ff, 0xea95, 0x4d20, 0xfff5, 0x4d98, 0x483f, 0xfd93, 0x6052, 0xfff, 0x54f9, 0x1483, 0xffd8, 0x54c5,
        0x20ff, 0xf6a1, 0x5348, 0x3ffe, 0xa960, 0xd20f, 0xff61, 0x7934, 0x83ff, 0xda96, 0xd20, 0xfff6, 0xd91, 0x483f, 0xfd83, 0xe452,
        0xfff, 0x6958, 0x3483, 0xffd8, 0x564d, 0x20ff, 0xf685, 0x8348, 0x37fd, 0x5364, 0x520d, 0xff64, 0xd984, 0x82ff, 0xda86, 0x4520,
        0xbffe, 0x9593, 0x4837, 0xfd95, 0xe4d2, 0xffe, 0x6853, 0x483, 0x7fd9, 0x3645, 0x20df, 0xf60f, 0x9148, 0x2ffd, 0xa364, 0x520d,
        0xff68, 0xf914, 0x837f, 0xd81e, 0x4d20, 0xdff6, 0x8593, 0x483f, 0xf930, 0xe612, 0xdff, 0x54f9, 0x8483, 0x7fd8, 0x564d, 0x20ff,
        0xe4c1, 0x9148, 0x2fff, 0xa560, 0xd20f, 0xfe6a, 0x1304, 0x82ff, 0xda3e, 0x6120, 0xffe4, 0xc391, 0x4837, 0xfd31, 0x6612, 0xdff,
        0x6979, 0x3483, 0xbfd8, 0x1661, 0x20df, 0xf685, 0x9848, 0x2fff, 0xa864, 0xd20d, 0xff54, 0x7934, 0x82ff, 0xda3e, 0x4520, 0xffe6,
        0xa110, 0x4837, 0xfda8, 0xe452, 0xffe, 0x6551, 0x483, 0xfed5, 0x2e4d, 0x20df, 0xf663, 0x9348, 0x37fd, 0x93e6, 0x120f, 0xfe61,
        0x5104, 0x837f, 0xd93e, 0x4520, 0xdff6, 0x5531, 0x4837, 0xfda9, 0x60d2, 0xdff, 0x6619, 0x1482, 0xfffa, 0x960d, 0x20bf, 0xf697,
        0x9348, 0x37fe, 0xa954, 0xd20d, 0xffaa, 0x5834, 0x837f, 0xda86, 0x4d20, 0xdff4, 0xc798, 0x4837, 0xfda8, 0x6452, 0xdff, 0xe959,
        0x3483, 0x7fda, 0x564d, 0x20ff, 0xd607, 0x9148, 0x3ff9, 0x5344, 0x120f, 0xfb54, 0x9934, 0x83ff, 0x9934, 0x4120, 0xdff6, 0x8f98,
        0x483f, 0xfba0, 0x6612, 0xdff, 0x6639, 0x1483, 0xff58, 0x14c5, 0x20ff, 0xe68d, 0x1048, 0x2ffd, 0xa366, 0x120d, 0xff61, 0x7934,
        0x83ff, 0x9984, 0x4120, 0xffe6, 0x9530, 0x4837, 0xfd83, 0x6452, 0xbff, 0xe859, 0x3483, 0x7fd9, 0x3605, 0x20ff, 0xe615, 0x3048,
        0x37fd, 0xa954, 0xd20f, 0xfe60, 0xd104, 0x837f, 0xfa86, 0x4d20, 0xdffe, 0x8593, 0x4837, 0xfda3, 0x6452, 0xffe, 0x4c19, 0x8483,
        0xff9a, 0x4c5, 0x20ff, 0xe4c1, 0x8148, 0x37fd, 0xa8e4, 0xd20d, 0xffaa, 0x5314, 0x83fb, 0xfa46, 0x4d20, 0xbffe, 0x8583, 0x482f,
        0xfda8, 0xe4d2, 0xdff, 0xe859, 0x8483, 0x7fd5, 0x3e45, 0x20bf, 0xfe8d, 0x9848, 0x2ffd, 0xa8e4, 0x520d, 0xff65, 0x5934, 0x83ff,
        0x9a54, 0x4120, 0xbffe, 0x8598, 0x4827, 0xfda9, 0x54d2, 0x9ff, 0x6859, 0x8482, 0xffba, 0x14c1, 0x20de, 0xfe91, 0x9348, 0x27fc,
        0xa94c, 0x5209, 0xff2a, 0x5534, 0x837d, 0xd93e, 0x4d20, 0x9ff6, 0xa391, 0x482e, 0xffa6, 0x6052, 0x9ff, 0xe979, 0x3482, 0x7ffa,
        0x3e45, 0x209f, 0xf697, 0x9348, 0x3fd9, 0x304c, 0x5209, 0xffe8, 0x5984, 0x827f, 0xda1e, 0x6120, 0x9ff6, 0x8d91, 0x483f, 0xf151,
        0x4412, 0xff6, 0x4c15, 0x3482, 0xffba, 0x661, 0x209f, 0xf68f, 0x9148, 0x27ff, 0xa864, 0xd209, 0xff68, 0x7934, 0x836f, 0xda6e,
        0x6120, 0x9ffe, 0xa391, 0x482f, 0xf9a3, 0x4412, 0xffc, 0x4439, 0x1482, 0xffba, 0x3441, 0x20df, 0xde45, 0x9148, 0x3fbb, 0xa44c,
        0x120f, 0xfa54, 0x9304, 0x837f, 0x930e, 0x6120, 0x9ffe, 0x9593, 0x4833, 0xfd98, 0xe612, 0x9ff, 0xea19, 0x1482, 0x7fda, 0x8e4d,
        0x209f, 0xfe8f, 0x9848, 0x3fd9, 0x30e4, 0xd209, 0xff68, 0xf984, 0x82fb, 0xfa46, 0x4d20, 0xffa5, 0x4910, 0x4837, 0xf581, 0xe452,
        0xbbf, 0x69b9, 0x8482, 0x7ffa, 0x3645, 0x20cf, 0xf605, 0x9848, 0x27ff, 0xa164, 0xd209, 0xbf69, 0xb984, 0x827b, 0xfa46, 0x4d20]) else (if i<2 then (fromLimbs [0xc061, 0x3412, 0xc360, 0xb2, 0x16a, 0x1413, 0x482, 0xd03c, 0xdc30, 0x3341, 0x8141, 0x4940, 0x804, 0x70a, 0xc292, 0xc0cc,
        0x3602, 0x881, 0x3800, 0x1070, 0x180a, 0xb82, 0x201, 0xe048, 0xe04, 0x1083, 0x1f0, 0x1024, 0xf08, 0x8dc3, 0x320, 0xc306,
        0x1496, 0x301, 0xe850, 0x782e, 0x98c, 0xb03, 0x98, 0x1c07, 0x9583, 0x6140, 0xf024, 0x70a, 0xcc07, 0x8120, 0x7010, 0x407c,
        0x380a, 0x2e0, 0x3ca0, 0xd0a, 0x381, 0x171, 0x4166, 0x1a85, 0x60c0, 0x7080, 0xc0b5, 0xcc3, 0x30a0, 0xc506, 0x149e, 0x14c0,
        0x6010, 0x3e00, 0xa58, 0x6025, 0x88, 0x1c0c, 0x564, 0xa0d0, 0x3045, 0x86c0, 0x83, 0x260, 0x480e, 0x284, 0x40b0, 0x6a70,
        0x2009, 0x1c0, 0xf202, 0xc040, 0x1e30, 0x3428, 0x282, 0x221, 0x20c8, 0x5a16, 0x1003, 0x242, 0x2058, 0x3428, 0x26c1, 0xd0a4,
        0x282c, 0x1681, 0xe7c0, 0x4070, 0x2606, 0xc82, 0x9098, 0xec18, 0x1004, 0x80e0, 0x7958, 0x601a, 0x8503, 0xc292, 0x8274, 0x290a,
        0xc305, 0xa079, 0x983e, 0x1b85, 0xc040, 0x9098, 0xd003, 0x700, 0x8101, 0x3516, 0xf30, 0xac32, 0x412a, 0xc1f, 0x4c2, 0xb080,
        0xc098, 0x2809, 0x520, 0x7968, 0x3014, 0x708, 0x8182, 0x80f4, 0x1810, 0x790, 0xf02, 0x40e0, 0x2098, 0x350b, 0x2e0, 0x2048,
        0x4c60, 0x4413, 0x1c1, 0x40a4, 0x2b30, 0x2642, 0x82d4, 0x1810, 0x798, 0x21c0, 0x4260, 0x8830, 0xa140, 0x801d, 0x83c0, 0x1865,
        0x82d0, 0x810, 0x381, 0xe507, 0xc210, 0x4c12, 0xb40, 0xf342, 0x803c, 0x2a0d, 0x81e1, 0xe02, 0x1730, 0xa04a, 0x8126, 0x2c13,
        0x1c2, 0x6020, 0xc0c2, 0x2741, 0xa240, 0x3a0c, 0x7e0, 0x2c2c, 0x12a8, 0x4e00, 0x3f0, 0x10a5, 0x83a1, 0x5864, 0x500, 0x9a12,
        0x383, 0x2090, 0x5a16, 0x2214, 0x8000, 0x703f, 0x161, 0x4093, 0xb060, 0x1d0a, 0xd85, 0x25a1, 0x58b0, 0x1c18, 0xaca, 0x1500,
        0xec28, 0x5207, 0x9416, 0x6148, 0x5a0c, 0x803, 0xcc09, 0x8100, 0x384e, 0x1316, 0x8344, 0xc070, 0x3f01, 0x6160, 0x9380, 0x6038,
        0x3610, 0x1008, 0x984, 0x982, 0x4428, 0x3007, 0x9407, 0xc188, 0x6098, 0x1609, 0x4c0b, 0x1460, 0x480e, 0x1014, 0x702, 0x40f0,
        0x2098, 0xb0a, 0x1130, 0x60d8, 0xe10, 0xd160, 0x4600, 0xc32f, 0x161, 0x7862, 0x1816, 0xc028, 0x3081, 0xe8, 0x2c04, 0x120,
        0x381e, 0x6a0d, 0x8361, 0x81f0, 0x4808, 0x3ce, 0xf80, 0xe0f0, 0x1e40, 0x7416, 0x241, 0x20, 0xa140, 0x2780, 0xd0a0, 0x1810,
        0x4e0, 0x1430, 0x6807, 0xac22, 0xa0c0, 0x708f, 0xc0, 0x4120, 0x800f, 0x255, 0xc300, 0xec5a, 0x1380, 0x84c0, 0x4026, 0x8e2f,
        0x83e1, 0x812e, 0xb01, 0x4c3, 0x403d, 0x3c18, 0x5004, 0xf0c1, 0x1864, 0x502, 0x203a, 0x4090, 0xc0e, 0x282, 0x101c, 0xdc10,
        0x2580, 0x8260, 0x3868, 0x781, 0xc808, 0x8070, 0x1b00, 0xc041, 0x2080, 0xf02, 0x53c3, 0x60d0, 0x3f0b, 0x8060, 0x2049, 0xc09a,
        0x1439, 0x6183, 0x401c, 0xdc30, 0x4345, 0xb0a0, 0x5068, 0x39c, 0x28c0, 0x700e, 0x986, 0x8c0, 0x7a14, 0x2c02, 0x1442, 0x8540,
        0x3d17, 0x8082, 0x61a0, 0x1e80, 0x2021, 0xc030, 0x103c, 0x937, 0xc03, 0x70b8, 0x602, 0x480, 0xe704, 0xc2a0, 0x1c21, 0x6168,
        0xbc04, 0x3403, 0xd20f, 0x4d0, 0x30c, 0x3f0, 0xa0a0, 0x1380, 0x81ea, 0x2178, 0x201f, 0x106, 0x6860, 0x4c34, 0x3d3, 0x8080,
        0xe805, 0x607, 0x82c6, 0x4f0, 0x1c, 0x2161, 0x701a, 0x2c34, 0x3d2, 0x1103, 0xd805, 0xb80, 0x86ec, 0x1830, 0x8e0c, 0x3e1,
        0x98bc, 0x685, 0x1cf, 0xc370, 0xa41e, 0x380, 0x440, 0x39f0, 0x18, 0x360d, 0x4090, 0x28c0, 0x8b0a, 0x3d1, 0x609e, 0x21a,
        0x1e8, 0xc050, 0x24, 0x803, 0xc073, 0x602c, 0x2f0c, 0x386, 0x20a1, 0xa83c, 0x700, 0x240, 0x803c, 0x738, 0x31c1, 0x7078,
        0x81e, 0x999, 0x2880, 0x1010, 0xa213, 0x4f8, 0x361a, 0x8502, 0xf5, 0x8360, 0x980f, 0x41b0, 0xb808, 0x5211, 0x2300, 0xe0c0,
        0x9c06, 0x8561, 0x82b0, 0x6118, 0x44, 0x38f, 0x10b, 0xc09c, 0x22, 0x1cc, 0x3d0, 0xa0f0, 0x4580, 0xb078, 0x10, 0x8027,
        0x1a0, 0xc236, 0x1422, 0x1cf, 0xc160, 0x2098, 0xe16, 0x81e0, 0x71c1, 0xbc00, 0x608, 0x985c, 0x407, 0xa0c1, 0x84c0, 0xfc17,
        0x17c3, 0x57c, 0x1e02, 0x402, 0x694a, 0x3830, 0xa200, 0x1e8, 0xb618, 0xf02, 0x12c1, 0x80fc, 0x2f0d, 0x8060, 0x2049, 0xf85c,
        0x700, 0xe181, 0x8024, 0x73f, 0xc10, 0xd16c, 0x2e02, 0x1200, 0xe708, 0x807c, 0x700, 0x800, 0xf024, 0xfc1e, 0x10, 0xe034,
        0x281e, 0xc583, 0x8e1, 0xb85c, 0x301, 0x24b, 0xc170, 0xdc5f, 0x780, 0x8266, 0x9f76, 0x7a69, 0xcf67, 0x69a, 0xc666, 0x6989]) else (fromLimbs [0x19, 0x8a8, 0x301c, 0x9418, 0x4d04, 0x8121, 0x1143, 0xc0ec, 0x2e0a, 0x130, 0x201b, 0x481, 0x8065, 0x4160, 0x100d, 0x81e0,
        0xc942, 0xc064, 0x2202, 0x2830, 0x5807, 0x3d0, 0xb41, 0x204a, 0x2603, 0x84c0, 0x41c0, 0x8802, 0x1a2, 0xc070, 0x3cd0, 0x40a,
        0x1301, 0x40b, 0xa30, 0x6416, 0x841, 0xb304, 0x4049, 0x604, 0x2c5, 0x8068, 0x5020, 0x720, 0x6611, 0x264, 0x2830, 0xb1a,
        0x1585, 0x90, 0x3c07, 0x2c01, 0x81, 0xe048, 0xe50, 0x64a3, 0x842, 0x2058, 0xb09c, 0x2542, 0x8300, 0x4140, 0x8270, 0x1b06,
        0x8092, 0x8540, 0xdc28, 0x1130, 0x7800, 0x4345, 0x8100, 0x3b0c, 0xc2b1, 0x8504, 0xe830, 0x2408, 0x3cc, 0x4181, 0x2040, 0x1e46,
        0x1813, 0x1c0, 0xf0a4, 0xa10b, 0xc17, 0x404, 0x468, 0x501c, 0x1204, 0xc290, 0x3cec, 0x2852, 0x381, 0xe4c0, 0x76, 0x141b,
        0x840, 0xfc04, 0x3a02, 0x5209, 0x90a1, 0x5052, 0x794, 0x503, 0x8180, 0xac8c, 0x1e02, 0x3d0, 0xb032, 0x1213, 0x1c2a, 0x62c1,
        0x3a14, 0x8501, 0xc290, 0x3d1c, 0x350c, 0x550, 0x6149, 0x4210, 0x9a0b, 0xc040, 0x7c00, 0x2238, 0x2c0c, 0x450, 0x9813, 0x4281,
        0xc18, 0x4780, 0x68c, 0x3301, 0x401c, 0xf18, 0x1e03])))
def xml11 : Packing := (148,3,7,0,0,14,0,xmd11)
def xmh11 (i : Nat) : Nat := (if i<1 then (fromLimbs [0x5443, 0xae4d, 0xfb03, 0xd200, 0x5208, 0x917e, 0xc08, 0x870d, 0x620d, 0xbc55, 0x7302, 0x3903, 0x4000, 0x90c, 0x5000, 0x0,
        0x0, 0x0, 0x904, 0x1444, 0xd109, 0x5903, 0x8e01, 0xa508, 0x40d, 0xdf0a, 0x680c, 0x6000, 0xf0a, 0x9000, 0x0, 0xd02,
        0x2304, 0xce49, 0xb30e, 0xe000, 0xf0e, 0x1a03, 0x1402, 0x690d, 0x4d4e, 0xab0f, 0x4606, 0x6f40, 0x6000, 0xe01, 0xc000, 0x0,
        0xd04, 0xf406, 0x2907, 0x8141, 0x4840, 0x4000, 0xa, 0xd000, 0x704, 0xb000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x80b,
        0xd26b, 0xc285, 0x7308, 0x100d, 0xfa0a, 0xad48, 0x4d0a, 0x760f, 0x2000, 0xd04, 0xd449, 0x9c4c, 0x9842, 0x5000, 0x340, 0xd000,
        0xb01, 0x130f, 0x6000, 0x0, 0x0, 0x0, 0x40b, 0x4b4a, 0xce4d, 0xe43b, 0xfd0c, 0xab03, 0xed01, 0xe000, 0x70d, 0x70a,
        0x270b, 0x944b, 0xe702, 0xb00b, 0xfd0d, 0x7000, 0x30c, 0x9101, 0x7588, 0x530b, 0xb000, 0xe47, 0xf201, 0x2000, 0x749, 0x8809,
        0xa306, 0x3505, 0x8209, 0xe000, 0x0, 0x0, 0xf05, 0xc965, 0x800a, 0x4a0b, 0xa205, 0x334d, 0x6d48, 0xdd05, 0x2000, 0x0,
        0x0, 0x10b, 0x384d, 0xa604, 0x6c67, 0xd09, 0xc207, 0x1000, 0xa41, 0x7000, 0x14d, 0xb997, 0xfc05, 0xfc03, 0xbc00, 0xed05,
        0x1000, 0x0, 0x22b, 0xfe4d, 0x4000, 0x807, 0x6000, 0x0, 0x0, 0xc0e, 0xc30c, 0xf502, 0x8000, 0x0, 0x0, 0x0,
        0x707, 0xb008, 0xdc4c, 0xcd03, 0x2904, 0x5909, 0x8d02, 0xad4d, 0x280e, 0x4430, 0x1508, 0xf902, 0xc007, 0x3b67, 0x3b4f, 0x600,
        0x3b0f, 0xab08, 0xb70c, 0xbc0d, 0x3102, 0x4000, 0x664, 0x50e, 0xf16c, 0xcd4d, 0xc000, 0xb02, 0xd906, 0xd06, 0xbf03, 0x7a06,
        0xc906, 0x7000, 0x0, 0x0, 0xe00, 0xd000, 0x202, 0x5000, 0x0, 0x0, 0x0, 0xa43, 0x9c4c, 0x1345, 0xe, 0xb504,
        0x9408, 0x7940, 0x2a04, 0x8468, 0x5f0b, 0x8745, 0x4000, 0x2000, 0x0, 0x243, 0x5e06, 0x8000, 0xf08, 0x617e, 0xb447, 0x5000,
        0x0, 0xc00, 0x100c, 0x1d04, 0x3f13, 0xa70c, 0xe05, 0xd000, 0x20e, 0x2103, 0x9746, 0x2605, 0xa800, 0xa37a, 0xcd0b, 0xe000,
        0x70d, 0xe847, 0x7000, 0x0, 0x0, 0x70d, 0x8000, 0x602, 0xe44d, 0x7000, 0x40c, 0x4000, 0x60f, 0x7000, 0xb03, 0xff41,
        0xe000, 0x0, 0x307, 0x5701, 0x6000, 0x106, 0xa000, 0xe0c, 0x2f44, 0x2606, 0xf000, 0xa0e, 0x987d, 0xb000, 0xa01, 0x5c40,
        0xf917, 0x3000, 0x0, 0xa46, 0x5701, 0x8409, 0x6000, 0x909, 0x3000, 0x106, 0x5000, 0x246, 0xd74a, 0x7442, 0xe0a, 0xeb85,
        0x4fa0, 0x2007, 0xdf48, 0x84a8, 0x4262, 0x9176, 0xd604, 0xed0a, 0xba07, 0x484b, 0x8507, 0xe308, 0x5005, 0x6e40, 0x9842, 0xf809,
        0x160d, 0x2000, 0x649, 0x1509, 0xd000, 0xb, 0x5201, 0xf000, 0x0, 0x0, 0xb48, 0xb000, 0xb09, 0x4000, 0x909, 0x7b45,
        0xe00e, 0x605, 0x7248, 0xee00, 0xba00, 0xcc0e, 0x3000, 0x0, 0x0, 0x0, 0xf04, 0x903, 0x3000, 0x0, 0x0, 0xb0a,
        0x8000, 0x0, 0x79, 0xc203, 0xc000, 0x0, 0xb09, 0x2000, 0x0, 0x40e, 0x7f0c, 0xc842, 0x4800, 0x810f, 0x3907, 0xe02,
        0x7603, 0x6904, 0x2e08, 0xe50a, 0x3c05, 0xd, 0xcd00, 0x650f, 0x8705, 0x9503, 0xa90d, 0xa000, 0xc0d, 0x5c05, 0xbd67, 0xee0b,
        0xb0e, 0x844e, 0x444c, 0xd000, 0x907, 0x7003, 0xa90, 0x8, 0x2000, 0x800, 0xd330, 0x7000, 0x2, 0x4b10, 0x2, 0x102,
        0x5600, 0x0, 0x40, 0x128, 0x7004, 0x800, 0x4000, 0x40, 0x50, 0x208, 0x1, 0x400, 0x8200, 0x80, 0x60, 0x0,
        0x280, 0x30, 0x204, 0xb006, 0x430, 0x100, 0x1003, 0x420, 0xc700, 0x1002, 0x0, 0x400c, 0x1c0, 0x10, 0x300, 0x2002,
        0x800, 0x100, 0x0, 0x0, 0x0, 0x0, 0x400, 0x8018, 0x0, 0x0, 0x0, 0x3, 0x60, 0x8100, 0x44, 0x0,
        0x8, 0x0, 0x800, 0x0, 0x83, 0x1410, 0x8000, 0x101, 0x10, 0x0, 0x2, 0x10, 0x4, 0x0, 0x0, 0xc,
        0x8000, 0x0, 0x0, 0x10c2, 0x0, 0x4000, 0x41, 0x10, 0x0, 0x100, 0x0, 0x0, 0x1008, 0xc00, 0x8300, 0x80,
        0x800, 0x104, 0x40, 0x0, 0x4, 0x80, 0x0, 0x8000, 0x0, 0x800, 0x0, 0x2, 0x0, 0xc100, 0x0, 0x20,
        0x0, 0x5000, 0x400, 0x4000, 0x0, 0x20, 0x508, 0x0, 0x0, 0x4014, 0x1000, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x0, 0x0, 0x0, 0x0, 0x0, 0x400, 0x240, 0x0, 0x0, 0x1000, 0x0, 0x0, 0x3000, 0x0, 0x0, 0x1]) else (fromLimbs [0x901, 0x9000, 0x0, 0x206, 0x1b0c, 0xe10b, 0x1000, 0xf01, 0x3b68, 0x6507, 0x2101, 0xb44e, 0xe000, 0x0, 0x0, 0x0,
        0xa, 0x0, 0x90d, 0x9502, 0x9d0b, 0x7907, 0x9c0f, 0xf09, 0xf046, 0xa000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        0x450c, 0x8eb5, 0x5e4a, 0xa90b, 0xcd07, 0xc10b, 0x600a, 0xfe02, 0xfa06, 0xe505, 0x4e44, 0x7704, 0xad07, 0xa30c, 0xd677, 0x404e,
        0xfd08, 0x2a06, 0xdc63, 0xd608, 0xa30c, 0x310c, 0x7c09, 0xb90f, 0x1f06, 0x4000, 0x5a5, 0x530a, 0x1d08, 0x4000, 0xf402, 0x140e,
        0x681b, 0xa44c, 0xae47, 0x4697, 0x483e, 0x264e, 0x1108, 0xc000, 0x200, 0x9a4a, 0xff4b, 0x5000, 0x0, 0x0, 0x30e, 0xd14d,
        0x3b41, 0xff0e, 0x5a49, 0x30f, 0x9e09, 0xf4e, 0x7000, 0x809, 0x9c01, 0x4c0a, 0xc104, 0x7000, 0x80a, 0x5000, 0x843, 0x3000,
        0x0, 0x30e, 0xa943, 0xb03, 0x5901, 0x6b8, 0x4003, 0x200, 0xe06, 0x97a5, 0x774d, 0x8b43, 0xfe0d, 0x1205, 0xe208, 0x3f0f,
        0x5147, 0x3649, 0xaf45, 0x7e46, 0x1949, 0x5d0b, 0x2304, 0x4805, 0x5e6e, 0xad02, 0xc07, 0xfb41, 0x8f01, 0xdf00, 0x7a67]))
def xmd10 (i : Nat) : Nat := (if i<2 then (if i<1 then (fromLimbs [0x68f9, 0x1483, 0x37ec, 0x9f4c, 0xc0a4, 0x11ff, 0xecfa, 0x1661, 0x20cf, 0x7f68, 0xd1b2, 0x2905, 0x7bfb, 0x464f, 0x9148, 0x23ff,
        0xd9b4, 0x2cc2, 0x411f, 0xf6e9, 0x53e4, 0x520c, 0xf7f4, 0x9d43, 0x2690, 0x779f, 0x93e9, 0x1934, 0x83ef, 0x5dba, 0xa488, 0x2411,
        0xff6c, 0xfa86, 0x4520, 0xcf7b, 0xbd2, 0x3269, 0x47f, 0xfba6, 0x5531, 0x4833, 0x7ed3, 0x347c, 0xc241, 0x9fd6, 0x7a1, 0x64d2,
        0xddf, 0x260d, 0x3730, 0x9047, 0xfdba, 0x6179, 0x3483, 0x3dec, 0xf48, 0xc9a4, 0x15f7, 0x6cea, 0x954d, 0x20ef, 0x7331, 0xd226,
        0x906, 0x7f7a, 0x1685, 0x9348, 0x3fe8, 0xc0a6, 0x98a, 0x41cf, 0xe4c1, 0x98e6, 0x120a, 0xfbf6, 0x6d4b, 0x690, 0x47ff, 0xb8e9,
        0x5934, 0x833d, 0xfd27, 0x4ac9, 0xa415, 0xf76c, 0xea94, 0xc520, 0xfed2, 0xa4a9, 0xa209, 0x47f, 0xfb56, 0x8d91, 0x4833, 0xdfd2,
        0x342c, 0x9a41, 0x57fe, 0xdda5, 0x64d2, 0x8ff, 0xb63d, 0x4326, 0x906f, 0x6d52, 0xe959, 0x3483, 0x7d7d, 0x22a4, 0xc9a4, 0x11ff,
        0x6eaa, 0x94c5, 0x20ff, 0x9260, 0xa972, 0x6904, 0x7fdb, 0x9e85, 0x8348, 0x37f4, 0xa934, 0x6882, 0x419d, 0xf697, 0xa564, 0xd208,
        0xffb6, 0x6d0b, 0x3090, 0x47ff, 0xb868, 0xf914, 0x82bf, 0xdd83, 0x4ac9, 0xa411, 0xff6d, 0x4a94, 0xc520, 0xcf7f, 0x48d2, 0xb269,
        0x5fe, 0xbb26, 0x9530, 0x483b, 0xec98, 0x2a7c, 0xc241, 0x1ffe, 0xc5a8, 0xe4d2, 0x8ff, 0xb6bd, 0x1f30, 0x906e, 0xf930, 0xe998,
        0x1483, 0x7ec9, 0x8746, 0xcc24, 0x1fe6, 0xed13, 0x54d, 0x20ff, 0x3768, 0x9826, 0x2905, 0x7f5b, 0x1aa5, 0x3148, 0x2bfd, 0xd835,
        0xc8a, 0x413f, 0xe6c3, 0xa960, 0xd20d, 0xfd2a, 0x5d1a, 0x2090, 0x6bfb, 0xa060, 0x5984, 0x8337, 0xec9b, 0x4dcc, 0x2418, 0xff6a,
        0x181e, 0x4d20, 0x9ff3, 0x63d0, 0x3309, 0x47f, 0xdb36, 0xa391, 0x482b, 0xdfda, 0x326c, 0x8a41, 0x5fbe, 0xc9a8, 0x64d2, 0x8ff,
        0xb71d, 0xb26, 0x9047, 0xfdb8, 0xe8f9, 0x1483, 0x3dfd, 0x2350, 0xc9a4, 0x1df5, 0x4c7a, 0x164d, 0x20e7, 0xea62, 0xc0b3, 0x904,
        0x7fdb, 0x8e95, 0x9348, 0x31fe, 0xd475, 0xc9a, 0x41ff, 0x8485, 0xa04c, 0x520e, 0xf776, 0x8987, 0x3090, 0x67bf, 0xa4e8, 0x5934,
        0x83bf, 0x4a92, 0x61cc, 0x2419, 0xfd68, 0xd81e, 0x4520, 0xafdf, 0x64d0, 0xb269, 0x5fb, 0xbb46, 0x4d10, 0x4833, 0xdfd2, 0x32ac,
        0x9a41, 0x1ffe, 0xe1a5, 0xe4d2, 0xdfb, 0x260d, 0x2f26, 0x905f, 0xebb2, 0x6a13, 0x482, 0xff9d, 0x8b26, 0x8824, 0x1cfd, 0x607a,
        0x1661, 0x20df, 0xd744, 0x9833, 0x904, 0xfedb, 0x2ea5, 0x8348, 0x23fe, 0xdc74, 0xbc9a, 0x411f, 0xfec5, 0xa3e6, 0x120c, 0xfbb4,
        0x698f, 0x3090, 0x5dfb, 0xb765, 0x5104, 0x827f, 0x7d93, 0x46c8, 0xa41b, 0xeeed, 0x1a34, 0x4120, 0x8ffb, 0x67d4, 0x7229, 0x4fe,
        0xfb26, 0x8d98, 0x4833, 0xfac0, 0x9529, 0x8a41, 0x7fae, 0xc9a8, 0x4412, 0x8ff, 0xf62d, 0x2f26, 0x9073, 0xf930, 0x6059, 0x8483,
        0x7f88, 0x8742, 0xcc24, 0x17f6, 0xecda, 0x84c1, 0x208f, 0xff63, 0xd432, 0x6905, 0xfebb, 0x2685, 0x3048, 0x33df, 0xda35, 0x2a9a,
        0x417f, 0xcec5, 0xa844, 0x120e, 0xdf26, 0xd37, 0x3090, 0x57f7, 0xb164, 0xd914, 0x823f, 0xedaf, 0x50c9, 0xa413, 0xfeec, 0x1a86,
        0x4520, 0xcf7a, 0xa3d2, 0x3269, 0x57d, 0xdb3a, 0xa583, 0x4833, 0x7ea9, 0xb4dc, 0xc241, 0x5fde, 0xc598, 0x6452, 0x8ff, 0xb6ad,
        0xf26, 0x9057, 0xbfb4, 0x64d9, 0x8483, 0xbec9, 0x8263, 0xcc24, 0x1cfd, 0x605a, 0x8e45, 0x20ff, 0x3768, 0x9872, 0x6904, 0x7fdb,
        0x5e85, 0x9348, 0x23fe, 0xd9b4, 0x3cc2, 0x41ff, 0x8485, 0x30e4, 0x5208, 0xffb6, 0xbd1b, 0x2290, 0x67bf, 0xb468, 0xf914, 0x829f,
        0xedc5, 0x52c1, 0xa417, 0xfaec, 0x9984, 0x4120, 0x8ffb, 0x67d0, 0xb309, 0x6fe, 0x952e, 0x8530, 0x4823, 0xffda, 0xb47c, 0xc241,
        0x1ff6, 0xe953, 0xe612, 0xbfd, 0x764d, 0x1a20, 0x9047, 0xfdb1, 0xe959, 0x3482, 0x3fed, 0xaf47, 0xc8a4, 0x19fd, 0x607a, 0x3e45,
        0x20ce, 0xfb2b, 0xd2b2, 0x6905, 0x7bfb, 0x468d, 0x9148, 0x2bdf, 0xda34, 0x7c8a, 0x4157, 0xfedd, 0x95e4, 0xd208, 0xfff6, 0xad1f,
        0x2290, 0x47ff, 0xb56a, 0x3934, 0x82bd, 0xfda3, 0x27cc, 0x2411, 0xff6e, 0x7a56, 0xd20, 0xff57, 0x48a9, 0x2609, 0x77d, 0x9306,
        0x6393, 0x4837, 0xf290, 0xf42c, 0x9a41, 0x5fbe, 0xc9a3, 0x6452, 0xcfe, 0xb43d, 0xb30, 0x906f, 0xbba4, 0x6853, 0x482, 0xbefd,
        0x9b52, 0xa9a4, 0x157f, 0xedda, 0x5e4d, 0x208f, 0xfb71, 0xd1b2, 0x2907, 0x3fbb, 0x663, 0x9848, 0x32ff, 0xdbb4, 0xbc9a, 0x415b,
        0xfed9, 0x81e4, 0xd20c, 0xfbf4, 0x6c9b, 0x3090, 0x57fb, 0xb068, 0x5984, 0x83fb, 0xa92, 0xa288, 0x241f, 0xd254, 0x9305, 0x4d20]) else (fromLimbs [0xba66, 0xe813, 0x9e4e, 0x76b9, 0xa4e5, 0x6392, 0x2e3b, 0x38b6, 0xe203, 0x84ae, 0x537, 0xdede, 0xa377, 0x2dcf, 0x3706, 0xdb43,
        0x6b0d, 0x9eb6, 0x18d7, 0x8b5a, 0xcd68, 0xb582, 0xd4db, 0x500d, 0x3834, 0x7ed1, 0x233d, 0xcec, 0x3390, 0xcd6b, 0x350c, 0xbbb2,
        0xa2c9, 0xb323, 0x6c7a, 0xb1ca, 0xc653, 0x15ec, 0x4fb1, 0x8c2, 0x9b07, 0xc14, 0x301a, 0xbf92, 0xfdab, 0xe92f, 0x6ebb, 0xdaec,
        0xb97, 0xae12, 0xb772, 0xd90b, 0x512d, 0xeb3, 0x62c6, 0xb0a, 0xabf4, 0xaefa, 0xb1aa, 0xb92a, 0x98a9, 0x8aa2, 0xca6d, 0x297e,
        0xa522, 0x912a, 0x3728, 0x7aa1, 0x1280, 0xe9eb, 0x2760, 0x9bfa, 0x6709, 0x8925, 0xd896, 0x3255, 0x6948, 0x24d4, 0x927a, 0x4689,
        0x723, 0xe68e, 0xc236, 0x48c6, 0x22e2, 0x8ab2, 0x2608, 0x7fa1, 0xb285, 0xf213, 0x839, 0x206c, 0x80d9, 0xfea7, 0xed1f, 0x3c7c,
        0x19ed, 0x7a6, 0x9e64, 0x77b1, 0xdb67, 0x601d, 0x3473, 0xa1cb, 0x271f, 0x1c46, 0x7041, 0xb986, 0xd89b, 0x2c6b, 0x29a9, 0x4692,
        0x19fc, 0x6719, 0x97a6, 0x5119, 0xe63, 0x618a, 0x2610, 0x180a, 0x5f51, 0x7885, 0xc416, 0xda5a, 0x3962, 0xc57d, 0x95c0, 0x5629,
        0x5545, 0x4794, 0xe852, 0xc947, 0xc501, 0x13b8, 0x4db1, 0x3364, 0xba92, 0xb449, 0xa120, 0x6474, 0x1184, 0x44e1, 0x1024, 0x3310,
        0x5440, 0x78fb, 0xc3e1, 0x8f50, 0x3c68, 0xee43, 0xa60e, 0x3637, 0xa8d7, 0x234f, 0xcda, 0x3238, 0xc583, 0x88b, 0xec2d, 0xd0b3,
        0xe2bc, 0x8a90, 0x28b8, 0x9f82, 0x7089, 0x6024, 0xa88f, 0x422f, 0x8888, 0x2148, 0x7f01, 0xe387, 0x421c, 0x306d, 0x61a8, 0x66a,
        0x18d0, 0x5d21, 0x6185, 0x3a14, 0x104c, 0xe126, 0x462, 0x1058, 0x3e00, 0xea83, 0x740c, 0xa02d, 0xc099, 0x202, 0x6d8, 0xd00,
        0x57, 0xfdb8, 0x54d9, 0x1482, 0xbfed, 0xaa62, 0xcc24, 0x15ff, 0xec5a, 0x954d, 0x20af, 0xff70, 0xa9f2, 0x2906, 0x7fd8, 0x52a5,
        0x3148, 0x2bfe, 0xdcaa, 0x6c0a, 0x41df, 0xd645, 0x53e4, 0x520e, 0xfeb0, 0x3d0b, 0x2690, 0x6efd, 0x5369, 0xb984, 0x827f, 0xedab,
        0x47cc, 0x241b, 0xfb48, 0x7a56, 0xd20, 0xdfda, 0xa5d0, 0xb069, 0x67f, 0xd956, 0x8f98, 0x4833, 0xfed4, 0x2a3c, 0x9a41, 0xbbfe,
        0x9953, 0x6052, 0xaff, 0xf70a, 0x9b22, 0x9077, 0xed52, 0x4c79, 0x8483, 0x7fcc, 0x2f46, 0x8824, 0x1ff6, 0x4c18, 0x54c5, 0x20dd,
        0xff4c, 0xc9b0, 0x2907, 0xfbbb, 0x44c1, 0x8148, 0x3ff4, 0xa926, 0xc0a, 0x419f, 0xf695, 0x31e6, 0x120a, 0xffb6, 0x354b, 0x690,
        0x7ff1, 0x8354, 0x5104, 0x83bf, 0xbc8b, 0x6c8, 0xa41d, 0xfde4, 0x5536, 0x520, 0xffca, 0x42c1, 0xf229, 0x6ff, 0x5816, 0x8f91,
        0x483f, 0xecc1, 0xaa68, 0x8241, 0xbfb5, 0x49a3, 0xe612, 0xefb, 0xb06a, 0x9f22, 0x9067, 0xfd95, 0xe858, 0x3483, 0x7f7d, 0x42a4,
        0xc9a4, 0x1ffa, 0x5498, 0x3441, 0x20af, 0xff6a, 0xcc72, 0x6907, 0x7f58, 0x164f, 0x9148, 0x33fe, 0xc8f4, 0xac1a, 0x419f, 0xf617,
        0xa364, 0x520c, 0xffb0, 0xad1b, 0x2290, 0x7fd9, 0x3054, 0xf984, 0x82bf, 0xed8d, 0x52a9, 0xa41f, 0xeee9, 0x1854, 0xc120, 0xfef3,
        0xaa9, 0xa209, 0x67f, 0xd856, 0x8793, 0x4833, 0xfec2, 0xb47c, 0x8a41, 0x9ffe, 0x8585, 0xe4d2, 0xcff, 0xaa6d, 0xf30, 0x9077,
        0xf581, 0x68f9, 0x1483, 0xff88, 0x82a7, 0xc8a4, 0x13ff, 0x6d7a, 0x864d, 0x20ef, 0x7b03, 0xd232, 0x6907, 0xfe95, 0x24c3, 0x9848,
        0x33fe, 0xc2f4, 0x2c9a, 0x41bf, 0xe617, 0xa14c, 0x120d, 0xff22, 0x1d2b, 0x690, 0x4ffe, 0xba54, 0xd984, 0x83bf, 0x7cc2, 0xa4c9,
        0xa41d, 0xf7e4, 0xd856, 0x4d20, 0xdff3, 0x4a98, 0x3029, 0x7fd, 0x9305, 0x4d81, 0x482b, 0xfedc, 0xaa7c, 0xc241, 0xbfe6, 0x15a3,
        0x4412, 0xbff, 0x766d, 0x4220, 0x9067, 0xfd53, 0xe859, 0x8483, 0xff88, 0x8307, 0xc8a4, 0x19ff, 0x6a19, 0x54c5, 0x20bf, 0x7f68,
        0xc9b0, 0x2906, 0x7ff9, 0x1e95, 0x8348, 0x3ff8, 0xc0a6, 0x1c8a, 0x41de, 0xfe91, 0x8564, 0xd20b, 0xfbb6, 0x754b, 0x690, 0x4fff,
        0xb56a, 0x3934, 0x82bf, 0xfd8b, 0x52c1, 0xa417, 0xf7ec, 0xda96, 0xd20, 0xffca, 0xa4c0, 0xa629, 0x67f, 0xda56, 0x793, 0x4837,
        0xdfd2, 0x30ac, 0x9a41, 0xdf76, 0xd53, 0x6452, 0xcff, 0xb03d, 0x2b26, 0x9057, 0xffb8, 0x6553, 0x1483, 0xfec9, 0x830b, 0xc9a4,
        0x13ff, 0x6d7a, 0x160d, 0x20cf, 0xff50, 0xcab2, 0x6904, 0x7fdb, 0xaaa5, 0x5348, 0x2bfa, 0xd8b3, 0x1c8a, 0x411f, 0xf6e7, 0xa960,
        0xd20e, 0x7eb0, 0x2cc7, 0x2290, 0x5fbb, 0xb468, 0xd104, 0x833b, 0xed2a, 0xa3c9, 0xa41b, 0xfae8, 0xba06, 0x6120, 0xa7ff, 0x70d4,
        0xb069, 0x57e, 0xfb26, 0x9593, 0x4823, 0xfedc, 0x343c, 0x9a41, 0x1ffe, 0xc5a9, 0x54d2, 0x8ff, 0xf66d, 0x4722, 0x906f, 0xe521])) else (if i<3 then (fromLimbs [0x44c1, 0x30c8, 0x280f, 0x683, 0x101, 0x4c0, 0x2040, 0x2411, 0x800, 0x143a, 0xe41, 0x81b1, 0x8007, 0x8071, 0x6010, 0x1e20,
        0xe10, 0x1e10, 0x760b, 0x8078, 0x2520, 0x2208, 0x38, 0x810, 0x1104, 0xc020, 0x603c, 0x388, 0x400, 0x7104, 0x2058, 0x201e,
        0xd04, 0x880, 0xd880, 0xda05, 0x1601, 0x30a2, 0x100, 0x1c41, 0x816, 0x804, 0x71, 0x260, 0xe20, 0x4c02, 0x402, 0x203,
        0xc038, 0x814c, 0x561, 0x20d0, 0x8020, 0x388, 0x1480, 0xf101, 0x8084, 0x400, 0x701e, 0x3d0a, 0xa44, 0x8142, 0x8268, 0x2807,
        0x104, 0x1e0, 0xd044, 0xa010, 0x913d, 0x644, 0x8b00, 0x4206, 0xc209, 0x8078, 0x800b, 0x9048, 0x2201, 0x4c1, 0x301c, 0x40c,
        0x780, 0x7100, 0x7010, 0x240a, 0xa40, 0x78c0, 0x3840, 0x3808, 0x1009, 0x442, 0x1e1, 0x4c0, 0x2048, 0xa2c1, 0x8090, 0x4a40,
        0x1f01, 0xc461, 0x8203, 0xc1f0, 0x8130, 0x810, 0x78, 0x710, 0x1b04, 0x4205, 0x4c, 0x903, 0x401e, 0x507e, 0x984, 0x4c0,
        0x2834, 0x1e4, 0x120, 0x9804, 0xc0a, 0xf1, 0x70, 0x4c0b, 0x87a0, 0xc040, 0xf18, 0x1606, 0x82d0, 0xa03c, 0x4024, 0x180,
        0x706a, 0x20a, 0x980, 0x4080, 0x4034, 0x1007, 0x102, 0x42cc, 0x4e41, 0xf01e, 0x11, 0x131, 0xc040, 0x2610, 0x505, 0x203c,
        0x701c, 0x408, 0x403, 0x4102, 0x8026, 0x480, 0x7834, 0x281b, 0x522, 0x10a0, 0xa440, 0xb810, 0x811, 0x341, 0x3836, 0x5002,
        0x219, 0x40, 0x2610, 0x2904, 0x4205, 0x8e0c, 0x8482, 0x6200, 0xa044, 0xa46, 0xa00, 0x82c, 0x104, 0x7072, 0x1780, 0x8290,
        0x1ec2, 0x4c01, 0xc078, 0x4118, 0x503, 0x603c, 0x601c, 0x1480, 0x8182, 0x6068, 0x200e, 0xac4, 0x880, 0xb034, 0x1822, 0x522,
        0x1e0, 0xa440, 0x9804, 0x8291, 0x81f0, 0x4020, 0x1e0a, 0x4405, 0x148, 0xf1e, 0x8506, 0x803c, 0x60a4, 0x1a08, 0x1480, 0x8158,
        0x601e, 0x806, 0x4c0, 0x2829, 0x1e4, 0x100, 0x1c07, 0x8c13, 0xf1, 0x10, 0x1003, 0xc601, 0xc040, 0xf18, 0x1301, 0x2050,
        0x1a00, 0xf282, 0x2052, 0x200e, 0x200, 0x78c1, 0x702c, 0x101f, 0xa020, 0x6c07, 0x8082, 0x8080, 0x1e20, 0x440d, 0x402, 0x1a0,
        0x8110, 0x2c13, 0x1381, 0x3c04, 0x1338, 0x5281, 0xb01e, 0x2036, 0x3c4, 0x6c0, 0x7829, 0x1807, 0x100, 0xa460, 0x3c03, 0x880b,
        0xf1, 0x70, 0x4020, 0x4c0a, 0xc4e1, 0x404f, 0x104, 0x40a4, 0xa01c, 0x1108, 0xb02, 0x101, 0x300a, 0xd00, 0x7920, 0x380f,
        0x1007, 0x1e0, 0x6c6e, 0xc07, 0x8081, 0x81b0, 0x1020, 0x2e0d, 0x78, 0xc078, 0x2910, 0x2604, 0x4205, 0x803c, 0x4058, 0xd88,
        0x8080, 0x704c, 0xa48, 0x6c1, 0x4880, 0x4029, 0x1007, 0xa000, 0x8860, 0xb204, 0x8090, 0x1e0d, 0xa01, 0xc078, 0xb00c, 0x701,
        0xe3b0, 0x7618, 0x780, 0x8202, 0xc05c, 0x205c, 0x3c4, 0x6c0, 0x7880, 0x382b, 0x1026, 0x442, 0x3a0, 0x3c40, 0x5807, 0x880d,
        0x8221, 0x90, 0x601, 0xc110, 0x1828, 0x704, 0xc0a4, 0x6806, 0x380, 0xf180, 0x701e, 0x2e02, 0x3c1, 0x48c1, 0x1041, 0x1007,
        0x780, 0x8060, 0xb003, 0x8090, 0x7a40, 0xe03, 0xc409, 0x8040, 0x2e1f, 0x104, 0x40ac, 0x601c, 0x1588, 0xd80, 0xf110, 0x9012,
        0xc1, 0x1018, 0x2807, 0x1e2, 0xd0c0, 0x1416, 0x82, 0x70, 0x5620, 0x440a, 0x4401, 0xc040, 0x8110, 0x3410, 0x800, 0xe03c,
        0x606d, 0x8480, 0x801e, 0x4044, 0x581, 0xa0e0, 0x4f00, 0xe020, 0xdc11, 0x1403, 0x8261, 0x280, 0x240b, 0x8131, 0x2038, 0x801,
        0xe303, 0x60a4, 0x403c, 0x130a, 0x380, 0xf102, 0x800c, 0xb00, 0x400f, 0x2829, 0x682, 0xe0, 0x3c14, 0x8c14, 0x60, 0x5802,
        0x806, 0xc028, 0x2901, 0x402, 0xc0d0, 0x4020, 0x788, 0x980, 0x5068, 0x3c8, 0x3c1, 0x81, 0x4822, 0x1022, 0x582, 0xe0,
        0x3c40, 0xa407, 0x8814, 0x60, 0x5802, 0x80b, 0x18, 0x1b04, 0xc400, 0xe020, 0x78e, 0x380, 0xf140, 0x7010, 0x2010, 0x344,
        0x1001, 0x4881, 0x1034, 0x1686, 0x80fa, 0xc0c, 0x1380, 0x80f0, 0x443a, 0x284, 0xc078, 0xc038, 0xf10, 0x701, 0x200, 0xe03c,
        0x40fc, 0x130a, 0x8080, 0xf052, 0x3032, 0xb04, 0x200, 0x6880, 0xd808, 0x1008, 0xe0, 0xac60, 0x1817, 0x81, 0x803e, 0x3a1,
        0x4110, 0x2629, 0x8500, 0xe03c, 0xd90, 0x383, 0xd01e, 0x3c00, 0xc040, 0xf409, 0x51e, 0x1403, 0x8462, 0x8a03, 0xd4c0, 0x403c,
        0x1301, 0x64, 0x1450, 0x48a, 0x3d3, 0x264, 0x4d0, 0x5bf, 0xe0fd, 0xfbef, 0xfb4, 0x3e84, 0xf93b, 0xe18f, 0x7e3d, 0xd8f6,
        0x8bd6, 0xcf4d, 0xbd00, 0xf32b, 0xcc0f, 0x2dbc, 0x6af0, 0x7bbf, 0xeef2, 0x3b92, 0xee23, 0xb68e, 0xc73b, 0x12eb, 0x73aa, 0x6ea1]) else (fromLimbs [0x1, 0xe01c, 0x4020, 0x1300, 0xf182, 0x2036, 0x201e, 0x1c4, 0xb01, 0x4022, 0x884, 0x2500, 0x9889, 0x8080, 0x4406, 0x8c01,
        0x43a1, 0x4038, 0x3418, 0x2200, 0xe201, 0xe01c, 0x4824, 0x2c18, 0x206c, 0x1108, 0xd82, 0x2102, 0x280e, 0x201e, 0x1c4, 0x980,
        0x4080, 0x82d])))
def xml10 : Packing := (251,4,7,0,0,14,0,xmd10)
def xmh10 (i : Nat) : Nat := (fromLimbs [0x1, 0x122, 0x620, 0x1cf0, 0x6cd1, 0xe000, 0x0, 0x0, 0x0, 0x14, 0xc0, 0x8650, 0x8c04, 0x6802, 0xd093, 0xc04c,
        0x1bd, 0x1de0, 0x26c0, 0xfc44, 0x601e, 0x3, 0xd5, 0x60, 0x700, 0x0, 0x0, 0x0, 0x8064, 0x0, 0x20, 0x1fd6,
        0xa02, 0x5209, 0xa41d, 0xa02b, 0x813a, 0xcd, 0x16e4, 0x5259, 0x6000, 0x1008, 0xd348, 0xc0e0, 0x4668, 0x17d0, 0x2f01, 0x5b05,
        0x8805, 0x9068, 0xc231, 0x804, 0x22a7, 0x104, 0x2d04, 0x0, 0x5484, 0x4, 0x515, 0x924, 0x1c00, 0xc110, 0x510, 0x3802,
        0x6021, 0x1290, 0x4000, 0x500])
def xmd9 (i : Nat) : Nat := (fromLimbs [0x4, 0x4010, 0x1e3, 0x9289, 0x1391, 0x21c9, 0x4489, 0xc890, 0xc142, 0x6102, 0x600f, 0x1013, 0x40, 0x801c, 0x2003, 0x1430,
        0x880, 0x2020, 0x1e10, 0x301, 0x4204, 0xc100, 0x1a04, 0x1c0, 0x2040, 0xa090, 0x813, 0x4180, 0x78a4, 0x1420, 0x1010, 0x808,
        0x0, 0x148, 0x604c, 0xd00, 0x3c60, 0x0, 0x4c0, 0x5620, 0x160, 0x1a01, 0x10e7, 0xa946, 0x2888, 0xe127, 0xd5d8, 0x71dc,
        0x26f5, 0xa063, 0xd7e5, 0xe574, 0x58d5, 0x2535, 0x3c47, 0xd1a3, 0xf4e0, 0x33cb, 0xe2b4, 0xa828, 0xc9e2, 0x6488, 0x17c5, 0xa154,
        0x5012, 0xc2e0, 0xa400, 0x87fc, 0xca6d, 0x5316, 0x6120, 0xc6ff, 0xa66e, 0x5536, 0x520, 0xc6fd, 0xa66e, 0x553e, 0x6120, 0xeee9,
        0x524c, 0x3a66, 0x520, 0xfdab, 0xb7e9, 0x1524, 0xc120, 0xffc1, 0x3054, 0x9814, 0xc520, 0xff49, 0x524c, 0x1536, 0x520, 0xeee9,
        0xa654, 0x930e, 0x6120, 0xa5ff, 0xc765, 0x5a3e, 0x6120, 0xeedb, 0xa64c, 0x1536, 0x520, 0xc6fd, 0xa5ed, 0x981e, 0x4d20, 0xe7b5,
        0x81e9, 0x3a16, 0x4d20, 0xe7b5, 0x8154, 0x7a46, 0x4d20, 0xc5ff, 0xb7ea, 0x1956, 0x4d20, 0xcebf, 0xb4e9, 0x9936, 0x520, 0xb6bf,
        0xc660, 0x7a46, 0x4d20, 0xf7c9, 0x524c, 0x131e, 0x6120, 0xe7af, 0xa4e6, 0x1526, 0x4d20, 0xf7a9, 0x52ed, 0x130e, 0x6120, 0xff49,
        0x5354, 0x930e, 0x6120, 0xff61, 0x5260, 0xd514, 0x4120, 0xc5ff, 0xb76a, 0x1954, 0xc520, 0xd3f7, 0xb8e4, 0x5536, 0x520, 0xeebb,
        0xa6ed, 0x1306, 0x520, 0xd7b7, 0xb460, 0x593e, 0x4520, 0xd7b5, 0x81ed, 0x1a3e, 0x4520, 0xff49, 0x5260, 0xd534, 0x4120, 0xe7e5,
        0x5260, 0x4a94, 0xc520, 0xa6ff, 0xc660, 0x7a56, 0x4d20, 0xeed9, 0xa64c, 0x153e, 0x6120, 0xff81, 0x21ed, 0x1304, 0xc520, 0xff09,
        0x52ed, 0x1305, 0x4d20, 0xc5bf, 0xb7e9, 0x1a56, 0x4d20, 0xc5bf, 0xb7ed, 0x1a95, 0x4d20, 0xa6bf, 0xc464, 0xda6e, 0x6120, 0xa6bf,
        0xc660, 0x7a46, 0x4d20, 0xf3d1, 0x314c, 0x1816, 0x6120, 0xc5bf, 0xb7e9, 0x1956, 0x4d20, 0xf749, 0x524c, 0x153e, 0x6120])
def xml9 : Packing := (39,5,7,0,0,10,0,xmd9)
def xmh9 (i : Nat) : Nat := 0x40400002a00
def xmd8 (i : Nat) : Nat := (fromLimbs [0x60, 0x4c20, 0xb941, 0xee49, 0x52e9, 0x9305, 0x4d81, 0x483f, 0xa17a, 0xea97, 0x6898, 0x2a69, 0x7b9, 0x2549, 0xa64c, 0x153e,
        0x6120])
def xml8 : Packing := (3,6,7,0,0,5,0,xmd8)
def xmsamples : Array (Bits × Bits) := #[((BitVec.ofNat 768 (fromLimbs [0x8e2f, 0x68d0, 0xb576, 0xb353, 0x20a3, 0xea59, 0x96af, 0x425b, 0xac81, 0xc829, 0x8cce, 0x45d4, 0x42bd, 0xe3f6, 0x4c50, 0xd91d,
        0x5626, 0x5692, 0x5c8, 0xaeca, 0x7f60, 0x84b, 0xb194, 0x900e, 0x8d14, 0x6680, 0x308a, 0x84a0, 0x4601, 0xcf42, 0x409, 0x3bf9,
        0x440, 0x4c00, 0x1109, 0x19a8, 0x863, 0xc60c, 0x408, 0x4202, 0x5, 0x643, 0x3375, 0x9a3, 0x3094, 0x343, 0x3e21, 0xf673])),(BitVec.ofNat 768 (fromLimbs [0x608, 0x6a02, 0x1080, 0x4031, 0x1201, 0x836, 0x8404, 0x10c4, 0x20c, 0x4088, 0x2302, 0x4000, 0x4, 0xa408, 0x1602, 0x819,
        0x84, 0x1060, 0xa82, 0x8a, 0x2a20, 0x8a49, 0xb0c0, 0x20e, 0x100, 0x6880, 0x389, 0x89a, 0x2331, 0x41b0, 0x1065, 0x510,
        0x4c0, 0xb184, 0x129, 0x1868, 0x845, 0x4608, 0x3440, 0x22a, 0x1, 0x424b, 0x2204, 0x123, 0x2894, 0x86, 0x2421, 0x2652]))),((BitVec.ofNat 768 (fromLimbs [0xf14f, 0x74ea, 0x63bc, 0x3725, 0x7a4a, 0xfbf6, 0x34d8, 0xf9b4, 0x76ab, 0x9808, 0xff86, 0x8bc7, 0xe340, 0x808e, 0xc7b9, 0x22aa,
        0x5983, 0xd1d, 0x3eef, 0xa735, 0x4482, 0x9591, 0x534c, 0xe3, 0x4dd1, 0x202, 0x14d1, 0xc20, 0xd000, 0xb, 0x64ec, 0x2bfe,
        0x8028, 0x4000, 0x40, 0x2004, 0x30a0, 0x183c, 0xe0e6, 0x3c32, 0x30c6, 0x2594, 0x3a82, 0x2604, 0x80ff, 0x4400, 0xc8c6, 0x487f])),(BitVec.ofNat 768 (fromLimbs [0x13, 0x420, 0x290f, 0x200, 0xc004, 0x36c0, 0x2068, 0x808, 0x5050, 0x2006, 0x4018, 0x8004, 0xa540, 0x116, 0x2830, 0x1422,
        0x1020, 0x2401, 0x2120, 0x3325, 0x4483, 0x1010, 0x308, 0xe0, 0x4c71, 0x20d, 0xd040, 0x3520, 0x508e, 0x384a, 0x8c12, 0x608f,
        0x8034, 0x4e00, 0x40, 0x2104, 0x31aa, 0x1827, 0xc01c, 0x5411, 0x20c6, 0x2594, 0x18c2, 0x4400, 0x8042, 0xc620, 0x88c4, 0x4829]))),((BitVec.ofNat 768 (fromLimbs [0x298b, 0xfacb, 0xced4, 0x78c, 0x1cfe, 0x7b1b, 0x2f42, 0x553f, 0xcb36, 0x45e3, 0x7dfb, 0x79e, 0xabff, 0xcd41, 0x27e, 0x8771,
        0xb9e5, 0x2a0a, 0xc9bb, 0x3a48, 0x9b26, 0x38e0, 0x4840, 0x5b37, 0x9e02, 0x1c30, 0xd06, 0x81, 0xbc02, 0x21bc, 0xd8d0, 0x0,
        0x2220, 0x12, 0x401, 0xc049, 0xc11c, 0x6073, 0xa8c3, 0xb6ac, 0x920, 0x79e7, 0xc000, 0x2046, 0x318, 0x2518, 0xf107, 0x8f9c])),(BitVec.ofNat 768 (fromLimbs [0xc028, 0x81d1, 0x4430, 0x10, 0x100, 0x4000, 0x4090, 0x1245, 0x2da0, 0x8220, 0xb682, 0x10d0, 0x1000, 0x1080, 0x444d, 0xc,
        0x8840, 0x42, 0xd400, 0x448, 0x1b44, 0x28a0, 0x4040, 0x5103, 0x1000, 0x1030, 0xd04, 0x8c8, 0x2d70, 0xc4a0, 0x50c4, 0x8c50,
        0x5c81, 0x910f, 0x1401, 0xc009, 0xc054, 0x6050, 0x822, 0x83e6, 0x1100, 0x1002, 0x8101, 0xa047, 0x218, 0x110, 0x7103, 0x8514]))),((BitVec.ofNat 768 (fromLimbs [0x53b4, 0xadaf, 0xbc76, 0xb3f, 0x6904, 0x64cc, 0xf42e, 0xea9c, 0x9810, 0xbef, 0x5184, 0xb2af, 0xf55b, 0xd47, 0xf9ab, 0x2ef6,
        0xf44f, 0x9d36, 0x2ae5, 0x7c07, 0xac14, 0xc35f, 0x1220, 0x8ae0, 0xba48, 0xc901, 0x834, 0x2471, 0x22dc, 0x115, 0xfb0b, 0x0,
        0x20b2, 0x526c, 0x9ac, 0x6, 0x194, 0x7fc2, 0x1001, 0x4148, 0x2e03, 0x80e0, 0xa, 0x78, 0x47e0, 0xd89f, 0x1f8, 0xfe0])),(BitVec.ofNat 768 (fromLimbs [0x2080, 0x5a02, 0x93c7, 0x4009, 0xc890, 0xac23, 0x22, 0x6000, 0x8210, 0x515c, 0x151, 0x2004, 0xa116, 0xa064, 0xb300, 0x4040,
        0x221c, 0x4a8, 0x280, 0x3, 0xa410, 0xc157, 0x3000, 0x8aa0, 0x8840, 0xc804, 0xc209, 0x30, 0x4284, 0xb45, 0xa00b, 0x1a2,
        0xa05c, 0x4440, 0xa18c, 0x26, 0x8, 0x1503, 0x1050, 0x6408, 0x2e25, 0xc1e8, 0x4a, 0x1830, 0x4de0, 0x50ab, 0xb0, 0xae0]))),((BitVec.ofNat 768 (fromLimbs [0x9c80, 0xe5ce, 0x3a51, 0x8d2f, 0xfd12, 0x1f6b, 0xd182, 0xee17, 0x8fa2, 0x9b8b, 0xacf8, 0xd5bf, 0x8d10, 0x4c62, 0x8327, 0x9b72,
        0x559e, 0x9a6e, 0x7773, 0x4975, 0x12d7, 0x30a0, 0x8f3a, 0x7511, 0x69d, 0x13b2, 0xc66, 0xf644, 0x16dd, 0xce42, 0x4200, 0x1000,
        0x4002, 0x80c, 0xcd0, 0x1b0, 0xe3, 0x8000, 0xc, 0x4, 0xc003, 0xbe00, 0xc10, 0x7e, 0xf000, 0xd9c4, 0x1ff, 0xf000])),(BitVec.ofNat 768 (fromLimbs [0x8955, 0x56c, 0xc10, 0x37c2, 0x162, 0x4100, 0x50d0, 0x8e18, 0x3940, 0xaa02, 0xc8ac, 0x9ca1, 0x48a8, 0x1012, 0x8fd, 0x2526,
        0x9c63, 0x8205, 0x9020, 0xf174, 0x10c7, 0x30a0, 0xf3a, 0x7511, 0x69d, 0x137b, 0xc66, 0xf744, 0x1448, 0xb402, 0x4b90, 0xfa4d,
        0x5a03, 0xa09, 0x4c52, 0x191, 0x1b2, 0x8040, 0xc0af, 0x9945, 0xd002, 0x3c00, 0xd31, 0xc04c, 0x9000, 0x8b40, 0x14e, 0xd000]))),((BitVec.ofNat 768 (fromLimbs [0x9af2, 0x6797, 0x95bd, 0x1c62, 0x321b, 0x5fce, 0xf27a, 0x7403, 0xfaec, 0x3274, 0x5522, 0xa86b, 0x4559, 0x2eb5, 0xce36, 0x156,
        0x1f72, 0xf4ad, 0x6177, 0xfb76, 0x819b, 0x6916, 0x10e, 0x6029, 0x7825, 0xf11c, 0x6c2c, 0x5164, 0x920, 0x1008, 0x0, 0x401,
        0x5465, 0xa481, 0xf302, 0x1e, 0xfe00, 0x0, 0xf00, 0x4005, 0xe7d8, 0x8, 0xdf7, 0xaf81, 0x800, 0x5b7b, 0xfe00, 0x0])),(BitVec.ofNat 768 (fromLimbs [0x20a4, 0x81, 0x4410, 0x100, 0xc900, 0x6000, 0x2ba1, 0x4800, 0x8451, 0x1020, 0x8400, 0x1ad0, 0x5e00, 0x1843, 0x6040, 0x64,
        0x100, 0x0, 0x419, 0x774, 0x8192, 0x6106, 0x104, 0x6821, 0x3800, 0x11c, 0xec04, 0x5060, 0xc4c, 0x1640, 0xc10, 0x406e,
        0x839, 0x641, 0xb280, 0x16, 0xa400, 0x43, 0xa0a, 0xf504, 0xbdb4, 0x0, 0x13, 0x3e80, 0x0, 0x5b59, 0xda00, 0x0]))),((BitVec.ofNat 768 (fromLimbs [0xaadd, 0x5e22, 0x55f6, 0xede0, 0xdfe0, 0xbab, 0x271f, 0xe268, 0xa489, 0xe434, 0x7f61, 0x49bc, 0xaee5, 0x573a, 0x56a7, 0x447f,
        0x9874, 0xf1e6, 0xd77e, 0xb6f2, 0xa910, 0xcd67, 0xa487, 0xf795, 0xb08a, 0x8972, 0x8ad1, 0x4aca, 0x8e00, 0x185, 0x24, 0xd006,
        0xa908, 0x110, 0x135d, 0xfe00, 0x0, 0x0, 0x4f34, 0xa90, 0x1000, 0x10, 0x1a, 0x77fe, 0xf3ff, 0x0, 0x0, 0x0])),(BitVec.ofNat 768 (fromLimbs [0xcbc8, 0x81, 0x9610, 0xc414, 0x109a, 0x412b, 0xda92, 0xf561, 0x840c, 0x44c0, 0x500, 0x690, 0x1293, 0x3a48, 0x4444, 0x8005,
        0x4583, 0x120, 0x4641, 0x852, 0xa910, 0xcd67, 0xa087, 0xf615, 0xb08a, 0x8972, 0xb91, 0x4ac0, 0x8f70, 0x785, 0x1100, 0x1370,
        0x2ac9, 0x151, 0xfb8e, 0x94a0, 0x40, 0x40, 0x1fc3, 0xaba8, 0x1820, 0x4008, 0x39, 0x3bff, 0x7bbd, 0x80, 0x0, 0x0]))),((BitVec.ofNat 768 (fromLimbs [0xc73f, 0x8ad1, 0x282c, 0x7f26, 0x36bb, 0xbb9f, 0xfbe0, 0x16f0, 0xdd0f, 0x9915, 0x4ab1, 0x76d4, 0xfe46, 0x4aa3, 0xb457, 0xa07f,
        0x769b, 0x337d, 0x82a0, 0xe889, 0x64a9, 0x163d, 0xbe93, 0xe6dc, 0x41cb, 0xe68c, 0x11c2, 0x8100, 0x4222, 0x212d, 0x2211, 0x1000,
        0x2302, 0xa823, 0x6500, 0x41, 0x8, 0x1, 0xf04, 0x8294, 0xe7fb, 0xfef7, 0xfc88, 0x8000, 0x4c00, 0x2420, 0x0, 0x0])),(BitVec.ofNat 768 (fromLimbs [0x1240, 0x7424, 0x200d, 0xde07, 0x14a4, 0x959c, 0xa, 0x853a, 0xa, 0x50c, 0x174, 0x4020, 0xa1c8, 0xc510, 0x82b0, 0x9a11,
        0x723d, 0x7108, 0x942, 0x81, 0x6429, 0x1619, 0xbe93, 0x86dc, 0x41cb, 0xe6c1, 0x12c3, 0x8102, 0x4283, 0x291d, 0xa323, 0x3381,
        0xa346, 0x28a0, 0x4922, 0x1e0, 0x108, 0x0, 0xf5d5, 0x819, 0x424b, 0xeffd, 0x7eec, 0x4000, 0x4c00, 0xa4a4, 0x0, 0x0]))),((BitVec.ofNat 768 (fromLimbs [0xc3cd, 0xb2e3, 0xbf7b, 0xd5bf, 0x957a, 0x95f1, 0x3ac5, 0x49ff, 0x925b, 0x67f3, 0xc8d7, 0x8449, 0xb0b3, 0xd64f, 0x7a74, 0xf59d,
        0x2fbb, 0x46da, 0xec7a, 0x3d88, 0x726c, 0x7288, 0x2ea9, 0x854a, 0x2574, 0x12f1, 0xf260, 0xd69f, 0x1902, 0x1084, 0x6103, 0xc400,
        0x5997, 0x5bf2, 0x867f, 0xfe1e, 0xfea1, 0xffbc, 0x1010, 0x141, 0x0, 0x18, 0xc88, 0x5000, 0x400, 0x2400, 0x0, 0x0])),(BitVec.ofNat 768 (fromLimbs [0x1411, 0x520, 0x2000, 0x20e2, 0x425, 0x1040, 0x40, 0x202, 0x7080, 0x2001, 0x5204, 0x121, 0x28, 0x4590, 0x8b9, 0x3a12,
        0x800, 0xb806, 0xa824, 0x5088, 0x526c, 0x1288, 0x4e28, 0x14a, 0x4134, 0x1281, 0x60, 0x850f, 0x1003, 0xe032, 0x40e4, 0xac01,
        0x5502, 0xb8ae, 0x471, 0x6b49, 0x5b95, 0xeabc, 0xe020, 0x43, 0x0, 0x10, 0xf84, 0xc000, 0x0, 0xa404, 0x0, 0x0])))]
def xmcolumns : List ColumnInfo := [(529,0,494,0,11),(644,0,379,0,11),(576,0,447,0,13),(832,0,191,0,11),(514,0,509,0,12),(536,0,487,0,11),(672,0,351,0,11),(519,0,504,0,7),(714,4,305,0,4),(258,64,701,0,8),(645,0,378,0,7),(578,0,445,0,11),(524,0,499,0,9),(693,0,330,0,4),(533,0,490,0,7),(690,1,332,0,4),(517,2,440,64,6),(538,0,485,0,7),(668,0,355,0,7),(521,16,486,0,8),(595,0,428,0,7),(582,0,441,0,8),(780,0,243,0,7),(792,0,231,0,8),(669,0,354,0,4),(40,0,983,0,8),(282,64,677,0,4),(788,8,227,0,5),(840,0,183,0,8),(769,0,254,0,8),(547,0,476,0,7),(561,0,462,0,8),(666,4,353,0,4),(808,0,215,0,7),(744,256,23,0,4),(992,0,31,0,7),(848,8,163,4,5),(709,2,312,0,4),(597,2,424,0,4),(26,0,997,0,7),(548,128,347,0,8),(543,0,480,0,4),(526,0,497,0,7),(626,1,396,0,4),(913,32,78,0,4),(836,8,163,16,5),(679,0,344,0,4),(680,0,343,0,7),(803,64,156,0,4),(900,8,99,16,5),(74,0,949,0,7),(793,0,230,0,5),(852,8,163,0,4),(632,256,135,0,4),(600,0,423,0,8),(527,16,480,0,4),(130,0,893,0,9),(848,0,175,0,8),(653,16,354,0,4),(812,128,83,0,4),(825,0,198,0,4),(782,64,177,0,4),(832,32,30,129,6),(322,0,701,0,8),(960,32,30,1,5),(916,8,99,0,4),(296,16,198,1,5),(809,16,198,0,4),(930,64,29,0,4),(448,32,30,1,5),(551,128,344,0,4)]
def xmautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xmlevels : Nat → Packing
  | 13 => xml13
  | 12 => xml12
  | 11 => xml11
  | 10 => xml10
  | 9 => xml9
  | 8 => xml8
  | _ => emptyPacking
def xmindex : Nat → Nat → Option (Nat × Nat)
  | 13 => lookupWord 26 37 3 13 5 4 xmh13
  | 12 => lookupWord 239 299 6 16 8 4 xmh12
  | 11 => lookupWord 370 501 6 16 8 4 xmh11
  | 10 => lookupWord 27 69 4 14 6 4 xmh10
  | 9 => lookupWord 3 5 1 10 2 4 xmh9
  | _ => fun _ => none
def xm : Forest := ⟨1023,13,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem geomxm : graphValid xm (boundsBefore knownx471) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_0 : block xm 13 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_13 : block xm 13 0 1=true := sxm_13_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_0 : block xm 12 0 8=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_8 : block xm 12 8 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_12 : block xm 12 0 18=true := (@block_merge xm 12 0 8 10 sxm_12_0 sxm_12_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_0 : block xm 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_2 : block xm 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_38 : block xm 11 38 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_47 : block xm 11 47 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_83 : block xm 11 83 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_119 : block xm 11 119 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_131 : block xm 11 131 17=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_11 : block xm 11 0 148=true := (@block_merge xm 11 0 131 17 (@block_merge xm 11 0 119 12 (@block_merge xm 11 0 83 36 (@block_merge xm 11 0 47 36 (@block_merge xm 11 0 38 9 (@block_merge xm 11 0 2 36 sxm_11_0 sxm_11_2) sxm_11_38) sxm_11_47) sxm_11_83) sxm_11_119) sxm_11_131)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_0 : block xm 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_2 : block xm 10 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_38 : block xm 10 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_74 : block xm 10 74 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_110 : block xm 10 110 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_146 : block xm 10 146 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_167 : block xm 10 167 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_203 : block xm 10 203 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_239 : block xm 10 239 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_10 : block xm 10 0 251=true := (@block_merge xm 10 0 239 12 (@block_merge xm 10 0 203 36 (@block_merge xm 10 0 167 36 (@block_merge xm 10 0 146 21 (@block_merge xm 10 0 110 36 (@block_merge xm 10 0 74 36 (@block_merge xm 10 0 38 36 (@block_merge xm 10 0 2 36 sxm_10_0 sxm_10_2) sxm_10_38) sxm_10_74) sxm_10_110) sxm_10_146) sxm_10_167) sxm_10_203) sxm_10_239)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_0 : block xm 9 0 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_9 : block xm 9 9 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_9 : block xm 9 0 39=true := (@block_merge xm 9 0 9 30 sxm_9_0 sxm_9_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_0 : block xm 8 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_8 : block xm 8 0 3=true := sxm_8_0
theorem tablesxm : checkedTables xm 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xm 0 0 0 = true)
  · exact (rfl : block xm 1 0 0 = true)
  · exact (rfl : block xm 2 0 0 = true)
  · exact (rfl : block xm 3 0 0 = true)
  · exact (rfl : block xm 4 0 0 = true)
  · exact (rfl : block xm 5 0 0 = true)
  · exact (rfl : block xm 6 0 0 = true)
  · exact (rfl : block xm 7 0 0 = true)
  · exact allxm_8
  · exact allxm_9
  · exact allxm_10
  · exact allxm_11
  · exact allxm_12
  · exact allxm_13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseUB : Impossible true (graphGoal 1023) 13 (rootB 1023).toFinset :=
  index_root (g:=xm) (i:=0) rfl rfl (before_sound knownx471 validx471) geomxm tablesxm (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseUA : Impossible true (graphGoal 511) 13 (vars 511).toFinset :=
  cut_root (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (128,0,383,0,13) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → (∃ g ∈ C.gates, g.op = GateOp.not) → 16 ≤ C.size := by
  intro C legal first h someNot
  by_contra! small
  obtain ⟨k,S,hk,run,sub⟩ := initial_live C legal first h someNot (by omega)
  have eg : graph=graphGoal 511 := by decide +kernel
  have er : inputs++[seed]=rootB 511 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : splitOK 511 [(0,20),(1,1),(2,9),(3,4),(4,1),(5,1),(6,2),(7,4),(8,8)] = true := by decide +kernel
  have g2 : graphGoal 1023=graphGoal 511 := by decide +kernel
  have v2 : rootB 1023=rootB 511 := by decide +kernel
  have hb := caseUB
  rw [g2,v2] at hb
  rcases strong_split ok run sub with e | e
  · exact caseUA k hk (e ▸ run)
  · exact hb k hk (e ▸ run)
theorem edge_any : ∀ x : Fin 9 → Bool, ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun a : ℕ => x (Fin.ofNat 9 (a / 10)) && x (Fin.ofNat 9 (a % 10))) = edge x := by decide +kernel
open PEqualNP.MetaComplexity

def rowCode (x : Fin 9 → Bool) : Nat := (List.ofFn x).foldr (fun b n => 2*n+b.toNat) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem rowCode_spec : ∀ x : Fin 9 → Bool, rowCode x < 512 ∧
    (∀ i : Fin 9, (rowCode x).testBit i.val = x i) ∧
    ([3,6,12,17,24,33,66,132,160,264,288,320] : List Nat).any
      (fun e => rowCode x &&& e == e) = edge x := by decide +kernel

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem oldValue (gs : List Gate) (w : List Bool) (k : Nat) (hk : k<w.length) :
    (gs.foldl appendGate w).getD k false=w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [appendGate]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem initialOr (x : Fin 9 → Bool) :
    appendGate (List.ofFn x) ⟨.or,[0,2]⟩=List.ofFn x ++ [x 0 || x 2] := by
  simp [appendGate,GateOp.eval,List.getD_eq_getElem?_getD]

theorem extendLower (C : Circuit) (legal : FanInTwo C) (someNot : ∃ g∈C.gates,g.op=.not)
    (allRows : ∀ r<512,C.eval ((List.ofFn (fun i : Fin 9 => r.testBit i.val)) ++ [r.testBit 0 || r.testBit 2]) =
      ([3,6,12,17,24,33,66,132,160,264,288,320] : List Nat).any (fun e => r &&& e == e)) : 15≤C.size := by
  let D : Circuit := ⟨⟨.or,[0,2]⟩::C.gates,C.output⟩
  have ok : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    · exact legal _ hg
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false=(x 0 || x 2) := by
    change (C.gates.foldl appendGate (appendGate (List.ofFn x) ⟨.or,[0,2]⟩)).getD 9 false=_
    rw [initialOr,oldValue _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have fn : circuitFun 9 D=edge := by
    funext x
    obtain ⟨small,bits,output⟩ := rowCode_spec x
    have row := allRows _ small
    have raw : (fun i : Fin 9 => (rowCode x).testBit i.val)=x := funext bits
    have b₀ : (rowCode x).testBit 0=x 0 := bits 0
    have b₂ : (rowCode x).testBit 2=x 2 := bits 2
    rw [raw,b₀,b₂,output] at row
    change (C.gates.foldl appendGate (appendGate (List.ofFn x) ⟨.or,[0,2]⟩)).getD C.output false=_
    rw [initialOr]
    exact row
  obtain ⟨g,mem,op⟩ := someNot
  have low := bound D ok first fn ⟨g,List.mem_cons_of_mem _ mem,op⟩
  change 16≤C.gates.length+1 at low
  change 15≤C.gates.length
  omega
end PEqualNP.Outside.L_meta_5100

theorem PEqualNP.Outside.L_meta_5100 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (14 : ℕ) →       x1.output = (23 : ℕ) →         (∀ x5 ∈ x1.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) →           (∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), x6 < x7 ∧ (3 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (6 : ℕ) ∧ ↑x7 < (13 : ℕ) ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x8 : Fin x1.gates.length), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → x8 = x6 ∨ x8 = x7) →             have x7 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;             have x8 : ℕ → Prop := fun (x8 : ℕ) => x1.eval ((List.ofFn fun (x9 : Fin (9 : ℕ)) => x8.testBit ↑x9) ++ [x8.testBit (0 : ℕ) || x8.testBit (2 : ℕ)]) = [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x9 : ℕ) => x8 &&& x9 == x9;             (∀ x9 < (23 : ℕ), x9 ∈ x7) →               have x10 : Finset ℕ := {x10 ∈ Finset.range (23 : ℕ) | (2 : ℕ) ≤ List.count x10 x7};               x10.card ≤ (3 : ℕ) → (∀ x12 ∈ x1.gates, ∀ (x14 x15 : Fin (9 : ℕ)), x14 ≠ x15 → x12.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x12.inputs = [↑x14, ↑x15] → ↑x14 ∈ x10 ∨ ↑x15 ∈ x10) → (∀ x13 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], List.count x13 x7 ≤ (1 : ℕ)) → ∃ x14 < (512 : ℕ), ¬x8 x14 := by
  intro C legal size _ _ negs
  dsimp only
  intro _ _ _ _
  by_contra! allRows
  obtain ⟨i,j,_,_,_,_,ni,_,_⟩ := negs
  have low := PEqualNP.Outside.L_meta_5100.extendLower C legal
    ⟨_,List.get_mem _ i,ni⟩ allRows
  omega
