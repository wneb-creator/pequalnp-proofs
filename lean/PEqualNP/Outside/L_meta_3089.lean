import Mathlib
import PEqualNP.Defs

-- The checker and the subgraph bound library are adapted from PEqualNP/Outside/L_meta_1674.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_3089
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
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 3) := by decide +kernel
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
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
def known47 := extendKnown known31 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64]),(151,[115,99,83,67]),(173,[113,97,82,32,65,48]),(188,[114,83,48,33,97,64]),(345,[130,50,115,48,49,98,65,80]),(369,[130,50,81,115,98,65]),(422,[131,33,114,99,32,81,64]),(440,[129,50,83,48,114,97,64]),(454,[83,50,133,114,99,32,64]),(460,[82,133,114,49,32,97,64]),(482,[81,80,128,113,98,49,64]),(484,[32,50,33,128,115,82,97,64]),(185,[115,50,83,98,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16]),(425,[80,129,50,116])]
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
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64]),(413,[134,117,33,32,65,48])]
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
def known127 := extendKnown known189 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112]),(223,[101,117,50,33,16,64]),(239,[32,83,116]),(247,[84,115]),(443,[81,130,118]),(463,[16,32,48,128,100,80,116]),(491,[128,81,32,49,100,116]),(493,[80,129,50,116]),(499,[98,99,81,131,114,65]),(505,[81,80,48,50,130,113,64])]
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
def known251 := extendKnown known191 8 [(251,[]),(254,[32,83,116]),(471,[16,82,131,100]),(477,[48,33,133,118]),(501,[80,16,33,50,116,131,100]),(506,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[32,49,128,81,116,100])]
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
def xud13 (i : Nat) : Nat := 0x1411329263e2d07211a04affd30
def xul13 : Packing := (1,1,7,0,0,0,0,xud13)
def xuh13 (i : Nat) : Nat := 0x601513000717f18178000a06672412003000766b73407d11d02b68e04c61a63062000000000000d152718083002051800d9980b
def xud12 (i : Nat) : Nat := 0x27286832983c9a27218d038096022168326898fe0f21164a63604c268086da0ca47d1316c1a4f218d81031a020265326898fa830716c863509026a0f4189ca64f218d01234194c9a27218d011ca1168fe832993c1a27218d012c3f89ca64f0716c8635400250074189ca64e3f90c6c5938e5451435cb0a3a5a8ac007ff64530ffec0a61ffd514c3ffa42987efe5130bffc8a617fd914c3ff240985efe5130
def xul12 : Packing := (9,2,7,0,0,10,0,xud12)
def xuh12 (i : Nat) : Nat := 0x101b707c816dc2e0000406a63740003849670600000000000e0460000000400856aa0001ea7504e502420680005040d440c075981a95200012eacd9c8000b766ec818195805e0bc000000040037052c128000033200002ed681b18000000228180880009088c24e04eb845803800000282054476c602c0077802507420a081660510000000145c400a662000000000000609881204c6f82d6b64c15498b7042705d855740c5d5500012d4e4537013516920f41ea9333589c000342680007175c0ec0007047a1a2614f003f3d3116584e88a70000100ce0e480cdb90016c6054000000000000000000000000008e9a0150000606e00000006838801f020f86cb83f0001204000058212018610c0004b048028000100f8000801b22d5985f04636b800000001b5d1096414bc15c05d923e8058045d84f367f46c901a385ab11a209d064902f608356824d01833504dc011c48481700000002dc580000000000000038200000e0f00004856a0120003000d11d20b200031e700000000ac700000000000002000308020000000002000a02001700000a010300040100080000000b000d110d00000004000406000000050d1c01
def xud11 (i : Nat) : Nat := (if i<1 then 0x183e4e89e438d01c0258042804e12f21c6f060da001e8394a271f64f90e378308c075b298b03dc1d41c6f210107a03a827e5289e802dc7f16e0f90e3593588f0ff06ca62dc871b5040406281c0480165393e8289c7f16e3783e4021684bc9d13d00438fe2dc1f21c6b28b805a0e53936271fe438dc59845513ca727c871a1705401204fe53a0a2790e342d009020729c871b50018011f94e4c2ce0f90e340207900880d50327c1f21c68180100ea2821f09f94e0f16e3593e42022000b6095c9f40ca721c68180123a0e53931380ce438d01c024f29c987350313c871a0f004947fa0e502ca2790e3693e0f16500ac4f075004fc871a0f00403a801e8316e531fe438de0c070d95ca727c871a010366e5393072a007989e0c39e438d06c026141ca7261ce2dc183ac4f21c6c040f33a062794e4f1f00716e37901344c583813729c9d138fe2dc1f21c6b40b00794e4c1ea25a009790e378309c1b6741ca72744e3e00e2dc871a980c1fef7e41f3b7be9e9b7a31e7d7879dbf7559ced7239c436fb9b8f6c71ad169f1a13672195f64298c961d180b5f017755c816cb59895ef56e156354b14f5525944b4fb13ab4cb92c549711f3462917b45b1103435909f4128feb3ef8f5f3bd8eb53840e0137c8db13688d393250c3f30c0bc72d78aeb2a58a2326e894723788571f9077b1c986d11a18631172054b13d849710e03cf0d982fd0af023f070814f037005f0003ffd8548530fff655214c3ffda548530fff6a5214c3ffd8254530fff689514c3ffd8164530fff485914c3ffd5260530fff649814c3ffda960530dff609914c2ffda960530ffe545204c3ffba064530bffea5514c3ff98148130dffaa5514c37fda954530bff6a5514c3fdda354530bffe89514c37fd9264530bffe89914c3ffba054530ffe645204c2fffa948530dffaa5214c37fd9564530dff6a5214c2ffda948530bffe95214c2fffa564530dff661914c2fffa864530ffe685204c3fbd81e5130fef547944c3fbd21e5130ffee85204c3ff98548130dff617914c3ff99548130dff60b914c37fd52e4530dff607914c37fd51e4530ffe695204c37ffa864530ffee95204c37fda864530ffe661204c37ffa564530ffe6a1204c37fda564530ffeea1204c37fd8564530dff485914c37fd5164530dffe89914c37fd8164530dff689914c37fd5264530dffaa5814c37fd21e4530def607944c37bd51e5130defe91914c37fba0645309ff695914c2ffba8481309ffe95914c2ff9a8481309ff6a1914c27ffa864530def487944c27fda2e45309ff697914c3fbb9448130ff6e8d204c3fd95348130ffa549204c27fda8e4530def647944c37fb9148130bfee81514c37f991481309ffea5514c2ffba064530ff64c5204c3fe92148130def687944c27ffa2645309ff689914c27bfa464530 else 0x2050119181a904240870e44f54b830710230aa1186f81b1a811004203a91003c0781d0738306d02432981818814040399022031fc0d8d2100c08c0849121224281404406074831a8018521244007839a40c24e3830950248942a0a61e04a15f07c820461299464e1311f1fa2790e378301d42107d44d29c6f21c184e0e2594e438dc5b83a800c38a1c1f21c684a0e00413a03ec7e89e438d09693e0c1c4b260f329c1873c6e2dc8540c4c04bc5b83e438dc7c2e0b4e0162dc1f21c6e3e1705a80fb1fa2693e438d08c25e0c1c563e8b7061b86c040187c5894c51a000b90e3423e0c0c570613d13c871ad000412a383e3405680070f0dd023fca721c6e2dc1818801450626a0e0f90e342700807507dc871a13f064204a7e5393e0f90e341b098fc1d13c871a12b2601038800b94e4f90e0f8d06c26403c1f03750513c871bc184e12a82825002c5316e4193e371fe0c845f0628326138785e0c27a2790e35940081c470602b280387851438de0c27078ae1407d0726c4f1aca7210127a0e5203e438d8080c3b0901f29c9b41c6f20c4c049e438d87f830180c343e0331216329c1f218b71b503270130298804868194a2790e35938094088a4c9f0750721c68720100ea09a1311d9365289e438d68202504d0a000ca327c8512d071b012889091210005265390c5993e0f8d074395329c180e1e138d87f8309c1e280412329c6f2013f060e205165383e438d09ea0008394b27c184e1e1047c5994e438d09f83074394846010498f84ac9f21c6f060e2b9365390e341e100d014a01e052143411009144e2cca63fc871ac9f0702242448405e0f8d6801c0f0c44841e06c0209390e35a00978309d40dca10104cca4280063f8b05c1e327c8707c6b4100ff1fe0f8dc5b900b82141121807a0e4d8965390c7f8dc59c25403d0313ca63ec9e2dc871a26a827943a0e5)
def xul11 : Packing := (95,3,7,0,0,14,0,xud11)
def xuh11 (i : Nat) : Nat := (if i<1 then 0xc77561040000000000e900000000000000000000000000009018509300000000000000000000600c801b000021580000f8d810ab309e0000000000000000000070e7d72330e0607b0000a0fb0000000061e00000308ae0dc07bba6c350de42d5000000000000160cf049602a01d70000000090170000e0030000a0e40000000000000000000000000000000000000000e7d400000000000000000000000000007289b7d5d04557ca00000000b2fd00000000000070bbc00b000000000000b0a810f90000009d000001bf16243607caac0000000000000000e0ed000000000000209c204de039000056f2000000000000000000000000104350aed0cd00000000c06d0000000000000000e0070000727e004ce0fd00000000c03016ec000000000000f0a2000000007082000000000000f0f400000000f6e10056d8a8f05a0000076c2bb500000000e098000001561016402e000060006015f055403b00000000000000000000000000000000a08c0000000000000000b0b7000000000000e083000000000000b00581f90000b066000055d5000020e2f45891f2000000000000f0bce67987ac00cc00000000000054b500000000000020ea907200000000000000000000c0460000000000000000000000000000000041dc729d528a0000000010d400f80000000040280000000000000000306e00000000000050af000087c9b063ebd200760000906f167b00000000000000000000804a000010a3f096e0d746f4e0eff0640000b077c0c061ef563f00000000000070d10000c074a02680020000203e00000000da86a0248052d02d0000000026ed000050bd0000f09fe0f20000e5ce98280000000000000000000000000000e0940000c62bc02b000037a60000700467f300000000000000000000d0230000d0b0000000000000772d00000000000050400000874d00000000000000000000000000000000000000000000000090ee000000000000b03240f5519a69b7b2dc901c401a000041f4000080caa0b9d037e06c66e6d02c000000000000000000000000216a000000008067c2a100db000000000000000000007061000041ad000000000000000000000000a05090891062b0cea08fb0cbc071000000002125000000000000000000000000878600000000b72b00000000905100000000e10a00000000b0a6000000000000b01320a1000040290000e0c30000000000000000d3d50100200000000060000000400008050040000800008000000100801004000080300c000000500c04000000000000003000040040300c0600002000000040000005004010100001402014000000301400004000000001401000010040000c00000000000100000004000000000401000030000000401010010000000c00020000040000400000000080100000 else 0x205e000020c5d0a060ad608d70f1808600000000c0e8000000000000e03f90d9000000000000000030f3e0887084d0d2009aa025e4790000604f000020e6000000000000000000007bb30000000000000000000090a4000000000000e0ec00000000a00e000010570000000020d014fd007c0000804200000000000000000000000000000000200ab696903530c9000000000000000000000000e3d20000803c000000000000000000000000e0c2e0e1e027000011d5205fb014d7cd61f3000000000000000000000000a0120000e17900000000000000000000000040b40000000081ea6033000000000000000040090000000066e5203ac0fc000027f20000000000003bd1c04b109500005085000000000000d06900005008000000000000a182000050d6000000000000402fd7d6000000000000103600001079e020342680b380c6d0970000b08e00000000167200000000ca7e00000000b7e050c40000000001a60000728600000000b1c900009159000004a90000b30a60d50000462c806a13b5000000000000000020100000a7a892d8000000000000000060590000000000000000000050a90000000061940000000000000000e0530000301f000000003130000000000000000000000000000070b631e1000000000000e2df70ac0000002246d990d30000907d20190000000060210000000000000068713970e3801e262812a6000000000041000050f0000031370000c43e00000000000080700000b0dd000040b20000b0754038000000000000000090da0000d01d0000a60b0000b1eb375dd0480000000080e5e65822ce10df000067dc0000218f0000000000000000000000000000000000b140b800000000d1e9e0d8000000000000000050ebc18ce058d07a0000800190cfb0110000000003bf000000000000d09b70bf0000f0b5000000000000b05b00000000405d000031e800000000000000000000000000000000e0a50000000000000000000000000000000000006667)
def xud10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x695914c23ffd8b4ac8a619feec1a564530ddf36dd42409857f7b1689914c23fedc74ac8a619df6d7a5645308ffb65d2b229867eca2689914c33f751744c8a619dfd47a564530cefaa3d2b22985ef9b6ea1204c37edd9b5090261bfaec9a848130d7f702d42409867bfb46a1914c23ffd9350c8a615feec1a5645308fff62d43229863fdb8ea1914c23ffdaf50c8a611ff6d7a8645308ffb65d43229857f7b1695914c31ffc0f50c8a619df295a564530cf7a43d23229863fd81ea1914c2bdfdd243ca2617faec9a848130af7f6a90f28985fdbb36a1204c2bdedaa43ca2619dfa97a5645308fff70d17229847ffb568b914c2ff5d9330902611ff6c5a2e4530cfde42d17229867ed2168b914c23ffdc34bc8a611ffec9a5e45308ffb64d2f229857fbb06a1914c23fed8b4bc8a615fdec5a864530cefea2d2f2298677d51697914c2befd9b50c8a61beeea39448130df7351ca2409856ffb66a1914c31fe54350c8a61bf66a3a348130bfb36bd1a40986f7aa5e95204c3fcdca746902618ffaa3a864530ff3728a9a40985fdbb3695204c2fedd8aa690261bde295a548130bbf76ed2a40986feba8549204c37f4d42a490261feae515248130cf7b05d2322985febb2655204c2bdfdd2a3ca2619ef547a4645308ffb6ad47229847ffb26a3914c23fed9351c8a615efee521e51308ffb62d47229863ff816a3914c31fec0b51c8a615efee551e5130af7f70c8f289857bdb8647944c2bdfdab23ca2615ef6d591e5130c7fd31d43229857bfb2647944c2bded9323ca2619dfa57a5645308ffb73d2a429857bfb46a5214c3bddd8323ca261dee48191e51309ff361d4a429877e952e45204c3bf490f22902619fe6e7a054530df7729d02a2986fd9b3e81514c27fdd9740a8a617faec991481309ff365d02a2986fd9a3e81514c33fd54f40a8a619fba4ba264530ef7768c8a409877ebb2645204c3bf490b22902611ff6cba9545309ff371d0322984fddb3e89514c37eca9f40c8a617f6ed53148130bfb36a98a409847fdb9e89514c3fcdca26290261ff46053148130bfd76a90a40985fe9b5485204c2febd8b46a8a61feae512148130ff92a690a40987fe3a1485204c33dea9748c8a615efee1a1e5130af7b70d0f289867bda8687944c2bdfdab43ca2615ef6d5a1e51309ff760d4aa29857bfb2687944c2bded9343ca2619ef689a1e5130af7f68d4aa2984ff9b0ea5514c27eed9f52a8a611ffee3a2645308ffb71d13229847ffb5e89914c23fedaf44c8a613fe2e95148130cfdca5d13229867ed52e89914c33f790f44c8a619fb487a2645308fff6ad13229847fdb5689914c277fdb352c0a619efed1a264530cfef62d13229847ffb1689914c33dec2f48c8a615efec951e51308fff6ad4722987f4953549204c2b5fdb303ca261ff04c52148130 else 0x8b2e06b782dbab652d8fb57ad43b4a2d18b3cacd7b2f2c8bb196c4ab092bc7aedeba7ae06b50ad02b1aabd2ac3aa4aa61a8969f4a7929a8a5de951a4ae8faa326898a22284c9fbe7df9e0a7679c2a6ef9a4a635983e5b29606545947e4c291c246090be3f38eb232e8c222a08a4228089c226088661dd86b219c852a12f83fa0ee832204a7f5df7a7cf9f2e7c79f0e7bf9ec27a19e1e77b5d7a75a9ce1718dc327089c127009b846c71aa969e19ef66cd9a3664d95764f18ea628d893618983160857e55f557af5e257635d4d7225b996aa59e561157ad5a4565151652b94464ffd36b4d6d34b4c3d2f44a8928748d522547fd1ad4675109438d0b241d903a4024ff93f20f813d40efe3b60e863928e193824dcd3670d8c3490cf332b0c7b3154c192e14b5f2cb8afd2b04a9b28f8a0d274495e24e08f122d488f20f47f61f1477e1cdc6e51ad067818985b315004c2121847610bc41f103c39c0c4c2c109bc23e08b81bb0578143036c0730003bdea9303ca2617feec1a548530bbff6ed12a29867fca96a5814c33fec2b44c8a619ff617a264530ef7a42d0f289877bd81687944c3ff8a8b0290261def549a1e5130ef7b0ad0f28987fe985485204c3fecc2a62902613ff6e3a254530dff30bd03229877f985645204c37f6a9744c8a61bfe60ba054530dff725d02a2985ff9b2e81514c37fcd1740a8a61bfe6cba054530eff30bc8a409857fdb5aa5214c2bffdab5290a61def48591e5130ef7b02c8f28984ffdb8e95214c3bdea9323ca261def61591e5130ef7b72c0f28987ebfb6607944c33fe90b51c8a61fed60551e5130cffaa4d47229877bdb9487944c2fdfdaa43ca261ffc607a148130bff762c2a409857ffb2617914c3ff4c0aa4902615ffed582e4530afff70a97229875ffb754b914c3bf6c12a5c8a617feee1a548130ffd750a9240987fd98154d204c3fedd8aa690261ff62e95348130ffb30bd1a40987fb981e51204c3fdcc2f28902619ff485a5e4530cffb02d2f229867fd82697914c33fec2b45c8a61def61521e5130ef7b6a90f289877bdba487944c33fea8f50c8a619ff54ba864530cffaa4d43229867fd21e95914c2ffcdaf5090261bfe697a848130afff64c2b229867fd81e95914c33fec174ac8a61bfe547a848130afff70a93229857fdb8549914c3affdbaa4c8a61dfbe895264530efdb04a93229877f985e81914c3bdea9748c8a61def6e981e5130ef7b0bd23229877bd82547944c3bded92a3ca261def6c981e5130bbff6ed2a429867fd21ea1914c3fe5d1aa4902615efec981e5130cf7b03d23229877b581547944c33dfd4748c8a619ef6a3a464530cf7f4bd23229867bda5e91914c3b5fdb303ca2619efe8ba464530cf7b45d23229857bfba607944c337fd3552c0a61deee93a064530cf7f68d2b229847ffb2) else (if i<3 then 0x1aa326104409009009027c7fc1f8df21c59ca02960290480240a026e2de0fc878de3ee4d60ac0e81c804451215121512104809810013e3fc5bc1f90f1ae5014ac14814e3fc5bc1f90f1ae8015241102902a0538ff16f07e43c682a5029049e0c0e101102904c0041071f02864fc878df060a180a78ff16f060b0a64c2a2420b014f83e3e090a01c200b5061f72960c13f16072717fe3413d94f06070c6503e0c0e8060724f0609c0e81e21930a3e04ee0c1cc062994080c00401c7e0c0e8071f83014030664c3c5bc1880072494187fc1f8d07a5729e0fc68270165941e350100c2289728e4c17401e3fe43c6807481d03900860cb8ff90f1a8041799448412026041c7f8b393f07e43c6809052b04404f8ff83f21e378b3a005490440a409f1ff07e43c6f16054904e097c878d404610c088148260240041071f32804fc6f83f200a1a6502a242097c878d404070a0941e081cc02729e3413f90038704e0f040e5c9825805e43c681c39940f8d0380f060e6013a0f21e34138253993082205200750689e3fc580a790f1a04fc18286f8d04d06c64171de3a038404fe35d00020725d400afc1828e2c572700bc680b21890e93607c5812128fe89d26e0f8b02c3689f060b0041015ba0f07a4f44f16058703a072010c15838a3fa4f44f8303a706e00bc18080185048c0c5b02221a00924f1ba80010272f8d04f0080e10c48414814d27e0fc878dd12e8013240e825057008809744e93f07c7c0e1812805f06070806e0100c1806b12e4e01007282904c00744f1fe2c05349f90f1a083c182c680c00401c7e43c180a00e403de37c180c261ff07e340e80c281101003072125061f706607c6f160188941e350100c2004f1be0c0300c2ba0512e5200f9005dc5b8fb93f1aae3e0cc178c1ab94f1a0c3c80323790061625ca0322f160660c060d1c9f90f1a0cb8f82f3e89d260af8b7830386e3fe34198322031741e43c683005e6f21e34183a0b120bcdc59c1f90f1bc7c1702d382bf07c580e1344e93f060b38f978ff83f21e3415716042704804804f1ff07e35ca790e2c08540a40a814727e0fc871ff1bc5815281482401205009f16f07e43c6826e3eb05601bc180201853401043c7f8b393f1a0a8ca242a2420a412026e3e05014783f21e35c9a81482404c0040af1f028e4fc8783f1a0a18e43c6e89d29e0c1381c382404ce0fc878d04e094e09b8ff9004a45121048e8144b94803c5bc871ff1ae4d403800ba0329c5bc878d2468044084404403202101e43c1f8d01601d264b00fa0f276278ff8de2d6513e53c9f8303c0740e790f1a06d012b440d06b3e9cf673a8ce3737dcdb7352cc5b2e5cb832dbca53279c9a7238c81f1e1c71b18ac567154c4e711ec43b0fec36309cc1af02fbffafe3bef6f97bdc6f4bbc96f15bbbeed4babae88b98ae52b else 0x180b20e34e1105b70306e3e3fc0e1b00820c20c018060a424101484811890989083d00e201c0ce00b8d300501c0ce009c820000ac49703120008161812c0d14200c05f06e340e118b394e060ac80b3c1c16180816c216c01a8b70371a5e06e3416008200133931026726231213121e06008140c1e44b71a09cc0141e02889672081280d1c2079e40b80b01990384404c0104033018251b8d00008861242003c1e030040306e401cc061e160839048120602dc80810822048305a0a4120cc680001633281059c58ca0c0eb9000c307a01dc80c0e0117203022019c80c001c1ce16720400f858409802094485ca04704c30521204720c20891b8d3006108038188331824090271a000130c1141280300e0838d04c0010a242018201d8b38d183c05180c24114485ca04704c300ec585b0c16829c060a0980cc683c0504c066340000b2205041e0ec6828284704d80cca120685d040371a0f013941a833385e40900c1e02819237285186601c6923308428c613c81c22037e070100e914487c1f8d04e0740f140700174064f8ff8de2c7090a242e538b593f1be438f923384804a0f0500812045729e3413f90038804e0f040902239304b00bc878d0388c03e83c9990f1bc7f8b1c2478d0380f0700812043741e43c682704a8f1a0c0191c22783f1a0b861021282470607060881271f04ae0fc878d0388052053c1f90f1ae80131d448411024f060a08e43c681e07a100a09b8ff9004be0c161812026041c7dca790f1bc5bc1813052b049c7c140c14814e3fe0fc878d741c581524d004d004c985448415f93721e340f040302b04fe0c0e8392f8304e1041c90ca041271f707e340e790042704c07040881278303845121049c7c140c12026040025c9f83f21e378ff16052b04809810716e3fe0fc878d052051408809f1ff07e43c682a04a8045c7f8b78305853281326151215121f21e341802f3085f1a09fc1841072501c004ca393e2de438ff8d3089057e0c0e81c212301c600c2001329c5bc871ff))
def xul10 : Packing := (254,4,7,0,0,14,0,xud10)
def xuh10 (i : Nat) : Nat := 0x6059c11a0e0000c0b80000001d2b00000008040000701d903000280e00000030000000d4a4c37e067c22806e4050002075000383c00034e600025a20187cb178c8000c0bf81a0000c2a90c40000002c29a08380b61900000003912c7c741d74ab4bfb05c42c70cc43b975b41f896483587fc000d04c000000000010a043e90eb9ee407a02dd6d0c1c00021bff0932bf0003c0ac2d283d908d4300060000c0ac000000080960d080db0080000003927741a027f094000000240100010210000012c0100006022026888840c88d8000e05600627054363003c14770a43f00c99f2000106600030c10000000403c0b50900010d02000a00000303080000020f0009000101000e0004010201010a0004
def xud9 (i : Nat) : Nat := 0x6010e8b7818bc5bc0c40340322010084804200000001808cb85e4c2726f1a2003c59e4c4000c90ca8c80c690634200070a400464de3440000585e342001c684e502326f1a2000e34232432020110067901804008bc80c02c01de4060008f0310058038803c20000001c100e080000080800088078300c581f8d00730060058050c019e2402001c900d00b108f0600458d713a18c1481eff9f6be87c6f79ecbd4786ec9d0b846fede9aeb586a6c7986b085eeb9964ac457eab94ea98526a0938a5449e9291ca1c3e6728d099c2fe588a894c28e5089e92c2364588890c1f63d8788ec13e1d820800d6bda2ed981e5130adfbc768ba054530adfbc76cba054530d6bdb9ed981e5130bed9c62e95348130c7bcba6e921e5130c7bcba6e981e5130b5bfc76c951e5130d5bf94edda54853097bdc5ec981e5130f3b58260551e5130f7355260551e5130d6bdbaed981e5130d6bdb2ed981e5130f6b551ed981e5130e7ad52e8ba464530ffc1854c52148130ded9536dba848130dee9526dba84813097bdc8ed521e513097bfc86d521e513097bdc86d521e5130d5bfc76d521e5130cdfba8edda548130efaba8e515248130fdabb7e515248130d7ad52ec991e5130cfbb946cba054530cfdba8ed53148130dfd3b56053148130d6bd52ed981e5130ff498554d2148130a7bfc854ba464530e5bfc754ba464530e7ad8254ba464530d7ad52ec9a1e5130cff1812e95148130a7bfc2617a464530a7bdc2617a46453097bdc8ec951e5130ff48ca54d5248130ff4bc154d5248130ff498154d5248130d6bdcaed981e5130afdbc360ba054530ffc152605314813086fdcbe9aa960530c6bfb6ed1a864530c777a5ec5a564530c3f7a8ec5a864530c6bfa4ed9a86453087bdcaee521e513087bdcaee551e513087bfca6e191e513087bfca6d591e513087bfca6c991e513087f9cbaa7a054530a5bfc754ba46453096bfc66e1a1e5130c6bf94ed9a960530ff0b9454d5248130bf4bc154d5248130bf49c154d5248130ff83944c52148130
def xul9 : Packing := (64,5,7,0,0,11,0,xud9)
def xuh9 (i : Nat) : Nat := 0x306d2440681485000e02824bb00000000783600
def xud8 (i : Nat) : Nat := 0x180428800f19dd4c890154bfd754bb6607944c24b7faee130bd2322985f92758ca54d5248130bf24eb782a9aa4902617e4bd660553549204c30d7994e576cc0f28987f42edf9454d5248130
def xul8 : Packing := (7,6,7,0,0,6,0,xud8)
def xusamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5d08196a6ab94f2cc0a2ac25680a4208344800af404600baf816401410012b19a81841c60c000c42020805074b337509a3308401433e21f673,0xd0800682ea0c92840000c0048172150480931233116251411ce40830401291860184746083044020a0801024b220801232884808224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd845701f1d11913202dc0733613022d37320007400800ad1afe020260200042200c22a0182ce0e23c1a30c625943a822604c0ef4400c8c6487f,0x180450191c01810002588723414c8c02232008a5840c9da018e001c34a80042210c21a81837c418141120c6259418c644008042442088c44829),(0x24838aa0756a21466e610150ba833388387300602bdb8190000420200120421c041c13c6063acc2b68c012038e7c000204603082518f1078f9c,0x24038ba0014e004660200050988072894082174842410058c50060381174421c001c0546040082603ee110010028109a0470218011471038514),(0x197c742262611d0db214d4442210696c0a51cd90211b80201007090088c098c000603967fd2100181402e03c0e0000a007807e0da9f01f80fe0,0x194874026221140882068084264d01702b41c810a41a00a00a3e0f44420a18c0026020a1513105064002e2580e0024208300de050ab00b00ae0),(0x24239f791d94e161f9b06f2bd910880890006d8ccca42002000100228941cd201b010e18010000c4004c003fe000c10007ef000dbc401fff000,0x24230b791d14e16179b06f3bd91288089008248d48e49506b4c100b38d95c52019101b08040c4ab9965d0027d000d35c04cd0100b44014ed000),(0x9292ca9480cd64d0bf20125add4044a265eb203100058084008c4f9441f200001eec0000000b000005efd800080df7bf810800597bfe000000,0x12924a94800904c0bb20102a85c0548225204a14442950806e00b35419b280001ea60000530a0a7504b5b4000000132e8000105959da000000),(0x336b26e0e8f854fcc5a748cca028013148c3c0162820064c00763206330137dfe00020000004b300ab010000010001267fef3ff000000000000,0x236b24a0e0f8547cc5a748cca0231131484bd7126873001c271e2e14151bbac94a0024000401bc3eb801020000002392bff7bbd008000000000),(0x3adc5057929368b0852dfca4026310028d2dc2073ae461020007108a80325000041000800010f000294effbfef7fc8090000c00262000000000,0x1ad45056929168b0840dfca4022300168d2dc806b9bc62a7381f94c2ae0090001e011080000f5d188114a4beffd7ee450000c00a6a000000000),(0x696cb5c93062b8b3008b689c98c626490e3304010243c24501a9b52b4ad77dfe1eeca3ffac10110161000000100c8850000410260000000000,0x4948b5411062b8330081610118062869480204813042a41d000d08a28644536b4159b5eaace424006b000001180d84d0000000a60400000000)]
def xucolumns : List ColumnInfo := [(36,128,347,0,8),(0,16,486,9,10),(9,16,486,0,8),(16,0,495,0,13),(6,0,505,0,9),(10,0,501,0,8),(5,0,506,0,8),(260,8,227,16,6),(1,32,94,384,7),(2,0,509,0,12),(5,2,440,64,6),(10,4,369,128,6),(34,1,460,16,6),(128,0,383,0,13),(16,8,227,260,7),(64,256,151,40,7),(64,0,447,0,13),(40,0,471,0,8),(0,64,189,258,10),(32,0,479,0,12),(256,0,255,0,12),(0,128,347,36,10),(8,0,503,0,12),(68,0,443,0,9),(64,16,422,9,7),(89,0,422,0,5),(338,0,173,0,5),(14,0,497,0,7),(4,8,227,272,7),(8,4,369,130,7),(7,0,504,0,7),(1,0,510,0,12),(4,0,507,0,12),(32,256,151,72,7),(0,32,94,385,8),(35,0,476,0,7),(0,2,440,69,8),(256,8,227,20,7),(0,4,369,138,8),(32,1,460,18,7),(0,8,227,276,8),(0,256,151,104,8),(2,4,369,136,7),(8,256,151,96,7),(0,1,460,50,8),(256,32,94,129,7),(4,2,440,65,7),(272,8,227,4,6),(48,1,460,2,6),(4,16,482,9,7),(20,8,227,256,6),(2,16,484,9,7),(32,16,454,9,7),(256,16,230,9,7),(34,0,477,0,8),(1,2,440,68,7),(12,0,499,0,9),(2,1,460,48,7),(24,0,487,0,11),(8,16,486,1,9),(11,16,484,0,5),(40,256,151,64,6),(1,16,486,8,9),(2,64,189,256,9),(13,16,482,0,5),(257,0,254,0,8),(258,64,189,0,8),(20,0,491,0,9),(48,0,463,0,9),(272,0,239,0,9),(268,0,243,0,7),(260,0,251,0,8),(288,0,223,0,9),(86,0,425,0,5),(281,0,230,0,5),(18,0,493,0,9),(276,8,227,0,5),(50,1,460,0,5),(19,0,492,0,8),(41,16,454,0,5),(3,0,508,0,9),(264,0,247,0,9),(33,0,478,0,9),(330,0,181,0,5),(323,0,188,0,5),(166,0,345,0,5)]
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
  | 13 => lookupWord 8 31 5 12 4 4 xuh13
  | 12 => lookupWord 49 211 8 15 7 4 xuh12
  | 11 => lookupWord 112 809 10 16 8 4 xuh11
  | 10 => lookupWord 32 137 8 14 6 4 xuh10
  | 9 => lookupWord 3 13 4 11 3 4 xuh9
  | _ => fun _ => none
def xu : Forest := ⟨511,13,fun j => xusamples[j]?.getD (0,0),xucolumns,xuautos,xulevels,xuindex⟩
set_option maxHeartbeats 0 in
theorem geomxu : graphValid xu (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
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
theorem sxu_12_0 : block xu 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_12_1 : block xu 12 1 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_12_5 : block xu 12 5 4=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_12 : block xu 12 0 9=true := (@block_merge xu 12 0 5 4 (@block_merge xu 12 0 1 4 sxu_12_0 sxu_12_1) sxu_12_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_0 : block xu 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_1 : block xu 11 1 29=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_30 : block xu 11 30 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_66 : block xu 11 66 18=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_84 : block xu 11 84 11=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_11 : block xu 11 0 95=true := (@block_merge xu 11 0 84 11 (@block_merge xu 11 0 66 18 (@block_merge xu 11 0 30 36 (@block_merge xu 11 0 1 29 sxu_11_0 sxu_11_1) sxu_11_30) sxu_11_66) sxu_11_84)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_0 : block xu 10 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_3 : block xu 10 3 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_39 : block xu 10 39 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_75 : block xu 10 75 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_111 : block xu 10 111 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_147 : block xu 10 147 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_170 : block xu 10 170 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_206 : block xu 10 206 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_242 : block xu 10 242 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_10 : block xu 10 0 254=true := (@block_merge xu 10 0 242 12 (@block_merge xu 10 0 206 36 (@block_merge xu 10 0 170 36 (@block_merge xu 10 0 147 23 (@block_merge xu 10 0 111 36 (@block_merge xu 10 0 75 36 (@block_merge xu 10 0 39 36 (@block_merge xu 10 0 3 36 sxu_10_0 sxu_10_3) sxu_10_39) sxu_10_75) sxu_10_111) sxu_10_147) sxu_10_170) sxu_10_206) sxu_10_242)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_0 : block xu 9 0 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_18 : block xu 9 18 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_54 : block xu 9 54 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_9 : block xu 9 0 64=true := (@block_merge xu 9 0 54 10 (@block_merge xu 9 0 18 36 sxu_9_0 sxu_9_18) sxu_9_54)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_8_0 : block xu 8 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxu_8 : block xu 8 0 7=true := sxu_8_0
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
theorem caseUB : Impossible true (graphGoal 511) 13 (varsX 44031).toFinset :=
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
def known49775 := extendKnown known42527 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65]),(44667,[101,66,16]),(53085,[130,50,115,48,49,98,65,80]),(60394,[81,33,80,128,97,114,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid49775 : Known false known49775 := extendKnown_ok (m:=49775) valid42527 low49775 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42607 : Lower false (varsX 42607) (graphGoal 42607) 7 :=
  strong_full (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=1) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known42607 := extendKnown known49775 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64]),(45041,[98,99,81,131,114,65]),(60380,[80,133,96,49,113,64]),(69617,[96,101,81,49,131,112,65,32])]
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
def known47679 := extendKnown known1599 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96]),(53228,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known false known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower false (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def known42559 := extendKnown known47679 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64]),(45027,[83,80,132,115,96,32,16]),(47775,[117,101,67,32]),(53086,[132,116,84,48,33,96]),(60396,[80,84,132,49,113,96])]
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
def known2237 := extendKnown known52799 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16]),(9702,[16,82,131,100]),(11965,[117,67,32]),(17755,[132,67,100,84,48,33,112]),(27110,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known false known2237 := extendKnown_ok (m:=2237) valid52799 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower false (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=1) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known1725 := extendKnown known2237 8 [(1725,[]),(17085,[82,48]),(8166,[16,82,131,100]),(14310,[32,49,128,81,116,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known false known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower false (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=2) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2749 := extendKnown known1725 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16]),(28134,[80,132,99,112,32,16])]
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
def known48891 := extendKnown known44221 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32]),(48382,[117,67,32]),(49403,[84,115]),(53725,[48,33,133,118]),(54743,[16,32,48,128,100,80,116]),(63227,[81,130,118])]
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
def known2175 := extendKnown known48891 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112]),(8171,[81,33,80,128,97,114,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2175 : Known false known2175 := extendKnown_ok (m:=2175) valid48891 low2175 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower false (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def known1151 := extendKnown known2175 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112]),(18940,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known false known1151 := extendKnown_ok (m:=1151) valid2175 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52863 : Lower false (varsX 52863) (graphGoal 52863) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def known52863 := extendKnown known1151 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112]),(60347,[81,130,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52863 : Known false known52863 := extendKnown_ok (m:=52863) valid1151 low52863 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44159 : Lower false (varsX 44159) (graphGoal 44159) 9 :=
  strong_full (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def known44159 := extendKnown known52863 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112]),(42995,[98,99,81,131,114,65]),(47863,[82,98,115,66,16]),(53244,[82,48,66,129,112]),(60382,[99,132,84,48,33,112]),(60397,[32,80,81,130,66,50,113,96]),(69628,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44159 : Known false known44159 := extendKnown_ok (m:=44159) valid52863 low44159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower false (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def known43647 := extendKnown known44159 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112]),(43447,[134,81,114,50,65]),(48863,[101,117,50,33,16,64]),(49643,[81,33,80,128,97,114,49,64]),(51151,[16,32,48,128,100,80,116]),(54253,[80,129,50,116]),(55759,[83,133,115,67,32,96]),(65017,[101,81,67,128,113,32]),(68595,[67,80,100,131,112,32,16])]
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
def known2239 := extendKnown known17087 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96]),(9710,[128,49,100]),(12479,[32,83,116]),(12733,[80,129,50,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known false known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower false (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=4) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2751 := extendKnown known2239 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96]),(13503,[32,83,116])]
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
def known44223 := extendKnown known58047 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96]),(69053,[80,129,50,116])]
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
def known17151 := extendKnown known2303 12 [(17151,[]),(8190,[32,49,128,81,116,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17151 : Known false known17151 := extendKnown_ok (m:=17151) valid2303 low17151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2815 : Lower false (varsX 2815) (graphGoal 2815) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def known2815 := extendKnown known17151 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16]),(3581,[80,48,50,114,129,64]),(6647,[115,82,98,131,66,16]),(6654,[117,99,49,32,65,128]),(28158,[84,100,49,113,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2815 : Known false known2815 := extendKnown_ok (m:=2815) valid17151 low2815 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6911 : Lower false (varsX 6911) (graphGoal 6911) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def known6911 := extendKnown known2815 12 [(17403,[118,130,81]),(5111,[16,82,131,100]),(7166,[128,49,100]),(7935,[32,83,116]),(8187,[128,81,32,49,100,116]),(14303,[16,32,48,128,100,80,116]),(14333,[80,129,50,116]),(17406,[32,49,128,81,116,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6911 : Known false known6911 := extendKnown_ok (m:=6911) valid2815 low6911 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1791 : Lower false (varsX 1791) (graphGoal 1791) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def known1791 := extendKnown known6911 12 [(17405,[82,129,48]),(1791,[]),(5115,[81,130,118]),(8183,[16,82,131,100]),(14334,[32,49,128,81,116,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1791 : Known false known1791 := extendKnown_ok (m:=1791) valid6911 low1791 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1279 : Lower false (varsX 1279) (graphGoal 1279) 12 :=
  strong_full (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (index_root (g:=x255) (i:=0) rfl rfl (before_sound known44223 valid44223) geomx255 tablesx255 (by decide +kernel))
def known1279 := extendKnown known1791 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128]),(3575,[80,16,33,50,116,131,100]),(6399,[32,83,116]),(6623,[16,32,48,128,100,80,116]),(11743,[48,33,133,118]),(28155,[128,81,32,49,100,116]),(28157,[80,129,50,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1279 : Known false known1279 := extendKnown_ok (m:=1279) valid1791 low1279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58623 : Lower false (varsX 58623) (graphGoal 58623) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def known58623 := extendKnown known1279 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48]),(48635,[81,130,118]),(49662,[32,49,128,81,116,100]),(55799,[16,82,131,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58623 : Known false known58623 := extendKnown_ok (m:=58623) valid1279 low58623 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58111 : Lower false (varsX 58111) (graphGoal 58111) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def known58111 := extendKnown known58623 12 [(68863,[116,83,32]),(55293,[80,129,50,116]),(74207,[16,32,48,128,100,80,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58111 : Known false known58111 := extendKnown_ok (m:=58111) valid58623 low58111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44287 : Lower false (varsX 44287) (graphGoal 44287) 12 :=
  strong_full (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def known44287 := extendKnown known58111 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48]),(43003,[99,81,115,130,65]),(44539,[81,130,118]),(48126,[117,99,49,32,65,128]),(52991,[117,67,32]),(53245,[82,48,66,129,112]),(60411,[101,81,67,128,113,32]),(69117,[80,129,50,116]),(69630,[84,100,49,113,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44287 : Known false known44287 := extendKnown_ok (m:=44287) valid58111 low44287 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42751 : Lower false (varsX 42751) (graphGoal 42751) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def known42751 := extendKnown known44287 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64]),(45047,[80,16,33,50,116,131,100]),(45051,[81,130,118]),(48095,[16,32,48,128,100,80,116]),(53215,[48,33,133,118]),(53246,[32,49,128,81,116,100]),(60414,[128,49,100]),(69627,[128,81,32,49,100,116])]
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
def known2431 := extendKnown known42751 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80]),(1983,[98,118,81,130,50,65]),(4991,[84,131,98]),(8175,[83,114,99,33,16,64]),(12783,[32,83,116]),(14319,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2431 : Known false known2431 := extendKnown_ok (m:=2431) valid42751 low2431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1407 : Lower false (varsX 1407) (graphGoal 1407) 13 :=
  strong_full (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=1) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known1407 := extendKnown known2431 13 [(28143,[33,80,112,97,130,49,64]),(6639,[16,32,48,128,100,80,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1407 : Known false known1407 := extendKnown_ok (m:=1407) valid2431 low1407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54143 : Lower false (varsX 54143) (graphGoal 54143) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=2) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known54143 := extendKnown known1407 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32]),(51135,[81,130,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid54143 : Known false known54143 := extendKnown_ok (m:=54143) valid1407 low54143 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44415 : Lower false (varsX 44415) (graphGoal 44415) 13 :=
  strong_full (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=3) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known44415 := extendKnown known54143 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80]),(45039,[33,80,112,97,130,49,64]),(53231,[83,133,115,67,32,96])]
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
def known42879 := extendKnown known43903 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64]),(48111,[16,32,48,128,100,80,116]),(53183,[32,49,128,81,116,100])]
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
def xmd14 (i : Nat) : Nat := 0x64120b8a81a151288c049ffd30
def xml14 : Packing := (1,1,8,0,0,0,0,xmd14)
def xmh14 (i : Nat) : Nat := 0xe6ba1400070987a000000b1221916ab07000e01a1a115d11000f71000000a05361000960270d0a613a0b167e72c06966763073a0391bb62c10b04b7b908502a180000000003c81432000ca140000
def xmd13 (i : Nat) : Nat := 0x4c9174a83680a2588c304038df228c1ab206c0512b221828680c1328c91785e0d44a154a900809016b46bb0e911a748a0ea8fa11785d2a8a9324480d4f62588c0e5956d633c5d44b11a28afac6945c414ed2a1249d426234ac22529ca7ab63c8a112c46892228ba87f2340d2a8d52d0cd2751425cce896230f1c469544ba244eb5ae026406c4b1186d01343205c2a834368962380900b82a8bc2a8a44712c048957109ddb665e6a51159c22622a82a800ffec8a61ffc914c3ffb02987ff20530ffea8a61ffc514c3ffa42987ff08530ffe90261ffd104c2ffb22987fe48130
def xml13 : Packing := (12,2,8,0,0,11,0,xmd13)
def xmh13 (i : Nat) : Nat := 0x119b00000000000db9e1000000000000000000002400c00000003196d40569df61cf440838194000000018100000204b80000000000000003822c9dd0000384ff0105c0480000000000014d7000000000c2300000000000000001c0600001de32e1240002803c00030582405c000000015971858800000000c156810c00000000000258440003c1f0000001bcc0b00000000080fc0000000000035d740003820c00010210000242200002ec9c0000000040dc0001c5a218a5011201780000000169c80002860dc05384cf0167c9d40000000000000000000000000001447c000000000000000000000002c90800000003820a404c023f989800005800000000000003015b848c41b80002019e8924000282299d2049c8589c0000000241f8000182140002d99c000001aa9cba858c0000998d00380002842800000003c1180001c520584b8120823904980000000099e902180003e9d0000345d844d89981d9d5c49e856a806d89d0000019600001c020000000000003022580841c680001001a8004000245bd820499bd98a28e200000000100f4000341a400c3d9b400028032cdee0098451e0124000305ac0001c12c0003415000000000000000000000000000026d70dd340003a9240001592e0003002ad9b812221d4000034034814f418400eb82000000819241c3818941a100f080c71d6e416f8173816281dec02c81441ca400000000c0cc000001298064c0ad85b80000000345180001c059c13800000000000000000000d09dc1f79950c07400000001d91504b540158c9c021c00000000000299d2813648955d27ee214183001ea9d6c0b8847a01eb008e00125c94000341c9c116d173807809f6016b006b8235857000000000862341ec0c2800014584000340450108599400000000811d00d1c130c0d48090000081d80001d85c000081c4000201e500ec2896c1b00001400b80bc0001a1f540959a111dc8417e80e641980000000318040002c57b415c000180a381d400000000414000039ca0000000000001d9a0000180c8000180f8000200ab01ae41e0000180a740b4407ec09d4176a9f680405db09d288024209545edd8400003da2000e3c1cc0000000000009de800019cb51dd400028088000000001c20d88400000000c1b5c0701d3000000000c18c4148c528000000000001190c0000413dc1d000000001c1fcd90400000a0001808020003004000000020000000000000900814120b0080c04060000800000300806010000c00000280002020080c0e010080004020080002030301004000001400160006c00000000c0000008380200068041401000180803008000602
def xmd12 (i : Nat) : Nat := (if i<1 then 0x232254448ba80ad17a2980b12e230387ffc3fa9fc83e8cf8ebde8f553c94f10bbfbedcbae9e983a50e903a30e74f929e17b7ebdba75fdd4f7472d0833a2cc3b2b1c9271aac4b30b9c19efb2bd2af03ba16ddbb5fad16b20ac25ae1ab08aaaea22a6ea973a3d68a3a0c27919bf665397da557944249d90aa3b78d6a2e789a61e0858a0ef8141fbc7cf9ed67961df075f5d157205c246e99b336b2da6367ed98864d989760bd81f5e2d7025a115f0559d4f452314194e993284b0125847c117d442908c4064fb13cccee13934e3d36d0da434c4d213208c042decac629209eb260c910221c82a1f6077b1cd06d719645f1162452113684670ffc3a20c902b1097c20d063c13204040c50148000fff6a1914c3ffca864530fff661914c3ffd8144130fff695914c3ffca564530fff655914c3ffd5244130fff689914c3ffca264530fff649914c3ffd8244130fff655104c3ffc8164530fff145914c3ffc2164530fff6a1104c3ffd3148130fff605204c3ffd9148130fff549204c3ffd8248130fff6a5814c3ffd5348130fff2a5814c3ffd9548130fff649814c3ffc9260530fff549814c3ffda060530fff695204c3ffda848130fff654214c3ffd5148530fff645214c3ffd9220530fff548814c3ffd8548530fff6a5514c3ffd9548530fff695214c3ffda948530fff608514c3ffda354530fff648514c3ffda254530fff289514c3ffd9254530fff609514c3ffd9154530ffe661204c3ff95248130ffe609204c2ffda214530ff768d514c3ff93248130dff2a5514c37fda948530bff6a5214c3ff99248130bff6a5514c37fda954530ffe685204c2ffda220530ffe645204c2ffda908530ffe54d204c3ff98348130bff694214c3ff88548130ffe605204c3ff98548130ffe255204c3ff95148130bff6a1204c2ffda920530ffe4c5204c2ffda960530dff648914c2ffda224530dff654914c2ffda524530dff660914c3ff98048130bff6a0914c37fc9164530dff649914c37fd9564530dff661914c3ff98044130ffe481104c37fda864530ffe655204c37fca864530dff695914c3ff8a548130dff295914c37fd8564530dff215914c37fda264530ffe695204c37fca264530dff609914c37fc8264530dff549914c37fc5264530dff605914c37fc8164530dff545914c37fc5164530dff485914c37fc2164530dff601914c37fd5064530dff481914c3ff8a948130ffe6a1204c3ff89848130ffe2a1204c2ffda914530ffe485204c27fda2645309ff695914c27fda864530bef690214c3fe92148130bdf694214c2efda6085309ff6a4214c3fd953481309ff2a5214c2fdda3145309ff6a4514c3fe952481309ff2a5514c2ff9a020530bef690814c37f99148130b7f69c814c27fda9205309ff2a5814c3fd93148130bfe680214c2ff9a848130 else (if i<2 then 0x88f12e02502e4928d8553a7502af4c23124fd89711b60042d0180c2adc7931453f12e23a2253807adc1b3222f88f12a7ec040d195241833282f0568be15228c0580602230b664ca9aca816cacb0a7625144901a857010a103945311b32c4a0894caa0bd1722803b11e2567a03d32aa4ec9791a4ca06d17c534501a625c46071b5d88953a25588ed180f8e88492a059921522045311b4400800d3a2c9951222f8569550001f407010035583ab30342687c143896c881c49832b245f0111437d894c881c482d0396fa0687c0c5896c88a2481c37c4509960230656712991060a81a284310a2c4b6440e1c068aa13a25c468ce19b4505a363c4b88c146027114255808df1832b3894c881c49120a976654c88932aa550d88be25c4603f01003693262f45f0ab2aa5444b12e2301f80801b19953262f45c4812ac4b88c07e02006b12e2344ed1201b6b414532c4b88ce060286cd15423406dc00510da99625c466b7011146332c1ac5c4785606989711e02006a624ca88ba9bc4789401e0201e9c1adcd9505e0f42ee1b625c04e1558358bb2ac2a1581a625c4780801a8133a701b4501a602c4b88ca107c676b040cec5dc3606980b1186c6ec90cc449a728151b8959636517690689fd8ba7e66589711e026549665835950561160d312e23c0400d40118932a42b854d7623c4b80807a8103ae86cd383d03804380b1186c746b6650c889037c1a91f12e236ba00d40e15a3b986cdcf12e23652c5d24499542a040ccb06b1786cc7b01307583870b0db11b84478dd8ecca1960d224c5e0b82a6550d980602602021a44820c98bc176550a906c36c4b88d9e838162c224102ec5d9db2a0ad0d94ee23656c2544482a752820d82ead01528d654d8c14436c4b88d3ab81928d75cdccc5028536b31c4b19710b51b0c99542a02e0d08a436c4b88c0423c600e4924411b28153645f0114230e6ba8a1adc4b88c0e4199517a2905d0a804c0588f1281c01eb01c1f10ad14c46c7f12822431f0060c701623c4a61c50b2a4e15b5967899112c4b88c07d5f006a060504a733b0aaca924914c46cad84910603205422c46436c4b88f01200b82ac1b0db12e23c04706405e1b090c478970108f414ec4b88c891170806676ca924b09c46cac8a02240208f253b15450a238971191222f191653aa7d5b8f314312917a2255d31e6a7d5b8a04488be25c4744520340ab32a2f4518fe23c4b80934aa24c9dc474244e18e5e0d2256b2cf625c46452af96354bab592aecf13222589711d5f480d02eccb0ad1463d80983a0508a20380881940d02403311e25060b3945cf0ada3aed4eb11914a9847d55d88fe23a7445095040381722945d1b623c4b808e268cc99623e260d1c752ec4523a1955da3aec44895475c474ea3a203e5000d00c0988da2114221808a628a7479a9f56f12e else 0x4831be3208447e0206872cd80b12e2315000cccca9911262f45f01028255c678d8300b0c92e700acb17c2e452990d486d03580301120d06980b8cf1b0bc038109c90166c05897118c601e701c4c98bd176554ab0171b05044b8c8300b0d240882554126554ab15030050218991ad81ac7983e0286d111780b8cf1b0bc0881a1c90602c4b88c320033332a644499552ac040a08bf19e360882c305b028c534ca0688648e6b4e0625c460718a6c89317a2ecaa95602265c678d80e05ac2241224122414556b78ce2386d80843034401c01ccca9932aa558a65529b22019311b4446c089e5a1344aa6654cb1940d04cca80402d06105580114c04c064bc91b32aa558088a117e33c6c1103450280b52aa4e91029c4ca06b12a2584b0ab2aa558a8101ad060c7b0130735d25ee0dc144aa35a440a7532c64c4a8961222e1541832a35d88f12b5d48f276a1282f02e05accb06d1262f856950b20700841a500c054062070070280b0c4a8932aa558a65549d46ca064be25c46a6c3e488c21cc054068019241c722ecaa95517068a6f8cf1b99b80816ac18332a6444a8952a52e5a02f045a01407013699215c040e280310a0283905a2341204408c218602a034012ccb19317c2e8541a1c041b85417068a0180a80ba4bcb46558a81a21599dc6f12c3c05ab92f2d1154ce42bc678d8348780b541028be25c4603e88803380f860030ac9170440b820d2a89245295e2341b4249dc02b517a132769dd2ac474ac112420623a5468e3a00f302d09a880541768e8c7a8a47534747d68c2181662822706993b2b25389528d502cb295d097c0d62ecaa9ee25c4603807a069058a124ee95141c474ac1124110410ab0889dd2a05c33e24c9dc474ae84b68485505d4ee95623a5608901c40183400831a5599e35891f12e23ac6d7689382f02162ecab1482e06b03712e2301cb3592eacf625c4744aaf834400f01ccab1502e81c33c1ae23c4b4f606b01080c81b8a98be253234f407a59553dc4b88c0700f301c01c1ac2300f00691e06e25c46d756c5d9553dc4b88c0700f3b326258560a917c4b88c01e0201ea35c61cc200d6540c08851429cc1d8f6020aa481c5088800d22e070a751448f88f12b5d0aa00da0c0a0912083678e5963c1b854d6625c466e6af914780e0a989711c0da7a02007a124a36502ea488055042f2de52477a3895e80c570cf81b8971186b01c6a2e1582d53ba551264ee23a57425544a8be15a774ab11d2b01f42401a99931242aca88be23c4a00f0100f551222e4aa9ee25c4600c0722892174558541c40dc4b88e9e8b5533242aca8111ad22989711e020620d161048f973c2a0c2bb1cac4600c8a54c346c228cca8bb2a22e8db12e2300780807af0ad4fab64488be25c4603e88803523648ea6e8ba154934518f833043))
def xml12 : Packing := (144,3,8,0,0,14,0,xmd12)
def xmh12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x85cc16b0000200c46622e997c60927d9bf286ba043e503a40000f08a58148f074400008b4d70141b10cfd9e7604b080990000200dec11060196000000000b68cfa20c0016400000000069d6660cdc9de98759860300001489f00001a0d000001c1510000000005163c40ed2060ad450504a18208000000000c02b80000000000000069419d845144519f9f891e41890000240b4806180000501596a0d00003e0b30000221d970890421c0019241f595884ea3e000000000906ca0113b12d4000000000d8518669c00000741b802a0077700be901aec20511847c07f000000000000000000d07400000801615e1100002d98b00000008100000000000003c07836100000000000d1bee63f00000708f5c032000009c2ef66440000e04880000e04fa0143378fa40adc090f0207000011a11d4881023418834581fc014dddcb3019d402e4093000008083e41c6504a7c604616900000600a1c24000002817c376b8000070558e22121887c20d476fc8254b000c81e292834d838878100000f005c000000000000000000000000001823ee62ac000000002804ce60e680da703484161e03d9d46f566c2816fd876c0000765018822d08291a0f303a19de6e07f140a09064081b3600ea4175a079901424286e80826086018f1803580000503ff192b598815deff041dc0eec4161012fc15a240fe947f3412064758add6104fd0031d012a5d608073e8191001695a164054fc0dd0000108fb512fcc498ab15f04e200000c16a00002c49a00000000041294d9ff000029c50d29040000604ec81be0000248d0300100000804ac000000002808b3750fc057000030635000000000000000000847bf104f2291e61dae164381473975b01af00002451300000000000003c05cc066c0000b278fc112d011000b7aa76ac150000014c5e810f7a1d5000039805e2141149c7078000000000240e37a76dc1ab070d0010000405000001050700010009020002001800090a12010100000207041a01000000050600000303070002030105010c0000040a010402000b0026010002020b0000000200010301000306012d0000010015000601000110030100040405000400020700050005100502060103010004000303020500010812040007030200061600020008000700000e02060700130f07051a00060006010018200205200e0002000b02060003000800000109000b01040603001200000000030d001c000102000b010802030105190a050401000000070f0a03000205010b000635070c001801030403000f0002020000030d00010201000304050d000014000a0906000601020a02010403041a00030301061a0c1114011108120500070000000000000b0502000000010000010603001100070100001a00090000000100030100010101000b0c00030006070303 else 0x18ac064f80ab2011601f8f105c40b3000000000708fddde0203eb813c60622c46a715cc411d405744221518ba69d800000a43c0000199a2000000000008a99a1ee583559d600002019c0000000000000381ae00003c19200001055a1024f0002b0802c13193892806a00001185800000000000000011ac130d4216a15df042cc05280000da830000000000422f500f145f9d0137dccb8003000006074c0000d36cc0000965f80000b2782c0c300001c0110020dce0dc04632dee000618136000000000b004e4624008980000a03c80000a21340000c02b0000000000805f00000000000002853e00002c1d82076a418100002812100002582e00003c0a5960af1c760000000003148400005173c0000e10bd00f5718340000000000000471b80000e078ede0d000000000802621d38708d658b67576ee89950515cc5fc852c002cd05ce8010604d344ad000000000e02180000c7772d9bd770944180c234e413df031c0000b13a10071312769a0df7223191a562c80000771d40000b032d421fb15800000d07b40000004729c480065000000603740e0d03cc000080589c0ecd0290996a000029dd65104401e1e03f3c022e71599d659182e41a1405b00000d02000000f640fc540000000047b15a80000000000000506e9c1b9910e40070308e3802150327c4a2a29118241600980000270c1c0fb44809c0a8000000000c00180000e75fb01e8e27582df0a6099406d70532e9dfc01d80000c04e31c71c226b46230000241bd0000381400000000000000000000000385a9276c040eb800e7c037f15d2c18b308c7097d000000000000000000000000000768c4449b5024484e3806c580a6f26b40000602c6193a0000121dd000000000000000000801380000304040000a22840000f28fa5827e03e441a4e67ea416768827850fa314000000000141a0d37bac23630793460aba4678210d03881dc3105340000800d00000000000000c067d9dd1f0119c629805d980f1616c8cdd6008ae80ba70107a9e0a06b00000a06e10160000000000516500000000000000068b80000d415b010e107d2005bf57580dfcc026c00000063d40a2e15e40000000000000914400000e16874e200000000000000084a400001c5a8f252d1c84f00000000602c280e4b06aa0124e0228696bb15ee008d000000000000000000402dba0a9107fc05aac1535417419672c6250000040947021280b9000011da80000340d3d072386130209000008756299a5501e9da3c470ad043f500900000000000000615e20183000000000463e8c068b05e5c212842e100488053b4090f243780f400000411700003024200001ca420000040cd910c9810f00001dde900001989537131c0f700002520d000001de410755988e70888e9dc5b8800001376d301f70067999e9204e5006510) else (if i<3 then 0x4073800000000000008033d9c0c70748c0fd805945d7a2092a44c4816bec201807108ce600001d8fd000000000d26950227806880000000000000000000000e017800000000000000000000000000380e69075000007704c84f2f1137c13a402a99a00b21bc00000000219a0c186000000000001cd664a80000000026d27800ed9d85e040bd9a1401d602115007c000000003ce12b6252c1e900001855b0000198ea00000000001524000000001418500000000000000809d00003c0954109b4c9e00003594d00001c04b5661400007052d81c7c0813c08e000000000f17150a0475659c5830000080a78171c0000a087bc620b1238008900001d8be905de41a95735d023a106680a3f000005822107b80000d06c00000908dc0000000000000000000000c069ac22ca0319c052000000000000000000a415fc1b4000000000000000000a0920c1e5a41765048342ec00873077d0467000034168000000000e650e815f000030085342255059c056f1c70f610481329043641fa871d2045a8070398342776f01ebc77420223d05b7c5884665ee1e2155afc1d72091cc051102edc5ba805f8dcfb207644009b07f4801e305625984e26bc99885605445230086a819d8003d802b405b91c55802e00649f017745bfb71cac074710ea4239e0496c1872028f418470021c244403c35c29105c2d036801b9849e38437002000000000050717c0ce00003c899000034033d027c00004001e49b82760b81c170524c137868a841c2d97bdd073b8060c20940918c0a1c63ac6181c149380693187d014f008300000000000000e642a015c901240000162aa40b2e018218813b8340000e17371d7860510d5cc0000049a8d66b80000e167c0000216269c05208c8984fd62df9ccf000000000d05a400000000000000000381de103a80000c08c000000000000000000000000000280a900002cdbee17180000107d80000d66520596d040c011ea058d04acf16c740bd7068e4115236bc460213263400570373052b6770941bc675980000e03bc0000000000000d0729810a2704000009048c00000000000df00000420300054000000003c09a970dd015200000000000000c1bfd07a8000000003c1c9a04c280e18369d0a1ca084e000b905995887a00bd9986c1165dc2d4082fc427b0551c252e0341c06c4a8ff802dd486640af00002c0db0000000000035d1ddd0000000003732b89e2501fa60d3000000000975d4000000001c17b100da244810328815e000010251d08ccc146805c505182049b9a3250663583a000000000b079c0000000011e3f809400000000000000001be8253503630119000000000134d5c09ce023ec45e000038105515af40306416b81f12024b421dd55f400000747800007002a41db000000000601cbc else 0x56827817fa085000000000081fb00002c19546249c0549010801c3bb7ed94f300000000031758403e30914000000397045f4380800000000304a9000030127e04cc0000806ef023cb10d0000000001d81800732dd9ae0839d8fe1008cc23b007f8017850809003d00003ca092166201ad0013d01cbe089781110055511af7166400000a26a5c6d00003c164f22a401f0113b00000000010197462e40000a02fd40d9406a000009567f1d7f00001908600000000041618000000001462a000000000000000000700fc0000000000000910540000000020135a02d40000f276d5c8e000005d80c07e400000000201a7d04b5802500000c2190000380e7866adc1a50000000002009c0000164b481b700001810900000000000001017a000028040344d40000c983480f8075de8106c0854000000000c108000000000c77100000000000000000030066f1744417d9075a05ff210ec00000000000000000000000000000000000000003102400000000101102143b0157201cdc029348dcc050000004077d08b8000090279a0bd0635e91b700003c450074fac21b907b04088c40f00000c05680000000034199b07be59d500000400d000018228512a3c1590000355aff08180038036c4c22042270000024146811f318b00000362ce01dc0000140550))
def xmd11 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x6a1914c33fe90350c8a619ff548a960530cffa42d49029867fd516a4814c3ff4dca4290261ffa6e12148130ffd35090a40987fe998485204c3ff4daa4290261ffa6952148130ffd32a90a40987fe985485204c37bedcb4a10a619ff605a920530defb30d28429867fdb16a4814c33fea935240a619ff6c9a920530ddfb30d3042986dfd5269c814c377ecab4c10a61b7f649a720530dbfb72d39029877f921645204c33fedab5210a61dfe5459148130cffb0ad48429867fdb16a4214c33fec0b5210a619ff545a908530cffa42d48429877f981645204c3bfcd0b2290261ff66e95348130ffb174a9a40987fd8a954d204c3fecd92a690261ff66495348130ffb2a4a9a40987fd9b154d204c3fecd0aa690261ff66455348130ffb302a9a40987fd95154d204c3fec90aa690261dfe5499148130eff304c8a40986fdd9268c514c3bfcd932290261bf7609a314530cffb64d48a29877f885645204c33fec135228a619ff6c5a914530cffb02d48a29867fd516a4514c33fe90b5228a61dfe6159148130ffd372a9240987fe8b9549204c3ff454aa490261ffa6a15248130ffd150a9240987fe998549204c3ff44c2a490261ffa6cd5248130ffd346a9240987fe983549204c3ff4a9aa490261dfe2959148130eff34ac8a40987fe9a1549204c3ff4c8aa490261ffa6055248130ffd262a92409877f8b5645204c33fec0952a8a61bfe655a020530eff36ac8a40986ff992680814c3bfc5432290261bfe549a020530eff350c8a409877f8b8645204c3bfc5d322902619ff6959824530bdfb6c10b22985ef9b6295204c37ec98b50902619fe649a020530cff32ad01029847fdb22a5514c35fcc035048a61fda54d5248130cff240d48a29847fdb26a4514c33eec934628a611ff6d4a948530ff9242a9a409877e952645204c33fc9035210a619fe601a9085308ffb6ad4842986ef980698214c3bf490b2290261bb754da608530cdfb2ad30429865fd9269c814c337ecc34c10a61bde601a5085308ffb64d4902986f5db3694214c33becc34a10a619df6e5a508530df7300d20429867bd95690214c33fc9035240a611ff6c8a9605309fbb66d29229847fdb26a1914c27fcdd300902611ff6e920645308ffb74a83229847fdba601914c2bfcd8042c8a615f76cc2164530af7b6810b2298577db5085914c2b7edb042c8a61ff46053148130d7f302d42409855fdb7085914c27fcdc34010a614ff6e02164530cff330d00429857bdb4205914c33fccab4010a61bf654da008530cff172d42409855fdb7205914c2bfad88a4c8a617fa6c88548130dfb166d42409847fcba609914c2bfad890ac8a613fe2e95148130bfb36652a40985fb9b4295204c33dec934840a619fe2e991481308f7972d2042987f4953549204c23de5cb4840a61ff04853148130 else 0x615ff6e95264530bff174c1a409857fcba549914c3fbca92a6902615ff6e15264530bff174a9a40986ff9206a4214c33fecab5210a61ffa4859148130dff242d4240987fd931645204c3bf6512a4c8a61bfe2e99148130efdb04a9322986fed92688814c33fedcb4440a619ff289a954530cffb44d4aa29857fdba149914c2bfedc0a4c8a615ff6c45264530dff10ad42409857fcba605914c3ff490b2490261dfe6459248130eff152c92409867fda56a5214c39fec1302c8a619ff688a954530dff16ad42409857fdb5205914c37fccab4010a615ff6c88164530aff974a8b229857fdb8545914c2bfed9152a8a61bf7289a354530dfbb44d1aa2986fed82688514c3bfac0aa2c8a615ff6e05164530affb6428b229857fcba485914c2bfedaa42c8a613ff6e1a214530cffb72d10a2986ff8ba661204c3bfaa8a42c8a615ff6e02164530dff330d0042986ff9b8680214c3fec42a62902615ff6d42164530ffb30a98a40987fd8954c5204c3feccaa6290261ff62953148130affb74c0322987fd9a54c5204c2bfe5d300c8a613ff2e982545309ff974c92a2985ff9b0289514c2bfed8b00c8a617f76cca254530e7fb02c03229857fdba541914c3fec5aa6290261dfe6e19148130bf7b68512a2985efdb6289514c2bfedc944a8a61dfe6015064530affb7490322987fd9b54c5204c2bfe5d240c8a615ff6e12064530bff360c10a29857fdb5481914c27fe5d32a90a613ff2e98548530eff300903229877f950481914c2ffcdc15290261dfe660a948130affb72d42409877f8b96a1204c27fe5d324c0a61bfe2a1a848130bff36ad4240986ff9a56a1204c37fc52b50902619ff6a4a960530bff366d4240987fd8b36a1204c2ffcd8042c8a617f76cc2164530bff362d4240986ff9a16a1204c2fbeda842c8a61efe605a848130bff36a4c2409867fda2660914c3fec5d2629026177f6dc2164530bff3624c2409877f991261204c2ffcda950902616ff6e02164530bff36654240985ff9b12a1204c2feed98a2c8a613ff6c9a914530cffb24d48a2985ff9b0205914c37ee98b5228a617f76cc8164530dff240d48a2985ff9b9485204c2ffcdc2429026177f6dc8164530bff36a90a409857fdb9609104c3ff4c124290261ffa5492148130cffb6ad13229867fcb5689914c33fec2b44c8a619ff215a264530cffb02d13229867fd51689914c33fe90b44c8a619ff601a264530cffaa0d13229867fd20689914c33fed934ac8a619ff2c9a564530cffb04d2b229867fc82695914c33fec0b4ac8a619ff205a564530cffaa2d2b229867fc51695914c33fe90b4ac8a619ff085a564530cffaa0d2b229867fd20695914c33fed9350c8a61ff66e93148130cff964d43229867fd526a1914c33fe29350c8a619ff605a864530cffb00d43229867fd50) else (if i<3 then 0x62c2a40987ff9a1615204c3ffcc8b0a90261ffe6058548130fff3024aa40987ff8b8695204c3bfec2b44c8a61dff6c58564530fff370a8a40987ff985545204c3ffcd9aa290261dff6c98564530fff306a8a40987ff953545204c3ffcd92a290261dff6958564530fff304a8a40987ff952545204c3ffc992a290261dff6a18564530effb74c2b22986ffd816a1204c3ffc9894a90261ffe604a548130dffaa4d4902986ffd816a4814c37fe90b5240a61ffe6059548130fff2a4caa40987ff985655204c3ffca930088261dff4859864530dffaa4d4b02986ffd216a5814c3bfec0b30c8a61bff6d5a224530dffaa4d11229877fd52661914c3bfe90b2ac8a61dff6059564530effaa4ca9229877fd21649914c3bfec0b24c8a61dff6159264530dffb64d2922986ffd526a0914c3ffc98b0090261bff549a524530fff302c0240987ff982601204c2ffeda950c8a61dff6155264530aff974a8322985ff9b2261204c2ffcd930090261bfe601a524530defaa4d2922987bf981601204c33fec934a48a61ff64c58048130cffb2ad41229867fd926a0914c27fed934a48a61bfe601a824530dff262d42409857fdb8245914c2bfeda922c8a615ff6c89164530dff2a2d4240986fddb3694914c3bfcc032a48a615ff6c99564530cffb44ca9229857fdb2654914c2bfed9330c8a619ff6899864530dff300d1122986ff9206a5814c3ff8c0a6290261dfe4819864530ffb2a6c0220985ff9b54c5204c3dfcc0b0088261ff64c58044130bff37090220987fd953481104c37fc5d32a902617fe6e19548130eff330caa40985ff8ba4c5204c37fc9035240a617fe6c59548130eff322caa40986ff9806a4814c2bfeda950c8a615ff6c8a864530cffb50d2b229867fca8695914c33fe52b4ac8a617fe6e0a548130dff302d4240986ff9916a1204c2ffcd994a90261bfe6c5a848130bff36252a409867fd926a4814c27fed935240a615ff6e0a564530cffb5052b229857fdb2295914c33fedcb50902619ff6e98564530affb74c2b229857fcba615914c3ff8c0aa290261ffa6c95148130ffb366a8a40986ff9326a1204c2bfedd10ac8a615ff6c88564530affb6242b22986ff9826a1204c33fed4344c8a619ff2a1a264530cffb4ad13229867fca5689914c2ffc5d2a290261dfe2e5a548130dff174a8a40985ff8ba615204c2ffcd9b4a90261efe6098148130bff174c0a40985ff9b1695204c2ffcd890a90261fde545a548130affb70513229867fda8289914c2bfeda944c8a619ff694a264530cffb74c13229857fdba609914c2bfe5d304c8a61bfe649a848130dff366d4240985ff9b9215204c2ffcdd10a90261bf76cda508530defb2ad2842984ffdb9694214c2bfedd104c8a615ff6d48264530affb62413229867fdb9694214c33fedd2a4c8a else (if i<4 then 0xc5bc85a045810567c54885324513050ec4f884dc44c904afc4968492447c0465c44c8448442f0412c3f683da43c103aac38e837543590342c3298325431802f8c2d682bd429e0281c2658261425d0258c25482504237021ac21681fa41f601d6c1d281b641970174c17081544138011bc10580e940ca00a7c08e8078405c0042c032801940003ffcc0b22902617ff6e0a564530bffb6452b22985ffdb5289914c3ffccaa4290261ffe6612148130dffa42d48a2986ffd816a4514c2ffedc0a2c8a61ffe544a848130bffb6428b22987ff9a52a1204c3ffca913090261ffe6949848130fff302d4240987ff9536a1204c3ffcc1b5090261bff2a5a960530fff30ad4240985ffdb22a5814c2ffedd324c0a61ffe2a1a848130effb52c93029877fca9649814c3bfe49324c0a61ffd2c59260530bffb7449302986ffca9681814c2ffed9b40c0a61ffe604a948130effaa4903229877fd82481914c2ffedc34a90a61bff6a1a548530bffb6ad4a42986ffda56a5214c3bfecab5290a61bff6e98214530eff95090322987fdd3268d514c37fed132428a61bff6a5a254530dffb50d12a2985ffdb3689514c37fed1b44a8a61bff289a254530effb02a8322985ffdb8289514c37fed4144a8a61dff5495064530effb04a8322985ffdb3289514c3bfec0b00c8a61dff5498064530effb04c0322985ffdba609514c3bfe51300c8a61bff6a19154530ffeb02c8aa2987ff521645514c3bfea9242c8a61ffe6615248130dffb72d10a29877fd82485914c37fedc34428a61dff6152164530dffb30d10a29877fd52545914c3bfec12a2c8a61dff6155164530ffbb04d1aa29877fca8545914c3bfea9302c8a61dff6098164530effb0ad4a42986ffd856a5214c37fec0b5290a61dff6158164530fff30ac92409877fca5605914c3bfe5ab02c8a61bff605a954530dffa42d4aa29877fdb0549914c3bfe40aa4c8a61dff609a954530effa64d4aa29877fcb1549914c37fedab4440a61dff6c55264530effb04a9322987ff952645204c3bfea933048a61dff6895264530fff242c8a409877fda5549914c3bfe542a4c8a61bff615a908530dffb02d4842986ffd216a4214c3bfed42a4c8a61dff2e15264530fff2a4a9a409877fdb8549914c3ffcd0aa690261dff2e95264530fff342c1a409877fdba549914c3bfed8304c8a61dff1458264530effb62c13229877fd85609914c3bfe52b04c8a61dff6d58264530fff302d2a40987ff9ba605204c3ffca9b4a90261ffe6e58148130fff330c0a40987ff9b5605204c3ffcd9b0290261ffe60d8148130fff2a6c0a40987ff9b2605204c3ffcc930290261ffe6098148130fff306d2a40987ff952605204c3ffc9930290261ffe6e98548130fff174c2a40987ff985695204c3ffcdcb0a90261ffe6618548130fff3 else 0xec7bac6e6c6a2c53ec49ac456c382c27ec23ac106bfa2be6ebd6abc06ba72b96eb86ab796b6c2b5beb51ab4d6b402b29eb19ab066af32aeeead8aac56ab22aa1ea91aa816a6b2a5aea44aa376a332a1fea0fa9f969e629dbe9cea9be69ba29a9e996a98669822974e964a951693e2930e920a90d69092904e8f4a8ea68d728c6e8b6a8b268a22897e893a87d68702859e843a8306820281be80ea7fe67fa27f5e7f1a7de67ce27c0e7b3a7a66799278ee784a77a67702762e752a748673b2727e71aa70d66fa26e3e6d9a6cf66c226b1e6a4a69166842676e666a659664f264ae63aa62d661a2612e60ba5fb65ee25e0e5d3a5c965bc25b4e5aaa5a66599258ee584a574656a2559e549a53c652f2524e508a4f864e524d1e4cda4c964b324a2e48fa47964662452e442a432641f240be3f2a3df63c923bbe3a8a392637c2365e352a33c6326230fe2ffa2ef62dc22bfe2b5a29c6286226fe259a23a621e2201e1eba1cf61c521b7e1b3a1af61ab2191e187a17161552132e119a0fa60de20c7e0b1a0a1608b2071e05ba045602f2015dff99fe35fcd1fb9dfa39f9f5f861f69df659f4c5f301f16df009eea5ec51eb4de9b9e855e721e58de3f9e295e101df6ddd19dbb5da21d8bdd759d595d491d3bdd259d0f5cf91cf4dce79cce5caf1c95dc7c9c635c531c42dc269c105c001becdbd39bba5baa1b8adb719b495b331b19db069af65ae01acfdab99aa35a931a79da5d9a475a311a2cda1399fd59e419cdd9ba99b0598e1977d973995459501930d92c991058fa18d7d8ca98b1589b187ed86b98555851184cd830982c58281823d80797eb57d517bed7ba97a1579d1780d77c9763574d1736d71796fe56fa16f5d6d996bd5698167bd66896585654163dd6249608560415e4d5cb95b5559f158bd57895595543152fd51994f454db14bed4a89492547f146bd44c9430541a1406d3f693da53c113a4d385936f53561339d31792fe52e812c8d2b292a2529e1287d26e92555233121fd2099205520111ead1d191cd51b4119ad181916e516a1153d13d911e511a110cd0f690f250d610b6d0b290ae50aa10a5d092907950751058d039901d4ffe0feacfd18fac4f900f6dcf4b8f2f4f0d0eeacecb8ebb4ea50e8bce6f8e534e400e1dce198dfd4dea0dc7cda28d924d7f0d65cd3d8d244d020cdfccbd8ca14c910c8ccc888c754c5c0c45cc328c164bfd0be6cbc78bae4baa0b96cb928b704b5a0b43cb2d8b174b010aedcae98acd4ac90ac4cac08abc4ab80ab3caaf8aab4a9b0a81ca5f8a494a360a13c9fa89e149c809a2c98f896d495d094fc9368920490a08f0c8d488bb48b708b2c8ae88aa4891087dc867885a483e0824c80e87fb47e507cec7af8787476e0754c738871f46fd06ecc6d086b746a1068ac674865e4642062bc61585fc45e605e1))) else (if i<8 then (if i<6 then 0xeec0a00b0553a733b3a9636034681b1e69be02b07033681c51b206f12f11f012a139da00d1855ca9c6c081c678080b50664c2ae54e36a29c0560e0aa068912063611772af1bb07e0200f400581a218406c0b89000228a701380380ad8dac7b809d10010a008070040e7746dc4bc47c040689052c0d71783270006b70183046d1c9578dabb4896a60141c959ca9c65c6d45f8080d0eb47e3723faed225a980507038a36e23e25e0258772a385404302681438f48fc8a2bb63a2605d855c65c6c0d38080b4e070050e55c47c4bc040f47037e15914f19f1b587e02034458baac834f12f1180e04a1c448204c74e6762d434da2874bc05285c4a0690f8c00f51001c514e23744e020040034cd248ff0a826ebb4b9e9d711ea6489280a368da6e45388f5324a95d901440820761420b5a65a25c4bc46038a0a20a1763e25e2395901c3a18019e8a010b8f82ad8f701583b1b284503c2a0b5b3dc47225abe140799fd9e04d69797be25e23d5f9124e95624e4ef11e8484e18089ca8ced45388dcadc2403d081a02f46c01ee3dc04e0e00881170c8be3cf12f11aade888079c12314356e44b89788c170e05b8f2ec7c4b29cab7a232ae81140b9938fca7712e28688810caba00b653b14356da6f89645f44655d213533313009b2ecd2f32d8e932a902d94ed4fc79c50e25917d119574ca763cc89711aade888168c72016b5da4ab88f4e82331d0e043ab7c4b29dc472258a1a22240902dc79912e25e2394ed11094470a8246ade2848948bf12f11e88a40b5d8f89788e44a538100e05b29d8a1ab7225c4bc460b88114082d68003e0341007016024e4525646481a78966440c140a586c0651200ac0b5c46069c4bc0511ebd1480de2502832ae2318e01c402f54681901501a712f11f01046045a805c0aa628cca836c66e26e2000d202fc2b6c741a654043c4bc47c04911208890444822241112090a88c4880045a2380f01001a345c01002f809451c01c0607003d22241028d4f55be25e2391294ec79d1148890661e5380a353f1e789788e44b44645d42241e15028d5b54fe25e23912d119174810c4338fc28711c89712e8881a4a728128147451a0b45c15789788f809a0403d62241b85363e0d056c36e23384b4b3764dc1f1299901a711d3f70119509024129a0b45c15789788da0780803d206008d48f6bbc460d81007056a7fa7eb17e25e23332e0232a48be81801f807c06d9ef12f11c8a022a81f0cec08409b450def88f89650b8080d1604c069285a29c4bc466760808e1504dd76e23d3a91f039381051b2a748a712f1181a70103d2653a45f1e714244b89788c1e11a28e3f63dc0560e5077d76875874973e23d3a072401139d88a088395711b95b84a2d476d372d29ed1cad0f6d022cfdecf9acf56ceb2ce6ecdcaccf6cc82cb7eca7aca06c992c8b else (if i<7 then 0x572c765602b02d33f82c399712f11f0139524135cca0c8c5d8542300a9c03809c04159609a62ec2ae55054064c1bc4bc46e7a0acb73283260dc3672ae2370972b05a4b46b9941918bb0a846015712f11f010142d835448c5d855caa0a80c9c65e25e200a16e65064a24e5505586dc47c4bc040b4a021f1be25e020b5281402b024712f11f010019c0dc0a00e02d789788dd7400d00900acd680b0e2fc4bc46e52e54902d33260d61570002ae027010384824395711b9d33a85998121c5e05d855caa0a983789788dcf41596a24133261569d01772a72be237090564824328712f11b88801980a1449c5e05d855caa0a9e25e21c64121606ad3a664a24c2ae5505402fc4bc47c04050c021f19e23e020342b9938cb8d802701001980800a015814b89788f8080850090c1aa246541640700b406986c041c04e3ce0ed056052058732e25e2363c717402b399419306b8bc0be1b3807013808292c0a1cca0c9449c5e05d85789780b88c1496c1aa24e2f02ec2a654064e32f12f10050b69d51261532a017e25e23e02034482402d680434418144a822241a4932a71bb2bb0900f321839930ac8a38dd84d9582aa1c6e451856c26cac15403ce283492e3765761201e640d82233b914b2af1bb09b2b055498930a99538dd84d9582a807a0505a6cca9c6ecaec2403ce0aa86006205a676e586b2d03613656a0b1c50d5b917f19f1bd1102d409504087447c6c4811900b4c224106705a058020c755a391292a71ec745765ad1c8949578debb6a602c1d56e55f53fc640874440b4e13005ae3d23f2298e8286795754fd5b917f19d1102d38d1c4c4bb78dc8fea60169c6c388e44a47f5306bcc228102854fd5b912f19f1b917d11058488a045382224111208890445c222811140b8db8c807f010019402c02145f8940cf88f80802900a2493a2963e502a2fc05e33e3601c068b3a940d71271b719e02003399938cb8d807f01001980846396b8ea5c640d0cedc7953b808481601006a014a29e33e37c0400680335ad72a71971b514e020344199406a8bb8cb8d807f01001a00c00cc02a03605403d450c7dc0000dc078098676a29c4bc46e7a01e603003324972a021514e2333b72b70954e5f8df01383a8b80217895d741e80108b59b3de33e372292c7abe0b0825608b72a71971be020343e55c99712f11c893ae8019d6b367a4ca44bc67c6f57c0a10070e64cfdc46051c4aa2fc04e549037cab832812e25e2375d00340890444822241112081c018814340b96712aa73b2a00d5ca9c6f80ac1c010c838c2bc0563d60e81c2407e02b0743000f2406c0b99930af8df0158381a0022503603445e05ec7b80ac1dc7d0042240664e3760fc0401e7055b1e61571fb0740e31d4a06b9538df015838021c0d1ca9c6cccac1f808010e016240e240aa954c6d63c74f60 else 0x917f19f1b912d1102840890419a834854ca8ccbc66cf7c6c0e122b2121722a06b04de25e2300e00c4299712f11e06a8969e8019c020039c6f0378974f4150f956b3cc8e0e20abc4bc472c6ebb224a32ac19832a0d42ac29701038408904448241a42b677655e33e3662f6120ac9a9d43232a82ae23c29b2b030038482c4d665582965d038818712f11c8a4b1eafb38378558aa44bc67c6e6e757c1693a29e33e36a21c04068681733b60de2303828890556e45fc67c6e44b4440d0ec5522fe33e378f3a2210c0688021e23b4402d383732517e0272a4889040c40bc0840c00b5cb2d10d65539d95522922042bc4768881ae76038831251771971b00fe020033b9da06f11da27010040079ccaad8fc6788f808084ce54e36008e33c0401e6037112317215b6332af19f1be02028502c01ff12f11dae85885b1c45f89788f4f603803cc04281bc4bc47a7a62e01e7028332c32317c1721532a82ae25e02e23056602c60690af12f11e9e98b807a021b0cb05c0ab065c068378080b5266575d6e7633e377100507312815e23b4473be02004392b38ca8bb8df0101a18068c5f89788c90003cc04201857181bc5432262fc4ba7a01ea00e00c05821722ae25e23d3d00f4e0bc0ce0da151b1dc40169cc5c17bc67c6f8080d0de36010241c040065037112e1532af19f1be02a0d0344c0b90aa15016f12f11f0101a226b267b89788c0a34cad7691f449341a22442a655855c46632041c04050aa9bd2ae23d2b93bd090b73d4682c49dd96695c956848a0a205d8550a9c65c6cc5c0b78080d1253a86441aa24c2ae54e32e3675cf10068b987f19f1b02d910a49e020344524e8a78cf8dcc3f0101a1c0a30f32d08c9857453c6f897808169406fe33e36068c2bc0405a7117e02d0019204529950705cc6c0d0c648578080b4f42ae36068c2a654e33c0405a800304aa15e25e2340de0200f439959938bd8bd06c8950ac95680701680af05cc64c6c0b78080d0c16de33e36c2a069c0405a711208890705cc640b4c6c8578080d0f42a654e32e36c2bc04a280688112088c60bf8c80228a701380807a0c48ca815409b89788cc7c0390144a65664a25c4a143c460388e23b44517e02008004308904c7cca803822f894460190e0f4071655c4742bc4a0c8702631232a030028e25e23987e0231f508904cab808a3c084863e625c4a00730fc04230711208142d66cf49948978cf8deaf82c240a1caa4a96b24cb89788e44b57c1614224111208890445026546326372216120686914332030b2b31bb09910055408904cee452cabc6c0c2c26cae440155381b22f82b255a64025c4bc476ba050a43011011761571bb09914b2b0554a1841808819dd9538f584c8a59582aa82d5cabc6f8978080d0c0ac0b40cd86dc4bc47c04068804805651231705a05268d681066e2)) else (if i<9 then 0x5c47689c0522000871140e0a99518c98d81688bf0101a200d0c4945ecaac66c6e45f8080b522541037056373332e25e23e020bb401b81403318b995712f11f01001a4cc9c5ec5ccab89788f8080a100500900adc4bc47c040067056b17e25e230bbe02034381319d99502501868a01a711f12ca11d3f0131c6e05780846002caa2f02a654e32e3605bc040688312f19f1b33be026150033b8c816f0138db0a81a1808545305f88ccef89780803d0e65265225c46b472558e80b085a3912f1b92ad76d4c058381002b1b1995711f12f0105da015814b0d9c5f89788f8080d100cd86c62e654008068040677c460d9c4bc04c052615d14f19f1be020343cacf06da7540f8cdb2d9602922ccacaad3bc66cb2d940a0e0ad51b69dc4b6596ca176700b00300800fc1532a700701b3d4c06f11f12d9e8079788ecf402003c8e64c2ae32e52e360060087332b1732af19f1be02028399501a199712f11f0103d1c60c20aac8e0940064732b3231732ae25e23e02058405a81402b02d61b599712f11f0139528cc9caaca8c5f89788f80816100ac0b586d655c4bc47c040688021312e25e23040b3d02600f478d95ef010100169403789788ecf403ca01550266422e655c4b6596ca0629c1732a31b034319e0202d3d80d803aea8800214c48086c03808028460d82e65463605a42a633c040688a7e32ae25034332917e02118418960bf12b9e807940800dc0a0ca80e0d3b88f89780800d40500ac0a4e65c4bc47c0404280373ae34e332048c3603802006ce23317e25e02681402402b712f11f010019c0d10cb83691f89788ed74135162f655e33c476ba0686e25e23b5d06c0032b0ab8cb8d99501a7010169dc65c6c0b40700d0a655e33e3605b22fc04068732af19f1b02da7ee02034384a0c768881a890140d645dcab447c67c6d1900b5005129fab7225e33e3722fa220b09bb932af19f1b317b2905839b981c18bf12f11d9485d9c6f83c1bc2b22522fe33e37a2216a8e0de1504df1be02b070b5385ad9958b99578dd83f0101420028cab89788caf6d800c4e66462fc0563d60e0d86a15055021181402402b02961b1a705e03658f701583ac02cccb89788c0cf8080c4e22e102813272a92a912e25e23917d11058508a050c1451cc8ca9c6d442055cadc2415542281038034037c36317020b1ee02b07485b28870178cf8d83201a1c0d00800dccc8ca82c82d591ec79d76c1d723fa9895005a4e0de1591292af1bd4cd7605a4299606a89712f11e9e8019d855caa8ab03485f88f8974f41592665e3262f70b6960b06038e23034317e25b4b0bb38c884ca820cc66441a42a655e33e37c040709249091b048542c1ac2aa55055c46a77a13a560b4902d037647c32c19317c29b01038482d606b95035f11f12c071c00c12814788f80863803ce224154fd5b else (if i<10 then 0x4055033034a15201018bf01583900a0af68546069c0560e3c290370521826e148360f0a5c6c0dc148806e0cd85269c0a4506cb5d0341b8ce1485e0291305e856c65c6c0b4460d228010c2b6024055034b196152001816a8be0af015809800c0b545f056c6e453808e010095602300304ab01180182558db0a90caac6c02c0cc00ca010c2a0956024003c15729b1b02d118330ad8d825288100a0af6c658548240e33636a2000850c5b1b510004260bb8cb0a8f05c205182f42a6556325003517c15729200199928be0a81a5b29b055c6c40500622030517c15b65003298fb8d8251ac92037809c6e070805057b82fc4a40bb0587651e14b8d82903311c6c020467782a6b2300e0b8ce1485e02910af50540846677228c2a300f91400d719008285d82c5b28e03705585400c010a2fa241228e32a2e5021415045004238d85d82c5b2902edc6ed9468600a4455c52e3781a22502a05a9026021040b3b6362807a8a406b8d804013180842a0481c675300d0c254112a0801c8be0ad94b8d88c0169c0840d1c66ca545ca05091b22f82a655652608680dc1592aa2a7190343817a8bd94e9499501698085c6646f8080d0480ca2923616ee120425512b29d2971b32a2820c8a70138c81802d180c016b809c64c5e450c042664a2f254e33653a52068802f517b29d2951202d3295195594e94b8da890169f035c641220c0952f86ca25653a5262e6a9752ab29d2971b02d512386205d82f594e949a701a1c03270e453809c640c00d4e241229255c04e3303860c28aa89de290285100a83818406f0138c99948a01a9cc4b0578a5c6c5a00b4ca8e22f82ac2bc52654503016631f058e02281003358ce148241a718448856eba836dcec67c6ee200a135040aa006392ac15e25e23215034e0202d4031499712f017118510079c137809c780d6451c1e070e2d1a3382aa28e03c0401e701c93272a92a04804de25e2395907c501786144ec95711ba2288701007a5c5e45c0724a802f89656788c1892e65265c4a143c472b2038705c05a12ae02035e23e2591481c4f010058c90d85780800c0108224111208890400e05402c01389788dcf403d198206a01e30b540de2500bd59e230623c9928b995695089711f12f01014242881214aaca807016945d44b89788c1f1609182a65581bc47c4bc0409a8028332d3251792a112e25e23e02058529959948918b895712f11f0102c264cb8081bb89788e564070ec2b232a2822f237c040687004701e02a150032a8bd8cd8d98ba8a70101a1c2fe23745f46746cc7f80803d004d229e33e37c0542a0067d1712ad19c36701e0200f3e8be8ce8dc4ece07010079e45d4ab46746f0db80a4500d10067a55a33a3735b22911bc0406890bfd14f19f1b510e020343e0a98c98d81a08bf010169d45e45cca80b78080d0c62401 else 0x11408180b31b182c701140c04838080d08240061c04042414172902d91020a0816d84c8810448222411120801e0b8130c448382ec2ae323c15719055b1f238cd410b05dc6c462855450a0160aa066068c2a50b6615158df0108ccb05c0a28549c05a022d062e460502e02de02d0121950417a448c5dca6ca414b404fa036520d03317082f016e8df011012b80b4040b88c0a460102e02d868329e29d01301828a70138d8134880169c081c670a4168834eb8c06f85205062f41a5055841319e2931b02e230382ad8cf14b8da11411295017200840b6088c67424a0aae32045a12a76502f729b2953b2714838d23825100df809f241780a0a0b016381a31ac0d8ce9e80780710caac678a5c6d03a038158e190633c520b181a500eb19e29058615c0d328910bd8cf14807c0718628208c01981a655c5200601e7912a17e2971b00f40e319918b98ce1481a010182020cb0a400c0a0a019c520b181ac2a5052c2971ba0d32a286399941538ce14a1001a1c0dc14b0a6834ca8a0d781a633c5263606a4607037e0202102820ac840ba4c8ca9c6c03f4f4c01f26462ee120425004020112719c290383173810e0ad8c81a701090180be45357c785206e6540084041914e294c605a28ac840c050645016357ca090e3385204001e6766046832c2900303828ac8415002003f034816a0cc65567a0ac582a719c29b1b420038301b98be14d8d829195180bc99a8a416880bc0442cda12068502e02212a71bd0902d30ac84a0420cdc056360680ac5b01c2939e181700738d89569e8169803945045dc24084a0698520b560e0405512085881c02351485a968a42c41586a2414a804191f719e2991405a3e14d83802010100800dccaac670a4d38010e042240060e33c04068a2e704d332c0d719b29067304599958cf0101a14450363262fc0406840b5037e02b1906c28a704448222e1332317b1971be02034305a999583e1481014ea5c6545e854985360e178008))))
def xml11 : Packing := (598,4,8,0,0,16,0,xmd11)
def xmh11 (i : Nat) : Nat := (if i<1 then 0x6480eda758d810800006070c0416310b4018000000001818140bae12820900000280c4a6b15049a8046c0380000105ec88fac24800000000003b110104e324016e82908242008af021b839c011fc0e4000000002011d480df06ab22d7e1fc8ee6d042b1383c107e0c22154943dac040c12be0234d29c14696135016c7138d047b6096511c100c2c530e0ea70828bacac013cc19174f482e29d8d4600d09e903286219e017b0937895c00000000700b504940000204be05a00224c1600000e060d383391380000b0948000000000000e05f581e8823d40dc3773a029dc21f410db027481b34187c0d1302f2baac000061303168281c800000000000060185807400ebe0576825140f0205c3083f3119c0470ec90000722ac4210c057909880000c23e211b40032814340932112605078036c058222f702d3828f189a2067a010d8236e1f9e237f01b88453c4c4c056306210100089ca0cd00005bab6402ba04fe08d122cfc03f2066206059498409ae109a043000006865eccd007e23a0201a140e11012784b6059a0000f077c83d9c50144d28050c3978c101a028985a98507dd60010b712f1001d00f3c0f75022892f10054c111502d902bf42316ee4f11a2821d0090432800005c820000160d9507d08cb000000000e40a000028246000000002048a41fa0000c09c1bba09d5ce0190000480f402084036002cbccacc13da21490110c8340001a0dfe07f800028057a0cb801ff01f00001e073d0190816000000a3ea1442d0f8416300718002d0049c2680000774ed84dbcc28000000001800400000000000048bb1c0094e9a9646cb3d9c095812ad05bb84f94238e0dad0018bb854088080cd0568000000000000000000000000100abb0780000000000000021f4051600278c0a104d68349045ca0f540a1331ee81d1a00a60899035e81cc60cf472ed94a9d8f420b5d03a504325d68625fb5172c0ca413ee00fa16d800a40073e01d204ec8295828120d3a1543033b046bf04520516837b51bb605fe02a48264804e601400000000281fc000000001014c0000a0bc000030318899600000000000014214000000004b324000020dd00710000041380000c704084b0c01000003275f838c0001ac2aa03db9bd55a194cc7000050132d9ff0035267e2824acd5522569059dc2be4201c084f3515b8e5d8f9ac040093883539cc1c055c130200d0000000000001010e02090e070000002e3e250a1c0800000217000a4d0202190e08050e000701110300160107030a000a040119120001001e040200211a0003090c0303030102030a0a000a0201010011040000060302340609070b09070305001905000e0125001900050900091d05031315002407151203040000010b060e000f20120206080400092d020a02000300010100000d04130000000b010101 else 0x601c784ca81ace0d8207c1c11a00a54117d08b149fa5861a03cd477b822e5c16611d00007006f1c120002163c4823000008cef2078f83244e1580101072d1350c1b66075570050206c47380c5b04d800010232932d3012c83ed4034a088c47823a3fe5bb013fc0136024100dc000082587838084c9607d60998000399190e37007c800000001a101b18bcb9fb412a809800001b1ded081c07f00005810780160250a283eb13b0995c076412e00003c4d5c00e0000700fa81dc803b90643228099b1a1030000400c640d5602f165980002005da24fd03f104540001c106409ba89552418e50940563229ec204ce3630638000349bde0189055702a04153405164a2880cec25e601e4706f3310dd5e687c5074a8443d1dba0bf90324843b80ee00009035984ba48)
def xmd10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xcf9da36d0a254530ff498354d5248130c7bda96d0a254530ff493154d524813087fdc86c9a914530a7ddc8649a314530cfd9a36c0a2545308fddc32e992545308ff9c02e9825453087fdc92e98254530bfd1c12953148130ff49854855348130efc920689a354530afd9c32d5a848130afb9c42d5a848130aef9c62d5a848130ffc1314859248130b7e9c15499148130aff1c1215a848130f769515499148130e3f985601a908530e7d953601a908530a7f9c2601a908530afe9c2215a848130e3f981601a908530e7d931601a908530afd9c3215a84813087fdc86d5a908530afb9c4215a848130c7f9806d5a908530f7e1514859148130eed98054da608530e6f980655a608530a6fdc5661a608530e6dd53661a60853087fdc56c9a920530ef59806cda508530e75db3661a508530a77dc86e5a508530e779806e5a508530ef9953601a408530a7bdc8655a408530e7b980655a40853087fdc56c8a960530cf5d526cda524530cfd9806cda52453087fdc56c9a864530cbf9816e98048130cfd9316e9804813087fdc26e98064530ffc1b54853148130b7f1c12959148130c7dda56cc2164530c7bda56d02164530c77dca6d42164530c6fda56d82164530adf9c7215a848130fbd1a86053148130efd1a860531481309ef9c62e9534813087fcca6e15264530ff49325495348130cfd9b32e95148130ffc1526053148130ebe952605a848130ebf151605a848130ebf131605a848130c5fda56dc2164530c3fda56e02164530c7bda56d08164530a7f9c8655a008530c7f9b8655a008530cfd9b854da008530e7d99854da008530c7f9b12e5a848130e3f9812e5a848130c5fda56dc8164530c7f5a86c45264530d7e9916c88548130dfc9316c88548130afd9c12cda848130ebd9812cda84813087fdc52e98264530c7ed522e9826453087fdc02e98264530c7f5a26c48564530d7f1206c48564530afb9c42e951481308ff9c82e95148130cef9c62e951481309fd9c32e95148130cfb9c42e95148130cfd9c32e951481309ef9c62e951481309ef9c62e93148130cfd9532e951481309df9c72e93148130cff1812e95148130cfd9a86cca5481309fd9c16cca548130d7d9916cca5481308ff8ca6d53148130ffc1954853148130cfb9a86d0a548130d7b9916d0a5481308ff8cb545a848130df99316d0a548130a7bdc5649a420530c7f9b82e99148130c7f9b52e99148130e7e9522e99148130ff48ca54d5248130ff49b954d5248130ff48b954d5248130ff49a954d5248130ff48a954d5248130ff49c154d5248130ffc1a54853148130ff49a154d5248130ff499154d5248130ff498154d5248130ffc0ba4853148130ffc1c94853148130ffc1c54853148130ffc1854853148130c7f9a56c0216453097b8c96d0a548130bf49c154d5248130 else (if i<2 then 0xffd0956053148130ffd1a560531481309ff9c82e95348130ffd0b56053148130e7edba2895264530b7edc82895264530e7eda82895264530e7eda52895264530b7ecca6095264530ffd1a86053148130c7fd526e98064530c7fd816d5a908530e7f921601a908530e7f952601a908530f7e9815499148130f7e9855499148130f7e8b96455248130f7e8b85499148130f7e8c85499148130c7fda86c8a954530d7f5816c8a954530f7e8cb5499148130bfd9c82953148130ffc9b84855348130ffc9c84855348130ffc8ba48553481308ffdc82e99254530ffc8cb4855348130cff5812e99254530cff9a86c0a254530ffc9cb4855348130dff1816c0a254530cfdda86cca254530dfd5816cca254530ff698154d5248130cfbda86d0a254530ebf952601a824530c7fd816c8a954530cefda86d8a254530efd9854c5a848130c7fda86e4a254530c7fda26e4a254530d77d526e4a254530d7f5816e4a254530def9316d8a548130def9816d8a5481308ffdc82e99548530cff9802e99548530e77d5269598245308ffdc52e99260530c7fd952e99260530aff9c52a1a848130a7fdc26a4a960530c7fdb26a4a960530dfd9316d49848130a7fdc26959824530bfd9c52e93148130d7f9b56449848130df79516d4a848130dfd9316d4a8481309ff9c56c4a848130dff1516c4a848130b7f9c52e19148130a7fdc82d5a264530a7fccb615a264530a7fdc52c9a864530a7fccb549a864530e7ecb2549a864530e7f581545a920530a7fdc1549a920530e77d51549a920530b7f9c52a19148130b7f9c82d59148130e7f581545a908530ffe1814c55248130bfd9c12e95348130ffc9534c55248130ffc9216c55348130ff59525455348130ffd1815455348130bfd9c84855348130ffc9b24855348130ffc9824855348130b7f8cb5499148130ffc9834c55248130bfe9c54c55248130a7fdc1609a914530e3fd81609a914530bfe9c84c55248130e7f551605a914530b7f8cb6159148130f7e9216159148130bfe8ca6055248130bfe9c12e55248130efe8a86a15248130bfe9c32a15248130bfe9c12a15248130bfe9c52615248130bfe9c12615248130bfe8ca60d5248130b7f9c82959148130f7e8986455248130c7fcba6a59260530bfe9c82e55248130aef9c6215a848130a7f9c0609a914530afd9c0609a3145308fdccb609a314530afd8ca6c55348130bed9c62e95348130e7d531605a908530b7e9c22d59148130e7e920549a92053097f8cb6a19148130dfd1316c4a848130bed9c62e9314813087fdc92e98548530cef9a86d8a548130d6f9916d8a548130cfe9a26c18214530afd8ca6d53148130ded9316d8a548130afd8cb4c5a848130afd9c54c5a848130cedda36d8a254530c6fda96d8a254530e3f995601a824530ebd953601a824530 else 0xf525d3e74c0d253482d15b437d097413cfd33d5cedb3a4cde3359cc4f2e7cb572c3c9f726bc967247c86f209c7771cbc6b3180c5bb142c45b111c3ff0edc3070bcc243064c11700cbf4efa7bdeef42bc8eef7bafaeacb9cee3ab83ade2b70ed97b5aed3fb3e6ccdb286c8fb1c2c37b062bdfaf02baeae3eb70ad46b25ac4eae7ab56a9ca9f6a44a8969eca76a9c8a6a6997a5e2966a51e942a45a8eaa2fa89fa202854a0d68169f767be9e7e78d9dba7699d2a7119bfe6ed9b6e6c99a7668b99e665a98ee60297c25c4966254594324b9929e46e917242390123d88de234c8c4e2da8aba27588f221d87c61ab85fe16084d20ba81d20147f05f887da5f3d7c11e977979e2577b1dcd76b9d8275c1d377495d137405cd57271c8a71e1c667151c016fbdbb66e91b5e6c95aec6acda6068699e1666d95564098c9620d8165f757b15e157595d1d7015a8565b58215b5558955054f94eb53314864f613784d312df4a65253489d1e1463913b43d50af41a50303f74fa43d44f183b7ce993980e2736b4d743450cce3220c423024bd02e90b442c60aec2acca60289c9ee273c9a325a893e23788bf21e48331fe87c11dec7281aec641178458114504ce118440e0e843340a8025a081c1a704e80e701e8000f7e8a85499148130a7fdca2499260530b3fdc82499260530aefdc6289a254530afbdc4289a254530afddc3289a254530aff9c0289a2545309fdccb609a35453097fccb5498164530b5fdc72055264530b77dc52055264530b7bdc42055264530b7edc2205526453097fccb6a15264530c7fcba6e9526453097fdcb1458264530b3fdc81458264530b7edc21458264530aff8ca6c58548130aff8ca6e15148130aff8ca6cd5148130a7fcc9549a96053097fccb605956453097fccb6059264530af7dc8549a524530ef7980549a5245308ffdc86c9a524530dfb9816d0a548130c7fda86c99524530cff9b5601a224530e7f995601a224530dfd9816cca5481309ff9c82e93148130cff9822e95148130cff9532e951481309ff9c52e9314813097fdc56c8a864530d7ed526c8a864530a7fdc2295a564530dff1316c4a548130d3fd826e0a56453097fdc86c8a564530c7fda86c8a564530d7ed826c8a56453097fdc22e98564530c7fda22e98564530dfe9b86c95148130dfe9b36c95148130a7fdc52a1a264530a7fdc8295a2645309ff9c82e95148130cff9832e95148130cff9852e95148130aff9c82e95148130cff9b82e95148130cff9c82e95148130cff9b32e95148130ffd1856053148130cff9b22e95148130ef79522e95148130eff1812e95148130cff9a82e98548130ff7181545a548130c7fda86d4a26453097fdc52e982645309ff9c52e9834813097fdc82e95264530c7fda82e95264530c7fda52e95264530c7fda22e95264530)) else (if i<4 then 0x684195052241489046541009005c03201b0148160c32a0c120055d11016902281306985722594ee889729d9576adf4449917f12e55fa224f12e539a9fd112004805401b00c80a40b066ad983722594ee889401994ee8880849912c8bf897c47d112e53b225e236adf444a030306985722483fca71b225e25f11c170994ec89788e0b8d5b2803402401501500a403601902d23228f0780e000c9959f01000c7e25f11f808701c780803c6510080c803202900d8160a0313953c65e37110b848084f542f12f88ce77e022805d854c1960db0a40b0600bb0a9832c1b21480b4c0176153065836c290241a2ae119504009701f8cf80823000f3002c006200580cfc4be020189405004802b014806400d00900ab86d34ef016c7b60ed7893ca9e32f2978d81540427c06ecf401030058150006c0d0025c07689e024780ae017010078010a004001bcf6e0200f2801000604a1b0a983735361480b4a0522154c5fc4be23d889809ac17995788f67534c3644bc4be23e88e45ca051ca7644ba220282c14002b912ca77444be25aa7f44729c47990055e32f2978d80a0d61568a3c0401e4026b05e655e2399d6d30de25f11ed2e62e4f12ccabc051172303582b332f014ca8a04a324f80801e4f013c0401e0042003402401700a80a803202900d81212034d238119e0e4009085403202900daca806879997897c47e0299516665e2558bccabc0450077897c4644008614061914d9e802c9e25c06ecf42184d9e803c0063022e45301be25f11801401e7c06ecf421830136cf401e3da278080140042002c01403f806ecf42186f11f8082860042245301af01d9e93c0400f14cefc040031e50bc4b33bf011004de020018c2823123953c65e377090169e08000f14ced82f23f11200d0a13e0058012e7a10c2c0f267600800793255e23e9d40e4801778cbc6fc040342805de54f1978dbca4068601c008006fa36f8df809e0e0344002c01171f48b9857c05b1ed83802920347893ca9e37e02d8380d4e41c48b985763db07f010480e0217893ca9e36332d83f8080688e8a780b60e0342071401000a68a6c1fe37e02090000d072a78d80bee12f1901698066d141993ca9e37e02d8380d100340903ca9e36917d83f808042809010c006600a68a1c7c008003f013c01e02bf11dcaca2f70901795e6472a78cbc6ee1202d320c0e54c0db84bc67e3602e380c506002f01700b5e5972bb84a002ec2a60cb06d8520283007044f026e8a7894449e2301120042120b8ff80b63db0720700200089f9a7e30f87bde5f6b3d73f4ebd01f357cc3f2c7c9ff1cfc47f0a3bfcef77bbeeee7b9aedefb5cecc3b04eb2fa85e9339f9e703987e5a393ce4778f1e34b8b3e1eb84ee08b803df937b8ddff760dd0772fdc436fedb4b6a6da1f65bd8f361dd7fb5dfd7375bbd673570d4d else (if i<5 then 0x120a05c655c2918080655e021dc66e5220360163852318bf0a45c290360800080130804df1d164a7236219554aba52319554aba52301a844bc047192000d0c5e02b8ca070a058f0104640604007809844ed1478d8020cd2a98ccca46544037780923301c21ca9e522007800de3631956854416d70ac034603f8068800800a101b00b1e0218c9006e32af010ce2fb2958b8e676e3610c5deba20360163c04398bbca5e3671723d740d82db2ad384f290c035e36280684e64b32d948ce54b2ad948c6540261012807f00d1844e01a20058430500d78d8b22980d14034204a0c035e3220044035a2e3005802166500d23854202d189705c7332794bc6ce6440360ccb6ba3d0a840d832af010de52f1b13ca42f290a07181a2016bc64432ad0a88008101a3ca760e301bf80840345996c65e52f1b280d3632f291dd74211808161e3302980d8080a9120a45c2917080e202ef1b1c05c3117d83dca4603709cc802e290b9c5de36303584041e02b838ce7672a0040c0f1b0d0343d3d02500c060007817ba7a3206c855e363606bc64400fa06c8540064007b03642ef1b2485401fc0d1bc6c0080031c069e3600f02012038f19101a1e3606b1f8a4e3600f60710094120748a5e3600f210380b0f199149022e2179148c0192290078e676e361003c2d40081859ba120301c4c9a55d09181a466451778ceca4a058f0100c0606888bbca4632a09ca4e36258b9c5ee5371b2003a65420338160a33b29200100422a8b8782e0031000e6542013705c4003e0b8098603708198e55e021dd942732f11f8080404f015c784020f015c7ae32409560a4423038ce0a400844890702e10107808411208010006268a06a28b32101e3200aa8a0c0a85140078c0aa03338d8ce24f1911538e542399545fc0430109ca85514b0a88460058c149c6c98290168804271b10448354ebb2880712005088c9e02d839c48872a09c7c271f09c7c240e38f9c48600a0e05c311770a8ae5371b10cc8c2be02d8390654101681440683baee448068309f64532c6015bae8144c035005780800640058020067e250057808c11208080e77e0201a112281016805fc04034278080062f0100200083c9de56729d92ad9674afa12770af80801e3f12ccef285e022691da65b5d68910063e020018e677e02004003c8004025780801e4007800c5c0de9e800c6e2a70c986dc520212f88f2b20621e56403829b0f03400630900028e3ef1230abc6f60ef60010a5c54e1970d98a404250053451e88f1b09078080067019004803201b0148160de25f11e44babe4e9e800c5d3d0130178602d00aed740684019004802e02a00c806c05205841cefc040080079281a72ab84dcac9d3d017303406a4001803c4440007880a3e020078c2201206c05fc0570720ca829140a538200fe88800c6615e8880b4 else 0x405c2071d94946c006418b87633e29007e038801ad8c803c0804007e03442fb1922034c2a770d8c900a816fe068020832ac1570a465120944825)))
def xml10 : Packing := (326,5,8,0,0,14,0,xmd10)
def xmh10 (i : Nat) : Nat := 0x19e2010400010045e1000281100000000000000d065020d60edcec01351f000300eb026c13424000000000000001c21508b0805480000000102300025dc0000000306000690500000002c0b000380a2174000307140000031a0b03cd9f0525417205800077020105678000c23c000000141a602000000000000003802601d894f04acc00002cc2e2449dd607b405876f2136077c0cf06d003f05741f062cd80040c393000000600180030000001
def xmd9 (i : Nat) : Nat := 0x3820000061fc7420807020057c05d838dd140801018039f1b11034f8c8800028400078231e0b8c004205ba151f228140169141701a102227806889120fa221f80800f000c6a8806f01003c4007301a0040c10c0014400282182002c008f80bb0720015d8380063dc242004760e0018c004000c40023e00f8080064f37c8f0fb0e7798e1756d0f30c3eeeba6d6b46a29ce608fe2c89e067cde06c59e5f54e4b50c33ca02345e0f400c7dce23665d2a2902615fc8db7212154d204c37d9242e3174a9a409877f0549316c4a848130d7e4a9194daa62902617fc1d52e9214c5204c3d6b2a4a9b00d4122985fd2744b954d5248130bfa4e8994a9aa4902618fd9c86ccba545204c31f7370e2174a8a409863ee6c9c42e95148130c77ce438c5d2a2902618fb9c8710ba545204c31fb390e1974a8a409867bc605c62e95148130cf78c0b8c5d262902618fe952329b54c5204c39f6388c0974a8a409873f470d812e95148130e5f8c13025d2a290261cf598554cba545204c3c7a262c0b00d48429878d661553601a90853087ec6db8a98b5090261cbd131605ba601204c357a382c0966d42409863e66cdc42e95148130c75ce33885d2a2902618f99c470cba545204c2fc93ac652a6a9240985bd2369c154d5248130bf60eb17490a6290261af48da70553549204c35e9350e0aa6a9240986fd0605c154d5248130
def xml9 : Packing := (36,6,8,0,0,10,0,xmd9)
def xmh9 (i : Nat) : Nat := 0x21200000000000204002c020300160400000000611c48001
def xmd8 (i : Nat) : Nat := 0x834005100002000315f010008000c7f6d5564038bd1c870d812e95148130e3ac605c6710ba545204c38f9181711c32e951481308bd23b5a870553549204c3ab41a8605c154d5248130
def xml8 : Packing := (5,7,8,0,0,7,0,xmd8)
def xmh8 (i : Nat) : Nat := 0x34000000000000000
def xmd7 (i : Nat) : Nat := 0x3f80b7c077c0074ad03f5a8605c154d5248130
def xml7 : Packing := (1,8,8,0,0,0,0,xmd7)
def xmsamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc93c600104800f00033a821010a4040000e784c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x2a2c892948494384049443e911490019504944c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03000c538c42003890004200000001bf8e7a10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x1092049602b0045b1b60a410c4864fe48810a10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x26010014d0082046000004200913f9d3b00800001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0xd485220dd0e2184e48942ed2940800050c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0x30030208803b402c44c001474203e88004100600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x20332dc802e0524012408c02d4a45a41ad0a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0xe420804100c080000035552a400000400380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x15c05216b516ac3be92b30142a12a5a602b4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x9803c2203009310323fc888000806200200400f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x58336c48484301962402c12a02457c025168000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x4081c02844008188003000a440000c49003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x2d293b48ac4cfaa06402188b33303003372f56a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x6000c1040009050300540080910116000083ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3234891b2271ce6219369100569b283f8a287ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x10c09122032340a044c03882a448020403107fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1244c0335113050689bd4364084b803c40c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xmcolumns : List ColumnInfo := [(50816,0,51071,0,13),(50752,0,51135,0,13),(43536,0,44015,0,13),(260,8,227,16,6),(10,4,369,128,6),(59925,0,60394,0,7),(98,0,413,0,7),(53888,0,54143,0,13),(5,2,440,64,6),(47632,0,48111,0,13),(58373,0,58874,0,8),(40,256,151,64,6),(53282,0,53725,0,8),(49153,0,49662,0,12),(49177,0,49638,0,8),(34,1,460,16,6),(48132,0,48635,0,12),(6160,0,6639,0,13),(59906,0,60413,0,12),(69120,16,69606,9,10),(43010,0,43517,0,12),(3080,0,3575,0,12),(43080,0,43447,0,9),(27652,0,28155,0,12),(43330,0,43197,0,8),(44672,0,44927,0,13),(49172,0,49643,0,9),(1600,0,1983,0,13),(55321,0,55782,0,8),(0,0,511,0,15),(53824,0,54207,0,13),(58624,0,58623,0,12),(48292,0,48475,0,8),(4,8,227,272,7),(47641,0,48102,0,8),(43584,0,43967,0,13),(55344,0,55759,0,9),(43648,0,43903,0,13),(5,0,506,0,8),(50736,0,51151,0,9),(0,1,460,50,8),(13840,0,14319,0,13),(47872,0,47871,0,12),(47744,0,47999,0,13),(69184,0,69567,0,13),(2,1,460,48,7),(1,2,440,68,7),(69134,0,69617,0,7),(26649,0,27110,0,8),(69127,0,69624,0,7),(42528,0,42975,0,12),(43048,0,43479,0,8),(32,1,460,18,7),(1,32,94,384,7),(42504,0,42999,0,12),(63236,0,63227,0,8),(4,2,440,65,7),(52755,0,53228,0,8),(9344,0,9599,0,13),(47648,0,48095,0,12),(12305,0,12782,0,11),(49168,0,49647,0,13),(54784,16,55270,9,10),(8,16,486,1,9),(9,16,486,0,8),(64518,0,65017,0,9),(3076,0,3579,0,12),(36,128,347,0,8),(48256,0,48511,0,13),(29,0,482,0,5),(49412,0,49403,0,8),(55304,0,55799,0,12),(0,32,94,385,8),(47624,0,48119,0,12),(8,256,151,96,7),(12304,0,12783,0,13),(9232,0,9711,0,13),(2,4,369,136,7),(69124,0,69627,0,12),(6176,0,6623,0,12),(6145,0,6654,0,12),(54312,0,54743,0,8),(0,256,151,104,8),(2180,0,2427,0,11),(257,32,94,128,6),(8,4,369,130,7),(0,2,440,69,8),(68674,0,69053,0,11),(0,8,227,276,8),(69122,0,69629,0,12),(0,4,369,138,8),(6400,0,6399,0,12),(44572,0,45027,0,8),(55312,0,55791,0,13),(256,8,227,20,7),(7696,0,8175,0,13),(59920,0,60399,0,13),(44036,0,44539,0,12),(27673,0,28134,0,8),(46112,0,46559,0,12),(6169,0,6630,0,8),(69136,0,69615,0,13),(48928,0,48863,0,9),(281,0,230,0,5),(12098,0,11965,0,8),(59937,0,60382,0,9),(43104,0,43423,0,9),(55330,0,55773,0,8),(27,0,484,0,5),(55296,16,55782,9,10),(59649,0,59646,0,8),(49152,16,49638,9,10),(43072,0,43455,0,13),(326,0,185,0,5),(59922,0,60397,0,9),(44800,0,44799,0,12),(9240,0,9703,0,11),(9233,0,9710,0,11),(9376,0,9567,0,11),(53778,0,54253,0,9),(7700,0,8171,0,9),(6152,0,6647,0,12),(42764,0,42739,0,7),(18464,0,18911,0,12),(12313,0,12774,0,8),(1188,0,1371,0,8),(27656,0,28151,0,12),(27649,0,28158,0,12),(44932,0,44667,0,7),(69128,0,69623,0,12),(4616,0,5111,0,12),(27650,0,28157,0,12),(59908,0,60411,0,12),(12608,0,12479,0,11),(69123,0,69628,0,9),(4612,0,5115,0,12),(44560,0,45039,0,13),(44608,0,44991,0,13),(44546,0,45053,0,12),(42508,0,42995,0,9),(52739,0,53244,0,9),(69121,0,69630,0,12),(46244,0,46427,0,8),(42824,0,42679,0,8),(59923,0,60396,0,8),(12354,0,12733,0,11),(58690,0,58557,0,8),(11297,0,11742,0,9),(59939,0,60380,0,7),(13632,0,13503,0,11),(54786,0,55293,0,12),(52737,0,53246,0,12),(43650,0,43901,0,9),(68610,0,69117,0,12),(17408,128,17755,36,10),(44552,0,45047,0,12),(69254,0,69497,0,8),(47617,0,48126,0,12),(7936,0,7935,0,12),(11296,0,11743,0,12),(52897,0,53086,0,8),(13849,0,14310,0,8),(69145,0,69606,0,8),(9348,0,9595,0,11),(1792,0,1791,0,12),(73760,0,74207,0,12),(43008,64,43197,258,10),(59936,0,60383,0,12),(9241,0,9702,0,8),(52768,0,53215,0,12),(59905,0,60414,0,12),(7681,0,8190,0,12),(7684,0,8187,0,12),(42500,0,43003,0,12),(44548,0,45051,0,12),(4,128,347,32,9),(32,128,347,4,9),(35,0,476,0,7),(32,256,151,72,7),(44558,0,45041,0,7),(13825,0,14334,0,12),(256,32,94,129,7),(268,0,243,0,7),(59911,0,60408,0,7),(59972,0,60347,0,9),(13856,0,14303,0,12),(7688,0,8183,0,12),(42792,0,42711,0,7),(420,0,91,0,5),(47880,0,47863,0,9),(13826,0,14333,0,12),(296,0,215,0,7),(42752,0,42751,0,12),(6657,0,7166,0,12),(46090,0,46581,0,8),(3074,0,3581,0,12),(53025,0,52958,0,7),(68108,0,68595,0,9),(7705,0,8166,0,8),(48385,0,48382,0,8),(52898,0,53085,0,7),(4736,0,4991,0,13),(52992,0,52991,0,12),(52738,0,53245,0,12),(47649,0,48094,0,9),(18433,0,18942,0,12),(11265,0,11774,0,12),(38,128,345,0,5),(52752,0,53231,0,13),(52800,0,53183,0,13),(57,0,454,0,5),(47968,0,47775,0,8),(18435,0,18940,0,9),(16897,0,17406,0,12)]
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
  | 14 => lookupWord 12 47 6 12 4 4 xmh14
  | 13 => lookupWord 86 433 9 16 8 4 xmh13
  | 12 => lookupWord 332 1433 8 18 10 4 xmh12
  | 11 => lookupWord 154 553 8 17 9 4 xmh11
  | 10 => lookupWord 20 89 7 14 6 4 xmh10
  | 9 => lookupWord 3 17 5 11 3 4 xmh9
  | 8 => lookupWord 1 7 3 9 1 4 xmh8
  | _ => fun _ => none
def xm : Forest := ⟨1535,14,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem geomxm : graphValid xm (boundsBefore known511) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_14_0 : block xm 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_14 : block xm 14 0 1=true := sxm_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_0 : block xm 13 0 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_2 : block xm 13 2 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_13 : block xm 13 0 12=true := (@block_merge xm 13 0 2 10 sxm_13_0 sxm_13_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_0 : block xm 12 0 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_23 : block xm 12 23 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_59 : block xm 12 59 35=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_94 : block xm 12 94 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_130 : block xm 12 130 14=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_12 : block xm 12 0 144=true := (@block_merge xm 12 0 130 14 (@block_merge xm 12 0 94 36 (@block_merge xm 12 0 59 35 (@block_merge xm 12 0 23 36 sxm_12_0 sxm_12_23) sxm_12_59) sxm_12_94) sxm_12_130)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_0 : block xm 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_4 : block xm 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_40 : block xm 11 40 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_67 : block xm 11 67 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_103 : block xm 11 103 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_139 : block xm 11 139 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_175 : block xm 11 175 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_211 : block xm 11 211 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_247 : block xm 11 247 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_283 : block xm 11 283 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_319 : block xm 11 319 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_355 : block xm 11 355 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_391 : block xm 11 391 21=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_412 : block xm 11 412 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_448 : block xm 11 448 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_484 : block xm 11 484 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_520 : block xm 11 520 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_556 : block xm 11 556 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_592 : block xm 11 592 6=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_11 : block xm 11 0 598=true := (@block_merge xm 11 0 592 6 (@block_merge xm 11 0 556 36 (@block_merge xm 11 0 520 36 (@block_merge xm 11 0 484 36 (@block_merge xm 11 0 448 36 (@block_merge xm 11 0 412 36 (@block_merge xm 11 0 391 21 (@block_merge xm 11 0 355 36 (@block_merge xm 11 0 319 36 (@block_merge xm 11 0 283 36 (@block_merge xm 11 0 247 36 (@block_merge xm 11 0 211 36 (@block_merge xm 11 0 175 36 (@block_merge xm 11 0 139 36 (@block_merge xm 11 0 103 36 (@block_merge xm 11 0 67 36 (@block_merge xm 11 0 40 27 (@block_merge xm 11 0 4 36 sxm_11_0 sxm_11_4) sxm_11_40) sxm_11_67) sxm_11_103) sxm_11_139) sxm_11_175) sxm_11_211) sxm_11_247) sxm_11_283) sxm_11_319) sxm_11_355) sxm_11_391) sxm_11_412) sxm_11_448) sxm_11_484) sxm_11_520) sxm_11_556) sxm_11_592)
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
theorem sxm_10_146 : block xm 10 146 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_152 : block xm 10 152 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_188 : block xm 10 188 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_224 : block xm 10 224 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_260 : block xm 10 260 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_296 : block xm 10 296 30=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_10 : block xm 10 0 326=true := (@block_merge xm 10 0 296 30 (@block_merge xm 10 0 260 36 (@block_merge xm 10 0 224 36 (@block_merge xm 10 0 188 36 (@block_merge xm 10 0 152 36 (@block_merge xm 10 0 146 6 (@block_merge xm 10 0 110 36 (@block_merge xm 10 0 74 36 (@block_merge xm 10 0 38 36 (@block_merge xm 10 0 2 36 sxm_10_0 sxm_10_2) sxm_10_38) sxm_10_74) sxm_10_110) sxm_10_146) sxm_10_152) sxm_10_188) sxm_10_224) sxm_10_260) sxm_10_296)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_0 : block xm 9 0 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_14 : block xm 9 14 22=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_9 : block xm 9 0 36=true := (@block_merge xm 9 0 14 22 sxm_9_0 sxm_9_14)
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
theorem caseFB : Impossible false (graphGoal 1535) 14 (varsX 44031).toFinset :=
  index_root (g:=xm) (i:=0) rfl rfl (before_sound known511 valid511) geomxm tablesxm (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨u,k,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 44031 := by decide +kernel
  have er : inputs++[seed]=varsX 44031 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : fullOK 44031 [10, 64, 128, 5, 1, 128, 2, 4, 32] = true := by decide +kernel
  have g1 : graphGoal 44031=graphGoal 511 := by decide +kernel
  have g2 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have v1 : vars 44031=vars 511 := by decide +kernel
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

lemma foldl_wires_extends (gs : List Gate) (xs : List Bool) :
    ∃ ext, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs = xs ++ ext := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨ext, he⟩ := ih (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => xs.getD i false) :: ext, by
      simpa [List.foldl_cons, List.append_assoc] using he⟩

theorem solve_3089 (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hsz : C.size = 14) :
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ edge x := by
  by_contra h
  have h' : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) = edge x := by
    intro x
    by_contra hne
    exact h ⟨x, hne⟩
  let g0 : Gate := ⟨GateOp.or, [0, 3]⟩
  let C' : Circuit := ⟨g0 :: C.gates, C.output⟩
  have hf' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [g0], by simp [g0]⟩
    · exact hf g hg
  have hstep : ∀ y : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) = (y 0 || y 3) := by
    intro y
    simp [g0, GateOp.eval]
  have hfirst : ∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = (y 0 || y 3) := by
    intro y
    have hw : C'.wires (List.ofFn y) =
        C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn y ++ [y 0 || y 3]) := by
      change (g0 :: C.gates).foldl _ (List.ofFn y) = _
      rw [List.foldl_cons, hstep y]
    rw [hw]
    obtain ⟨ext, he⟩ := foldl_wires_extends C.gates (List.ofFn y ++ [y 0 || y 3])
    rw [he, List.getD_append _ _ _ _ (by simp)]
    simp
  have hfun : PEqualNP.MetaComplexity.circuitFun 9 C' = edge := by
    funext y
    change (C'.wires (List.ofFn y)).getD C'.output false = edge y
    have hw : C'.wires (List.ofFn y) = C.wires (List.ofFn y ++ [y 0 || y 3]) := by
      change (g0 :: C.gates).foldl _ (List.ofFn y) = _
      rw [List.foldl_cons, hstep y]
      rfl
    rw [hw]
    exact h' y
  have hb := bound C' hf' hfirst hfun
  have hsz' : C'.size = 15 := by simp [C', Circuit.size] at *; omega
  omega

end PEqualNP.Outside.L_meta_3089

theorem PEqualNP.Outside.L_meta_3089 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = (1 : ℕ) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  intro x1 C hf hsz _ _ _ _ _
  exact PEqualNP.Outside.L_meta_3089.solve_3089 C hf hsz
