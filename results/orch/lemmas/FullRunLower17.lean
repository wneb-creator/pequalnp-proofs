import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_2592.SignedFloor

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


end PEqualNP.Outside.L_meta_2592.SignedFloor

namespace PEqualNP.Outside.L_meta_2592

def structuralEdge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def structuralRotate : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]

def structuralExchange : Fin 10 → Fin 10 := ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3]

lemma structural_rotate_edge (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralRotate) = structuralEdge x := by
  dsimp [structuralEdge, structuralRotate, Function.comp_def]
  ac_rfl

lemma structural_exchange_edge (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralExchange) = structuralEdge x := by
  dsimp [structuralEdge, structuralExchange, Function.comp_def]
  ac_rfl

lemma structural_rotate_bijective : Function.Bijective structuralRotate := by decide

lemma structural_exchange_bijective : Function.Bijective structuralExchange := by decide

def structuralExtend (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, b]

def structuralDeletedEdge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

lemma structural_cofactor_false (x : Fin 9 → Bool) :
    structuralEdge (structuralExtend x false) = structuralDeletedEdge x := by
  simp [structuralEdge, structuralExtend, structuralDeletedEdge]

lemma structural_cofactor_true (x : Fin 9 → Bool) :
    structuralEdge (structuralExtend x true) =
      (x 4 || x 7 || x 6 ||
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 8 ||
        x 8 && x 5 || x 5 && x 0) := by
  cases h4 : x 4 <;> cases h6 : x 6 <;> cases h7 : x 7 <;>
    simp [structuralEdge, structuralExtend, h4, h6, h7, Bool.or_assoc,
      Bool.or_comm, Bool.or_left_comm, Bool.and_comm]

def structuralNeighbor : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]

lemma structural_each_input_essential : ∀ i : Fin 10,
    structuralEdge (fun j => decide (j = structuralNeighbor i)) = false ∧
    structuralEdge (fun j => decide (j = i ∨ j = structuralNeighbor i)) = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma structural_independence_number :
    ∀ x : Fin 10 → Bool, structuralEdge x = false →
      (Finset.univ.filter fun i => x i = true).card ≤ 4 := by
  decide +kernel

lemma structural_iterate_edge (n : ℕ) (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralRotate^[n]) = structuralEdge x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc, structural_rotate_edge, ih]

def structuralExponent : Fin 10 → ℕ := ![1, 4, 2, 0, 3, 1, 2, 3, 4, 0]

def structuralMove (v : Fin 10) : Fin 10 → Fin 10 :=
  if v.val < 5 then structuralExchange ∘ structuralRotate^[structuralExponent v]
  else structuralRotate^[structuralExponent v]

lemma structural_move_last : ∀ v : Fin 10, structuralMove v 9 = v := by decide

lemma structural_move_bijective (v : Fin 10) : Function.Bijective (structuralMove v) := by
  unfold structuralMove
  split
  · exact structural_exchange_bijective.comp (structural_rotate_bijective.iterate _)
  · exact structural_rotate_bijective.iterate _

lemma structural_move_edge (v : Fin 10) (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralMove v) = structuralEdge x := by
  unfold structuralMove
  split
  · rw [← Function.comp_assoc, structural_iterate_edge, structural_exchange_edge]
  · exact structural_iterate_edge _ _

def structuralPoint (k : Fin 11) : Fin 10 → Bool :=
  fun i => decide (k.val = i.val + 1)

def structuralSetPair (x : Fin 10 → Bool) (p q : Fin 10) (a b : Bool) : Fin 10 → Bool :=
  Function.update (Function.update x p a) q b

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma structural_pair_cofactors : ∀ p q : Fin 10, p ≠ q → ∀ a b c d : Bool,
    (a, b) ≠ (c, d) → ∃ k : Fin 11,
      structuralEdge (structuralSetPair (structuralPoint k) p q a b) ≠
        structuralEdge (structuralSetPair (structuralPoint k) p q c d) := by
  decide +kernel

lemma structural_no_funnel (p q : Fin 10) (hpq : p ≠ q) :
    ¬ ∃ a b : Bool, ∀ x : Fin 10 → Bool,
      structuralEdge (structuralSetPair x p q (!a) b) =
        structuralEdge (structuralSetPair x p q a (!b)) ∧
      structuralEdge (structuralSetPair x p q a (!b)) =
        structuralEdge (structuralSetPair x p q (!a) (!b)) := by
  rintro ⟨a, b, h⟩
  obtain ⟨k, hk⟩ := structural_pair_cofactors p q hpq (!a) b a (!b) (by cases a <;> simp)
  exact hk (h (structuralPoint k)).1

lemma structural_independent_four :
    structuralEdge (fun i => decide (i = 0 ∨ i = 2 ∨ i = 8 ∨ i = 9)) = false := by decide

lemma structural_set_pair_left (x : Fin 10 → Bool) (p q : Fin 10) (hpq : p ≠ q)
    (a b : Bool) : structuralSetPair x p q a b p = a := by
  simp [structuralSetPair, Function.update_of_ne hpq]

lemma structural_set_pair_right (x : Fin 10 → Bool) (p q : Fin 10)
    (a b : Bool) : structuralSetPair x p q a b q = b := by
  simp [structuralSetPair]

lemma structural_bool_collision : ∀ g : Bool → Bool → Bool,
    ∃ a b c d : Bool, (a, b) ≠ (c, d) ∧ g a b = g c d := by decide

lemma structural_no_binary_factor (p q : Fin 10) (hpq : p ≠ q)
    (g : Bool → Bool → Bool) (H : (Fin 10 → Bool) → Bool → Bool)
    (hH : ∀ (x : Fin 10 → Bool) (a b z : Bool),
      H (structuralSetPair x p q a b) z = H x z) :
    ¬ ∀ x : Fin 10 → Bool, structuralEdge x = H x (g (x p) (x q)) := by
  intro h
  obtain ⟨a, b, c, d, hne, heq⟩ := structural_bool_collision g
  obtain ⟨k, hk⟩ := structural_pair_cofactors p q hpq a b c d hne
  apply hk
  rw [h, h, structural_set_pair_left _ _ _ hpq, structural_set_pair_right,
    structural_set_pair_left _ _ _ hpq, structural_set_pair_right, hH, hH, heq]

end PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592.FullRun

open PEqualNP.Outside.L_meta_2592.SignedFloor

lemma kept_mem {R : Type} {w a : Wire R} {k : Bool} {xs : List (Wire R)}
    (h : w ∈ kept k a xs) : w = a ∨ w ∈ xs := by
  cases k <;> simp_all [kept]

lemma comb_apply_eq {R : Type} (d : Nat) (a b : Wire R) (x y : R)
    (ha : a x = a y) (hb : b x = b y) : comb d a b x = comb d a b y := by
  unfold comb combine inv
  split_ifs <;> simp_all

lemma run_agree {R : Type} {u : Bool} {goal : Wire R} {s : Nat} {ws : List (Wire R)}
    (h : Run u goal s ws) (x y : R) (hx : ∀ w ∈ ws, w x = w y) : goal x = goal y := by
  revert hx
  induction h using Run.ind with
  | stop => intro hx; exact hx goal (by simp)
  | perm p _ ih =>
    intro hx
    exact ih (fun w hw => hx w (p.mem_iff.mp hw))
  | @two s a b rest d hd ka kb _ ih =>
    intro hx
    apply ih
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact comb_apply_eq d a b x y (hx a (by simp)) (hx b (by simp))
    · rcases kept_mem hw with rfl | hw
      · exact hx _ (by simp)
      · rcases kept_mem hw with rfl | hw
        · exact hx _ (by simp)
        · exact hx w (by simp [hw])

lemma first_keeps_left {u : Bool} {s d : Nat} {ka kb : Bool}
    (p q : Fin 10) (hpq : p ≠ q) (rest : List (Wire (Fin 10 → Bool)))
    (hrest : ∀ w ∈ rest, ∀ (x : Fin 10 → Bool) (a b : Bool),
      w (structuralSetPair x p q a b) = w x)
    (h : Run u structuralEdge s
      (comb d (fun x => x p) (fun x => x q) ::
        kept ka (fun x => x p) (kept kb (fun x => x q) rest))) : ka = true := by
  cases ka with
  | true => rfl
  | false =>
    exfalso
    let z : Bool := decide (d = 1 ∨ d = 2)
    obtain ⟨k, hk⟩ := structural_pair_cofactors p q hpq false z true z (by simp)
    apply hk
    apply run_agree h
    intro w hw
    simp only [kept, Bool.false_eq_true, ite_false] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · by_cases h0 : d = 0
      · subst d
        simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
          structural_set_pair_right]
      · by_cases h1 : d = 1
        · subst d
          simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
            structural_set_pair_right]
        · by_cases h2 : d = 2
          · subst d
            simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
              structural_set_pair_right]
          · simp [comb, combine, inv, z, h0, h1, h2,
              structural_set_pair_left _ _ _ hpq, structural_set_pair_right]
    · rcases kept_mem hw with rfl | hw
      · simp [structural_set_pair_right]
      · rw [hrest w hw, hrest w hw]

end PEqualNP.Outside.L_meta_2592.FullRun

namespace PEqualNP.Outside.L_meta_2592.FullRun

open PEqualNP.Outside.L_meta_2592.SignedFloor

lemma first_keeps_right {u : Bool} {s d : Nat} {ka kb : Bool}
    (p q : Fin 10) (hpq : p ≠ q) (rest : List (Wire (Fin 10 → Bool)))
    (hrest : ∀ w ∈ rest, ∀ (x : Fin 10 → Bool) (a b : Bool),
      w (structuralSetPair x p q a b) = w x)
    (h : Run u structuralEdge s
      (comb d (fun x => x p) (fun x => x q) ::
        kept ka (fun x => x p) (kept kb (fun x => x q) rest))) : kb = true := by
  cases kb with
  | true => rfl
  | false =>
    exfalso
    let z : Bool := decide (d ≠ 0 ∧ d ≠ 2)
    obtain ⟨k, hk⟩ := structural_pair_cofactors p q hpq z false z true (by simp)
    apply hk
    apply run_agree h
    intro w hw
    simp only [kept, Bool.false_eq_true, ite_false] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · by_cases h0 : d = 0
      · subst d
        simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
          structural_set_pair_right]
      · by_cases h1 : d = 1
        · subst d
          simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
            structural_set_pair_right]
        · by_cases h2 : d = 2
          · subst d
            simp [comb, combine, inv, z, structural_set_pair_left _ _ _ hpq,
              structural_set_pair_right]
          · simp [comb, combine, inv, z, h0, h1, h2,
              structural_set_pair_left _ _ _ hpq, structural_set_pair_right]
    · rcases kept_mem hw with rfl | hw
      · simp [structural_set_pair_left _ _ _ hpq]
      · rw [hrest w hw, hrest w hw]

lemma first_keeps_both {u : Bool} {s d : Nat} {ka kb : Bool}
    (p q : Fin 10) (hpq : p ≠ q) (rest : List (Wire (Fin 10 → Bool)))
    (hrest : ∀ w ∈ rest, ∀ (x : Fin 10 → Bool) (a b : Bool),
      w (structuralSetPair x p q a b) = w x)
    (h : Run u structuralEdge s
      (comb d (fun x => x p) (fun x => x q) ::
        kept ka (fun x => x p) (kept kb (fun x => x q) rest))) : ka = true ∧ kb = true :=
  ⟨first_keeps_left p q hpq rest hrest h, first_keeps_right p q hpq rest hrest h⟩

end PEqualNP.Outside.L_meta_2592.FullRun

namespace PEqualNP.Outside.L_meta_2592.FullRun

open PEqualNP.Outside.L_meta_2592.SignedFloor

def retRaw (n : Nat) : List (Wire (Fin n → Bool)) := List.ofFn fun i => fun x => x i

lemma ret_raw_injective (n : Nat) : Function.Injective (fun i : Fin n => fun x : Fin n → Bool => x i) := by
  intro i j h
  have hji : j = i := by
    simpa using (congrFun h (fun k => decide (k = i))).symm
  exact hji.symm

lemma ret_raw_nodup (n : Nat) : (retRaw n).Nodup :=
  List.nodup_ofFn.mpr (ret_raw_injective n)

noncomputable def retMoveEquiv (p : Fin 10) : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective (structuralMove p) (structural_move_bijective p)

noncomputable def retProjection (p : Fin 10) (x : Fin 9 → Bool) : Fin 10 → Bool :=
  fun i => structuralExtend x false ((retMoveEquiv p).symm i)

lemma ret_projection_zero (p : Fin 10) (x : Fin 9 → Bool) : retProjection p x p = false := by
  have hp : (retMoveEquiv p).symm p = 9 := by
    apply (retMoveEquiv p).injective
    rw [Equiv.apply_symm_apply]
    exact (structural_move_last p).symm
  unfold retProjection
  rw [hp]
  rfl

lemma ret_projection_goal (p : Fin 10) :
    restrictRows (retProjection p) structuralEdge = structuralDeletedEdge := by
  funext x
  change structuralEdge (retProjection p x) = structuralDeletedEdge x
  calc
    structuralEdge (retProjection p x) =
        structuralEdge (retProjection p x ∘ structuralMove p) :=
      (structural_move_edge p (retProjection p x)).symm
    _ = structuralEdge (structuralExtend x false) := by
      congr 1
      funext i
      change structuralExtend x false ((retMoveEquiv p).symm ((retMoveEquiv p) i)) = _
      rw [Equiv.symm_apply_apply]
    _ = structuralDeletedEdge x := structural_cofactor_false x

lemma ret_extend_cast (x : Fin 9 → Bool) (i : Fin 9) :
    structuralExtend x false i.castSucc = x i := by
  fin_cases i <;> rfl

lemma ret_raw_available (p i : Fin 10) :
    Available true (retRaw 9) (restrictRows (retProjection p) (fun x => x i)) := by
  classical
  let j := (retMoveEquiv p).symm i
  by_cases hj : j = 9
  · right
    left
    refine ⟨false, ?_⟩
    funext x
    change structuralExtend x false j = false
    rw [hj]
    rfl
  · have hjlt : j.val < 9 := by
      have hjten := j.isLt
      have hjne : j.val ≠ 9 := by
        intro he
        apply hj
        exact Fin.ext he
      omega
    let j9 : Fin 9 := ⟨j.val, hjlt⟩
    have heq : restrictRows (retProjection p) (fun x => x i) = fun x => x j9 := by
      funext x
      change structuralExtend x false j = x j9
      exact ret_extend_cast x j9
    left
    rw [heq]
    exact List.mem_ofFn.mpr ⟨j9, rfl⟩

lemma ret_projection_constant (p : Fin 10) :
    Constant (restrictRows (retProjection p) (fun x => x p)) := by
  refine ⟨false, ?_⟩
  funext x
  exact ret_projection_zero p x

lemma ret_comb_constant {R : Type} (d : Nat) (bank : List (Wire R)) (a b : Wire R)
    (hc : Constant a) (ha : Available true bank a) (hb : Available true bank b) :
    Available true bank (comb d a b) := by
  unfold comb
  split_ifs
  · exact from_constant false (Or.inl hc) ha hb
  · exact from_constant true (Or.inl hc) ha hb
  · exact from_constant false (Or.inl hc) ha (avail_inv rfl hb)
  · exact from_constant false (Or.inl (inv_constant hc)) (avail_inv rfl ha) hb

lemma ret_deleted_nonconstant : ¬ Constant structuralDeletedEdge := by
  rintro ⟨b, hb⟩
  have h0 := congrFun hb (fun _ => false)
  have h1 := congrFun hb (fun i => decide (i = 0 ∨ i = 1))
  have he := h0.trans h1.symm
  simpa [structuralDeletedEdge] using he

lemma ret_rest_invariant (p q : Fin 10) (rest : List (Wire (Fin 10 → Bool)))
    (hp : ((fun x => x p) :: (fun x => x q) :: rest).Perm (retRaw 10)) :
    ∀ w ∈ rest, ∀ (x : Fin 10 → Bool) (a b : Bool),
      w (structuralSetPair x p q a b) = w x := by
  have hn := hp.nodup_iff.mpr (ret_raw_nodup 10)
  have hn1 := (List.nodup_cons.mp hn).1
  have hn2 := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  intro w hw x a b
  have hm : w ∈ retRaw 10 := hp.mem_iff.mp (by simp [hw])
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  have hip : i ≠ p := by
    intro h
    subst i
    exact hn1 (List.mem_cons_of_mem _ hw)
  have hiq : i ≠ q := by
    intro h
    subst i
    exact hn2 hw
  simp [structuralSetPair, Function.update_of_ne hip, Function.update_of_ne hiq]

lemma fullRun_lower17_of_deleted_lower
    (H : ∀ (p : Nat) (bank : List (Wire (Fin 9 → Bool))),
      Reach true (retRaw 9) p bank → Available true bank structuralDeletedEdge → 15 ≤ p) :
    ∀ k : Nat, Run true structuralEdge k (retRaw 10) → 17 ≤ k := by
  intro k h
  cases k with
  | zero =>
    have hl := h.length_eq
    simp [retRaw] at hl
  | succ k =>
    obtain ⟨d, ka, kb, a, b, rest, hd, hp, ht⟩ := h
    have ha : a ∈ retRaw 10 := hp.mem_iff.mp (by simp)
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
    have hb : b ∈ retRaw 10 := hp.mem_iff.mp (by simp)
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hb
    have hn := hp.nodup_iff.mpr (ret_raw_nodup 10)
    have hpq : p ≠ q := by
      intro he
      subst q
      exact (List.nodup_cons.mp hn).1 (by simp)
    have hka := first_keeps_left p q hpq rest (ret_rest_invariant p q rest hp) ht
    have ht' : Run true structuralEdge k
        (comb d (fun x => x p) (fun x => x q) :: (fun x => x p) ::
          kept kb (fun x => x q) rest) := by
      simpa [kept, hka] using ht
    have hall : ∀ w ∈ retRaw 10,
        Available true (retRaw 9) (restrictRows (retProjection p) w) := by
      intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact ret_raw_available p i
    have hs : supply true (retRaw 9)
        ((comb d (fun x => x p) (fun x => x q) :: (fun x => x p) ::
          kept kb (fun x => x q) rest).map (restrictRows (retProjection p))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [restrict_comb]
        exact ret_comb_constant d _ _ _ (ret_projection_constant p)
          (ret_raw_available p p) (ret_raw_available p q)
      · apply hall
        apply hp.mem_iff.mp
        rcases List.mem_cons.mp hv with rfl | hv
        · simp
        · rcases kept_mem hv with rfl | hv
          · simp
          · simp [hv]
    have hl := projected_bound (rows := retProjection p) ht'
      (by rw [ret_projection_goal]; exact ret_deleted_nonconstant)
      (p := 0) (roots := retRaw 9) (bank := retRaw 9) (L := 15)
      Reach.start hs (by
        intro j bank hj hv
        rw [ret_projection_goal] at hv
        exact H j bank hj hv)
    have hc : cost (restrictRows (retProjection p) (fun x => x p)) = 1 := by
      simp [cost, ret_projection_constant p]
    simp only [List.map_cons, mass_cons, hc] at hl
    omega

end PEqualNP.Outside.L_meta_2592.FullRun
