import Mathlib.Tactic
import ExistingMonoNineSlim

namespace PEqualNP.Outside.L_meta_2590_aux.MonoNine
open PEqualNP.CircuitLowerBounds

def orbitWire (i : Fin 9) : Sig := inputs.getD i.val zero

theorem orbitWireMem (a : Sig) : a ∈ inputs ↔ ∃ i : Fin 9, orbitWire i = a := by
  rw [← input_list, List.mem_ofFn]
  rfl

def orbitEssentialRows (i : Fin 9) : Row × Row :=
  ([(3,2),(3,1),(6,2),(12,4),(24,8),(33,1),(66,2),(132,4),(264,8)] :
    List (Row × Row)).getD i.val (0,0)

theorem orbitEssentialChecked : ∀ i : Fin 9,
    witnessB graph inputs (orbitWire i) (orbitEssentialRows i) = true := by decide +kernel

theorem orbitAllInputs {u k s} (run : Live u graph k s) (raw : ∀ a ∈ s, a ∈ inputs) :
    s = inputs.toFinset := by
  ext a
  constructor
  · exact fun ha => List.mem_toFinset.mpr (raw a ha)
  · intro ha
    obtain ⟨i,rfl⟩ := (orbitWireMem a).mp (List.mem_toFinset.mp ha)
    obtain ⟨p,n,diff,isolated⟩ := witnessB_sound (orbitEssentialChecked i)
    exact raw_required run inputs (orbitWire i) raw p n diff isolated

namespace Extended
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
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

def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 1024
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

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
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


def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def initial : List Sig := pins
def first : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def assign (r : Row) (j : Fin 10) := bit r (pins.getD j.val zero)
def f10 (x9 : Fin 10 → Bool) := (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowInputs : ∀ r : Row, initial.map (bit r) =
    List.ofFn (assign r) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowTarget : ∀ r : Row, bit r target = f10 (assign r) := by decide +kernel

theorem realize (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ initial := by
  have legal : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have nonot : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (mono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates initial).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (initial.map (bit r))).getD C.output false = _
    rw [rowInputs]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=false) (execute C.gates initial) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates initial legal (u:=false) (fun _ => nonot) hp
    (out.resolve_right (fun h => h hp))
  have ns : initial.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  refine ⟨k,S,?_,run,hs⟩
  exact hk.trans (List.countP_le_length)

theorem first_needed {k S} (run : Live false target k S) (raw : ∀ a ∈ S, a ∈ initial) : first ∈ S := by
  have hd : bit 96 target ≠ bit 608 target := by decide +kernel
  obtain ⟨a,ha,hchange⟩ := live_row_difference run hd
  have stable : initial.all (fun a => (bit 96 a == bit 608 a) || (a == first)) = true := by decide +kernel
  have chk := List.all_eq_true.mp stable a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha
end Extended
def embed (r : Row) : Extended.Row := ⟨r.val, by have := r.isLt; omega⟩
def projected (a : Extended.Sig) : Sig := a.setWidth 512

theorem observe_projected (a : Extended.Sig) :
    restrictRows embed (Extended.observe a) = observe (projected a) := by
  funext r
  simp [restrictRows,embed,Extended.observe,Extended.bit,observe,bit,projected,
    BitVec.getLsbD_setWidth,r.isLt]

theorem graph_proper : proper graph := by unfold proper; decide +kernel

theorem monoNineFloor (monoRoot : Impossible false graph 15 inputs.toFinset) : Lower false inputs graph 16 := by
  intro k bank path hit
  have plain : plainWord graph = true := by decide +kernel
  have init : inputs.all plainWord = true := by decide +kernel
  obtain ⟨j,S,hj,run,raw⟩ := reach_live graph_proper plain init path hit
  rw [orbitAllInputs run raw] at run
  by_contra! small
  exact monoRoot j (by omega) run

def canonicalExtra (j : Fin 2) (d : Fin 4) : Extended.Sig :=
  Extended.bin d.val (Extended.pins.getD 0 Extended.zero)
    (Extended.pins.getD (j.val + 1) Extended.zero)

def canonicalWitnessA (j : Fin 2) (d : Fin 4) : Extended.Row :=
  if d.val = 0 ∨ d.val = 3 then 16 else if j.val = 0 then 128 else 48

def canonicalWitnessB (j : Fin 2) (d : Fin 4) : Extended.Row := canonicalWitnessA j d + 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalWitness : ∀ (j : Fin 2) (d : Fin 4),
    Extended.bit (canonicalWitnessA j d) Extended.target ≠ Extended.bit (canonicalWitnessB j d) Extended.target ∧
    (Extended.pins ++ [canonicalExtra j d]).all (fun a =>
      (Extended.bit (canonicalWitnessA j d) a == Extended.bit (canonicalWitnessB j d) a) ||
      (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalProjects : ∀ (j : Fin 2) (d : Fin 4),
    (Extended.pins ++ [canonicalExtra j d]).all (fun a =>
      (projected a == zero) || inputs.contains (projected a)) = true := by decide +kernel

lemma firstNeededCanonical (j : Fin 2) (d : Fin 4) {k S}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [canonicalExtra j d]) : Extended.first ∈ S := by
  obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run (canonicalWitness j d).1
  have chk := List.all_eq_true.mp (canonicalWitness j d).2 a (raw a ha)
  simp only [Bool.or_eq_true, beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma suffixSeventeen (monoRoot : Impossible false graph 15 inputs.toFinset) (j : Fin 2) (d : Fin 4) {k S}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [canonicalExtra j d]) : 17 ≤ k := by
  classical
  have hfirst := firstNeededCanonical j d run raw
  let front := Extended.first :: (S.erase Extended.first).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> simp [front, ha, hfirst]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  have supplyRoots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (canonicalProjects j d) a
      (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true, beq_iff_eq] at hh
    rcases hh with hz | hm
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 16) (same ▸ monoNineFloor monoRoot)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac]
  omega


end PEqualNP.Outside.L_meta_2590_aux.MonoNine


namespace PEqualNP.Outside.L_meta_2590_aux

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9),
   (5,7), (7,9), (9,6), (6,8), (8,5)]

def petersenAdjacent (a b : Fin 10) : Prop :=
  (a,b) ∈ petersenEdges ∨ (b,a) ∈ petersenEdges

def pairSecond (a b : Fin 10) : Fin 10 :=
  if (a,b) ∈ petersenEdges ∨ (b,a) ∈ petersenEdges then 1 else 2

def pairMove : Fin 10 → Fin 10 → Fin 10 → Fin 10 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
      ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
      ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]],
    ![![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5]],
    ![![2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
      ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
      ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
      ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
      ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
      ![2, 7, 9, 4, 3, 1, 5, 6, 0, 8]],
    ![![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7],
      ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5]],
    ![![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
      ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![4, 0, 5, 7, 9, 3, 1, 8, 2, 6],
      ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
      ![4, 9, 7, 2, 3, 0, 6, 5, 1, 8],
      ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1],
      ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5]],
    ![![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 0, 4, 3, 8, 7, 1, 9, 2, 6],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![5, 8, 6, 1, 0, 7, 3, 9, 2, 4],
      ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 7, 9, 4, 0, 8, 2, 6, 3, 1]],
    ![![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
      ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
      ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2],
      ![6, 8, 5, 0, 1, 9, 3, 7, 4, 2],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2]],
    ![![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
      ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
      ![7, 2, 3, 4, 9, 5, 1, 8, 0, 6],
      ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8],
      ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 9, 6, 1, 2, 5, 4, 8, 0, 3],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![7, 5, 8, 3, 2, 9, 0, 6, 4, 1],
      ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8]],
    ![![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
      ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
      ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7],
      ![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 5, 7, 2, 3, 6, 0, 9, 1, 4],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![8, 6, 9, 4, 3, 5, 1, 7, 0, 2]],
    ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma pairMove_properties : ∀ a b : Fin 10, a ≠ b →
    pairMove a b 0 = a ∧ pairMove a b (pairSecond a b) = b ∧
    Function.Bijective (pairMove a b) ∧
    ∀ i j : Fin 10, petersenAdjacent (pairMove a b i) (pairMove a b j) ↔
      petersenAdjacent i j := by
  unfold petersenAdjacent
  decide +kernel

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma edgeFunction_edges (x : Fin 10 → Bool) : edgeFunction x = true ↔
    ∃ e ∈ petersenEdges, x e.1 = true ∧ x e.2 = true := by
  simp [edgeFunction, petersenEdges, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

lemma edgeFunction_adjacent (x : Fin 10 → Bool) : edgeFunction x = true ↔
    ∃ i j : Fin 10, petersenAdjacent i j ∧ x i = true ∧ x j = true := by
  rw [edgeFunction_edges]
  constructor
  · rintro ⟨⟨i,j⟩, he, hi, hj⟩
    exact ⟨i,j,Or.inl he,hi,hj⟩
  · rintro ⟨i,j,he,hi,hj⟩
    rcases he with he | he
    · exact ⟨(i,j),he,hi,hj⟩
    · exact ⟨(j,i),he,hj,hi⟩

lemma edgeFunction_pairMove (a b : Fin 10) (hne : a ≠ b) (x : Fin 10 → Bool) :
    edgeFunction (fun i => x (pairMove a b i)) = edgeFunction x := by
  obtain ⟨_,_,hbij,hadj⟩ := pairMove_properties a b hne
  apply Bool.eq_iff_iff.mpr
  rw [edgeFunction_adjacent,edgeFunction_adjacent]
  constructor
  · rintro ⟨i,j,he,hi,hj⟩
    exact ⟨pairMove a b i,pairMove a b j,(hadj i j).mpr he,hi,hj⟩
  · rintro ⟨i,j,he,hi,hj⟩
    obtain ⟨i,rfl⟩ := hbij.2 i
    obtain ⟨j,rfl⟩ := hbij.2 j
    exact ⟨i,j,(hadj i j).mp he,hi,hj⟩

end PEqualNP.Outside.L_meta_2590_aux


namespace PEqualNP.Outside.L_meta_2590_aux.RowEncoding

abbrev Row := Fin 1024
abbrev Sig := BitVec 1024

def position : Fin 10 → Fin 10 := ![9,7,5,8,6,4,2,0,3,1]
def variableAt : Fin 10 → Fin 10 := ![7,9,6,8,5,2,4,1,3,0]

lemma variableAt_position : ∀ j : Fin 10, variableAt (position j) = j := by decide +kernel
lemma position_variableAt : ∀ j : Fin 10, position (variableAt j) = j := by decide +kernel

def decode (r : Row) (j : Fin 10) : Bool :=
  (BitVec.ofFin r : BitVec 10).getLsbD (position j).val

def encode (x : Fin 10 → Bool) : Row :=
  let word : BitVec 10 :=
    (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 10 => x (variableAt j)))).cast List.length_ofFn
  word.toFin

lemma decode_encode (x : Fin 10 → Bool) : decode (encode x) = x := by
  funext j
  simp only [decode, encode, BitVec.ofFin_toFin, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [Fin.isLt, dite_true, Option.getD_some]
  change x (variableAt (position j)) = x j
  rw [variableAt_position]

lemma encode_decode : ∀ r : Row, encode (decode r) = r := by
  decide +kernel

lemma decode_injective : Function.Injective decode :=
  Function.LeftInverse.injective encode_decode

lemma encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

def move (p : Fin 10 → Fin 10) (r : Row) : Row := encode (fun j => decode r (p j))

lemma decode_move (p : Fin 10 → Fin 10) (r : Row) (j : Fin 10) :
    decode (move p r) j = decode r (p j) := by
  rw [move,decode_encode]

lemma move_injective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Injective (move p) := by
  intro r s h
  apply decode_injective
  funext j
  obtain ⟨j,rfl⟩ := hp j
  have hh := congrArg (fun t => decode t j) h
  simpa only [decode_move] using hh

lemma move_surjective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Surjective (move p) :=
  ((Fintype.bijective_iff_injective_and_card (move p)).mpr
    ⟨move_injective p hp, rfl⟩).2

def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val

def table (f : Row → Bool) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

lemma bit_table (f : Row → Bool) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]

lemma bit_ext {a b : Sig} (h : ∀ r, bit r a = bit r b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact h ⟨j,hj⟩

def transform (p : Fin 10 → Fin 10) (a : Sig) : Sig :=
  table (fun r => bit (move p r) a)

lemma bit_transform (p : Fin 10 → Fin 10) (a : Sig) (r : Row) :
    bit r (transform p a) = bit (move p r) a := bit_table _ _

lemma transform_injective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Injective (transform p) := by
  intro a b h
  apply bit_ext
  intro r
  obtain ⟨r,rfl⟩ := move_surjective p hp r
  have hh := congrArg (bit r) h
  simpa only [bit_transform] using hh

lemma transform_zero (p : Fin 10 → Fin 10) : transform p 0 = 0 := by
  apply bit_ext
  intro r
  rw [bit_transform]
  simp [bit]

lemma transform_one (p : Fin 10 → Fin 10) :
    transform p (BitVec.allOnes 1024) = BitVec.allOnes 1024 := by
  apply bit_ext
  intro r
  rw [bit_transform]
  unfold bit
  rw [BitVec.getLsbD_allOnes,BitVec.getLsbD_allOnes]
  simp

lemma bit_and (a b : Sig) (r : Row) : bit r (a &&& b) = (bit r a && bit r b) := by
  simp [bit]

lemma bit_or (a b : Sig) (r : Row) : bit r (a ||| b) = (bit r a || bit r b) := by
  simp [bit]

lemma bit_not (a : Sig) (r : Row) : bit r (~~~a) = !(bit r a) := by
  simp [bit,r.isLt]

lemma transform_and (p : Fin 10 → Fin 10) (a b : Sig) :
    transform p (a &&& b) = transform p a &&& transform p b := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_and,bit_and,bit_transform,bit_transform]

lemma transform_or (p : Fin 10 → Fin 10) (a b : Sig) :
    transform p (a ||| b) = transform p a ||| transform p b := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_or,bit_or,bit_transform,bit_transform]

lemma transform_not (p : Fin 10 → Fin 10) (a : Sig) :
    transform p (~~~a) = ~~~transform p a := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_not,bit_not,bit_transform]

end PEqualNP.Outside.L_meta_2590_aux.RowEncoding

namespace PEqualNP.Outside.L_meta_2590_aux.MonoNine
open PEqualNP.CircuitLowerBounds
lemma map_live {u : Bool} {T : Extended.Sig} {k : ℕ} {S : Finset Extended.Sig}
    (h : Extended.Live u T k S) (φ : Extended.Sig → Extended.Sig)
    (hinj : Function.Injective φ) (hz : φ Extended.zero = Extended.zero)
    (ho : φ Extended.one = Extended.one)
    (hbin : ∀ d a b, φ (Extended.bin d a b) = Extended.bin d (φ a) (φ b)) :
    Extended.Live u (φ T) k (S.image φ) := by
  have hproper : ∀ a, Extended.proper a → Extended.proper (φ a) := by
    intro a ha
    constructor
    · intro he
      exact ha.1 (hinj (he.trans hz.symm))
    · intro he
      exact ha.2 (hinj (he.trans ho.symm))
  induction h using Extended.Live.ind with
  | stop hp =>
      simpa only [Finset.image_singleton] using Extended.Live.stop (u := u) (hproper T hp)
  | @binary k U a b d hd ha hb hab hf tail ih =>
      simp only [Finset.image_insert]
      apply Extended.Live.binary hd (hproper a ha) (hproper b hb)
        (fun he => hab (hinj he))
      · intro he
        have hm : φ (Extended.bin d a b) ∈
            (insert a (insert b U)).image φ := by
          simpa only [Finset.image_insert, hbin] using he
        obtain ⟨v, hv, hvEq⟩ := Finset.mem_image.mp hm
        exact hf (hinj hvEq ▸ hv)
      · simpa only [Finset.image_insert, hbin] using ih

lemma first_binary_split (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    ∃ (k : ℕ) (U : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      k + 1 ≤ C.size ∧ d < 2 ∧ a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      Extended.Live false Extended.target k (insert (Extended.bin d a b) U) ∧
      ∀ v ∈ U, v ∈ Extended.initial := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  cases k with
  | zero =>
      obtain ⟨rfl, hp⟩ := run
      have hmem := raw Extended.target (by simp)
      have hn : Extended.target ∉ Extended.initial := by decide +kernel
      exact False.elim (hn hmem)
  | succ k =>
      obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩ := run
      have hd2 : d < 2 := by
        rcases hd with hd | ⟨hu, hd⟩
        · exact hd
        · exact Bool.noConfusion hu
      exact ⟨k, U, a, b, d, hk, hd2, raw a (by simp), raw b (by simp), hab,
        tail, fun v hv => raw v (by simp [hv])⟩

lemma binary_floor18_of_suffix
    (suffix : ∀ (k : ℕ) (S : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      d < 2 → a ∈ Extended.initial → b ∈ Extended.initial → a ≠ b →
      Extended.Live false Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin d a b]) → 17 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  obtain ⟨k, U, a, b, d, hk, hd, ha, hb, hab, tail, raw⟩ := first_binary_split C legal computes
  have floor : 17 ≤ k := by
    apply suffix k (insert (Extended.bin d a b) U) a b d hd ha hb hab tail
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact List.mem_append_left _ (raw v hv)
  omega

end PEqualNP.Outside.L_meta_2590_aux.MonoNine
namespace PEqualNP.Outside.L_meta_2590_aux.MonoNine

open PEqualNP.Outside.L_meta_2590_aux PEqualNP.CircuitLowerBounds

abbrev inputPin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma assign_decode : ∀ (r : Extended.Row) (j : Fin 10),
    Extended.assign r j = RowEncoding.decode r j := by decide +kernel

lemma pin_mem (j : Fin 10) : inputPin j ∈ Extended.pins := by
  have hlen : Extended.pins.length = 10 := by decide +kernel
  have hi : j.val < Extended.pins.length := by omega
  simp only [inputPin,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

lemma member_pin {a : Extended.Sig} (ha : a ∈ Extended.pins) :
    ∃ j : Fin 10, inputPin j = a := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
  have hlen : Extended.pins.length = 10 := by decide +kernel
  let j : Fin 10 := ⟨i,by omega⟩
  refine ⟨j,?_⟩
  simp only [inputPin,j,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    Option.getD_some,he]

lemma transform_pin (p : Fin 10 → Fin 10) (j : Fin 10) :
    RowEncoding.transform p (inputPin j) = inputPin (p j) := by
  apply RowEncoding.bit_ext
  intro r
  rw [RowEncoding.bit_transform]
  change Extended.assign (RowEncoding.move p r) j = Extended.assign r (p j)
  rw [assign_decode,assign_decode,RowEncoding.decode_move]

lemma transform_bin (p : Fin 10 → Fin 10) (d : ℕ) (a b : Extended.Sig) :
    RowEncoding.transform p (Extended.bin d a b) =
      Extended.bin d (RowEncoding.transform p a) (RowEncoding.transform p b) := by
  unfold Extended.bin
  split_ifs <;> simp only [RowEncoding.transform_and,RowEncoding.transform_or,
    RowEncoding.transform_not]

lemma transform_target (p : Fin 10 → Fin 10)
    (hp : ∀ x : Fin 10 → Bool, edgeFunction (fun j => x (p j)) = edgeFunction x) :
    RowEncoding.transform p Extended.target = Extended.target := by
  apply RowEncoding.bit_ext
  intro r
  rw [RowEncoding.bit_transform]
  change Extended.bit (RowEncoding.move p r) Extended.target = Extended.bit r Extended.target
  rw [Extended.rowTarget,Extended.rowTarget]
  have hm : Extended.assign (RowEncoding.move p r) = fun j => Extended.assign r (p j) := by
    funext j
    rw [assign_decode,assign_decode,RowEncoding.decode_move]
  rw [hm]
  exact hp (Extended.assign r)

lemma canonical_second (a b : Fin 10) : pairSecond a b = 1 ∨ pairSecond a b = 2 := by
  unfold pairSecond
  split <;> simp

lemma suffix_of_canonical
    (canonical : ∀ (j : Fin 2) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig),
      Extended.Live false Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.pins ++ [canonicalExtra j d]) → 17 ≤ k)
    (a b : Fin 10) (hne : a ≠ b) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig)
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ++ [Extended.bin d.val (inputPin a) (inputPin b)]) :
    17 ≤ k := by
  classical
  obtain ⟨hzero,hsecond,hbij,hadj⟩ := pairMove_properties a b hne
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (pairMove a b) hbij
  let j : Fin 2 := if pairSecond a b = 1 then 0 else 1
  have hj : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin 10) = pairSecond a b := by
    rcases canonical_second a b with h | h <;> simp [j,h]
  have ea : e.symm a = 0 := by
    apply e.injective
    simpa [e] using hzero.symm
  have eb : e.symm b = ⟨j.val + 1, by have := j.isLt; omega⟩ := by
    rw [hj]
    apply e.injective
    simpa [e] using hsecond.symm
  have hp : ∀ x : Fin 10 → Bool,
      edgeFunction (fun i => x (e.symm i)) = edgeFunction x := by
    intro x
    have hh := edgeFunction_pairMove a b hne (fun i => x (e.symm i))
    change edgeFunction (fun i => x (e.symm (e i))) =
      edgeFunction (fun i => x (e.symm i)) at hh
    simpa only [Equiv.symm_apply_apply] using hh.symm
  let φ : Extended.Sig → Extended.Sig := RowEncoding.transform e.symm
  have moved := map_live run φ (RowEncoding.transform_injective e.symm e.symm.surjective)
    (RowEncoding.transform_zero e.symm) (RowEncoding.transform_one e.symm)
    (transform_bin e.symm)
  have ht : φ Extended.target = Extended.target := transform_target e.symm hp
  rw [ht] at moved
  apply canonical j d k (S.image φ) moved
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have hr := raw w hw
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i,rfl⟩ := member_pin hr
    apply List.mem_append_left
    change RowEncoding.transform e.symm (inputPin i) ∈ Extended.pins
    rw [transform_pin]
    exact pin_mem _
  · have he : w = Extended.bin d.val (inputPin a) (inputPin b) := by simpa using hr
    rw [he]
    apply List.mem_append_right
    change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈
      [canonicalExtra j d]
    rw [transform_bin,transform_pin,transform_pin,ea,eb]
    simp only [List.mem_singleton]
    rfl

lemma suffix_of_canonical_with_extra {L : ℕ} (condition : Fin 4 → Prop)
    (canonical : ∀ (j : Fin 2) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig),
      condition d → Extended.Live false Extended.target k S → canonicalExtra j d ∈ S →
      (∀ v ∈ S, v ∈ Extended.pins ++ [canonicalExtra j d]) → L ≤ k)
    (a b : Fin 10) (hne : a ≠ b) (d : Fin 4) (hd : condition d) (k : ℕ) (S : Finset Extended.Sig)
    (run : Extended.Live false Extended.target k S)
    (hasExtra : Extended.bin d.val (inputPin a) (inputPin b) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ++ [Extended.bin d.val (inputPin a) (inputPin b)]) :
    L ≤ k := by
  classical
  obtain ⟨hzero,hsecond,hbij,hadj⟩ := pairMove_properties a b hne
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (pairMove a b) hbij
  let j : Fin 2 := if pairSecond a b = 1 then 0 else 1
  have hj : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin 10) = pairSecond a b := by
    rcases canonical_second a b with h | h <;> simp [j,h]
  have ea : e.symm a = 0 := by
    apply e.injective
    simpa [e] using hzero.symm
  have eb : e.symm b = ⟨j.val + 1, by have := j.isLt; omega⟩ := by
    rw [hj]
    apply e.injective
    simpa [e] using hsecond.symm
  have hp : ∀ x : Fin 10 → Bool,
      edgeFunction (fun i => x (e.symm i)) = edgeFunction x := by
    intro x
    have hh := edgeFunction_pairMove a b hne (fun i => x (e.symm i))
    change edgeFunction (fun i => x (e.symm (e i))) =
      edgeFunction (fun i => x (e.symm i)) at hh
    simpa only [Equiv.symm_apply_apply] using hh.symm
  let φ : Extended.Sig → Extended.Sig := RowEncoding.transform e.symm
  have moved := map_live run φ (RowEncoding.transform_injective e.symm e.symm.surjective)
    (RowEncoding.transform_zero e.symm) (RowEncoding.transform_one e.symm)
    (transform_bin e.symm)
  have ht : φ Extended.target = Extended.target := transform_target e.symm hp
  rw [ht] at moved
  apply canonical j d k (S.image φ) hd moved
  · have hx : φ (Extended.bin d.val (inputPin a) (inputPin b)) ∈ S.image φ :=
      Finset.mem_image.mpr ⟨_,hasExtra,rfl⟩
    change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈ S.image φ at hx
    rw [transform_bin,transform_pin,transform_pin,ea,eb] at hx
    exact hx
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hr := raw w hw
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i,rfl⟩ := member_pin hr
      apply List.mem_append_left
      change RowEncoding.transform e.symm (inputPin i) ∈ Extended.pins
      rw [transform_pin]
      exact pin_mem _
    · have he : w = Extended.bin d.val (inputPin a) (inputPin b) := by simpa using hr
      rw [he]
      apply List.mem_append_right
      change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈
        [canonicalExtra j d]
      rw [transform_bin,transform_pin,transform_pin,ea,eb]
      simp only [List.mem_singleton]
      rfl


lemma monotone_eighteen (monoRoot : Impossible false graph 15 inputs.toFinset) (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  apply binary_floor18_of_suffix _ C legal computes
  intro k S a b d hd ha hb hab run raw
  obtain ⟨ia,rfl⟩ := member_pin ha
  obtain ⟨ib,rfl⟩ := member_pin hb
  have hne : ia ≠ ib := fun he => hab (congrArg inputPin he)
  exact suffix_of_canonical (fun j d k S run raw => suffixSeventeen monoRoot j d run raw)
    ia ib hne ⟨d,by omega⟩ k S run raw

end PEqualNP.Outside.L_meta_2590_aux.MonoNine
