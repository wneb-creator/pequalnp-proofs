import PEqualNP.Defs

-- Profiling copy of benoitrazet public PR12184, commit23cfcb8f020d4c1dfbf6b54a16284e8f1a932234.
-- Source: https://github.com/open-goat/pequalnp-proofs/pull/12184
-- Original Apache-2.0 attribution and proof declarations are retained unchanged.

-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670.Projection
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
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 6 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 6) := by decide +kernel
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

theorem raw_modes (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ u k S, k ≤ (if u then 14 else 15) ∧ Live u graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph=false := by decide +kernel
  rw [nrm_id pg] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates inputs legal mono graph_proper targetIn
  have ns : inputs.all plainWord=true := by decide +kernel
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
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
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
def g15samples : Array (Bits × Bits) := #[((-0x1b8b8d),0x173652),((-0x168581),0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
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
def spanChecks (g : Forest) (k : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | i, (n,a,d)::xs => cells g k i n a 0 d ∧ spanChecks g k (i+n) xs

theorem spansBlock (g : Forest) (k i : Nat) (xs : List (Nat × Nat × Nat))
    (ok : spanChecks g k i xs := by
      simp only [spanChecks,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals first | exact True.intro | decide +kernel) :
    block g k i (xs.map Prod.fst).sum = true := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n,a,d⟩ := x
    exact block_merge (cellsBlock ok.1) (ih (i+n) ok.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact spansBlock g15 3 0 [(1,4,0)]
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
def g31samples : Array (Bits × Bits) := #[((-0x2ea2e99cf4d8d),0x11525c6a12412),((-0x16f3d79b9b181),0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
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
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g31 4 0 [(1,5,0)]
  · exact spansBlock g31 5 0 [(2,6,0)]
  · exact spansBlock g31 6 0 [(1,5,0)]
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
def g111samples : Array (Bits × Bits) := #[((-0x52af9237396d7c609ad),0xf04d190d4828112652),((-0x655c481ac6e81d9b781),0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
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
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g111 5 0 [(1,6,0)]
  · exact spansBlock g111 6 0 [(1,6,0)]
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
def g189samples : Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),((-0x53ba7568affbd0d237b1),0x4c61e4544061425c84a),((-0x66a71be859ffde31f071),0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
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
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g189 5 0 [(1,6,0)]
  · exact spansBlock g189 6 0 [(2,7,0)]
  · exact spansBlock g189 7 0 [(1,6,0)]
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
def g191samples : Array (Bits × Bits) := #[((-0x25717f105ceccb07488eef5d6b05d3ebfeedb891de8d9d),0x1a8204e622010a10823154424006181028000900212202),((-0x1aaf9ec211b94e8e1afe7bdff1ecfffe9c5dc8333bb7c1),0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
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
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g191 6 0 [(12,7,2)]
  · exact spansBlock g191 7 0 [(13,7,2),(36,8,3),(36,8,3),(31,8,3)]
  · exact spansBlock g191 8 0 [(3,7,0),(36,8,3),(31,8,3),(36,9,3),(7,9,1)]
  · exact spansBlock g191 9 0 [(12,8,2)]
  · exact spansBlock g191 10 0 [(1,7,0)]
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
def g383samples : Array (Bits × Bits) := #[((-0x1c7c0abe5eb0b5b794deac53933ddf265b3fbd77debbbff7ed3e5fc7dbfeb5c1de09ad),0x3835041a0c802027c003361601060690134460c209508104109022004008a24212652),((-0x38674d2c70fe63326aa5fdf75df7c25df7ffedf3fef5e2aba91da3790bdf73739b7e1),0x1c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x7f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0x3d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0x80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x8003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0x167c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x147c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x183c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x18382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x119338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x11338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xfc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x6c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
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
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g383 7 0 [(2,8,0)]
  · exact spansBlock g383 8 0 [(36,8,3),(8,8,1),(9,9,1)]
  · exact spansBlock g383 9 0 [(3,8,0),(36,9,3),(36,9,3),(36,9,3),(8,9,1),(17,10,2)]
  · exact spansBlock g383 10 0 [(6,8,1),(13,9,2),(28,10,3)]
  · exact spansBlock g383 11 0 [(6,9,1)]
  · exact spansBlock g383 12 0 [(1,8,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def x31d6 (i : Nat) : Nat := 0x1a230180fd10fc20
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def x31d5 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[((-0x13fb5c5de098d),0x2a912c2212652),((-0x375fa4539b781),0x56291cc44829),(0x2f8585078f9c,0x309c463038514),(0x135b045f80fe0,0xb41b88b00ae0),(0x3507a41fff000,0x142e4354ed000),(0,0),(0,0),(0,0),(0,0)]
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
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x31 5 0 [(5,6,0)]
  · exact spansBlock x31 6 0 [(2,6,0)]
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
def x111samples : Array (Bits × Bits) := #[((-0x5e3fe83c986d7c6098d),0x6456218245928112652),((-0x23c7183367e00d9b781),0x1021104810085244829),(0x627e830e1e31c78f9c,0x474a42a0e1430838514),(0x207083f01fc1f80fe0,0x38b5bd5f00bc1780ae0),(0,0),(0x21c0103ffe001fff000,0x1ba9de7dba001eed000),(0x5818003fffffe000000,0x6fdeefb7eff7a000000),(0,0),(0,0)]
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
theorem tablesx111 : checkedTables x111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x111 5 0 [(1,6,0)]
  · exact spansBlock x111 6 0 [(2,7,0)]
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
def x63samples : Array (Bits × Bits) := #[((-0x37827ec0fe38c1de098d),0x765c43000224212652),((-0x1ef9ff22995b3739b781),0x3601a1ac64a488c44829),(0x238268c08738f1078f9c,0x9aa0e13831071038514),(0x16807e00f83f01f80fe0,0x125451e4502f00b00ae0),(0x1c109622ffc001fff000,0x2d89a218afc0014ed000),(0x690100fffffe000000,0x3f89a3bcfffdda000000),(0,0),(0,0),(0,0)]
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
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x63 4 0 [(1,5,0)]
  · exact spansBlock x63 5 0 [(6,6,1)]
  · exact spansBlock x63 6 0 [(7,6,1),(5,7,0)]
  · exact spansBlock x63 7 0 [(2,7,0)]
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
def x189samples : Array (Bits × Bits) := #[(0x98543c01121d833f4fc,0x1e6c550011215802a4ac),(0,0),((-0x3d97dfe07df980d33731),0xa9854a582041528c8ca),((-0x19bff3c9e3c79e30f0f1),0x146729421c3060870605),(0x25004de0e03f81f00ff0,0x219082bde00e81700950),(0x18979200ffc001fff000,0x9328e7ca8001fd5000),(0,0),(0x103ab009fffffe000000,0x35648318357bea000000),(0,0)]
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
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x189 5 0 [(3,6,0)]
  · exact spansBlock x189 6 0 [(3,6,0),(7,7,1)]
  · exact spansBlock x189 7 0 [(5,7,0)]
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
def x251samples : Array (Bits × Bits) := #[((-0x1ffde11fe0001b6f1bfdef603d98f1bf00d81),0x208080808080490a402108a80450a401222a),((-0x1b771eefffe01ffcc0339cec3267cc035b3b1),0x156067666666600212cc63114910212ca4c45),(0,0),(0x1000fe000071c380f83e331e1c38f38f8c,0x66caaaaaaaaa718380f82c321e1838a38b0c),(0x1000fffe0181fc0f003fc3e01fc0fc0ff0,0x199355555555580740f001341e007405c04d0),(0x1b761ee000001fe000fffc003ffe000fff000,0x1036e0f1e1e1f24000a948003fba000fed000),(0x488e11000001fffff0000003ffffff000000,0xa9f989999999ffded00000036efded000000),(0x1b74000000001fffffffffffc000000000000,0xfc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
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
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x251 7 0 [(1,8,0)]
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
def x127samples : Array (Bits × Bits) := #[((-0x3cf3e03bfc0f6f265cc36bfe38c1de098d),0x3301d20130c00091222c94000224212652),((-0x3b4e7fff000e9cd9fb3f00995b3739b781),0x8d421c20c30420400804264a488c44829),(0x30400032fc098c38470f188738f1078f9c,0x2322c82492498838470a18831071038514),(0x3842603b000e0fc0780fe0f83f01f80fe0,0x1ccd1659659407c03005e0502f00b00ae0),(0x9026ec9000ff0007ff000ffc001fff000,0x3229a68a2bf0004dd000afc0014ed000),(0x20c1104000fffff800000fffffe000000,0xcfe2dfecf3fff6e800000fffdda000000),(0x4b18000000fffffffffff000000000000,0x372bde3df3cfbdfbff7fbd000000000000),(0,0),(0,0)]
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
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x127 7 0 [(2,8,0)]
  · exact spansBlock x127 8 0 [(1,8,0)]
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
def x191samples : Array (Bits × Bits) := #[((-0x3bfd11b8dcbfd8ff7def8a4cfe38c1de098d),0x516b7a00004108082102532000224212652),((-0x6bfe3efffee378ccf39db63c995b3739b781),0x38c8481ffffae3330c6248c164a488c44829),(0x133511089c9ec04010038e7c8738f1078f9c,0x4321b34000011cc010010028831071038514),(0x235800308c800883e07c0f80f83f01f80fe0,0x24960cb3b52cc103e0580f80502f00b00ae0),(0x604a2032204028fc007ff000ffc001fff000,0x5a69404c4ad32e7c0027d000afc0014ed000),(0x8800ec54221107fff800000fffffe000000,0x52a908506683ef6a59000000fffdda000000),(0,0),(0x8a410885023507fffffffff000000000000,0x2c5644af997c0015a6feffd7000000000000),(0,0)]
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
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x191 5 0 [(2,6,0)]
  · exact spansBlock x191 6 0 [(2,6,0),(17,7,2)]
  · exact spansBlock x191 7 0 [(17,7,2),(36,8,3),(36,8,3),(36,8,3),(12,8,2)]
  · exact spansBlock x191 8 0 [(5,7,0),(36,8,3),(36,8,3),(36,8,3),(32,8,3),(36,9,3),(36,9,3),(36,9,3),(36,9,3),(36,9,3),(36,9,3),(26,9,3)]
  · exact spansBlock x191 9 0 [(7,7,1),(36,8,3),(5,8,0),(36,9,3),(36,9,3),(2,9,0)]
  · exact spansBlock x191 10 0 [(10,8,1)]
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
def x255samples : Array (Bits × Bits) := #[((-0x67efe8fe7ffb0973ff883bb7e2cdff7def8a4cf6f265cc36bfe38c1de098d),0x7892404800340000422904481532008210253200091222c94000224212652),((-0x7b72ef8dffbeffff09083fff9e3c4cf39db63ce9cd9fb3f00995b3739b781),0x30db990d14ace6f3090c0004081330c6248c10420400804264a488c44829),(0x6401400c52820973fe802081863c4010038e7c98c38470f188738f1078f9c,0x2c32446006102010020520810028401001002898838470a18831071038514),(0x260480809b801730000070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x50c43b9c31a55a2554aa470c07c003e0580f80407c03005e0502f00b00ae0),(0x1a6008010938f6000000380ff8007c007ff000ff0007ff000ffc001fff000,0x7298423ce4aa5daa954b803e8007c0027d000bf0004dd000afc0014ed000),(0x112a780a404008c01083ff000007fff800000fffff800000fffffe000000,0x469af34f68936130486f2a000006a59000000fff6e800000fffdda000000),(0x8c00720041000000003fffffff8000000000fffffffffff000000000000,0x7cf2466f2eb53190cf6f3fffbf7e8000000000fbdfbff7fbd000000000000),(0x6102a0847602080009083fffffffffffffffff00000000000000000000000,0x5384108b0966c9ecf9780d5effd795a6feffd700000000000000000000000),(0,0)]
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
theorem tablesx255 : checkedTables x255 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x255 8 0 [(1,8,0),(7,9,1)]
  · exact spansBlock x255 9 0 [(27,9,3),(9,10,1)]
  · exact spansBlock x255 10 0 [(4,8,0),(3,9,0),(4,10,0)]
  · exact spansBlock x255 11 0 [(1,9,0)]
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
def x383samples : Array (Bits × Bits) := #[((-0xf7edefdfa075ff47fd7ec9ffd39ffbdfc0e6cf6f265cc36bfe38c1de098d),0x1a6b048b813a54161041804002c6004202519200091222c94000224212652),((-0x3b737f9aa7cddf5bfffc6c9feff7e6f3d379e0e9cd9fb3f00995b3739b781),0x5909b044884ab21e4880c201008190c2886090420400804264a488c44829),(0xc240015520000003083a40960f060704f181c98c38470f188738f1078f9c,0x2a0760dbb36254861b3092d960f0607047181498838470a18831071038514),(0x8601e9022015e0030942c9203000180701fe0e0fc0780fe0f83f01f80fe0,0x10e894240419815884476d0203000180000540407c03005e0502f00b00ae0),(0x137002048460b8004001c7c007e007fe000ff0007ff000ffc001fff000,0x25146b507ac42aa16bb812bc7c007e007da000bf0004dd000afc0014ed000),(0x3110400a858081500828000f80007fff800000fffff800000fffffe000000,0x2094b2646e818949ce866faf800055a9000000fff6e800000fffdda000000),(0x20a8060080600a44740400fffff8000000000fffffffffff000000000000,0x3a6c2460a71b145a0a47e3cfcba50000000000fbdfbff7fbd000000000000),(0,0),(0x3524888800519504f50488fffffffffffffff00000000000000000000000,0x503499b106462a431381010345aaa56fffabf00000000000000000000000)]
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
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x383 5 0 [(1,6,0)]
  · exact spansBlock x383 6 0 [(3,7,0)]
  · exact spansBlock x383 7 0 [(2,7,0),(5,8,0)]
  · exact spansBlock x383 8 0 [(11,8,2),(17,9,2)]
  · exact spansBlock x383 9 0 [(16,8,2),(36,9,3),(36,9,3),(2,9,0),(36,10,3),(36,10,3),(36,10,3),(5,10,0)]
  · exact spansBlock x383 10 0 [(11,8,2),(36,9,3),(23,9,3),(36,10,3),(36,10,3),(36,10,3),(30,10,3),(36,11,3),(15,11,2)]
  · exact spansBlock x383 11 0 [(3,8,0),(15,9,2),(30,10,3)]
  · exact spansBlock x383 12 0 [(6,9,1)]
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
def rootLookup (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 2 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none



def rootSSamples : Array (Bits × Bits) := #[((-0x3b3efc6733ff4e7fef7f80e79e776fc59bfefbdf1499ede4cb986d7fe38e077c08c79),0x4c10098c400b1801080251c4088901a6401042029620009142392800010908115182),((-0x1ef5ad9ef3fbfdf9bcfa6f9f807fff3c7899e73b6c79d39b3f67e00995b1bcf377c01),0x210a526108040206430490602b000040816618c492840420400804162a444304c8254),(0x1c01f2583c181c09e1807e41030c788020071cf9318708e1e308738f840f0fcf8,0x40052583c181c49618054410100288020010029308708e0a348508b840b014a0),(0x600607e0080c000600e01ff800e1c0f8007c0f81f01c1f80f01fc0f83f007f00ff00,0x600002a0080c00060000029000e140f8007c0681f00417805015c02837001900eb00),(0x380c7f80031f001f800ffe0000701ff000f800ffe001fe000ffe000ffc0007fff0000,0x380c7f00031f001f800fda0000700be000f80097c001be000adc000d7c00066ee0000),(0xf800003e0001ffff00000007fe00000ffff000001fffff000000ffffff80000000,0x3e0000ae51000000053200000aa69000001fff6e000000fffed600000040),(0x3ff0000003ffffe000000000007fffffff0000000001fffffffffff00000000000000,0xe50000003e9d4a000000000007fffbf7e0000000001fbdfbff7fbe00000000000000),(0x3ffffffffc00000000000000007ffffffffffffffffe0000000000000000000000000,0x3ffffbffac00000000000000002cdeffd75596feffd60000000000000000000000000),(0x3fffffffffffffffffffffffff8000000000000000000000000000000000000000000,0x31afffd5fc162b551aeffdd6598000000000000000000000000000000000004000000)]
def rootSCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,2,312,824633721541,8),(0,4,305,77309412042,8),(0,8,99,824633721748,8),(0,16,486,521,10),(0,32,30,17179870145,8),(0,64,189,770,10),(0,128,347,548,10),(0,256,23,412316861160,8),(1,0,494,134218256,12),(1,2,312,824633721540,7),(1,16,486,520,9),(1,32,30,17179870144,7),(1,64,156,4294968098,7),(1,128,330,134218292,7),(2,0,445,77309411904,12),(2,1,332,412316861104,7),(2,4,305,77309412040,7),(2,16,480,1049101,7),(2,64,189,768,9),(3,0,428,77443629648,9),(3,16,480,1049100,6),(3,64,156,4294968096,6),(3,128,344,548,6),(4,0,379,824633721472,12),(4,2,312,824633721537,7),(4,8,99,824633721744,7),(4,64,57,824633721730,7),(4,128,347,544,9),(5,0,378,824633721472,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(6,16,480,521,6),(6,64,57,824633721728,6),(6,128,281,77309411936,6),(7,0,504,512,7),(8,0,487,33554960,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,64,165,33555218,7),(8,256,23,412316861152,7),(9,0,486,512,8),(9,16,486,512,8),(10,0,437,77309411904,8),(10,4,305,77309412032,6),(10,64,165,33555216,6),(11,0,480,1049092,5),(12,0,355,824667275920,9),(12,64,177,770,6),(13,0,354,824633721472,5),(14,0,497,512,7),(16,0,495,512,13),(16,1,332,412316861090,7),(16,2,424,581,7),(16,4,353,650,7),(16,32,78,897,7),(16,64,165,6292234,7),(16,256,135,616,7),(17,0,494,512,11),(17,2,424,580,6),(17,32,78,896,6),(18,0,428,77309414977,9),(18,1,332,412316861088,6),(18,4,353,648,6),(19,0,428,77309411904,8),(20,0,355,824652595848,9),(20,2,424,577,6),(20,8,99,824633721728,6),(21,0,490,512,7),(24,0,487,512,11),(24,4,353,642,6),(24,256,135,608,6),(25,0,486,512,8),(28,0,355,824633721472,8),(32,0,351,412316861056,12),(32,1,332,412316861074,7),(32,16,198,15393162789641,7),(32,256,23,412316861128,7),(33,0,334,412451078800,9),(33,128,330,134218260,6),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(35,0,476,512,7),(36,0,347,512,8),(36,128,347,512,8),(37,0,330,134218256,5),(38,0,281,77309411904,5),(40,0,215,15393162789632,8),(40,256,23,412316861120,6),(48,0,334,412316862081,9),(48,1,332,412316861058,6),(48,256,135,584,6),(49,0,334,412316861056,8),(52,0,330,1537,5),(56,0,455,512,7),(64,0,447,512,13),(64,1,396,562,7),(64,2,312,824633721477,7),(64,16,166,13194139534089,7),(64,32,30,897,7),(64,256,23,412316861096,7),(65,0,428,134242834,9),(65,2,312,824633721476,6),(65,32,30,896,6),(66,0,445,512,11),(66,1,396,560,6),(66,4,305,648,6),(67,0,428,134218256,8),(68,0,313,824633729666,9),(68,2,312,824633721473,6),(68,8,163,784,6),(70,0,313,824633721472,8),(72,0,167,13194173088528,9),(72,4,305,642,6),(72,256,23,412316861088,6),(73,0,166,13194139534080,5),(74,0,437,512,7),(80,0,431,512,11),(80,1,396,546,6),(80,2,424,517,6),(80,8,163,772,6),(80,256,135,552,6),(82,0,428,3585,8),(88,0,167,13194139534080,8),(96,0,31,9208409883520,9),(96,1,396,530,6),(96,128,27,8796093022980,6),(96,256,23,412316861064,6),(100,0,27,8796093022976,5),(128,0,383,512,13),(128,1,332,562,7),(128,2,312,581,7),(128,4,305,77309411914,7),(128,8,99,788,7),(128,256,23,616,7),(129,0,334,4966056496,9),(129,2,312,580,6),(129,32,30,17179870016,6),(130,0,313,77309936196,9),(130,1,332,560,6),(130,4,305,77309411912,6),(131,0,312,77309936196,6),(132,0,379,512,11),(132,2,312,577,6),(132,8,99,784,6),(133,0,378,512,7),(134,0,313,77309411904,8),(136,0,355,33817108,9),(136,4,305,77309411906,6),(136,256,23,608,6),(140,0,355,33554960,8),(144,0,367,512,11),(144,1,332,546,6),(144,4,353,522,6),(144,32,78,769,6),(145,0,334,4831838752,8),(148,0,355,18874888,8),(152,0,355,262660,8),(160,0,351,512,11),(160,1,332,530,6),(160,64,29,770,6),(160,256,23,584,6),(161,0,334,134218256,8),(164,0,347,512,8),(176,0,334,1537,8),(192,2,312,517,6),(192,4,305,522,6),(192,32,30,769,6),(192,256,23,552,6),(193,0,318,512,7),(194,0,313,524804,8),(196,0,313,8706,8),(224,0,31,8796093022976,8),(256,0,191,17179869760,12),(256,8,99,824633721492,7),(256,16,166,17179869769,7),(256,32,30,17179869889,7),(256,64,189,514,9),(257,0,190,17179869760,8),(257,32,30,17179869888,6),(258,0,189,512,8),(258,64,189,512,8),(259,0,156,4294967840,5),(260,0,187,17179869760,8),(260,8,99,824633721488,6),(264,0,167,17213424208,9),(265,0,166,17179869760,5),(266,0,165,33554960,5),(268,0,243,512,7),(272,0,167,17186161224,9),(272,8,99,824633721476,6),(272,32,78,641,6),(273,0,238,512,7),(274,0,165,6291976,5),(280,0,167,17179869760,8),(288,0,31,429496730304,9),(288,16,198,521,6),(289,0,222,512,7),(292,0,27,17179869760,5),(296,0,215,512,7),(320,0,191,512,11),(320,8,163,532,6),(320,32,30,641,6),(321,0,190,512,7),(322,0,189,512,8),(324,0,187,512,7),(328,0,167,33554960,8),(336,0,167,6291976,8),(352,0,31,412316861056,8),(384,8,99,532,6),(384,32,30,17179869761,6),(416,0,31,17179869760,8),(448,0,31,536871456,8)]
def rootSAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootSD14 (i : Nat) : Nat := 0x20d84d72a811e41a8f13ff
def rootSH14 (i : Nat) : Nat := 0x2f0000014edb20106622b8c2510416615140348080
def rootSD13 (i : Nat) : Nat := 0x32898903572a99181643c4d83b08f1aca26098d5caa649a1f61480f16ca2609921caa649a3014c19a878cd97100ffd30ffd20ffd10
def rootSH13 (i : Nat) : Nat := 0x310815207a1a1856a8d3a40000372b480e2304301249142c9b9e8e8724b382c72589335c8f91509a2e05557399451794c982231d89f1adcc108500900e8182cfc5d029a6cccbb35d8b2e2b723c552840469a5a860000cd0048e03402020002888800380004010010c20407400825c0
def rootSD12 (i : Nat) : Nat := 0x931180b34c253186dca48b0ce72a26e0cc48f16a8795a6630251882f4780a321c197450ad41638afd3326c3da051c2514e900b9ca8f192644c1669993148db88c6703ce55211e2d4e72a6af28c90970f49a90d844b6823c64122f69987b94167944c04bb08a74828ed09bca025ca930b7d30a407876095470ba905aa3c83942f24c4a7942169993520b547812b0bb0974ca80a46ef18850be051479ab8372a3c78a01614a216999317c12b951e32135301431431f28ce12b265594c294548f26a641c1897c5b8a1e514ba60daa384a1a47935320ed331814dca0b190f28541b526e0c6f109ae524da6043e564c2a3203688412adca14031f2842d332624e3c5a82558a0e5795a6131b0d20a384a92bc50d304ac98938f1ca09521e6c20c699e5059b5520a3a414063cad3326084250f1909a942d92ba664c3e61ee55211e24350b014f2b4c3489ec6126e0e6a8f1810829e5699931aa3e84ac84d51e2fca3434c29718e0d6a0b1016795a664c6a8f80ed211e2d4a0b3ca357261506d6404244125df95a614c38ec212d20a3a8b7f28a515025e0d261b4424879c1ec3e5741c86d415a0ca1434cc98ac31025a423c7295c1ec313413e5741c86d415a74e72a30aee6ac76a5a7c65d2366171f2dce9acd9017355b943d2c111cfa0dacbe0a8c8e87945f047432017c003ffb02987ff64530ffecc241ffd81483ffaa6907ff64d20ffe98a41ffd91483ffb06887ff60910ffea9221ffd32443ffb26887ff64910fff0ca41ffe39483ffd12907fe4c120ffc902217fd98482ffb26885ff64910bff0ca617fe19482ffc52885ff8e520bff1ca21fbe494c2ffd12905ef92530
def rootSH12 (i : Nat) : Nat := 0x509ba7d9f513e4c102bd116f3216b00c00280ba0c760c00002db7a105d14d91f218702129e92bc0bc0610445a6c0839a293611cec5bb4d8624148066437a119aea21e4c2a4800000014b420210148c644e86850889460795e892a20a2ac0d1bab4a18b89b008114b73f0491ec812978109d50f493537c992a3f819a0aba590bcc194001239d0c1dac837aa8ab00216912a7c95710d40a974383912b455b07184d2b128ccbbf5cdc06680d0a780a066c5279d75bc99700dd034c496e61630796ca380c20249d3d1c5c3092893c2438aae0da416958013002a05c3acd66113f0d9a22ecf610c090a4a8002c7c2a2948831963c05a85e0a58000000242834603b43e23d823813eadba23d10b3ad9745be59653a8281935008017003933caf3a81101f9629b2601a022b1098801980c1a1642bc0fe7b931d8a94156a09214d2f8027476566e024000048232043335a2b4204deb4f89046c8542861aa492135a2988d36138511c3c95856c843882354e48c83212e01140b3941018af6044895be6ecf400b4852003d66e07e03542a412d080d84001c8ea496ce1290cdb24a581241f602da83386c9c3250ba803581ea05e068d0742ca94c082856819d131000858017c8ef0ba1cdd8ea8e9a6bd33d0700d900b5c2514458c48ba6a972000129e5e52f6a1620008425a1e82646800c6a62d330b9db3a0e2f6e01753353600f14b28574302948b0396617160c1a9fdeceac2c4f02681547644bc40a822c04691b60d81b012c127b5859151c811f24082dd87e88c000961800213670e20cc33e0b0000a5dc994590a97b22c15b05a797b406d94338478ad1411216e4b54ec08fe562896b07521a5074030160de6ca305382b983c15806f21c8b100630aa1da41ce87f02589ed0a889bad026a02f60650bf063914d40794f247d06a07410d39e111352da40b2ea62749c0c8d5ba13a59c25080e10785975b120112dd06f1b6200800410002383072904441030000184045060500547950111882400401d0a9c0000004285041894408449886e005091c000100a0800e0200380088400502a038008000821614002001421008000002a29003120d28e305420d164820002a00800c0028000081a217200210014c0006e8003003c0a70c00206000038000140820000b93000004000000011c30685062c01f160090c00ac80000345810000482
def rootSD11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x3ffd5386520fffa6982443ffe3a60910fff96982443ffea954d20fffa2993483ffe8a64d10fff54e89483ff9a04c520ffe6a130483ff9984c120ffe60530483ff9a54c120ffe65530483ff9514c120ffe68530483ff9914c120ffe61520443ff98348110ffe6a120443ff99848110ffe54d20443ff9a548110ffe65520443ff9a348110ffe64d204437fda166120dff6a5824437fda960520dff6a5524437fd9864d20dff655934837fd8564d10dff6a1934437fd9864530dff609934437fd9864d10dff695934437fd9564530dff549934437fda264d10dff649914c37fd984c520bff6a1914c37fd8364910dff6a1924437fd9864520dff661924437fd5364910dff655924437fda364910dff64d914837fd9364910eff66181482ffda864520bff6a219482ffda88e520bff69593482ffda58e520bff68d91482ffda386520bff68e89483fed8254910bff6a193442ffda864910bff69592442ffda364910ffe82998483ffa0a64530ffe829934437fe1a66120bff86998482ffe1a64d20dff54a194c3ffa194c120ffd606194837fd9886520dff6a2194837fd5386520dff64e194837fda386520bffa6982442ffe9a54910dff8a993442ffe2a64530bff8a9934437fd858a510dff60e294437fd538a510bffa6981482ffe3a66120bff8e982442ffe3a60520bff8e9524437fd988e520dff8e5814837fda88e520dff696394837fd858e510dff60a394437fd528e510dffaa5314837fea94c910fef92993483fbe4a64d10fef925814c2ffe5a60910bff969934837fe5a64d10bff969914c2ffe5a64d10ffe965304837fe5964d20dff965314837fea954910dffaa553483efe6a60520f7f9e952442ffe8a64d20dffa2993442ffe8a64530bffa2993443ffa894c120dff54e894837fe8964d20dffa25314837fda3a2520dffaa5814c37fea960520dffaa5824437fea960d10ffc54520443fe9524c120dfe66130483fd9534c120ff64c5304837f99348110ffa549204427fda864d109ff6a1924427fda8865309ff6a2194827fda88a5109ff6a2394827fda88e5109ff696194c27fda58a5109ff696394827fda58e5109ff68d924427fda3865209ff68e294427fda3a2520bbf69a894827fca954d209ff2a5314827fda2865309ff68a394427fda18e5209ff68689482ffa0a66120dfe82993442ffa0a64530bfe829934427fe1a66120bfe86930483ff21a48110dfd606194837f61a64910bfd869924427fe9a609109ff8a9934427fe3a64910ff68e5304837fa39481109ff8ea19482fbe4a64d20def92993442fbe4a64d10fee929304837be4960530def925914c37bda1925309ff969934427fe5a8e520bbf9a981482dfe7a549109ffa29934427fe8a64910dfea25304836fda6a2520cffa25984827fe8a865209bf69a894827be4a64d10 else 0x612672b1e02538130ce3244986004a6f942dfa60ac0ac24c2307604a9f94078638ac0a6e42b502c40b417427c2a7830db51c12a3e574c1aa1f74836aa8e0951d33930ae189a431e5ca04a8ed414c12809479a403f84017c94780bfc18141960b05385c06891a6286b502c0685f95e0c50e6a0840d0c0ac170a4b941f029e90c78da93f2812853d20da8161be502e0a76413543c04a721fd33931b71660074863c7949029f2817053b218f13502547cae4c14ec863c0da094e0a0678a6b219ab1e0be3f4c04a09c6909e1759ab1e3904f4c19a2c053590cd4d1c12a05d025059d844985308c71741533559068e094dd30280b01a35a849b4704a883bd3387fcaec214f4802c47cae99c60217831742873502c4f83f95e83c802c8da60662ebb0853d200acd463a64a4e316dc15e26c1372bc1a2bad4cb9553021590f062e850d6a056918812c602a40b808bc1b6a0569e3013468d2614a2cb3563c7409126347b0ba0a8e094d9331374ce4d43c5b5af03c6db4863c5cc5863f2b9305502f5328c155cd58f17e4044d260ad83c688ba1478f1e528558600b56431e3ca04a78582e85f05a04af2aa3e904061e99c983a05a3958f34808109209560102d01f395a404084904a87942dc2807212616ab5046474ce4da431e0b72f83f95e83c866a05869a5b331662ecc00975d2d7257a4aa294a128264dbc9659253238a44848338fc31e123a9c7178db71a26313c6588c4f17562d2455d8a43133e244444187f50ea21a5c2f984f7087a0db414e81cd02aa0213fc47ecefc81f513e457c28f6b1ea7bd13796cf139dedbb73762cea35d1839de72ece465c5e386a6fc2dde5b93b6bf6caed791aceb5616a34d245a35b42467a4ce2d9a232e7652ac90d8e831896242c33d833afe95f02bcbd7742e965c9eb7f56db2d645a0eb2a9626ac065752ad5d582aa71543ea7614ce296b521ca299424a7ec4f1e9c9d370266d4bf4967529524d848ca90d11f6a39046508b2d152a25e445a87f10bf210b411a8094fe41f6b3e747bccf459e393bce7654e911caf388e6f50db09aee34ca67c8cba192231a061ccc2118112f265c28b5c16452ba455a8a811484284e4f289bc131b2566495890211a72252433082c8fe61f123c847678e881c40370c6b30d09195831105ee0ba016b22bc45550a5813e0264c4a088ef110e20a83ec07910e681b5c33786280bc21560278048808400f641ad82dd04d408600dd813d01c0020c0238000fff6a5814c3ffd5260530fff549914c3ffd5366120fff54d81483ffda954d20fff64d81483ffd5364520fff2a553483ffda960d10fff69582443ffda360910fff6a582443ffd5360910fff60d52443ffda354910fff6a552443ffd854c910fff6a532443ffd8564d10fff60993443ffd5264d10fff61592443ffd8364910fff54d9244) else (if i < 3 then 0x250de60166fc9a83414e0942e1c0ea091721fc4b0403014478248380ba058170ff281623c1221b42e180408d0800941736a0a6717382429b0f1680502001e403161f8242982c0281000f202a0cc14a73ab502c7210b1002446b6a0a6100129ba67260426bf4863c79407902d81282e11af282305338af7940b84685308c1ace074db85ac1234c1706f0e01802a3a0ad4d1da6dc1a0460a61ac4984039b7068234298460d660840b0538250b8537629c1285c27a04a00d05d63c0e0e4022203863c1481d85d3900570b022a4168b405869837b9004a0790e80548c988452ec83ca0a88154a9064b47b20095e5442405a56e34c3046d35b641a385449afa1e1370481e08060b58602832619e258255cac780b94c98439d60b41705f590cd40971e285085a64c1185be3cd206dd0c985a0340d02c02166a0ad8f0ab292f0be0e611b0c09305c78a0a2412e9033e175a38cead407942f80e8ba05c40982c0398461260b8c0324f0d2296e82a3bca0a880a82f83d4a47211b621025174916030452c6d2fb51dd0025456a05c0786940128b00f40d047182582c11c0cc8108160530604e99c62dba3c067e0e5250f05772915ac5d5183301e0518becd4151d063c50b5022d305a5261421fc16046c7814d63078c2b7c781503866a74017138f0dbba01261b41642c0a68168171d007f33c0b02a05340147401701290608591261fc2305330ba04aa74ead470ece82b501e4d90148158660482ac22ce0940f5264282a4228b5385a2d5a431e0b636c078ff2b9345432025864055cd58f0aaab8784fc12078d704017d51f483ca505d15f83d2803d1a6f2b1e0ba482d1a78f1e50a41741b415c2c180a17413c1580af06740d302579510940cc2d42c17c14c2589379551c12a80f0c99122a9a3dca88532812e3cd2016980ce166184bc2045f3ca12751c12a85f3af16e097482a614751c3b56a03cb17d7283a0461260942d1c36d6a16e28c221b70d07ad42dc36825146124db86840251362041711368a33a01149f2b930256981539aa6a03c1b42e5905c3c063da92b02c85815be507f05ce82a3b21e0be04da4029bcaa8e7e6a0742cb4cec22ebbb82c0a7a4150f05d05304a0d00f040059a41b5281a0180582e812853cd4d1ec827e51560ac14c1282e8799a9d02403004c1fe0e9307e13c16848bcac78b00c0945307d0b56431e66a41b7f06293c80711475a81620648930f816b4863cad4716f8f05204b0b4126c806d402ec122903e85a04ba41e55474c2c1a5e0c4c0ba146f2821238c0d50e2e806a56a0587169c985a8980da10ac80544056c300bb048cdec227c6602574151d62d05a89f04be0c36d470a880080d0128d10a62985d590cd58f1402c0ee091743543e053d20d1eb5282a0b405c294210c0b201b5006b048a41a216812b47d21729244fa672 else 0x2b16c6ddbba2c07a1ace6ddc1cb74ad8d4ab42c4595a93cd40d4142ac0ac2582e85828536bc2d0b504f8240e8ba09a864d826b505a36f2dc0f1c2b01d058165cc84d01874586dc2150fc128c41281e0d6904f05287e09842094269e9305903ad8400003c1270282dc160bb3a0908c55a8c2147407145c802393164d460dd80217c2e8e2dc5c8004da094ac9a8c05404a2e82d18ddd83577158ab2148287f066950a00c262154ab011405534a5582a00c142094ed30e2d1858b0c498a1482880589081a02521c58850b0000542c428580b80002529568840661602e04a284f0521080004a404b084000542053c3102610d0f03a0b8e0019a81104a4b5e6ed93027172094d6bce2b4c09e2e4b4980e81a04e1642680c38338582f85d54700060610b0dd8b0a8e000cc9b04caf0b57280e980a50f05c2481603403c717d51c5d04b1241fc1604040b924d061d787f12c100e0ae0c42c794a941284017da42a3b6a58590a02342587f1740b02020dd9260a1499d00560fe25820245d034741061b504bd2151c29a41a01487823425b6a1740b02e240a30f14209420155b82e04b0621e0780a99a9d0260a41856ea32048250fe0d2c866a68eb1730601760f1081e012853413116c2101286d0b868130615b825a300d035e6a0a8d1dd02c2805659c0bb353a004a10101400a0780a8456ed1f0782c1080c43f82508097940b42102c1080943685c40256d42a02005a28b31a16bc12e090822a02d20098d003c096e508a0ba6dc3a240e0980a9640088250d2304ab09651caa8f824933af17c1fc4b04048c13761341385e1302a020221a8398580ac2a0c093c078693a0c78f2980b19a8afc78f286987f0888174108160c411a1fc229c2a87f19e2782163c7219a85d26a3bca19c108160850b81bd00b19ab4cc78150508cb088809a1081605e1a61ac229c21c2c05d1b56704a1839a8298a5a8ee4180b19a825c78c601a0d30fe11120b0258421081ac5d05c3d2654c7583b6908bcf2b1e02e480b16d8f05d17711a1fe160454c14c1f25040d9014231012b47794a15ef284207f04a120c2f85405c04a0b8a3089886d1340943f982a05a56f4624a0cbcd41fc30025740d1d8150128781bca68e0d0538250b8636ed1c1a0840fe094201de504206829c1285c30afd215a81282e03c62ee2db0c50f1501701282e40cfc795a8298c21260b8f4983985ec7833c4982e381c016164db8bac126643f896080a0e78f0e88561260b8c02cdf935c300d04207f04a10138245f06b0a60b02308e385a17d824281d1b9424da3825495616e1545f094c78f28240c7b419a9604c058bba8ef28bb8a18841bd204cbb92617229c1285c39990aa6ec4d))
def rootSH11 (i : Nat) : Nat := (if i < 1 then 0xb2454e0049e98c89400d0c69400010924e7cca0000a00a5a001841758020969018a52981460cd82d4103a250106ada229583d6e1425be94a002414101bc17dce74ea623a0179d0b009401c812c062819a82941360060974502882322c4420125ec3e8cf2519d5ca0ef82be2ed06821395c8377c817941495c457c01b654ca21e0788103723060c00b445a07c153e119828286d0434cf68470123391604d5d6267381cc08f1c880d631940b000d4131853e06386408801488927809693602b64da22648f8c8073a104ed615043b53722d2100857417805b4171015d5a5cdbe160107a0cad054041a614e33855c89a803200ec3c54af245b381025e197065010c13c005f40a8075815a99c558a01f06712e782320fb3a1a15f2cd336c4e26f7283a603fb3fe0843e740f0828e0b210ba4d483e80ae80f88a3a082105187002c05004e485626e8044c052be8055a04440b9ce1c0f4851a13305ba8fc948218c84d60aab1468c38086023a4200d43be6f3bb5aa1662d80048862c0b1b6940c205e80f280e4152836449e80f4251a3ba9638071310a3920ea22c20e120a97a5226d71ba4cc0dfa3748e1841206c0000fa4051454e80f209fd00082b0000991268958382f8087852d6a0024403401a69124cf498b001af3da4996ac832571e063753f85548d73dbe51e0396080120cb37433200785240b6258a80e91660380012d3c058ec1f01a212992128c0000e0aba2ca07e22840d201aa04323ef347108404789c605402e171a549a89e03708615aaf79a855935b00000c60002c8e0002830539617edcd410784c08b35338000817400081245a7145000085bcba3a57842da35815e02436c4058ae6683b64144d440e7568201485da80b50980e6b3c6042803532added52902fc558a22698803fb55fb92f3a301b882181c1486028961fc28e02eb2a101fd11480ca2db56780db39eb15216cbdc682211250000050405120002010240e700005b0003030119000a020602044d07000c000001e20b173702000c031000136f00293b060102090a00070d0400000100001600033701000106003400030864001809010318370a031f003d3002000204000000011f041600150132050900000003280f340502000009fb0066050001010006270b0414760518072b1a000005216c1a0a03000003030000110d000031070a0b0e080003000d00005700080b0000000137745e001a024f00000b23071e0628010d010211390b08000a16021900032a020603133108240e04002f00000a001900130209c2030201070003000008070e04781f0c00960603130256010c0d00001c0a04134f022400071311030c000905120200243a0f12010a032e0200010004b706020612681b00141b31005700090033280000020015000205100f0701072b0000050000032504020389 else 0x97355c4e4f838f4ac005a8b50000122ddfed2282f60d1a3bc13a065842c0000000cc5c000008a0a733ae8a004bc15086560e439b807bd66c94d59c68e90406ea922200b420b28e28248482835411a20ca15a5dda0ba10080e2a1a9650009c12d433a0e0824c09d8180d3b046c06b95ba11283af3a483f4170011003ace4a09c005e14e02f0473833e169042e16a0534144032e120816051c04baaeca20601023154a5b27e61fbcf871aa03f51f04f211791bd0a2a39d60a853257784853155c860a68564132c0ae87425980db4db7122850eced21aef9f816d3655e48108857207d83bb4a183c50e3d66207602ec19ba22e015519a19d5e61352b29c0b30522e4c5d74e4a031f4cc80de083811a182d3b292952988fa143e572429e082431241b24ac0f9c662898014e0a186880d72078872a34c88282165a603dee263ce373d4292e9da5865113c5c15b90684dbb310164107e142068e07abb7b46780b5316a22a102054e0e8817338fa59682f81e608d1c8617b8322114946c177016687f20a441d539a01b53b410f15fe96e022cc4e05c80f3816b77d82388c40638517882d0b75d70c0da330913a0c413426120da55c2019ba1682882628515d2c0d802b2cb789f006425909a5bd01111cc440960044191ce94f3fa4968c185a2fa184276aab2fee0ebce614a8256f3aa462193364b799147556b842811e02780de22372f5201552401df192a29282723c24f524d2081029001384984a58156154d87098680ed667859c180d69a89c32428e35c888f9004816b)
def rootSD10 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x6a581482bfb0db50c92213fd86da864910bfe436cc2408847fe1b6a239482bfb0db4ac9a217fc86da5481108ffc36d2c72905ff21b68d204433fb0db46c92215fd86da264d10afec36d1b24884ff61b68d924437f4a9434982411ff86da3a2520ffc2a50d2408873f598606194839fac0b510ca419fd6a21a64910cfeb310d3248847fe2b6a193442ff515b50982417fa8ad9848110afdc56d4b048857ee2b66192442ff515b30982417fa8ada848110dfd455053309047fe2b6a2194c23ff15b511ca217fa8ada54c1208ffc56d2c329877ea2b64d20442ff515b42982417fa8ad9348110cfdaa5153268857ee2b64d924427f715b46c8a415fda6d8186520aff536a8a609047fe3b6a192443bed1db30982417f68ed984c120afbc76cc326885fda3b6a1304823ff1db510ca411ff8eda88a510bfb476caa60907fca3954930483beccc47298241dfa54a39481108ffd56cc2629067be4b6a1934433df25b46c92215ef92da364910bf7496d1a408867be4a661934833df2532ac9a415ef92d9364520af7c96c9c329077ba4b64d20442fdd25b26902219ef6164a64d10cf7b51253268867be4a609934433df25330c9a219ef6964a64d10cf7c94a93268867be4a68993442bdf25b26c9221dee92a0a64d10df7495053268867be4a8a993443fd5252a498241dee929984c120ff3494a9a60907f9a4a4c5304837dd25342982419ef6a24964530cf7b7524b029867beba925814c3bdd24c14c8a619ef9262a64530af7c56d0c92987f9a4a8e5304833df4d492c0a619ef92da386520af7c96d1c329047fe5b6a2194c23ff2db5114a211ff96da88e5208ffcb6d44728847fe5b68d924433df2d494c9a219ef96a49645308ffcb6d1c329047fe5b68e294423ff2db4744a419ef92a5964d208ffcb6d14329857be5b686494c23ff2dc54c9a215bf9ada864d109dfcd6d43229866fe6b6a192442b7f35b42cc2415bf9ada8649109dfcd6d4322905efa6b66120442b7f35b30c92217be9ad814c120cdfcd4d4b029066fdb99a98148337f5ccd4c0a41dbd9ad8186520cdfcd51cb02906ebe6a925814c337f35b5114a2137f9eda564910bbf4f6caa60905dfa7b69520443ef53daa49022197f9e9a954910abfcf6a93268865fdb99e9524432ff5ccf4a922157f9ed5286530abfcf6a94728865fe7aaa5524432ff3db4b1ca4157f9eda58e5208ffd16d2c329847fe8b696394831ff45330c9a418ffa29a864d10cf7d15253268867be8a925914c23ff45b470ca411ffa2da38a510efd512a92609077d953a2530483bed44a6298241dbe6da894c120e7f512cc2609073fa89829984833df25512c9a41dee92a894c1208ffd16d14329857be8b686494c337f35552c0a411ffa2e2a64d108ffd172d326887f615254520443fa4a9aa4982419af9aa4960530 else (if i < 2 then 0x217fe96d814c120cffcb51cb02904ffe5b6a2394833ff2d304c9a219ff96a2a64d109ffcb6d1d129057fe5b8a9934427ff2dc54c8a613ff96e2a64d109ffd74a9b309067fe9aaa553483f7d35b0298241bbf9a95360520ddfcd4c9b02906efdb39a98148377edccd4c0a41faf9aa4960530bbfcf6d2b048875fe7b54993442eff3daa4c8a61f7b9e98254910dbfcf4c1aa4886dfe7a68d524436ff3d352a922177f9ed5264d10dbfb673d2a48875fe7b54a194c3aff3daa51ca213ffa2da564d20bff516a9a408857fe8b54d92442bff45aa70ca415ffa2d538a510bff516caa60905ffa8b69520442bff45aa4c9a215ffa2d5286530affd16a9472884ffe8b69639482bff45b4b1ca415ffa2da3649109ffd16d1b22904ffe8b68d92442ffd45b46902219ffa299564d20affd16c9b229057fe8b64e194833ff454b2c9a417fea2d9348110cffd14a93268857fe8b64d924437fd45414c9a219ffa2a5a64d10cffd152ca62904ffe8b68e19482bff45b470ca41ffaa25524c120eff512caa609077fa8954530483feca9d12982419ff6968964d20cffcb544b269067fe5aa25314827ff55aa6c12213ffa2e2a64d10affd172d326884ffe8b96993443fe8c0a6298241ff86c95148110bfe36b0d2408877e95264d20443beccc26298241cfe661814c1209ff37105322985fd9b58e530482f7cdb512982415fe2e5514c120fed2a6a9240884ff9b1829984827fcd8534c12213fe6c29a549109ff3614d3029067f58168e194827fadac34c92213fd6c69a60910afeb6354a629057f5b1aa5814c2bfad8d52c0a415fb6caa94c910afdb6554aa48857edb2aa582442beed9d5298a415f76cea94c910afbb6754aa69057ddb396531482beed9d1298a415f76cea960d10a7fb7154b029053fdb8aa5824429fedc472c0a411ff6e1a58a5108ffb70d2c728847fda9aa5834423fedc34714a211ff6a6a9609108ffb70d14728847fdba8e5814823fedc454c9a211ff6e23a649108ffb711d4329047fdb8969934423fedc4b51ca411ff6d5a3649108ffb6ad1c329047fdb568e294423fedab4744a419bf54da6a25208ffb6a54a629047fdb568a194c23fedab451ca211ff6d69a609108ffb6b153268847fdb58e9924423fedac750ca411ff6d68a64d108ffb5354a648856fdb6a25934823fedd4b298a411ff6ea894c5208ffb670d3309047fdb3a299244337ed334744a411ff6ce8a865208ffb731d3029047fdb2969934423fed9514c9a211ff6e63a609108ffb731d2a48847fdb9969824433ded434324a619ef689a192530aff416d4326884ffa0b6a1914c27fd05b50c9a219fe82da8649109ff416d4322904ffa0b6a192442dfd05b30c0a413fe82da564d20aff416d2b26884ffa0b69592442bfb0db50c9a217fc86da848110cfec36d43248857f61b else 0xc6c9d5844ec13b06bf9ac95729aa0697da1267759a865fd9566485904630d63462095ca61058185f5d78a5d257145b1d6925975634579d5ca5685584553d53253f545453514b7526947d515142b4fd93cd4ec136f4ce927e4c452dc4a6d27e332924948811d3464914543e10c341d90414090fef3f18fa93dd0f3f3c28ee13ab0e6b3848ddd36a0d8b3588d453470ce73328cad3240c7331ccc562d50b5430e4bec2eacb8e2dc4b542c1cad22aa4a7428fca2227e49d026cc95a24948d8222c85620247a41dec75e1c746e81a9c67218045e4165c55614244e012dc49a11f446010dc40e07f81fe0fc43d40eac3820d6430c0bbc2c60a14268086c1fe07241ac05ac0fa01c4000ffe302a8a60907ff18354520443ff4a930298241ff654d814c120eff30ac9a40885ff9b5a2530483fec5caa698241ffa60d5248110ffb306a9a40887f798554d20442ffcdc2a690221bfd605a386520bfeb634d3048877ed82549934433fed2b3098a419ff6a15264d10cffaa4d44329867fd526a2394433fec1b4b14a215ff6d63960520cffb04d2c728867fd8568d92442bfedad12c9a415ff6d6a94c910affb70a93268857fcba61593442bfe5d2a4c9a215ff6e2594c520affb6b44a629067fd8568e29442bfedc2a6c92213ff6d5a3a2520bdfb6c54aa6906efd5369a894827fe5d2a6cc2413ffaad53a25209ffb6b1d302904ffdb5a29934833fe54b52a9a419ff615a28e510fedaa6c12a4885fbdb4a69824427fedc474a92213ff2e953609109ffb6b1d304884ffdb5a29934427fe5d304c9a213ff6ce9a609109ffb674d2a4884ffdb3969824427fed9514c9a215ff6c6a954d20cffaa6d0d12905ffa0b6a5814c2ffd05b52c1a217fe82da960910bff416d4aa6905ffa0b6a552443bfcc2c14c9a21bfe6160a64d10bfec36d4b04885ff61b6a532443ff8c0c3298241ffc6161a48110ffe3070d240887ff15386920443bfaa9b030ca41dfd64d8186520efeb02d1c329077f58386992443bfaa9c34c9221bfd6161a64910dfeb070d324886ff55386992442bff4db4ac12215ffa6da354910affc56c2b26885fee2b6a5824433ff15b510ca617fb8ada354910cffc56d2c329877ed528a9934437f6a9454c8a619ff6162a64d10dfdaa515326885ffa3b61520442bff1db0b14a213ff8eda864910bff476cc2408857fe3b6619244377f1db4d44a413ff8eda564910dfdc74c12a48867fd858e992443bfcc2c7290221dfb609528e510affc56c2c72885fbe4b64d81483bdec2c94c9a21def9295264d10df7b0b25326886fbe4a609934437df252a4c9a21fee929814c120ef7b5324b029877bdba925814c3bdf24aa4c0a61def9255264530ef7b6524b02985ffa5b60d20442bff2db06c92215ff96d838a510affcb6cc2629057fe5b66239483fb72db04a92)) else (if i < 4 then 0xfe605b05c0d306f20320637350182165c81810c11034c1fc904a0b8204283402c030240a01e8180c2440c055200568560a6482605c0ba040201585d0298229014c2e810060a743012408045610b00400a10702a3386002004d02e02283c1c2681701156dc8085068056060409203013c80228180c14c0cc40b8124b6e30b004603306c20358198814c22c409e16a204f0ba10028298814c2d441120ac16415207c05c602b06802303e097282e0198814c07840b806020890560b20a803e02e371e06983f822138f014f0b060c256e142090406609a07f02e24128398b86017007860ff08403c3825078158781560c6a3f4861600f1c06420422812480de0d014e1020f20e860a7081e3c6a607401e30b545780c83413a402ced1c1ec288078df07e99479f21a1fb5eb6d456806d0b801e1e0a02e0b498284070258100bc1e0380b904a4055c3c02e15508e28088458660241210f0b00b805f9a83502a38f017d202e12c20d409666d6d009c42530176b506a0416161749b1b435020310a094c1a80e7484309305702e184b02b880202d4416a0b420530be02e18020150050c0202e8416005c2a90c3c05a1f9a82d05d0fcd40782e860661263a004a08c0b4604605310540248298c13a24e096f280cca17406620b706708808104901e30600180818c28c124078817405c202e08a02407403e281282b05af9ad352c802a01700f27cd41540741640b02d50b3d86a401140b97f07b5fa1fc4dc13f41f20b6d4569fc5b35cfbb7ec4fa9fe96f9e7e68f92fe22bb83df9f773db3f62bd3df453cf7f36bca5f223c5ff10bc19eff3bdfeedbb99edf35fd572bb5fecabaf5ead3a7fcaff322e8fb69fcd734f1e70f9fde7839c3e70edc3b70f9c3e70f99ae5c7948e00b8e5c79b91fe40b7f1e3978e5e3235eccd738b7e20b84de0c3802e04f7f1e00b7f1df2379fdddb765dd2372bdc3b6e5daf369fda0aee0bb0edc3d9c7654d8aedc3d86b5fdd7b35dbd6fb589d58352bd43b4f1d32349fd17b41dcfa33b3cdfaee0cd86ec3315ae26cd72ee0ccff322cc172e8caff296c95722cc80f1e6c6f7188c51f11ec3a70b4c1ff056c056ff8bf6efb2be26f60bd0ef1abc6aef1bb82d3eb9b2ec3ba9ada6ba26e6cb90c47db89ae09b782dc3b69ad89b4facadb442d78b56ed3eb4b6d10b3ceccab2b6c84b16ec32b056bc8aeaeb76ad66b59acf2b13ab7aaa9aa02a3fa82a9d5a6e298fa4da901a3628a36a81aa0a1ea839a0727f39f5a79597be76c9d0e71a9bc66c89a7e66a98d660c97be5c6967655c946e12a933a12a06b248d91003d40f52423901a3ad8d823378c6a2c18a3224b87f8c56872617c84ecc9084aa0b981e20377fa947d7ea5f8c7d5df167b55e88791ddfa7685d6c5351d377439cf17321c0c727dc7670d5c0c53515846f8dba25729b795611b5 else (if i < 5 then 0x6c0788b6d46b456ad44d180028b901721c182f8170fcd70531280bb0b0a16a2aa2abba1410010cad0a0c15c23c160785805d884308601711c182a8170c2d407400078301019002160c015082c80ec402000220b2008003180181388094000417403a0003014000160c707882c0220417410b00a31058004082c0200a09a204d005105d00e8080c00404050ac0e603a30ba093856180f12902d0c0741fc4838817c136c2192b32607f0b51044032817810102e8008418a06020000140051be561e05d00f100949e4150078809a03a08030a105c05602e053281681705d020101d00b810016881740922025048053181983a61602d7486a38129c0a80b011814c987874005c30530b904001e201284b00f0c2dc2cb8255a82e8a04a080202508d01e18340128813c0780501241a0a00604a05c302702508b18440128170c0941a00b8600606805c30310d40531da60658128229021c1e80942e881660340923025068104701282d0c0780941d060260ce15209203c502701d0a9054049280980f04385582e837982dc19c28c1a0120a02601c15603c10208a60b205c10040658801c01001426404434c1e0e03801613a15217408060d407a01e182d06009c9a04da7805ba438f0168e0d213806816a40560890d4073040282b04485a85401f017182d41c0270078803811216a15207c05c60560690c109302e2d04840cc0ef0b30c424c72828b51c095214201619614c03c505000c0a703d0ba281e0058468298658209816811824c0941d0a054124208407405c02e202785a0540240299400022c1441b0300a00c0dc00212e0fe090602a0b908507f048280303700005382202d18c3c11417002c3101e8100e61e09606c044400904d0ba0402004a3680f0c094078404a0b803c301101e053180e02e0170fcd40501340680f4a00004a03c366a02501e1fb080980c82d034140941ac078605c1742b4c00302c01e206581280f0c2c00501e8078802004a03c3f8305584a05302e285b83382d05380f024996400b811814c816c0d603c05c40af0110681857be500f0df282d00941ac800403c201d0ba02e092040280004b059840817140ac2d02341700b8a04a0b805c30b920907f0960402806f0485a84084d817181400302a0094300a03a05c124080405a0c7e3c0a803e02e301284681700f100ac0b8248100802204a03c304f04c39004d01a08e30000128802417007860b803c202a0260480532013822882f80a812014c802818003c30c70401015022880a82e8404e1740803093048053185f013812820121096400b8605c03c2e6a0350490a106f281a82086983f93060172094603e1500b805c40b189807f04808d2c128240814c0b364011090280b904a37a00910307ca82c0c633e505f86005083794190170056e439a82e8d0dba4c134060088 else 0xf029890b2da80b876d40a6174374c818100e841fc1c05028134cc1811d799360c0c0420742e8617204a20b93af038181700f0298d01ae0d0101940e0154cf0600a0aa30880ba100282a0881c2d821433080a8164204d0c6039182e81c8b4600c40086108070200503010010268180c2c80a8400a0b4205a00c102ce9300ef0491c9816b824074836604fc1203a0fe5002e0900001d201000f839dcc83494058028740054100a10802e200001416930168018dc98004094617a0d601430580a100c1ba640a08094008503a0d6202e0db09d7b93058101ac0b51182c0806e0d62726003100184150200404a0323025011091180006301c0c0642030010200c156100c0028bcd40d0284603409014230020ba100c850880682054006210606603218ab0409c2c04e9813af08018010b43f8260941ac906a06009a3b184350300a1200022a08002094403302814230bae1806b18182dbbb085e6b5140497382c75a96dcb36f7072adad4403043f9560a1210203c0112db9013c014400270031027806081342c84004032200001d00c182a8180508c0c05580ac2840f8a02202e122301d04d00c1826806080a8da8078764c0b5c1203c4b47a2ce0901ea3128830148340c0341a)))
def rootSH10 (i : Nat) : Nat := 0x900018000000a4e43205624f00f03371b215070b38a5e938490a5343b42a75c29620466a21fa50662a9402a404825b4245a72208b05570d401b8106a91705998589966171606075407a993708524a4a41c00198d29400003d97d85e04200041393440678842196e03fa4c06c04000384b74ea2504463b42c92c75106f06604e05b04795db4400000106548386000006902e03763778600107e62800000148b978b4a07400000120b027137030a1178d42745e98f048072698b3a001976900080038000004448140280260183f700a62806103c0a1880408a805582018ae0
def rootSD9 (i : Nat) : Nat := 0x202812166da805c0b52615803a281601cc0d23061f5a8402000fee646c1c605b664602e00f014c60300f49bc1229d7840f004010210206b080b8342c0c81e5062f0487c30106181d4403a0c8102a040d01a8094771ae0c34350d0ac3d6a0d0fc3b610080905801d0398c174101680780a6300f00b84036080ac174053215828408a600b840c4102ac0941163002e816a05a18e60591f6224257f20b01602c7b4eb9c13566880b01602c64a0b1683133acb897a2e25a00b0162be5580b01628d4f69a52523844c850f402c0580b0161d63880b0d91a031c5bc1602c05850c9882c0584141602c0583986a02c1021bc2e82c0580b01602c0580c416000ffc152605314c120d7f0b9605514c120ff61835495148110ff4953549814c120bee9c6a25524c120ff48c954d524c120bed9c62e5534c120ded9536da894c120ff498354d524811097bebc6a64960530a6fdc62a5a954d20c6fda56da8964d2087fccb695984c52095fdc796e2a64d1087fcca6e15264d1087feca8ad8564d1087fdca8ad858e51087fecb2a5a954d20c7be4a6d68964d20b7b64c64d8186520e7ae4a6095264d10c7bdb89295264d10e7ae4a54a2a64d10b7b61c6ca4960530e7ae4954a2a64530d7b64b605a386520c6fe5a6da8964d2087fdcb96a894c520dfd25b605314c120deea6b549814c120deda6b54d814c120e6f66c605a386520c6fe6a6d63960520cebe6a92d9360520deba6b929814c120e6be6a6a64960530e6bdc99aa4960530e6be6a6ca4960530e6bdcb9aa4960530c5fe7b6a15264d10a5fe7c549a886530a5fe7c549a88e510c5fe7aa6da354910a5fe9c6ce7a54910e5be7b9295264d10d5be7b9295264d10cdbe7b9295264d10fdaa7b929524c120d5be7b9255260530d5be7b9255264530b3f68c54d8186520c7be8b9299564d20c7be8b9295264d10c5fe7ba295264d10ff4953a25524c120f7aa4aa25524c120d7da5ba25314c120d5fa7ba25954c120f3d198605314c12087bebc6a2496453086fecb9a9a96052085fecb9e9a95491087f5caa6d818652087bdcba6a4960530c6be4a6da8964d20ff0a4a54d524c12085fdcb9eaa95491086fdcb9aaa960520c6be6b92da864d10a6be6c6a24a64d10a6be6c6a24964530c6be6b9299864d10a6be6c6ea4960530c5be7b9299564d20fd627c5495148110c5be7b9295264d10f74953a25524c120
def rootSH9 (i : Nat) : Nat := 0x1934800019a01960194b04
def rootSD8 (i : Nat) : Nat := 0x6058160b032160642b083ead800502fc93ac64aa6a9260906f9254dc6a25524c120ef2535aa6a93029824145be7d6e24a54993443fa14f7252a6a926090712f9aa7b9255260530
def rootSLevel : Nat → Packing
  | 14 => (1,0,8,0,0,0,0,rootSD14)
  | 13 => (3,1,8,0,0,8,0,rootSD13)
  | 12 => (30,2,8,0,0,12,0,rootSD12)
  | 11 => (220,3,8,0,0,15,0,rootSD11)
  | 10 => (424,4,8,0,0,14,0,rootSD10)
  | 9 => (77,5,8,0,0,11,0,rootSD9)
  | 8 => (6,6,8,0,0,6,0,rootSD8)
  | _ => emptyPacking
def rootSIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => rootLookup 11 19 3 7 2 4 rootSH14
  | 13 => rootLookup 37 67 6 10 5 4 rootSH13
  | 12 => rootLookup 181 431 7 13 8 4 rootSH12
  | 11 => rootLookup 331 719 8 14 9 4 rootSH11
  | 10 => rootLookup 53 127 5 12 7 4 rootSH10
  | 9 => rootLookup 5 11 1 8 3 4 rootSH9
  | _ => fun _ => none
def rootS : Forest := ⟨511,14,fun j => rootSSamples[j]?.getD (0,0),rootSCols,rootSAutos,rootSLevel,rootSIndex⟩


-- Successive groups record a common live-wire count and the number of states in the group.
def rootGroups (g : Forest) (k : Nat) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | first, (ar,n)::xs =>
    (header g k first n ar = true ∧ rowCut g k first n ar 0 ar = true) ∧
      rootGroups g k (first+n) xs

theorem rootGroupsBlock (g : Forest) (k first : Nat) (xs : List (Nat × Nat))
    (checked : rootGroups g k first xs) : block g k first (xs.map Prod.snd).sum = true := by
  induction xs generalizing first with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨ar,n⟩ := x
    obtain ⟨⟨hd,hr⟩,rest⟩ := checked
    exact block_merge (cutsBlock hd hr) (ih (first+n) rest)


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb8_0 : block rootS 8 0 6 = true := by
  apply rootGroupsBlock rootS 8 0 [(9,6)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel8 : block rootS 8 0 6=true := rootSb8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb9_0 : block rootS 9 0 77 = true := by
  apply rootGroupsBlock rootS 9 0 [(9,16),(9,3),(10,16),(10,16),(10,16),(10,10)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel9 : block rootS 9 0 77=true := rootSb9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_0 : block rootS 10 0 83 = true := by
  apply rootGroupsBlock rootS 10 0 [(9,3),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_83 : block rootS 10 83 96 = true := by
  apply rootGroupsBlock rootS 10 83 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_179 : block rootS 10 179 95 = true := by
  apply rootGroupsBlock rootS 10 179 [(10,16),(10,16),(10,16),(10,15),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_274 : block rootS 10 274 96 = true := by
  apply rootGroupsBlock rootS 10 274 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_370 : block rootS 10 370 54 = true := by
  apply rootGroupsBlock rootS 10 370 [(11,16),(11,16),(11,16),(11,6)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel10 : block rootS 10 0 424=true := (@block_merge rootS 10 0 179 245 (@block_merge rootS 10 0 83 96 rootSb10_0 rootSb10_83) (@block_merge rootS 10 179 95 150 rootSb10_179 (@block_merge rootS 10 274 96 54 rootSb10_274 rootSb10_370)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_0 : block rootS 11 0 80 = true := by
  apply rootGroupsBlock rootS 11 0 [(9,2),(10,16),(10,16),(10,16),(10,14),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_80 : block rootS 11 80 96 = true := by
  apply rootGroupsBlock rootS 11 80 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_176 : block rootS 11 176 44 = true := by
  apply rootGroupsBlock rootS 11 176 [(11,11),(12,16),(12,16),(12,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel11 : block rootS 11 0 220=true := (@block_merge rootS 11 0 80 140 rootSb11_0 (@block_merge rootS 11 80 96 44 rootSb11_80 rootSb11_176))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb12_0 : block rootS 12 0 30 = true := by
  apply rootGroupsBlock rootS 12 0 [(9,1),(10,12),(11,16),(11,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel12 : block rootS 12 0 30=true := rootSb12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb13_0 : block rootS 13 0 3 = true := by
  apply rootGroupsBlock rootS 13 0 [(10,3)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel13 : block rootS 13 0 3=true := rootSb13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb14_0 : block rootS 14 0 1 = true := by
  apply rootGroupsBlock rootS 14 0 [(9,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel14 : block rootS 14 0 1=true := rootSb14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSGeom : graphValid rootS (boundsBefore known383)=true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem rootSTables : checkedTables rootS 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootSlevel8
  · exact rootSlevel9
  · exact rootSlevel10
  · exact rootSlevel11
  · exact rootSlevel12
  · exact rootSlevel13
  · exact rootSlevel14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSImpossible : Impossible true graph 14 inputs.toFinset := by
  have result := index_root (g:=rootS) (m:=511) (cap:=14) (i:=0) (ws:=inputs) rfl rfl (before_sound known383 valid383) rootSGeom rootSTables (by decide +kernel)
  exact (show graphGoal 511=graph by decide +kernel) ▸ result

def rootMSamples : Array (Bits × Bits) := #[((-0xffffffffffffffffff000fff000ffffff001),0x544544544544544544544544544544544544),((-0xfffffffffffffff000ffffffffffff000001),0x823823823823823823823823823823823823),(0xfff000000000000ffffff000,0x314314314314314314314314314314314314),(0xfff000000000000fff000fff000000,0x69069069069069069069069069069069069),(0xffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00)]
def rootMCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,2,312,824633721541,8),(0,4,305,77309412042,8),(0,8,99,824633721748,8),(0,16,486,521,10),(0,32,30,17179870145,8),(0,64,189,770,10),(0,128,347,548,10),(0,256,23,412316861160,8),(1,0,494,134218256,12),(1,2,312,824633721540,7),(1,16,486,520,9),(1,32,30,17179870144,7),(1,64,156,4294968098,7),(1,128,330,134218292,7),(2,0,445,77309411904,12),(2,1,332,412316861104,7),(2,4,305,77309412040,7),(2,64,189,768,9),(3,0,428,77443629648,9),(3,64,156,4294968096,6),(3,128,344,548,6),(4,0,379,824633721472,12),(4,2,312,824633721537,7),(4,8,99,824633721744,7),(4,16,354,824633721481,7),(4,64,57,824633721730,7),(4,128,347,544,9),(5,0,378,824633721472,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(6,16,480,521,6),(6,64,57,824633721728,6),(6,128,281,77309411936,6),(7,0,504,512,7),(8,0,487,33554960,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,64,165,33555218,7),(8,256,23,412316861152,7),(9,0,486,512,8),(9,16,486,512,8),(10,0,437,77309411904,8),(10,4,305,77309412032,6),(10,16,480,1049093,6),(10,64,165,33555216,6),(11,0,480,1049092,5),(12,0,355,824667275920,9),(12,16,354,824633721473,6),(12,64,177,770,6),(13,0,354,824633721472,5),(14,0,497,512,7),(16,0,495,512,13),(16,1,332,412316861090,7),(16,2,424,581,7),(16,4,353,650,7),(16,32,78,897,7),(16,64,165,6292234,7),(16,256,135,616,7),(17,0,494,512,11),(17,2,424,580,6),(17,32,78,896,6),(17,64,172,770,6),(17,128,330,548,6),(18,0,428,77309414977,9),(18,1,332,412316861088,6),(18,4,353,648,6),(18,64,165,6292232,6),(19,0,428,77309411904,8),(20,0,355,824652595848,9),(20,2,424,577,6),(20,8,99,824633721728,6),(20,128,330,1569,6),(21,0,490,512,7),(22,0,353,824652595848,6),(24,0,487,512,11),(24,4,353,642,6),(24,256,135,608,6),(25,0,486,512,8),(26,0,165,13271448945472,6),(28,0,355,824633721472,8),(32,0,351,412316861056,12),(32,1,332,412316861074,7),(32,16,198,15393162789641,7),(32,128,347,516,9),(32,256,23,412316861128,7),(33,0,334,412451078800,9),(33,16,198,15393162789640,6),(33,64,156,770,6),(33,128,330,134218260,6),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(34,64,29,412316861312,6),(34,128,281,77309411908,6),(35,0,476,512,7),(36,0,347,512,8),(36,128,347,512,8),(40,0,215,15393162789632,8),(40,16,198,15393162789633,6),(40,256,23,412316861120,6),(48,0,334,412316862081,9),(48,1,332,412316861058,6),(48,128,330,1541,6),(48,256,135,584,6),(49,0,334,412316861056,8),(56,0,455,512,7),(64,0,447,512,13),(64,1,396,562,7),(64,2,312,824633721477,7),(64,4,305,650,7),(64,8,163,788,7),(64,32,30,897,7),(64,256,23,412316861096,7),(65,0,428,134242834,9),(65,2,312,824633721476,6),(65,16,166,13194139534088,6),(65,32,30,896,6),(66,0,445,512,11),(66,1,396,560,6),(66,4,305,648,6),(67,0,428,134218256,8),(68,0,313,824633729666,9),(68,2,312,824633721473,6),(68,8,163,784,6),(70,0,313,824633721472,8),(72,0,167,13194173088528,9),(72,4,305,642,6),(72,16,166,13194139534081,6),(72,256,23,412316861088,6),(73,0,166,13194139534080,5),(74,0,437,512,7),(76,0,163,13194173088528,6),(80,0,431,512,11),(80,1,396,546,6),(80,2,424,517,6),(80,8,163,772,6),(80,256,135,552,6),(81,0,428,25090,8),(82,0,428,3585,8),(88,0,167,13194139534080,8),(96,0,31,9208409883520,9),(96,1,396,530,6),(96,256,23,412316861064,6),(97,0,30,9208409883520,6),(128,0,383,512,13),(128,1,332,562,7),(128,2,312,581,7),(128,4,305,77309411914,7),(128,64,29,536871714,7),(128,256,23,616,7),(129,0,334,4966056496,9),(129,2,312,580,6),(129,16,326,4831838760,6),(129,32,30,17179870016,6),(130,0,313,77309936196,9),(130,1,332,560,6),(130,4,305,77309411912,6),(130,64,29,536871712,6),(131,0,312,77309936196,6),(132,0,379,512,11),(132,2,312,577,6),(132,8,99,784,6),(132,64,57,770,6),(133,0,378,512,7),(134,0,313,77309411904,8),(136,0,355,33817108,9),(136,4,305,77309411906,6),(136,16,326,4831838753,6),(136,256,23,608,6),(140,0,355,33554960,8),(144,0,367,512,11),(144,1,332,546,6),(144,4,353,522,6),(144,8,99,772,6),(144,32,78,769,6),(145,0,334,4831838752,8),(146,0,365,512,7),(148,0,355,18874888,8),(152,0,355,262660,8),(160,0,351,512,11),(160,1,332,530,6),(160,16,326,521,6),(160,256,23,584,6),(161,0,334,134218256,8),(162,0,349,512,7),(164,0,347,512,8),(168,0,23,15410342658880,6),(176,0,334,1537,8),(192,0,319,512,11),(192,2,312,517,6),(192,4,305,522,6),(192,32,30,769,6),(192,256,23,552,6),(193,0,318,512,7),(194,0,313,524804,8),(196,0,313,8706,8),(224,0,31,8796093022976,8),(256,0,191,17179869760,12),(256,8,99,824633721492,7),(256,32,30,17179869889,7),(256,64,189,514,9),(257,0,190,17179869760,8),(257,16,166,17179869768,6),(257,32,30,17179869888,6),(257,64,156,4294967842,6),(258,0,189,512,8),(258,64,189,512,8),(260,0,187,17179869760,8),(260,8,99,824633721488,6),(260,64,57,824633721474,6),(260,128,27,17179869792,6),(264,0,167,17213424208,9),(264,16,166,17179869761,6),(264,64,165,33554962,6),(266,0,165,33554960,5),(268,0,243,512,7),(272,0,167,17186161224,9),(272,8,99,824633721476,6),(272,32,78,641,6),(272,64,165,6291978,6),(273,0,238,512,7),(280,0,167,17179869760,8),(288,0,31,429496730304,9),(288,16,198,521,6),(288,64,29,412316861058,6),(288,128,27,17179869764,6),(289,0,222,512,7),(292,0,27,17179869760,5),(296,0,215,512,7),(304,0,15,429496730304,6),(320,0,191,512,11),(320,8,163,532,6),(320,32,30,641,6),(321,0,190,512,7),(322,0,189,512,8),(324,0,187,512,7),(328,0,167,33554960,8),(336,0,167,6291976,8),(352,0,31,412316861056,8),(384,0,31,17716740704,9),(384,8,99,532,6),(384,32,30,17179869761,6),(384,64,29,536871458,6),(392,0,23,17716740704,6),(416,0,31,17179869760,8),(448,0,31,536871456,8),(2016,0,1567,0,7),(2528,0,2079,0,7),(7648,0,7199,0,7),(1880,0,1703,0,7),(4440,0,4263,0,7),(8024,0,7847,0,7),(12632,0,12455,0,7),(2246,0,2361,0,7),(6833,0,6990,0,7),(4764,0,4963,0,7),(9372,0,9571,0,7),(42976,0,42527,0,7),(44512,0,44063,0,7),(48096,0,47647,0,7),(53216,0,52767,0,7),(58336,0,57887,0,7),(42840,0,42663,0,7),(44888,0,44711,0,7),(47960,0,47783,0,7),(55128,0,54951,0,7),(68952,0,68775,0,7),(44230,0,44345,0,7),(60102,0,60217,0,7),(52913,0,53070,0,7),(60081,0,60238,0,7),(42652,0,42851,0,7),(44700,0,44899,0,7),(49820,0,50019,0,7),(52819,0,53164,0,7),(59987,0,60332,0,7),(69203,0,69548,0,7),(42820,0,42683,0,7),(47937,0,47806,0,7),(69253,0,69498,0,7),(69194,0,69557,0,7),(44420,0,44155,0,7),(44868,0,44731,0,7),(53057,0,52926,0,7),(42792,0,42711,0,7),(47905,0,47838,0,7),(53025,0,52958,0,7),(42764,0,42739,0,7),(44812,0,44787,0,7),(52929,0,53054,0,7),(60037,0,60282,0,7),(44618,0,44981,0,7),(47672,0,48071,0,7),(52771,0,53212,0,7),(59911,0,60408,0,7),(69127,0,69624,0,7),(1472,0,1087,0,8),(1440,0,1119,0,8),(11616,0,11423,0,8),(1352,0,1207,0,8),(3400,0,3255,0,8),(1304,0,1255,0,8),(18626,0,18749,0,8),(11425,0,11614,0,8),(18593,0,18782,0,8),(18577,0,18798,0,8),(1164,0,1395,0,8),(18566,0,18809,0,8),(11331,0,11708,0,8),(3100,0,3555,0,8),(2912,0,2719,0,8),(8353,0,8542,0,8),(69254,0,69497,0,8),(47665,0,48078,0,8),(69148,0,69603,0,8),(49825,0,50014,0,8),(2370,0,2237,0,8),(2212,0,2395,0,8),(12313,0,12774,0,8),(1858,0,1725,0,8),(17218,0,17085,0,8),(11586,0,11453,0,8),(1188,0,1371,0,8),(6169,0,6630,0,8),(13337,0,13798,0,8),(43330,0,43197,0,8),(58690,0,58557,0,8),(43728,0,43823,0,8),(46244,0,46427,0,8),(48292,0,48475,0,8),(49177,0,49638,0,8),(55321,0,55782,0,8),(44354,0,44221,0,8),(44866,0,44733,0,8),(53058,0,52925,0,8),(55106,0,54973,0,8),(58178,0,58045,0,8),(42660,0,42843,0,8),(44196,0,44379,0,8),(58020,0,58203,0,8),(47641,0,48102,0,8),(54809,0,55270,0,8),(69145,0,69606,0,8),(59649,0,59646,0,8),(43048,0,43479,0,8),(55330,0,55773,0,8),(46090,0,46581,0,8),(58373,0,58874,0,8),(73857,0,74110,0,9),(43904,0,43647,0,9),(50824,0,51063,0,9),(43650,0,43901,0,9),(50817,0,51070,0,9),(43104,0,43423,0,9),(58436,0,58811,0,9),(59395,0,59900,0,9),(1696,0,1887,0,11),(13984,0,14175,0,11),(7812,0,8059,0,11),(17028,0,17275,0,11),(16913,0,17390,0,11),(17216,0,17087,0,11),(2192,0,2415,0,11),(2368,0,2239,0,11),(4800,0,4927,0,11),(6848,0,6975,0,11),(2208,0,2399,0,11),(9376,0,9567,0,11),(4752,0,4975,0,11),(6800,0,7023,0,11),(2180,0,2427,0,11),(9348,0,9595,0,11),(9240,0,9703,0,11),(12305,0,12782,0,11),(2880,0,2751,0,11),(1216,0,1343,0,11),(18624,0,18751,0,11),(1184,0,1375,0,11),(18592,0,18783,0,11),(1168,0,1391,0,11),(18576,0,18799,0,11),(1156,0,1403,0,11),(18564,0,18811,0,11),(27672,0,28135,0,11),(6161,0,6638,0,11),(27665,0,28142,0,11),(1856,0,1727,0,11),(2240,0,2367,0,11),(6816,0,7007,0,11),(9360,0,9583,0,11),(4740,0,4987,0,11),(16962,0,17341,0,11),(13841,0,14318,0,11),(42816,0,42687,0,11),(44224,0,44351,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(44676,0,44923,0,11),(69252,0,69499,0,11),(59970,0,60349,0,11),(69186,0,69565,0,11),(42520,0,42983,0,11),(44568,0,45031,0,11),(52753,0,53230,0,11),(59921,0,60398,0,11),(58688,0,58559,0,11),(64320,0,64191,0,11),(50880,0,51007,0,11),(53952,0,54079,0,11),(46240,0,46431,0,11),(43664,0,43887,0,11),(53904,0,54127,0,11),(48260,0,48507,0,11),(43600,0,43951,0,11),(43074,0,43453,0,11),(64066,0,64445,0,11),(49169,0,49646,0,11),(58176,0,58047,0,11),(47808,0,47935,0,11),(69312,0,69439,0,11),(44192,0,44383,0,11),(73888,0,74079,0,11),(49796,0,50043,0,11),(57988,0,58235,0,11),(68625,0,69102,0,11),(44352,0,44223,0,11),(44864,0,44735,0,11),(53056,0,52927,0,11),(55104,0,54975,0,11),(42688,0,42815,0,11),(44736,0,44863,0,11),(52928,0,53055,0,11),(60096,0,60223,0,11),(42656,0,42847,0,11),(49824,0,50015,0,11),(58016,0,58207,0,11),(60064,0,60255,0,11),(42640,0,42863,0,11),(47760,0,47983,0,11),(60048,0,60271,0,11),(69264,0,69487,0,11),(42628,0,42875,0,11),(44164,0,44411,0,11),(60036,0,60283,0,11),(73860,0,74107,0,11),(44610,0,44989,0,11),(68632,0,69095,0,11),(69144,0,69607,0,11),(47633,0,48110,0,11),(54801,0,55278,0,11),(69137,0,69614,0,11),(26632,0,27127,0,12),(3076,0,3579,0,12),(18434,0,18941,0,12),(11265,0,11774,0,12),(18433,0,18942,0,12),(47624,0,48119,0,12),(47872,0,47871,0,12),(9344,0,9599,0,13),(16960,0,17343,0,13),(9232,0,9711,0,13),(53888,0,54143,0,13),(64064,0,64447,0,13),(43536,0,44015,0,13),(47744,0,47999,0,13),(57984,0,58239,0,13),(57920,0,58303,0,13),(42512,0,42991,0,13),(59920,0,60399,0,13),(43648,0,43903,0,13),(46208,0,46463,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(43072,0,43455,0,13),(43584,0,43967,0,13),(53824,0,54207,0,13),(58432,0,58815,0,13),(49168,0,49647,0,13),(50704,0,51183,0,13),(53776,0,54255,0,13),(55312,0,55791,0,13),(42624,0,42879,0,13),(60032,0,60287,0,13),(44608,0,44991,0,13)]
def rootMAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootMD15 (i : Nat) : Nat := 0x92360d87ff
def rootMH15 (i : Nat) : Nat := 0x102900157db68d4297000014000d3d0400b121d016f07000032a275464aeb889ba016b643bec888b331a1d2d47420db71568b48f28610be04c067392476876c1ec003180064d02c00010213044005000d2004000002001
def rootMD14 (i : Nat) : Nat := 0x3bce83c4f0bc0efbacedbaa74158268ee1eb3ef14c25059de775e5770e82f8770f5db634cf13c2f009ae2384d132ccaba2d5b78b538e814c1603c25025d7745dc6714740a612b405087aed9dd51dc3d78db362d936ed0b8384e0adaba2ecb51da86899e65990611835a50e3b2ac92f6bfb22b51f02a15f462d403aca012c00ffd64ffd60ffd40ffd30ffd20ffd10ffc30ffc20ffc10
def rootMH14 (i : Nat) : Nat := 0xb0e821c2754b84a12890f1353d223f52739524188c38ea1c13492385a92995db1e11f9109110a692f43e3a53bd83802aa2ed16510251840c248235ae33e8303aa24800283984fcbc5ac9ada1d422536306954b20a3b8aa3b205d88b12b8ad11eb269180443a3d22bcb5cf04bc20816b8640b3a4140933834860addba7028a4903d8a34c33453e183514b00b107d602398bda0a004a2881f5b5d48ba623a91605802f8d2b1ba08000b9b04ca31006535a424b3a3c0090d98b424a053c085c6000000000c4b8a5855031ba1a44898d94c535d5da5d9d010833b4d841000000bcd856324a9242380a1308c722109c3018578a4c97a13ac78865e121bd4a10b20545d8528c48261318d381e40f24b05f090100b4f051a46018448a3d05c3e001b5b7b4610401932755d80f9198e0b4213283f80c51f89bd5ed9f20c0cda0dbc201a80311a01c12e84db9015009233d103024396d4eb8124532a96058ca4000732c21984510211d44e82b829b5b45ab23561c9245084292ad378321098d1b0bab438ba22040000030000010001047a00016f0804382600000c36001c720002011a9602000312000500010002c31b080007222e0406000208171d0501000806000000030e020f00020a03050200000506000000025503002c050100180002230085011d07084706010001004a040000160004010c00001a090300070005000101101e03
def rootMD13 (i : Nat) : Nat := (if i < 1 then 0xcb28078602b03fc816004d7bb243b0a697fb2b64523400481b268f902817fb225ec7fd9558d005771c3b97bb2c5fc805a04bda7ae6f4de19e320600dd9882e98daed862b4063de05812da07a305926ddb73ef5d2f79ee9bf3136ec095d53406bcc59145dd5b176cec99bb34063c4784f01c232c656d5dbc0566888a2c049dd1d0794ee0770a6778edab587a3418779f13e17aa70ce11a232c0ad5616a1a067c8a38049dd1d07703b8253bc76f4924d87a34182d4268775d12861e98cf1a22d45d4e4983320658c2242984d02cf65ec5de34a690b73d7bb66146843d0c45e603a0129c7036644bf97b14c6a8bca82982502c03def5e133e708d118c0566ac8a34298167bcf75ee5d5024136c99bf3406bcc591470160eef74e11a2ae8048e29852d45b5614c128777bc678d10730245a8d418458257c176ce21c2344658ca9830ee62ad002b3785dde14ec5db3b763a050c09bc71dcc9a8d41c9388688b5077b08678cb101519233d5ece3995afe644b5207405304b62ed9d93376708d024e41c7324644c51832ee080c49952feb38860ab69b331668aba1c232645146a0d9993388658b518bb08678d10ff59c838e70cca9923155ecc896a49c732a64abdd7f3225a8e710e1570ae85d8b518e39c3354654c917b2fe644b5274f7cf5332ac7c7131c276f85b9e2d60b43acbcb152b47a9c69c7a44a868a0027569ade65a97f6574924e4368eb630e890e16d8231ff87d0de6d765dd3a731dc076e25b376b11a5168299ad64bd8bc60757735b2561f56dd53952ed41c4ed134c4ab523a469911d432d0583f68f883caceb83a1ce1f3684d39323cc272ea4b622b90a5b26f093323b08841f3c75c1b2062916ac52d120c4100e743400b6025a079c16904040af02bc0680003ffae4b27ff5c164ffecc2c1ffd84583ffb02b07ff65d60ffeb9ac1ffd71583ffae0b07ff65160ffec8ac1ffc95583ffa84b07ff50560ffeb8a81ffd63503ffac4a07ff58540ffe992c1ffd814c3ffb22987ff24d60ffe90ac9ffd84483ffb30907ff60520ffec0241ffd74483ffae6907ff5c120ffea9a41ffd43483ffb28907ff50520ffec9a41ffd31483ffa60907ff14d20ffec8a41ffc98483ff926907ff24960ffe292c9ffd83443ffb04887ff60110ffeb2a21ffd63443ffac4887ff65910ffeb0221ffd52443ffaa0887ff4c910ffec9a21ffd30443ffb24887ff48110ffe40a61ffc914c3ffb04187ff5c430ffeb0861ffd81083ffac6107ff0c420ffec1021ffd73043ffaa4087fe5c120ffc98241ff960443ff240887ef50540f7eb2ac1efd64583dfac6b05ff66120bfecc0417fd97582ffb2e085ff65940bfecb2217fd960c2ffb2c105ff65120bfec9a217fd93082ffb26085ff64910bfec90217fd910c2ffb22105fb64810beec98217bd94042dfb2c1857f65c10 else (if i < 2 then 0x7e6bcd00ff1a0450bce20b3d9bbc668cc96e56a710e11a232c6563bce8bb8615ec1b07af76d508b90f46a8d7e6ef3e12ee0acc60d02287bbd774c493635e3408a1c04b9bbb976c9b1151a0d9c8a2629dde7c0935ea9c4354688cb4771a1795f13e133e70859ce832aa86ed9770564531779f13e17c067dea9c33846fcd51a23405dc8b1155583401591499872e7136cb17d34c670dbbda7b2630801bc21b689e8581ebcdbc2652e15a2aeef78cf91435664c7d98cb2d00241a81e82b7bd756d156a7ba67c8a1bc356436e13c1ebde319786d319f21a6ac8a2629812bbd7750b477bcb772ed83171c654d89ad228f4a667e29c165423417405084b0253bdd7bb9745cba129aa14ee0aeebddc3268013796eeddb726614b69144086bbd751c6de2bc2648dc10a3843fecfb15624d3866a8d12777c4f85f01c432a60cbb9963856825082bbb662a883d5aa4d5d168250c3dbb684a689629c2502c02650c3d28ef69f01a061a296a9dce49c832c654e21c2737681ec5db314e158f81ce99e388708d15a032c63cca98a056608de5db200e724f69ec24d376640c01694ee6f4de19e31e621ebda00c576c809749bda56a678e49c4384688cb27732af61eb9882e863ed00b9bb66ece1d27405304a0590780956a936d03979430f6edb5f0be07a2710d1196306654c517709b682ed9c2352e4e0f85f03d149af54e21a232c60d3b98a2ef680ca84b05776ce11bc9be27c0f39269c3344658c1ab57c2628bb84632a60815ca134070a6ba15aa7744b68250ddb32a85d094e7445304a02526c3d33c6815284e49c434460cb5277390658c517738568015bd7bb6656235412b6b2d25a818da020176dc6b935ae84a6894121bb384680e3806abcb72edaca3824314621c5a9e53c17036806f9c804976cba39355e5bbd770c2369228610d781cf1771fceeecfb7b43b6b676ec843bd32c646f198b326455694d12c0f81211ad9d93baa6ecc5aad99c9388654c519630764ce15bb026f60d118b72167bcf75ee5933136ec091a022862cd9dd52066fde859ef3ddb66f70c4dbb37e0483d18b35e64cd01087a5344af79eedb37b86fec98120fd754c5914376681ef79ee989b766fcd01af3164512f79ee9a22d4f72dd9bf3406bcc59145ae844b02423593b166cca9bddbaa6ed6710e11a232c654c19772d562ec99b3304400dfb9d6db371d62cc99bb32a4448a25742535436ceddd8bbc664c8a26d99c9390658ca96a38562eddbdc344f5c3d19372e84a6896c5db3b26708d01bb228ab16720cb18a2ef6cccad93344090dd9a0384d1c0081b8bac18edd43d3cc740584bb3a365d1012e80a6dd7724500e16009809ae0364a6da22da5d2bb29e601bb82095ed174200616c08ffb44b7ba6143bdc02da44c8a1c2c02bad228423184b456790024095a279af78280ff30967a else 0x286ef1b1bbe6e1cf10133b1dce19aeb3edfda219ecddeba8ad4c65e2bc0674b95db388708d119632af60d819c5420ac8a1c335e402cfe929ddd35c6b4cc197359772edaac2da6125f43d1a0f8a665cd61ab7c4f85f019f49b76ce21c33846a8d11952ef1de5098b32c629560d030645015978e453bba6b4cbddc2da610df9a0324644c498b7c10f4cc8d08ddeba86c4cd1b07af76c45ab55430f4c28d069a5348668cca4d7b1778c65dc0c4341ecbd33646c4d83d7bb66be742b55431de1e985c862bbd750d899a2df3a150992323135ecbd83486655addc3))
def rootMH13 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xd6488b409456ca16482d92f2996391c107a6c3e80d3493ba56c85f6827a2bc07140319c38135168fc0939c9e8236053e0d5a122528005f088f2cb9ba42424920a581fa33042e812440e3b39f153a03d117c21b4040511305785c32606e11300af3a4e011e4864964b410736c120c040d91b68e08680033db7988dc8cce4ae83e2032810b68bd8289b2600c8416203d641e221a11dfd173057c0e181aca17e42b60b68933843d727200b81f358d17342866ca3103930434e732848aa0f045001c115b013706040000122b46c67d42bf809e049720a62df4149000073b60502992000170f701681de4a4226662a24172841825ac102ca3f82c6000000051d72221480e2a1921f58df392c0854221d288a6a74e6c5680910000242c9224000104e223354de00b61092444c2404451b41006681d40001654708c1902025f54984db0d258904432a48c640a000002c42bf4099b03d60080cd9062000102e00b00007010240e407188420181001c24050450d4070080511c06024050001602409000010182b054000000c0000b03400024060300f038050040100c05014310102500005398010a400004030000407c0000001000000140100c044c0a3000040600c01c1422001008030001e048010549509c03011830540e0000e0042c048020140d0001606c05234000b00306c4e6900300800000080140e03c110141b00818004060342d100000080000c610503802c67000040dc3104c03180020244709403004030680000809014de00408034050584e058020000503c0011c02028010100d0240704009014660780e008bc0041400c02008120a402000000000004c0100400004020080800c0200d0b0080b0000b0000308c0007c0000400030011940002003038311b46f05c020344e0040900812018000500a38008084034540003801000000003705400014000f01d000000000000c0000800020050180b0000001c2b00401000050380702400018000d00f0940a0e0010380002c76010001dc020500e000000045a000030007800c0e024180180000c040000c4f41a008140040d08c000280113c060003e0040701c02018060040800017210010c01f00000004000000a000f80040b00c041c80100001004020002c000030000701c0004089008000041908c090cc03090000000106c1905c002c408034040641965801000700001a000041e01e0088c0180000401188940c000234110005200005000040d42708400000000a5710280b3d409204030000124812010010380d00000060170006700004084050090300403004000cc01014160008a0001e2dc0000d9b000050a00a00800014020000a0003a000010080706000044820102d10803004120000000040028030280101c00012110000801c08074020040f0000801c0400c020040d004010080d else 0x222a16828223288c3820312dfa712887812158db8041423004b041103c08f501b75c4a63e0028e0f78085037f22e0850c271019e0ff6934214877f085b807ea42408e64c319a5387942d40d0ecccdc874628472e4ce891ba2372b58054c9ba01d282e892da2ef436e401e13f88550652d17112eb0e524760534915a40d06468f0dd80d1b605a4117210202a605d6d24dc95382115c448d6070423b47c0c532980312d0110e13120b112e08aa83d65945043059cc1c188781f483fc911aa1e138596ee104818a0218079e23a41f623ef2262eaa807daa2f00c601e01ef3a38062411d88b701fd853c062c01aa28a361e03040e4000021486ea015801ee546e8389d198bda550e8f0046109e507548f201a513670240066291f448f726b28748db8018b70888a5047db1bb72107ac107d856a3da2df8151ac34430a4d259aa214404b830d406b33b52124445405780ec270c0811c7304369848e2d91460000007a014ee3a00000000c63809a30dc63076c62a44033903860cfc0d08836a9220824e455a40a8a48ed005c31f502d40e644b713796574631ac6c8a3503d6899088402d7060a217451b32b0033a063003410b00574ec8553982962174ef72952224870e74c99a3982557002038985f02fc209604e64a8812f0230018004f5c69479e0aa9035a16978f748d895f035242db0b18174ab4924f64d501fc814f02b00abc00e8b17483488d91fe023a008e425286db01206884e2885a2860704604248320449053a71710ab240b642e86e0197010a00020e7c080849346200e3891c10dd618485d81508330007e83da11593dc63dc239c1e123d604ea854ee24832702922a680d8927c06c406140eab3bb072166e4131b92133392a0119b027304fe0c2d9bc0a4d74340b0c18ea3e921aa6e065eca91a02940b8591538ca015a82f416c417e21ac23f0c889301b11d6d2ccfab1fb43072ee018843ec70aa4ad2dccdbd5081f6a001b920f9111c834a9cb040006bec7ae8d1016f625324891ef988fa03f23281dd53dd0462c57dc3a022aa33eaacd18013812634858409283f2240c0df40a101d3966444b48dfd0f3108d44d804d80e564f229b04bf88792680b0c54c28039b6f4e41c0e501fa75384b8406cd296037526bed8f0bec145c0dacdd68b24426e0c3823c0b8604ac0c340c90223b52eafb5202a1a842f20ce921d807306eb4c8e0db82b566e48588dd110e734c841998c00166068c11e8078a9ed7318d099da3938ca1c485501aea1d603b40bdd18288ae050e51c913da442a3710a24dd5528b61e408fa42384405754061c11011400508100d220aa05732f6988006226870d8e1b80c48351046ae6408188009435426f2cf6c272057a11d413e03e9152803854f2a43d519ca8fd90a9b4b8078890c03603a5455203fc8198396478c0fee60e81) else (if i < 3 then 0x2b70418e230088a3ba07800f7009f0319a046846d1e281f903b0f19081630e767d20260227b2c5832c02c10a3041574160b8c842a01678c405901368ab3480525dc99ea42982180000000b8b4a4108edd9b71ac003c4063d9f2036003a202ec1370250a4f52fe187881b7425d6918000a4380000e1dc15c2b6c20382e2c05a022501dc0b3021800008922c3bc88e911f405211f48c4a2dc08c761105d2db9600340e74541023835f28bec22d0325014c43641da0182615e478dc79c3aa000107d421482d403e400ddc5e20d50204cbd9dc5000071d4f05a82c92c347964d6ac2cd27e02fe122ad954991b47a0412493c226245002cd1480b1326860ddc4c023b0091ecca85a6dabcb09cc89182450e9a7200bb45c70a8424b28fdc955b9dca312cdd41d6134f20c624508448233554811f820b02b2021e88cd42e5282308d2a9c03f8341010d4a659e8dc5ca8d56a6417923f8038811404ec5b03215a8318094b994781cc00c467d85d18be048887408c1075c02ae60b390801cceb58152d1e770716c7694312a0155a099658840ec08e0e0945294481570e86cc19903e100f809ee981aa9b485d25a29a78abda3c4037e112046c80542cada2c826a845c10aca1bc2744444ab86d4d83da07084ab6c6601a343164839213a172009444de88f004505dc2811d3cc3a7062c85401f7a303226807302062313483f67d1227240f86a94e485acb24f41dd6e320f6138313c44b4c12003eb67dc02f41a44a0e0592ebcc09d39e6b49a86950bd02d0022b518e611c208519a07a003a1abd00ca816020282ad06120fd4618b0ed424f68d986801a9083c0984133bb1102a8427c8d6003a674827dd215808342684ab9984531d14e00b7c9b9c26906b40922d41819016948344079000e225008040a35011249f511d01db10c012acb9c1b6c9cd453008b916a83792254cdc417a0a3d20804cd41db228e0703465516b00bf80d0094c0bc241209090a4120ca05fa0b4043096d526e20fa0d34096aa834333016415402fa221a8f36157b924048ceb7d1ee1277268c024dd99811b00f60fc121b42c52828aca10609a66022c09a01b28457b10eec180988445004d634c8fa5b26a44cf078462d3df65734b7c06d3133147e04188888368042646c09be92b2014a0b2820d219d07600cd5c9b1245571ec52d88c131907fe08440e7819751e40c78c583a9f1560cec897ca22521bc8bb083f00c504780b9d12d839573c709dd0d7db5367a812301605bde0014b0559f100a06054077a520a282673a092e610812a429d44d0195b16505e20c1c180b0c8033c6c4c03702dd68dd03ac000d34718b8ef651918126854e4218845588c01384b050c85842630a070595e40c108dea9b11deda8a13eb67950ae004947d7307c1d080c2065a4d299f6d9bd208e811513f205141c81 else 0x840800034e9d8f481fe00000000000d44b84056ad0000811c55096e71d51cbc467ce01a8d9504600302905611a822c256d06ba607337769281199175821643a806a86460000000249fc1d10))
def rootMD12 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x3dfd875cd20f7f5d173483dfd735c120f7f5c570483bfd9860520bff6a174482ffda865120bff6a053482ffda864520bff68980482ffda824d20dff66120442ffda750520bff69d93482ffda564d20bff69493482ffda364520bff68c98482ffda914d20dff64d20442ffda114d20bff68498482ffda124d20bff2a5814837fc9864d20dff261914837fca954d20dff255934837fd9258430dff2a5314837fd9824d20dff24d914837fc9524d20dff6a1920437fd5364810dff69592043efca258d60fbf59492583efd6324960fef504525937fd9114964dff249914c3fed8254910ffb54920443fdd314c910ff754d30443fdd314c110fbf59562443efd6358910fbf59560443efd6358110bff6a193442ffda864910bff6a120442ffda64c910bff69993442ffda54c110bff69592442ffda548110bff68d92442ffda14c910dff2a582442ffda020530dff61d910c37fd8264430dff6a1910c37fda764430dff5c5910c37fd6564430dff589910c37fda864420dff605910837fd6364420dff648814c37fc3166020dff65431083efd6258430f7f61d710c3bfd8160830bff695610c2ffda258430bff68d81082ffda158c20ffb60952043dfd875cc10bff68d82042ffda354810ffc54560443ff15148110ffa50970483fe9524c120efe601815837f9984c120ff654d30483fd9314c120f7e5d570483df9745c120f7e5cd70483df9715c120dfe64d20442ff9a014d20ffa54920443ef96558110fbe58d60442ff9a020530fbd58581583f755159510dfb649820c37ed8764810dfb6a1920437ed8264810dfb5cd920437ed5364810dfb695920437ed5264810df761d930437dd8264c10df769d930437dd7364c10df7695930437dd5364c10df754993043ebd8459160def55194482fbda414964faf591415837bd9650540def651414837bd8765010def609940437bd7365010def54d940437bd5265010dbf659635036fd8265830dbf69d960c36fd7165830dbf689960c36fd6265830dbf685960c36fd6165830dbf58d960835fd975c560d7f609970435fda365c10d7f5cd970433fd9860560cff605980827fda8651209ff6a1934427fda8649109ff689804827fda9608309ff6a1920427fda8644209ff6a5725927fda95cd609ff69d930427fda7644309ff695965027fda9589409ff6a4525927fda9585409ff6a5325827fda664d109ff699930827fda664430d7f65d610c27fca9605609ff695920435fd5265c109ff2a5425827fca9505609ff68d924427fda914d209ff2a5325827fda920530bef690814c2dfda7205309ff2a5814c35fca365c10bbf69893482dfda724d209ff2a5814827fca954d209ff2a5314827fca960d109ff2a5824427fca9595109ff2a5634427fca9589109ff2a5524427fca94c9109ff6a4310836fca165830 else (if i < 2 then 0xffe64d70483ff9a04c520ffe6a130483ff9984c120ffe60930483ff9814c120ffe60130483ff9a54c120ffe65530483ff9514c120ffe68930483ff9a14c120ffe2a130483ff8a54c120ffe64530483ff8984c120ffe25530483ff8a94c120ffe4c960443ff99358110ffe60130443ff98548110ffe60d20443ff9a848110ffe66120443ff98048110ffe54d20443ff9a548110ffe65520443ff95048110ffe68d20443ff99348110ffe4c120443ff55160560ffd4c581583ff53148564ffd54563443ff55158910ffd54596443fed524c120ff74c563503fdd314c960fef50572593fbd4250560fef61d41503fbd7350540fef5c541503fbd6550540fef58d41503fbd6250540fbf59571583efd8759160fbf59173583efd645c560fbf58d71583efd635c160dff691984837fda166120dff6a5824437fda960830dff6a5820437fda960520dff6a5810837fda166020dff5d1984837fd985c540dff661705937fd985c160dff661704837fd955c964dff645725937fd915c164f7f5c572593dfd735c164f7f5c570592ffda848564f7f61d71583dfd715c160eff60981583bfd8060560bff6a095582ffda260560bff695715837fd9558940bff69532582ffda524d60bff68c95582ffda548564dff6a5524437fda954810bff69492582ffda225560dff655610c37fd9825560bff68d415837fd4366120dff655434837fd9865120dff649635037fd9258540dff54d94483efd6550960dff661425837fd9750960dff64542583efd6350560dff661414837fd9750560fbf58d62503efd6258540f7f61d71502ffda358940bff68d61502ffda258540bff68d21592ffda14c960dff661934837fd9764d20dff65593483efd654c960fbf58d32583efd614c960dff6a5325837fd3265910bff68c92582ffda224d60dff615934437fda864d10dff661914c37fd8264d10dff661934437fd9360110dff595934437fda664d10dff589934437fd9664d10dff64d604437fda564d10dff655914c37fd5264d10dff689934437fd9264530fef4c5415037fd984c520dff4c5965037fd944c520bff6a1914c37fd984c120dff66130442ffda824530bff694914c2ffda920530dff261914c37fc9564530dff605930837fd6564c20dff699930837fd6364c20dff695930837fd5364c20dff61d930437fd8264c10dff69d930437fd7364c10dff695930437fd5364c10dff549930437fca366120fbf594935837fc5366120dff60d924437fda864910dff661914837fd9864910dff54d924437fd9564910dff68d924437fd9364520dff64d924437fd9114d20fef61121593efd6348564dff661215937fd9548564dff6a5215937fd9248564bff688814c2ffda114964bff688914c3fdd534c120ff74c530483fbd8450d20fef55194483fbd8450520fef6514148 else 0x83ffd845c560fff69571583ffd985c160fff55197583ffd8225560fff61d42583ffd9850960fff65d42583ffd425c560fff5cd41583ffda258d40fff68563503ffda358940fff6a532583ffda54c960fff54532583ffda14c960fff4c562503ffd314c960fff6a5814c3ffd5260530fff6a1914c3ffd9864530fff605914c3ffda564530fff655914c3ffd5264530fff689914c3ffd9264530fff2a1914c3ffca564530fff2a5814c3ffda848564fff69521593ffda348564fff4c921593ffd214c960fff61d84483ffda466120fff61198483ffda366120fff68598483ffda360520fff6a581483ffd9860520fff68181483ffda260120fff60980483ffda160120fff5d198483ffd845cd20fff5cd98483ffd985c120fff55173483ffd5366120fff54d81483ffd7454d20fff54d70483ffda954d20fff50d98483ffd9865120fff54d94483ffd8750520fff66141483ffd7350520fff54d41483ffd9550520fff61d93483ffda864d20fff66193483ffd9360520fff5d593483ffda764d20fff5cd93483ffd9764d20fff69593483ffd5364d20fff65593483ffda164d20fff2a193483ffca564d20fff66131483ffd3160120fff55131483ffd954c520fff65131483ffda94c520fff68131483ffd984c120fff60930483ffd814c120fff69530483ffd534c120fff65530483ffd524c120fff68530483ffd314c120fff28d98483ffc5366120fff14d81483ffda864520fff66191483ffd5364520fff68d91483ffd9364520fff14d91483ffc9864d20fff26131483ffca954d20fff25593483ffc954c520fff2a531483ffd9824d20fff24d81483ffc5266160fff14981583ffc5264560fff149814c3ffc5264530fff14893583ffca264530fff0c998583ffc3260560fff6a583443ffda560910fff68d82443ffda960910fff68582443ffda060910fff68980443ffd5360910fff54d80443ffd8354910fff54980443ffda354910fff6a552443ffda054910fff60950443ffd9854110fff61532443ffd814c910fff59532443ffda64c910fff54532443ffda94c910fff68532443ffd8564d10fff6a193443ffd8264d10fff66193443ffd9360110fff59593443ffda664d10fff58993443ffda564d10fff54993443ffd9354110fff68993443ffd3160110fff60930443ffd984c110fff60530443ffda54c110fff54930443ffd8564910fff60d92443ffda864910fff66192443ffd5364910fff69592443ffd9564910fff68d92443ffd9364910fff6a120443ffd9848110fff54d20443ffda548110fff64d20443ffca960910fff548914c3ffc8524530fff208914c3ffda160830fff68d81083ffda158c20fff69582043ffda360810fff54d82043ffda354810ffe61170483ff9985c120ffe55170483ff9535c120ffe54570483ff9415c12)) else (if i < 4 then 0x51b9a82ad3c869b1b4c89a562d27068e7b45d9a252d0d06841b40d99feacf9067a7b3b199c4acd9066a1b32e9981acb846565b29c993d2c96c646bb22299002c79c6395b1b798d0ac6506307b17098b1ac5106267b1209880ac3d061afb0c1984e2c22460f1b04d9818ac06c5fe5afd397d2abe545f03af7497b3abd2c5e75af2d978eabc345df9aeec97652bad05d41ae93973bab99c5cadae46971b2b8985c1fae0296f1ab7285b13ad559693ab3f059a7ac9396312b130584dabfb95e82aeb856f9ab5a959c2ac7055f3aada95622aab8551daa75952b2a8c4543baa0194efaa7245365a99694bd2a5605283a922947eaa3785183a8a2943d2a1545047a81393f8a9f244f5fa78193afa9d244e4da704936fa9b004d53a68a9335a993c4c47a5fb92dc2964c4ab7a5189273a9314493fa48f923ca91744887a41e91f9a8f14472da3599192a8c0c45c7a2b5914b289644449a20b90ea2868042dda146909b2842c418fa0a2903d281544071a0198ffea7f903f959fae8fcda7e2c3ebf9f378f8c27b843d899ea88f3ea78e83bed9dce8ed3276283ab19d398e88a73f839b19cbf8e502722838e79c578e11a6f98377b9b988db6a6d6836759b248d8726bbc35a59ab38d44269a4348d9a1e8cf9a6738333f997d8caf264fc322d98f48c6aa629c30f7985f8c21a606c2ff197d68bd5a5e302edf974d8b9a25c602e0396df8b61a5ab42d1b96718b24a58b42c3396098af9a57cd2ba815b7cad2456512aea1555ca984542d29de14c3ca53c521528c61452ca1cc5081281a13f9c9f344f412756138ec9b944d1d264a1305c971c4b112556127fc933448f9242c11fcc8f3446e1232c1179c8abc44b1220810f0c8644428120f0105bc81b440751ff00fd5c7dfc3e991f260f7cc7b643d4d1e6e0f26c783c3bc51dc20ecac75bc3a611cf80e6ec730c39511c6a0e18c6fcc37811b820da7c6c2c35a51aa00d36c68ec340519d60ccbc657c327119000c60c620c307118120becc5eb42ef517300b75c5acc2d0116600b10c57d42b9d15a80ab7c55242a5d151a0a7cc531c2935146e0a29c50b4280d13e009d3c4e1c26c113280980c4a6424cd122208fac46f423511164088fc436c215110820827c40a420050fd007cec3d4c1e350ee20754c39f41c890e0c06efc36841ab90d2a0569033f6197e0a67064343138184f0bf505e442e4016c70b3d058242b4815330a67051a4285013c309c104c7425b8128309270480423681167088d03164219a103807e383d581de20e80072b837681aea0d1006738326818b20c0005e582df8167a0af00539827d813520968048d8230810a2081c03f381cb80d92064c0311816680ab204e8025f81258081a0384017d8093803d201c000c580588025a00e00055801d8009a0000fff5d598583ffda95cd60fff695735 else (if i < 5 then 0x21c30d002b31f04de0e20d10bbeed8aa015a0059780dfcdec3e03fc0ace7c27aa3863542efd240561a0228900f7dd1aa10d0d002b11438c18c12de4d0086815980ad4adf903b15ee6595fc40264920b1af73241d829aaff32b32280d05347e405057f99157b0ff99548106bfcca8280a42bdcc94cb200ae71d5ec3b26595fc402681007bbc23180561a050d99c40580fb9a20d057499342b8404880880068142adf681e84027043415d268913260b13542021a050585749930099aa1010d03ce008986808a101dcf7670044c340450c04a7bd2ff3542021a06dd43d7179c3d0d006234c90a687f8314cacc8983420f41dc142644188c01fbba35a32fbb937f3413137c133387a1a0c9c99c4996009d6660f18499e9a24829812df04e24d10623744de015a76cf6ec2182ee64d62f78c455010c0cdb67b2616934137738428e914a8099d81809eb82d107706c8802c9cb6cba2b52b5ee6482e43b05365fe65664503160b12d40a133cb081ff34480620d002b1d26cbc81b61e8310681a0f43b0142644188afb4b0b0121ab3262280c470a65a602b0d02029807cde08681586818dec4003fc3400acbbc2b5405621a1a0228606600fddeddd9b1a250acaa19950d0501b0313eeadfad0604859ed9cc986829f7a5fc1626a8404340cfbb3802261a0228501bbdd5c096d11311436ee8a409683bccc86808a1c63c0ae71d5ec3b265a5fc402681338f07b3220c441160eb111114200d83b804eef5f15f0ce1cd54bb88b08a86805901588a3c0db62f6ce6803d964e6ec45117132d40b12d21d979a2036d67266f6a9ad13411418c9db8de61df8af8315ba9d04bb1b588a2ef32dc4eb8e480aca6e277e6ea0c42be0f47412ec7569dd714013e1b1288807f8cf28f14f04e070f576c3427200925d0e4d6794783b401bf3900482e80c5bb614a726b00f01600915014f148142be0bda04b13e581280d80b0b800580485282587609f8a06ed8730123802c3801dc12c5fc51667a6811bc61fc228306098b9bb114201208188a0ef766bc3f8450801f7bc0c131621c2286d93115144114208b03009a08a101805603fc62180244d81fe0261f66857d42a5614310947846b42226101907bf8341417b60af904b781ff40e96068102e78153408a60329012f8059400a5ff28ff177f653f9f5fbe8fdb37eb33f345f920fc437de93ed85f610fabb7d2b3e825f378f93f7c313e0b5eeb8f71b7b6d3da05ec50f5b77aaf3d475e8c8f3f379af3ca95e3f0f1b778a33c2c5e038ef5777553b795daa0ed0f761f3ac95d4f0e9d7748f3a1f5cf40e7537383399f5cba0e2ee72a3b93e9c912e3b871a3b8bb9c4fae22470e5b8419c052dfc46f91b7af9bc9ade006ea9b7269b882db706d7fb6859b362d91c6c5bb61d9afdad7ac6bbbb5be9ad72d6606b15b5749aadad5146a63b else 0xd1134830a128908ac00e8696ee0a609b088a8b1f03f02454f64f75562e6cd04a7b1732c2a7b260ba048b67341344a5bf99559212701d03539e1144129ccb0c9ce16dddee6c582ec3d2d9cd12e70a68845b62d680174076f5c45124a7baa7b9b26b662293761a08225db31bf07a5939bb1110d041ee4d109b08a0d02d986808b20f746fe5de68868164c6bc3404553bc616c2a6b1732614422a7286db39c210010800ad930679bb58b56d98800a688a02ecd12c5cddc8a256fc2e664e6ec340450cfbab7e03ab402a7326b5e1a022890d09c20a6bdcdbb114d8b5b307899351566c5ad9ec98844e14d002ec8a4dda803e68a65b62f64c420e3c0400926096ce6819b16206b2616c22222865bf99559215000a12799339e1144a07a04eea88e4dda8a0909e5d8040e8009039375ceb04510fb4ae815603608c20602aae0adb3941ff344c0589b30350d904602d5749a256d0ff9935cd54d108b030055ab6ce505108aa5f6828002835664d5c15d04510fb5326ae022a1fe50779a20847dd0120ff56d9ca57011653ee8094d14e52b688a07f9e67a6881800d4458438c06b33d34428222c21c60770129a20ff7de38958499e11548815638640901ba88a1836660c4e83ec822c0c022430120ff16d11611328b80ba1e600dee51312b6ed1208583641976885b65d364cf84a1b20252da06627a22c7012c090ff10a202c4c26b306908a8871839016804a61045444cc1a028805b87b2f7b226d910d001b13417b17f262d95d9248a80088900a6887165fc1dc4800b764443cd7bbb26341b76024344228b673169d8bd935b31a01a29bb30c7bf01dd0d11ce8cb0ca8cf0e10c40808ddeed831015ed01ce4402405994e89768376df3ef451bba35a35832e3082db324f377c13321a0b0256e8c16bd1bd7ddb14d3804812b29e0b6edbcbde8ed05eba6f4568167867b437a37837633c31071bbb6f81b400c4b7e01951bd1bb19e17f1017d079837306259ed0de8de0dd8cf0c46d00ba6ed8808312c6f06206005fc5d38d96801891b17b6602d340b27376602539bbcdb6b969b8939338d40a9ec5ec9eeacd02d99b6ec1e86837556cc340c7ba37fb763400f435eb261a080253bfbccb71b753a09763a342ee8d68cb8d63da2ee0d03d45f061e8cc86832f741e868004b64f6ec6cd68a62d235bae0b84b441b2aee2e92dab26902b99552b7e40ff57b98a100992482c4c96bd8a687fccacc89c16002664b5ec5fc5343fe65664521a0269386fc80a1322af61ff32a902099505014857b9929963868015ce3ccacc883f4c52bd8804d0283400ac02671e6566441f95ee70c4026816056a561d8af732cafe20132480d005057f99157b0ff995386800489a3f20282bfcc8abd87fccaa80800275fe6541405215ee64a6592056a8938eaf61d932cafe20134093e118be9))) else (if i < 9 then (if i < 7 then 0x115733f22bdcc88a609a140d66543485215ee644560e1a029738e1fe0a0af605aaff3232d4a06bddb7c0da0ca1065ae802d14d484883b5c98c286808b1a1dc0b4dac528534af6cb26b162202501f6b2cb2277aa10a13bdb3d9300a11105d9c29bb04e58b509dd29d1290782e8120888a3cdd8544e14d03294c54c85b64c1744204440926ec28a70962d8b261cc049376f2eb6738534022296e8103a25111216d939bb0240609a05a201d1145b376d9b7435aec5cddcd002e8602c9a44eeba043c51c0909de6ed65419c44668174a62102a642cdd1b1622337616d340b26b02d11f13b5a01112eee882ac5cd20680e147f88522e3778564e6e004a7083fc4291bc220b37138402421461140a610a38d9c20d036ef09d889ce10680869b7784ece7814a708340434f6e20b077e1a41e00560486eb2ec75a204740cdd4de08fe00b39e9773b3d9f10d49e5ee89bf8ac05ceeb9531d00a6a494de5e65a65662a60a7102e40ac576f5f76c176709c41f3893853152ee05603a0bab3cb4132ab3e11a20df3931771c2da09a93a302b51f09f00e20e10c10c50bbeed82ecde015acf88f3870cf846085dc51f2866800ad47c23042ee3140bab7934005683da3d81bd1bb19e1803d71bc174188ddb101da006273f00159dc3e82c56d0031088a0f68f60f5c67a6580ae6566285945d376e708189a7b07af39339132d32b3142fe020048b413840c4d20f14705dbdabe002d01d9a044e14c50126d01cc0310159c94c896f86f8271260817776e7083fe5ddba26f01e40ade1aa7940387272d3b402001b26d66ec736b28606a02d1019c21479bb0679a049cbac7cca82e8120a68a5016abf9c5ce12c398354f28e04e4f680404db436672376c0925d0f05c0c5b2734532a28e0a53901420bab173772ef340d01c2e898a9a006202b311b0a3bed2deaddabf8ab88a2c46ed816cca8313406f6805742741740b4ab051e65444b76c1e443da794727b401be28e6e02b5390263bb60492e8782d2e806a01d2869c29bb0671119a048731e59c58a39b58ca8770124c44c50809cbb2e26f3451e5a6dac1e0e34e4d09d1b172ee0562c7314142b260bb341377384c14205d2e801c03502d10001d5a038d39359cb9b58e14c44c50a38941cf28e047084a65d1680e4c4a1041e2ba14a09628e25060f80240d212058899578b3bcbac42c53b5894141890590272844c449b76c47914eef6cb8caee0ba240049bb621e9bdd01296d11611328078158ae092a0b01761eccf08d01aa818c3fc09019776e5d0534e242ae9340252222502b062ddb02414011e119382c6bd89d0a6cca8871a64818c0801405215ec0d66466565fd41a0af621c06a2740d405b32a1fe9c0978f012108203b5b486808b1177ada43404548bc002573c0a41fc2ee01776685621aa01248cb7b0e400b9770591 else (if i < 8 then 0x114062be19c297701280b0b30fb412aa158b995b5f15269cf4e14cb4c52b74158292684ca88a0313411f77b7516fd6803fc09ef865dc42162d6bc451b7c27273873552ef5580561a022a9be1be09c299614d0bd14a042027ca19a082b1470449a291483eceef4e14d108007fac2a3106808a2809cf7965370b6889df6980486ad64cb426f3659a7bdad433e35622a21a601bc4d3d91a618719c1b710d1bc2625abda266d310900905caca1d6cde08a23784538848048e266316526ac44c45140177bdad533f35622821a7b8d06a00b08839e10a11438035c72df83a0781e54d69cf08a2489583e83c2a02d82740b443ead5ba0ba053776c17665430010e35d141ed7cfb4f9eb7ab3cb20b1eb762ae0bab1057c21e05bbb732a0ceaff46e8ae825305d677a7722502d10fddb99558f0436a29aef2740832ed88a23b8682680199c74cab009577977404976ce4d1dee38f284506c46b40ce655cbbc8ef71c35a750228643640f018106114b8e9ad02d9b199550092c9cdfbc71d6add88a1f797778343772610da4450e6e9bcbbbb30bbb61f07812da556228a81679058b1580f85b35925039934b29b1b6d9edd888ef182e8514c9ac5a994cba044034a64da86a8483f77017775c4201f5659cca6027b661a41f029a242b16b77326a653a532250b66a1aa110805d0a299358b5eddce14c182e815cc50740a508a5ec4c5847ac9b605b6ed680018445f7562c4516cc3e023d6fe64d40dcca6c6db67b76fbab40222b5e0ba144b17326c653062db37dd59200607c07a4120c51085bb5a04ff9937beead7adf89b4c9ad008185b0512c588a2ef766fe6804d83e017564e62e6bc4514c6cc2db761a4210021b160f8b67326a108a165941092b511105d277ddc0d2dd70789936ad9e048780846c582305daa9beeaddcc9ad94c4218db6cc02b62c45023d6ee64d4ca62115d021e42c1a441f3260bbbb9bae2282221d2b2af9e29e19e09c211611510d9a238914e01d02b7d911470138a50164d025a8168a68a3ccf2403f786708e266300ac43434045120580d4fc06ecb88b14b06aee05b34133c21a056d06a10805d2862a1ddc0d2115dd708f9935ce24e14cb4ca88023bcc56eddeb82e8a6ac1ab6ee70a65440c0967226882aef5c4502da64d62dc42c32dba27402801725a1bae72429aa0d5dd114d14037b05ddd73a015848350285b8dba880de64bb05b1c48249d5aea8509455853047851775c421023cad429a0ba2ac1f1bb8ee228a99a21000ec03558496a99e38833ef4d10682b302801987fac24b54cf2c161f782140626780d453161044d222606afbd33d3442681f671139961580fb99e0355660e914c11254cf06cccb0a601aab33ef0ac089254ac57e64434006d5fdf901403c83fd5ee656625a0b01a532405b32a1d8aff32229a90d20ec57f57b99 else 0xbdf11ceccf8d71dc87db509dd4ca8800683577af606c5f88e7567c616a84e4d71170d70968af64f01654400340c04ee53400aecbbc73a6e7542b877b2b442007701fe1a0228c5de1b11a419aab5bd7185aa11bf1a002bbd964d1af1791140ff0d090cd0bd0d855ace24e14d14caa3baef5ecaedccb0685ec5eb8d7d50c5c8c2a684d558195f85f81f442a16a8275ad59df28453776c1743095dc0b600ca15a0ced6ac9b94387a15016c09eb40b453486d9302d101065dd5147c3d9bb98b04e6008cb6cba2d1090975ed2d45341965fd655644f34181296a89a0cb7c17b409e28e94534259845a206559e56a14141c5ce4cc18724cf4d102807f832cc24c84cb3009e03df69e7568b6805242b5678535654528e61e71c156037338b2d4ee1bd7b205734c14c856b57378b0721af0a599dddb9c29aa9a2098aa19af9c358b1149b00f802b7decccd4ccacb87c6edcd7ac5ce44e1ce14ca83d5eb87588082ecd52d60af5103e67a6ee71265a260176f6af5c51c2f852a60f76c53410e63e271d73c20001735c14c71a9a13862176feb15148c40b00b0b999d4779c39ae1135004d5aef14cecb94d52d008b5ec4e187fcd848001588a3f77b75377c674e78da670e6bb67c43547b27b1bbc56bbc5bc0b80b29bb654338938738534532a9f78efb3e4c405743d93d8dde2b5de22a19c25bf9a25a011611501b4d082b2621148904ef08444dc4e108286808520f64f616b469168d65cad4f5d5b4a866fe6803e26483ff0f498834247b3bbc56a54338534422c22a13a1307b1bb8b7e9a0b404c42291c53197ddc16d1849bf9a0991989ddd1ad07ebe0c3d9990d086ee8cbeee4dfad14d009b08a07582eccc86808b34e6c4d8340418454bbbb35b32fbb937f3400fc0e73337c00e820a2141a0e0060ba00b99a3b538e38d98c9910ff812c4d39b38601bddc08b0f821b9a03b3914b0092e12058768158802d108a2d34d5aca486b00c71dc04b77376c5901d84184526566b4e3a451a0fc025bbbbb66e1bca1220ed2db30a70222cc39bddb8d0012ddc13611437c1154eea6f100584448507dcc8ce11c6ecfaa6cc0b53a1137754336f7413854d29d084b2f619a05a87ab222888ddeddc1acde507698436911641e31cdeee08ac686ed89b1b388a2404af765b564c4f4458c26c23a0241f022a5216be2be19c39bf9aa9a09771160b9aac15202b1147013c07bdabf0bf03e8ad10276d00839d1ad48a6b409ef8265ae8c548138ed768268844940d57c37a338938532d32a29a0977c021a28e0ba49bbb737805b2ef25a2577bdebcd0ee5bc9ab10d02b4def4cf877005abba15cd588a086a418c09411af8268b682658521e5cf04551f7a6f00adc0c411c0169d149abb77ab32c8eebbd7c57c35433893853441a02290562009a132b60275985975ac0ebbe09c39aa9a2)) else (if i < 11 then (if i < 10 then 0x3d07946a13a02d38900a80a684f101976443483340b45115ee5fc53452140c405a21e19a0ec088288136801b1a239d39c1953b899e1016777e03ba9bb98fda018a10002b974ddb8623b9ab12deb833cdecddccf4c80a533bded05415602e852eed821cc7c5f80ee8688e7419e6f66f267a62070b68040776c18843df7b476a71b37937733d32070d2ffbb676c202f2e0c4ebda3713869bd98898097438d98f05d1a25a00626bf00d11ce9ce1c38588e14decde4cf4c84c78808310c1021cc4015c312d01dc55ba2f6a6f66ee64263c2ad9de678ad417429465776c19e5fe003a82c05a1a534072733c76538256770d24a105dddb196bd702b07d0436307ed0016b5a912c0b6ed82ede8b740a6deb840021b994d7196796200599dc5356f564376df883480b5601cca605702d04a06344b82ca8efb4fc0b40b1831821c9cb51c86771c41961951c205d7d818addb02b0438374412a0b33b82eeed8695eb88903c1ca2dba00b48960599dc176f4444b76c10d63d6dd182d02c9423457ae298b400ba96e86533ca59e5906770d2ddb58805d3935b74329c12a0b5eb86908885b2d01c9a889453050151ef5de5c558e44a2d429a0bbbb6ece2ac76e86532258161560241c25bb5a0067506abe586c8690120c52c43cba2059edb6805017185df76c17412de35472829ab8cb3cb2028ab107260bbbb6b1e2acc15078e59398b5bb11435eecd009b081cd7ac9cc585b08a247276cc656f5c6887081776ec2d962e64d7340388b16252f82720b2479a07b658b1285933bd5913b29a07ec98888122c5cdd833cd02454c85844764e68009019d62e6ed232c32a314392f373400480ba345376b16b0249bb7975935b31119a03ec58a3ec9b26a3b821812016ad9cd029ba044485b64c1816cc09068a6801744526ed834432cf2871ef580200482ef340b66ad8b1476b54770249bb0b65939a048a9ed9b74150ec581202ecd02c9cdda87236cc6585a851f62c6883fc0901766ee68164db35b32f3163132db309bba0e81e1332b441a0cc53ddd9971899ac1a09849adddc0ee79e074be0999c3d0d085c68444e11cf08516f76a846836ec0486241ea64d6ce62d6896298025b260fc0c17ba3413762280f8b45316b66dbdd1140601a001798b5b31164031507ce4ce44e24d14cacc5004ccb415dee5eb82ecb53f78465064f708848048e244366326ac451602571cb7eb1335a73c22871b8dde9b1b9e48c99a59f1c39ae42b10d59f16ee9eacdf8d54d008b46807f81588a2c6700adf69f6461d69a0ac4016ae6896f24518fb42d8fb22fcb1907ab78b4c21a056a19c82b7da7d95a611510d3bef3ee8cfcca9c4909086ad5ad308b29f79f744526a8e248496ac4340ac4554016fbcfba33f345056b5622821a9453bd93b538ebd7aa11af1a038617926210038d0d070458c else 0x955a80752d450813c4040b4391e6e681e4d6cd81261000480ce50c006702402d25740ad3cb89d8888438124d04e14dda9ba18d830009019ca28eb2b34012611e048086711f38911106722c40ae9783c58528258941c391f2c12c34962a67851c07500ca0c403a057bb62ba2b474090b608f2f804b05d30723c6825abbcd00a580e9c83d0580ae67a6800b4074e2b52e810009614a05a604f1310241015747939a001d401980903387c81115ea1e79e6c4380483fd5de34040d20660241ff2281a6599f02001d8d007d1400b810002479eddc57779b682e8158690888478a00249e0240ac0483e64500ccc4c441e0fa2221a428a092712e7bb1360120fc02234c90093d409b46808418479a8778c454420bb2629a22e05bbaa253316b6680655939bb98b1212b366c9832b5a82a00e890eeaa8a4ddcc5af6cf64d0240296fd645ad448419775511a6ed681a1a281eb2cb2ad6a0ba29a0ca8f5376b45316c40f14d98b5bb078067303286923d09088f4230122d9cddac9cc5ac33418009270a62b28432c15164c478450e6e65a62dd0c42502a6b26b2223c76c22ab16b2d376bc254620cd02b0249c99961530e40545bb1149a298b39b7b744dd8755eea3d2c98a99dba18943366ec0b5450074153756f7454d6dd0c4a19a0a81008f53677bab442a6a99699511711c00014d9b358b0609a238f9bf6312b50cd108b0300339845841964840c4856ccf0449d62e654e416b7eb2532a0c13273762a0228808f9935bf0d01119bb58b38e1144887adf808ac588888a1834265564a64e6ec49c450e24224e22822245bf9950351141112894ac58511e088188b1962c28845419c9b660560a820624208c03ab76b17326a2251080a21150672cc597435088888a83398049f79f756fd6bc4d962c40c45823d4b161442280ce49937dd13658b5bb5a010311407c488431b6c5cc982a05683e1f62d54c40c4200756cc151f7454c45264d6ed81c8d433442280c00ce6108d8b0a21140672cc5adfce14c1ac9b5088b08a01a8725ec4d12d008abb14c34815268804e64d6ed62c535244a1a132614422222a0ce709d58b9931161140cf06002402bbd79a25a01156884069207cc98a64c104983c0a0033a842118809272665b3a00aa6881516ec54ef704516ce64de2acb1672022c252506059358b3bd1151283312ad7812033904456bc09019c9376f2e23c22211e049340b66b2696e86255af0240672cdd83001203391ba04502fc09019cadd01262280480ce514d0ff9a00240672cd008883d01203395e5f62e65823c47964d6cc0926826ee7096c4b34428f340b6604808676e89a009d1140240673094cdd890a8a137465360240b4bb0141f3ee82531205705625a2000ba534880912f85030d2816a09854085032951605040f84381d0a0b40241f61fe19c557b029c) else (if i < 12 then 0xc44c5496282b42001748730fc2b88b86b2cb2a71620017016c29afc0b8428e49a746b151636ae80a808f04328a3ad00600338169594ce45ab2f82f6851c074f340d6ac9b7c17b428e03a738b6b564d065011010be0bda1474b129c5b5aded2ca8a380e9c534db55d023c10cab20b1075a716796b1f38932d32a29428e29ab76709314f6259c99c838b41698a0935a00674880815d07bed2de2bfbdb8a50a68571cc056b02aa67970cee4ee0e75608e704499dc40376e6ec0ac405e157bb741efb4b7ab3cafe8c429aae8fae0c55d0150e14d08fbcf0a50432eedae107dac14dd831015887889241885680ac19683f6800700b4174528534e5d8d599582b428e2902ba0ca03b7c17b472f340c06479d01e5c25823c179c381101062114111ddb11002b11281cd9d9ce24c54bf89903d5ebce11db098eed831087b8189a49ba00ad8dae5f6805680319dc0b457417434b76c43e005741efc0b2ab04fa2f26200f6a29a74609ccbd509308004b05d28ad4cb02a5e89c9d746eddf0825ce14c14bbbcb9e0886cde015c6f8010c1e8ee5678e7563d06c07d6f0e7268a654edc4056400ac402608e1e68162270af55808d7c029b3453052ee20028f384057340088086e0433b939d39c1129c35881003769829a002b11168ad1c09bb4cb4c51c982200e9e0df088a4c10804d0015bc0aef8051e68a62a60a5dc44845270a68163c10da5ec558fb4836b7ab3cb1eafe0c4156b20b7628e0f1bb621f32ab1126369956e80a808f04333744ca97405404782199894074175ad651c12c0b451ef6965668165ec0c4f9ef1ab3cb20b1eb11bb74ee21eafe78016cea779953c05bd11110f134ddb59e1010a85ccaaddd7403385281699a49ba18da6543480b415030010d35d00c44a7b407947807027262b405b4ee0381a4fbc0ba21e78316e8ae822599558f05402d0c00434b7431b4ca8690540478219c895f2c348480044407682655e2d244a02228024011e21e0ba76b514714d01099e9a002d380e80e4e14cb4c1cbb87f8ae4e24ca816872021ad02cf4c5400b5f85f800b819c079709628e04dd8e4d6543fc1a95de67a6800ae429622428e228021340b1e05a87e011404b5c25957d139358a5779a05bc02b02d6b7431b35accf08a4d001680ea052c175709ba128667a681654075332b31413a11e29a086605859e5909c299698a57f07a58f97702dddb5bb14d700ecd14cb4bbcb50b12a39764e402e8285eb8122d04cabdba265662827423c50010ce70215731429a29828a72872732c2b02ac0f01477afbb732a28116e82259c958f98a11208f9c80434b742cf2c82ddce4ce44d14cb4c52bfcbbce103c83c6ed85d8282c7ccacdba265455a6282741e051419d00b06ed31429a29828072828b32cb3cb402acc15a2d506536d0800a814d02d41b583397d8a5016 else 0x2d50092cd08607c46805b1d8d817e614338c0545098934107687378ef35e7808f530a0c42184c4abd9a16bd85a306a7e25c337e1168773b85a226202b3870d01158eee1c31b89cd88a00d92b08683a2415162d0483ac30c10cd30a76bbbd54273a0242011a022c0cea10691564d9140d00f8310dc13acca091d4025ad62d1c399dcccf9cece14d507c05980d86800588007fac587d9c84caab7681a80bd6603aef8670c2b65dcc04341340451875205e1862006021a073a9a022899996253a9bd87e259f39d5a258a9bf01b39e57700b11410d86ef1dca0dad887fbec0804e1cdfcd00682d788a015c8a3c4243f96f00488483ec100e21b318212024a00228210080846a1140122ca59410d0403887cd8819a6808a1406043d3424502ac0b44526566b4e395bb9bba02423a0e80c0b40462b7f35a71c228cb8e3ca5bf1060189ad39e11445ee815ee14cfaca0824d5ac988688a2b77ae3804b7716fc061624dda6b4e784516ca6b3ed4203a1a40ba0ca5d88a1bafbb9ba2c99f8d02bb4bb2ec850450ddc7cfdd150082cfcc98790478249a64cba014027423c124d4a67241a554203a5a0fb40ba0a0741326b9930b60e914c0492cc992984e8748a60249aba194c34885985a9dcaedf74140175f3e64d93261461d22ac0ce51569930930e91450673107d0780001588f07906908406da498883c0ac47a64c2d823c17419d3bb9ba2a9a691baea9868e79a013b10a0ff0d008830096ea1c689dce1085086844200484ec4504283fc220c02473c0fc214226228601101239e13b5bf5a03ca9ad10e11453ed2c79dc4d51cecca9ce0805f01dc9bf2dd8328a39dd1d1a))))
def rootMH12 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xee404078460140108e80900001d4380600600000023044039fa0400c40a81302f02c0200784f00604400156004000158020200000000802c04c004510020c80001717a03400d8300601c0281803600c1b0000000600000f01e004008090160c40086009e0c00183e022020180000720100380e09a1d8cb000006400078060000100080905003c0001401208c010230060100e0000000c80a0000160580400801e0180a0040000180000400200401000001574058001200200100a004008030010020a40080801a004148000065f40207713c0a8000050000002f0260009840780a04e0640200101c0000008300000c0c24d02a2000000500c00000004000024019af00211c1e8360000840000100c20001001000028048ac01012c14801018000100020d40e41d00400a0a8088000020100001e00c014000a90120f0338000280087886c0d201c0000000e0080080028e004000020a0180028060005c8008010000b8050000025b0009ae0300dc01004006068430010305a00980d00a02c06041010054060550000040000304e000048000181680000000000495b6900e00c4980b07a000000040080ac030071800943880501c004800000501200e0080c2000020b600004c0080900c0002b34906e0000000000004c010030000080d80001000df200604205c0100b00400c0780100801c09c4300604c000630b0005ec8040160655801501201c0380a10a00c0789300600037c8401a0380004b00000002000033be40781f000040048074420c40180629e0604621402a0f8058220030780081602e06c2380d080028060020000000000ab2a0000306304200c0004a25603c0080b00200c270a0016020450000080b0128f20000000a85403e0080002b01c23c0585c01a0004081b04c5f02080900000001001012049ff80002e00c0880d042018038000120000001c0160d0108870022a8098080401101a0150480180000b0000980382f0020040100002607006d910461500101a018010128aa0720000f80d002404000100000080000d003168020110000000d8000000502684309604c4180073e2880180001204c0790b0260000004102a0000301600000002000014260400000000240000e000034100250c600e33802198016470000080000002800a6300f00b160054020b30120d00100d0460e40000dea003c350250000100180a73e14c0501200605cc9831008004048020080150480c01a004018000200181b80500401c0000002208c27001004664330340041240700d8a2078160060020000e01200c1dc0308d0401340780184c008010170b40000701900600400812094368360010640f00100200339c0683b000004140161f2078200180000000382400c0280200f00a0041d0010180180180009a000008610200440800000a06800007 else 0x7f737bc478c07f6079e25c7081863996062b3c127c02a6b48f6276591cfb81b483803572235068c00b800964aa627600175b4a6a39578e806ab02d08515512542dd07b06555008027cf00e40ad3474d04df0891046821b564f17686084a4abd090c59f109d1471f12e2049d724321aa49fa4ad0734c19292365018d49d209fa02060ad641f6057d323400fe0075623a02b172fd03d16413052208d427aa0045754402f2489b73f5591804b5573514bd027123f31a4406220833446006b943ed06f3062a57f0007fb7ad08f0b3c3899da2c00abd8382098b61820aca67a08849959e0a3d839c2596058323fa134739dc026f08ca27f99026476108220a7c372744f64144214b4339433da5092905004e07890a89072502d391b924014635446a0610749f098067f8155900d337b100a1474723ff69d731050293003a4a670351a4984095045b878e48ca97f4b1050224049823dcaa2908df02d4539563734a4444b508e507c424f441f3025a009e692c2690018648444778146eb722560b4638038527bf0347405e049602e279fa853c485126ae082c79d921be016600e8a9e4b9b603a5b1bb09bc0a262aa0070a050c06144ab401de031b20d683c34456467904db01d4459c0a91a0ff130e20c1b7ab483207bc05a8218f07d3064c5aaa74f00a8e4280023628233929044e544d48b208f769ab00e2923346e5062503ef023d028c3691916c03c140590a3e459137ba66a806365982626948f4ba420824a993215304e80a6f943001b041db0a2e98363aa0026049436a5045d7a3a109a206c0765c03a1016f02e89241483a070006055150063224c40596030591f785e00a3529b1437b075b153c6a3caa0e20f505732a340a7404ee0a5301c378dd91cc014a7713005103711459894e421f511a91b7b1bd61b503cd02510455354446852795043116280a50217bb820a94b73840283681601e01c048650020480c00500353c000010380200000001206c048045300084100c0000c80181305c07c0b001022058006c00020303480103a02c0302a00c004010001ba2841104b06e2140300001e020028c50100500280300003c0781005408c0902c0001401b800000044068250040301d00200619006015000018098038a20b4088120120083c80f0060982c0030600049000101002c0103700c004000000005ec2a00c07000c0068c00000400001008020a1045298018000340360580581b000000010060ac96c0282509c0b03080500005806017006004008d709e214018b8026000068000280000207900c008cc80001e6e0000290351b4050000001200602a0220f4058060000d4000080021180207c00c0380780163a0087300806e000148010100080001c000010030404040080080100e00bd281e0040340000100001c000060060000001600003c000) else (if i < 3 then 0x10991b0671d539647380554161f69290535034c23110677a7622127210e097d20c2052d21ba63814245022743930923095c02480372451901a03260b2be13a74a6d14f108be4207162643da04436abe0941494f256365de788a01100502006a05e8039806f9831d037905ce070e02e515042106024e00ac8275903266d27986002306f4013301f1763a895f45d339ec07eb594c0588081c0888a63b02b43948069a27f3116307cf915d02f0900a04240364030c07f1b48207c849249a1520f621a405641617012a0180283002ebaa60b7a705bc006d06df414c020b1a9908cd040e066f0aab0645161447b985d8038bb15403134594069c011a4633069707fe172701ce24b94012011c07ee619e235f61e0009505d21a1500cc3a9d045d05d81131278109df004c4296405d6371429207b25167084d0706434a2a00a30f4909058533d5021401049332036c066b65d8011506e199df068b063d0428042d001ca782b01204a462602aa3113e25f7018a05a683a949cb3300091904c3b7d098d60a80b812a29890fd0122991244660234071f91f5837707d9842ba49f79f8a5ef727469b90209291542200383896d20be5a7909260731253d00b2427d41dd063f251401c620d1a51da4569a476706046a7667095e463d044bba7e66aa793b36de68d4b3f0b4a50a9b05ac916f494545e105b63016634c00c8218d7a590995b4bb08274a41026504e3444929ae05b248ba00ea7a8d0ab825f8513c00f872db032e8381b23843482a1d0409032409607383473c07c6a4d10828073241fab1a4475264e70932b490621c654a18a7920206c203e902b265da0279173704b0047244ee840303a62517092b0331466f013603950978144c07be088c25cb4859b81c25c5673318a3908320ef148017c80a9c066d76dc03d9ba2523ef243c09d5486138a7086b005939431a9523eb7206a4870653018e74c9b5a4b3c506ce56ed85f1412e5510b74d7057b99096fb0526705200ab638e01b507d005fe0089469a8386448200c761c0080500914099b1c1573709c0294e2a5331a7469605ea065f8973034e098908a2374904c104e69330000902f74a1aa2da45e3088003220515422b8a4403b84147103f08788a2b0550275a0857a16802af78828948090649db15ed6948060605a2b9ae11537188697e27b601dd09ab1496020e318465e601e8080b0a93065605ec34c4427048ac771725c969e10ab4059113f8a949a3c3466a042bb8043515631f3510916501e771cfa120047ab428b8de23896886047c2942054233d1076eb48b0475609c47436a44277a2790000e017244fc107a990955fd5726093f38a4475c02fc2605422786c27441343d584b0ac327660a2816ff12e8a8e908749788070583fa11b1565692954836092c6701462f658b09621a869776685573982 else 0x7aa0359029e3710974f16db62182aae00b7016c259a00000258000167ab066108e8979c0000139402ef06a442649a5993a905f8000109a90402b929098c062600000796497a081a02a4427a97c40001ba3584c60153645fa19a85f3483e20af0a18077009d6634607f229990a6725b8429da7d8b77408b8147d694a09429a44b4d7a0af00f59129054d01f611a241d94948215aaab946646705aa0221b1a914158e78a7b08354d185eb4298099d08ff423044210acc0150050f291846e002f806b4441a42dfb3930416041b034889660914475e08e041420a094239078509b14350064914b89a8c02bb635e460290293a3608c9297d073509d32443612329a3448f798f0434423b092e616019710a45a79439780a849a17051aa94d783aa996490f012642cf984300d4aa710983077c1433276a2148085841331151428266490345b41066c3b7e263ab98e123be096772704ab2067141167ad4ba1556c715ff61f156eb169c27c37a6e791c07640772001e007c05c033cf0712062002c32601030e001703c4059505aa054861445431078007da359701e39a1314ad843e77ec03f609e2916373f813af01a86115046e43f007d782da22ac06e3412b0774060b008742bcb7dd81514846042f00af24f9a4a4238c037403922a6207e4a8f907c005e40aa003c9989c074001d20a653acb59484a9324da263a932da7e03436088702540a4900cf04320040a4f8032744ec044908ce55ecb43a70b0b486085409f26650070929e109f404d40749631bb74f072809bb05b883ed315e07bb44a62631989f49cc03631a83b1c291fd06556645065926fd04d10576053ca13e46d82a8646a40057041408470952851605b57ab7b5af84e927f4012072d7895da13d093c080e078a3658060d0397262308b1017007e004bf4621053b14c30199261608f800fca991a1af27b4054f25aab44ab8107508490b437d06d30a6a245308f5767403a9a1ac09ed0553898a45e74a1791f9770e03c6027288ea039ba446422866b5b15705ca340217ac09ff276e12c49554082f0307931609c70a580567006e5432229ba78546f108d07546b7a374cd0638b2ccb7ee239d69a8420d290601a693810a1c010661e349fd088a41b8009d88e84a13016400f0630c0a2a991da493071b48ef74e6483d0444165e042002ec91ff12460368297a56a04084116185534713172a9718794a20da06e8b949009b650a24dc59ef00bca4cd8912041207cd01ff278903bb47402523b73e0ad525253ac97a6697f3055b09d802c405db0a5f4ad27ad048c201ee744e1135a963698304c4613e1a32198c517022e9789709760275760c4751b97e41bd01460532b81505c603dd49c44876b9db09fd6a3a07980a03168321b307930608392d784700078448256f0195030b207f835d6354007308d70)) else (if i < 6 then (if i < 5 then 0x68110a3976f546600000000095a0406a95406920000759399fa00f6275e9015037f0141170908b448920a99091c448569a201b300ec0ab2067c5a7704ab021627d569630119072d021a00009a6e0000000069ac98bb44be00660000653e012e0001017954cc000009be0001b3e10a042a5fb9bc00d6189d082a000116570092484044ae696d34427752000048aa23aa1a2e00e778d907a078e1b43813d4211f606e8a5583f10569169867a70870036016a062cd06d87a0009c503fe06d708161927a93ab38c6a3909b3aaba289627c461a906e7252714a400004728b1a85247b7a809b7a1f30aa2b16349d424df078f078c20cf480604bc542a09eb086423c120bc48a989d8a8ae07ca05c2b7d367a9b94414eb047061edb347b49302c735c67642058e71d1a8cc07374025b72606dd874e037b101b050b09560303468d27fa00de33d3607626bb49ce000108c10642745146779593aa2277fb4756012427c62290290d03b5087219480958211c14ff24210a0a336d63c0485ea35d93722573a4bd9896000124f791fb08e2056a1654792ab99d415d0abe27bc00010518034a031985e602cbb9979754040c78de832f0309067eb84723c624ca025f20ea0000048f4834003652189778339916f10869a7ed038c00c104c7077fb4150a7896c6076701d65060047648424903097326560739b771806393372816a48e129e06fe04ac04810a97b5fa138c279352d34aa005af73bdb084004606850a2c0803b968789c068e052869c3015e29480001422c7914705a42034aa50937051648ccb1580437428948c1059b0a100000000019820000080162c5761225ba000000001138027d707a066411b204d201c00a5d0243034008eb254e000001aa09f6472c960c20689a6600000000058c000063fb087600010a7f77ffa3dd2247a043654d06b7a0530a7b43a600010a54000007140619014e036bb4a204cb172484202331085c989b7a31278d08634240043919609262081404fe12a298d9b7a10a8624ff45d500c542a0a6f5a6077a75019c063a67f772617209238f03429a3f06a841cca88800100630040ab80b0aae638305ba1720b41242110a1eb42e088fa5f7697497a221860ac52422051061c57acf077a0495026c08dd4725446d474b02676979b9f49949079d43c066dea953655697730447487d706007aaa1c84a8ab3fd02210ac8819e770d03faa0a2a26e02a71a0406bb33a5485a61e75a34172f4237076b20a2271106c621b78219084807a92768684e05c571b60580022c09dd06cb2a4472cd085043d800009ad002860001087a71b40001a43268e9075206ee490127fc03afb7e6489f780003da12a00ac1413604e004661723a6a2000043360491599903e5044c07a2a47c2811897a0a77a951030007a508fc466d0760998ba74f97ab06af5 else 0x94a696e52d5a4ae08c7010aa472025227b200bf27ff24f0b15b2100426c08f30681659c69a6423e0247a3a3907a09014912b4be5a45445a015808a5b80285100ab106bc0a8da3ab21b8008c01927305942b060306fc6945434e03a3632ba7b401eba0fb0505645c673f40191a8404e403f821c0b744045707af02bd02904a9db7b1422f035514ef06be936100ca6377baac08b708d30102b9ef095524510a395a5d042305b0403226d6081f085304dc27cc48fa0678670309a505a543e0008ba33f0005465a338c21d404b307dc05dd9a1e02a1a7e403eb344449d166637001427907e662da02c99ace09963a44058601442a70370e0a24516a017d459b0a9508391300778a733e201914d248b800a268a40a7204ba54f846ff97bc018508c248c5961ab95371b3016902d906a012fb085a06e4636d468a4347b1bf44a816d5654100c3894a172d239321ae1a7d01ada72102694366087c403069ae63b24910960e664b0928055733e142b4b32c00fa26379598248e219f433471fa513a04b95056ba1a99a9480983c10a5709ac3112a9b798a099f9005a09e906284598057806f7a450067346f657b74ab10a1533fe0821b7bb080625c2768f167f71f5062e086e95d6420b771460b3099b2103971612c7230306ad07b7250412d151534a3f091f1546ba0908db415e35c0516214cf02ff0100061c0a4b03151aadb9b5511c7718ba44055e8440402b98ad00bb0257031071f748c865dc12f9688b23796a27066308138268047801fa61ea07100a00b1aab9fea2d3064740a508d90a2009e5b6240570060008311732766f15063598703872f10a334403a53f0916a390608403e700a847599883426365480a42099372d4a8f2307b2544402013b1474e0001252985ef6009032b03e12a4a4465b39b238393f1118527f0053720819440474809a778da466854d224fb072309cd02ab0a5b00ef2157350e24e0670b61e504f32a57a6562a4e8956026a434484f6916b7733057e275c0545aa73b72e00017ac7aaa0067403f52154000105de14f3a05a420e118304cc014249b472f4035e441d0a610690000109b807f401c4061a07e8428a05f245971693b4d4b74a84c4056e069403d70061046c09af05988961448c608a03532002059d544e0687024c00010a4c44957a70076861e9065a0001995971a348a006cd48dd06ea24ab053e096501b8405489542577794944a5a8beb819079102a9016a0a7031300000000020640a8ba4aa0974031e000122b0b599674db499045104f6815c1973814f63ac09245aad654ea8edaa24712702813332021c6ac006f1206a77fc0000b7246846aa7e000c16b208eeb8a38ab3006536a62762011ea44b33c5a5a0278ea938090203cb7789099f965d04eb0204021848d3435229b30640b48d05fb064e0a6d054706347) else (if i < 7 then 0x9c925a9473a12ce85ed48d6898309f817b740fd848e351a052ba793088522d104f1baa0079504530a3105bea4b5771a244702e643d0342309da23c90a07011208350285835f6a9970df03204674473ea4600a2202b80191312b427f429f038eb94ab7d46a54b63f71cb3746614f442b27dc02296a2805130949412d0ab776c1013e05754a5962fa09358122b1730abb2aba153e01db096a00b485f85abca039428f054b00711aaa0a69012999a40860396a6744989901bb04b727b9039e197e54b7215801bc0946a7e779383887439f48bd11400689635762ff638c811a01f522a9052135c4013093f4080907e3014c7a6281c9983b943c0222097b9201a9f303b792bf0782b7a44463b7c9069846f803cf0a0ca7c305fc718d43a446e3a445b502298a2547a971214d4078a24267a4b3942146001b3a4f424a4469b823a502096f10a177c50667096c6a9bb2a025bda0a098da44892a4c487162346966057b091a086c79de97f002130176471b192db9e3b46104f804a912d2b3ce03b185cc4a910a4601ae70fd98dc02fb929765581a300401a0607741b7e1017b007729b905620507596202b71771097e22f1029c21a60ad0147e0426411400dd2a0e0a4e636b05e7ba8109ce081103e316b8695d433b01d909a103911466037c06d4056d055801ed004b065000352128099802ac017f048845ea0721397e4a4731a8aa1c25b3097168857acc33f9b13b664607761a2663a803de05c90896062d84e7051da490409f07f912352800029a48490a3601880aa7008f031c8085a1cf04107abb00f2093133c102cf0524037646c904a000a668a969d82a65040404fd051e14a209c2070c012ca7df07fc2759263d3aa26964099171c507de20df241f145d51b1b1ac2627003c3512036f148bb38009efb3901aa9636100d9025c609001830617a8c0094e1a6806c826d1010c00d00464074646982a6f10b6441e674e078607a628e83a1d2160420462c6695a005c05d143f40196053809b5449b067b317202f577cd05ee48cf05cd0a40004907420160633c033c01f3002f54b903bda45d06ed075d402d899225bf22872a9e27c989f4436063a04a4316dc25030069087e23d106b1032901b7066893eca2be0458089d109011a812190a63609205f005f4047e0ace42237657833f240309f1052f22434857084eb169a5fb0894444600240055113a9a7b05e104ed053017350388680328090745276c04d782cf655116ac7a440210131341cf058a45d017ce06c564296959a1d0022e52d098ee84f5650c055d726c014806a7289c2048a6e6434329850921b80f680525b603870a3a046125b443df27caa35a979108e703d3743f44450276a84d623941fe03bf05e2043d426e35bd021f04d801cd00db260820c464eb449707fb3a9f633e050160234754aa459 else 0xac605610867b7d914880332a8d306db0aa923f9010e0aa5110508af445e0a9e4653054089f7a9694a8c69f2a483b5abb72b01e5041905f7769e00e173fa43d6717e0682074a693901a389ee23e0069f083a4128695506d1080d083d47be46eea2e006b3079a043ab473ba162a7709e7ba07489c938469734)))
def rootMD11 (i : Nat) : Nat := (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x66130482fecd992a982413fe2e9545c120bf73684aa60905ef9b625530482bfc5caa298241fda54d5248110cff32ad01029867f992680814c3fca98ac6a0a81ebd6096160560f5eac2c0302b073f598545815839facc262c0ac19fd2a53160560cfeb42c88a6907ed5634c521593f3ab2aa2b12219fd2a55158910e7eb02c13221877cd8254993043bd6c12a4ca0219fb6a1a564810cfdb4ac13240876ed52609960c3af6c12a4cb8219fb6a15264810cfdb24d1102987f4d53549304839f6c0b24c1061ddb54da564810eedaa6a93240875ed875cd920439f6c3b50c90215fb6dda864810afdb70a9b240857edb869592042bf6dc2a4c90215fb6cda864810afdb66c13240857edba5cd92042bf6d9b4ac90215fb6cd52648109fbb66d292298775da554993043baea9aa4c9821d7761da764c10ebbb0eb9b260857ddb869d93042beedc34ac98215f76e15364c10afbb70a93260857ddba60993042beed9b04c98215f76e95264c10afbb66a93260867bca950941583b9ea9aa4ca021d6f61d7365010af7b70a9b280857bdb854994042bded9b04ca0215ef6cd5265010adfb6c51b309066fd9869893483a7eb132eb0861d3f61d7165830e5fb02c132c1856fdb7285960c32fecc34e49a4157f6cd8265c10abfb7051b2e0853fdb814d984831fed4304c88618ff605a960830a7fb66c0b301053fdb80c5980823fedc152a12c11ff6e853661208ffb66d43240847fdb36a1910823fedd062cc04197f69597584308ffb6a54b02b047fdb32a5815832fed132eb08611ff6c8a9605608ffb6a54a84b047fdb568d924423fed9b2ac9a411ff6cda564810abfb66a932e0847fdb52a5325823fed8b4a982215bf6d8a954d208ffb6a54a629047fdb52a5824423feda952b1a211ff6d4a9589108ffb6a54a648856fdb5285960c23fed9952a0ac11ff6c8a9505608ff974a9b289066fca958d415823fed8b24c8a611ff6e5a2205308ffb74c88a69057bdb4255934833dec934840a615bf6d89564d20cbfb24d39029847fdb32a5814823fed9152c0a611ff6cca9609108ff974c13268847fdb32a5654423fed9952b12211ff6cca954910adfb6c54a629055fdb72a5314823fe5d33098a411ff2e9944c520afb966d23309056fdb624d91482afedb926c8a411ff6c8a960d108ffb6454aca8847fdb22a5634423fed8952a9a411ff2e95364910adfb6450b2c1847fcb96a1744823fe5cb4ea0a419bf6d8a954d208ff972d29269066fc956989348337edb15298a411ff2e5a114d20cdfaca54ac48866fd632a562443d78b0b00c0ac1fd85495148110fce2caa8ac0887f495354930483ed4ba284b82415bb6c8a165830ad7b6850b2c18567db5285960c237edb152a9a411bf6d8a94c520a9fb6e50b2c1852fdb8285960c22fe5d2a4cb8211ef2e5a420530 else (if i < 2 then 0x615ff6c49264530bfbb664c262905fddb325531483faea9aa4982417f76d5314c120bdfb6c51b30906efdb86989348377ecc34c49a417bf6d89360520ddfb6ad3126906efdb16989348377e5c34c49a4177f6dca366120dbfb30d3926905dfdb724d81482dfedc0a6cc2416ff6e09360520affb6acc240884ffdba14d98482bfedc326902213ff6e853605209ffb62d1300904ffdba24d814827fedab46c8a413ff6e9524c120dbf96ed2b269057fdb564d20442f7edb152a9a413ff2e953661209ffb744c262904ffdba255314827fedd0a6c8a417ef6d09564d20bdfb6c4ab26904ffcba61d934827fed9952c0a417ef6d0954c520bdfb6c4aa62905efdb62a5314827fe5d33098a413ff2e931601209ff974caa62905fdcb369198482bfe5cb46c0a419ff2a59360520aff972c0a609067fda5261934833fed1930c8a417bf6c0a258d60efbae654aa69077dcb954d30482bfe5caa6cc2415ff2e55360520cffb4e54aa69067fd742a5534833feb9952a9a419ff2a5a954d20aff972a9a829057fcb954d934833fed412ac9a419ff6959258430efb97298a609067fda82a531482bfe5ca62c02419ff550a94c520cffb4a54a629067fdb52a5314833fed215298a419ff2a5a94c520cff952d02629073fd9824d814833fed4126c8a419ff6949364520eefaa6d2b240857fdb854d92042bfed9b4ac9021faf58d4114964ef7b30a08a4b273fd9814981582bfedc322292c99ff6a45260530cff95229302b067fda8249914c39fecc064c0ac1ff3609314c910fedaa6c12a4886feda854920443df6c130299221fdb54d5248110febaa6a9260885fddb54c5304427fedc34a982213ff6e1a5481109ffb70d1b24884ffdb36a1204427fedab46c92213ff6cda5481109ffb62d2a60884ffcba54d824427fe5d2a6c02213ff2e98264d109ff97498b008857fcb969582442bfe5cb06a9221dfb2e58254910cffb4a54b048867fca96a5824433fe54b42c12219ff2a5a060910cffaa654b048867fd95680814c2bfe5cb46a92219ff2e5a54c110efb972a9a608877ed52609910c3b7eb2ac4c8861d7f61da764430ebfb0eb8b221873fd826a1910c39fec0b04c88615ff6e1a764430affb64d43221877f4b16a532583b7ea9142cb0617fd6c48524530bfdb6442922985fddb3214914c2bfedc90a48a615ff6e48224530bdfb6c42922985dfdb7214914c3df6a9302c1061bbf69562584309ffb6ad12c2184ffdb568563083fb6a9b04a9021bfb68d82548109ffb70d1aa4084ffcba54d82043df8a8b00c0ac1efc4c58060560ffa30298a60907fe1b254520443f78db2a2b0221fbc58d5158110ff5284a0ae0907de97350970483bf4a9326902217fa6c8a54c120efb33098a609073f99860530482bfcd9300982419fe2e9984c120aff36029b309077d8b3 else 0x62cc3289067fda5649615033fed1b24b0a819ff695944c520edfb30b2a84b076fd6366142582bfedbb30a0a415ff6cd9850520affb72b9a829057fdb954d414833fe5d330a0a419ff2a57350560ddfb46b12c2a04ffdb568d625027fedab46b0a819ff615a364910cffb50d13268867fda868d924433fed1b30c8a419ff68d9864910affb64c9b008867fda165d934833fed12cac9a219ff6a5a64c910cffb4cd13268867fda9551314833fedab46c92219ff695a264d10cffb4ad1b248867fda3655924433fed4b2898a41bbf595a14c960cffb30d0a648867fd9568d215933fedcb4690ac99ff6a5a348564cffb72d0a64b067fda968532583afeb9b2ec9a41cff6619360520affb70cbb269067fda8649914c33fed4326c8a415ff6e09564d20affb66cab269067fda564d91482bfeda930c9a419ff6e99220530affb72293029857fdb3255934833fedc35229a415ff6e45366120affb7229b029067fdb16a453483f3eb2aa2992c17bf6d9514c960bdfb6c98a64b057fdb9695325833fedd264cb2215ff6e5314c960ddfacad1924b06efd6368c9258377eb2b4449ac13ff6e85224d609ff974a8a64b076fd6558993443b7eb2b26b02215ff6e1a564d10affb70a93268857fdb868993442bfedc12ac8a619ff6a19364910cffb50c9a408857fdb8249914c2bfedb34ac9a215ff6d9a264d10affb6ad13268857fdb5261914c33fed2b26c92219ff6959348110affb6a493229857fdb2261914c2bfedc8a4c8a615ff6c89564530aff974c2b268867fdb26a4814c2bfe5d304c9a215ff6c49864530aff974b2b268857fcba58993442bfe5d2a4c9a215ff6c49564530affb7054a629057fdb52a531482bfed8946cc2419ff2e9984c520affb6229b309067fdb968453482fdeda0a4c0a61bdf549a524530dbfb72d3902986dfdb069c814c39fecc302982415ff6d5984c110affb64cc2608857fdb954d304827fedab4448a613ff6e885245309ffb7429322985efdb6149914c27fe5d2a4c8a619ff2a5a960530aff972a93029857fdb560593082bfedd302c98415ff6cd8164c20affb6cd2b261057fdb159593083bbed2aa4c9821ddf54d5264c10ebfb0ed3b260875fd875cd93042bfedc34ec98215ff6e15264c10affb74a93260857fdb354993043bee59b48cc2419ff69ca366120cff946d0b309067fcb36a1910833fe59b4ac9021cff6605360520cffb5229b029057fdb854d92442bfedc346c92215ff6e19364910cffb50c88a69057fdb824d91482bfedab46c92215ff6d59364520affb6ac9b248857fdb524d914833fedd32229a415ff6cc9864520affb7229b229057fdb126193482bfed8952a9a415ff6c49564d20cffb30d09269067fd95688814c33fedcb4440a61bef611a114964ddfac6d08a4b267fd98684525927fedd10448a)) else (if i < 4 then 0x1583b7eb2b30b82c1dbf661635c160f9facab8ae0b07cfd875917358377ed2ac8b8ac1f3f5cd635c160f9fac6b8ae0b06efda558d71583b7edab04cb061dbf6c58265830ebfae6ba3309075fd7366170583afeb9b30b8241d7f661715c164ebfb30b8ae0b075fd985c570483afedab04cb821d7f6cd8265c10e7fb30c3b089073fd816a5820c39fedcb02c1061cff6cd8166020cffb4ed23309067fda961d844833fed1b48cc2419ff6e5a360810cffb64d43268867fdb968d810833fedcb5029a419ff695a960910cffb48d0b309067fdb36a1924433fed1b42cc2419ff68da960910cffb46d4b029057fdba5d198482bfedd286cc2419ff6e99850520cffb74cc2629057fdba14d984833fed8b40c12219ff6c5a960830cffb42d4b041867fd986a0934833fedab50c90219ff695a960810cffb66d43240867fda36a5820433fedd304c9a219ff6e98264c10cffb74c13221867fdb36a1910833fed1b52c08419ff6e98164c20affb62d13008857fdb3685980833fed3b30a0a419ff68d7466120cffb42ba3309067fda9611734833fed3b30c9a415ff6dca366120cffb50cbb269067fda869d910c2bfed8b30b8a819ff6a17164430affb66cc2e0b057fdb566170482bfed9b30b82415ff6c5985c120affb6ac8ae4b275fd955c572592efedaae2b82c93ff6e1a5485649ffb70d08a4b26dfd8769571582efedb864cc2c177f6dc3260560bbfb6ab8ae0b05bfdb80c998582dfed9300c0ac16ff6e05260560b7fb7019302b04ffdb8688955827fedd0a4c0ac13ff6e83260560cff972d1302b057fcb969573582bfedab24b0a81dbf6556258540cffb2ad12c2a067fda5661934833fed2b2ec9a41bbf695634c960ddfb4ab0a64b067fdb9695325833fed4b4a992c15ff6d53265910cffb72d1aa4084ffdb568c925827fedab4449ac19ff2e5a54c960cffb50d2b268867fda6695934433fed2ac4c9a219ff6959664d10affb6ac9ac08867fda566131482bfedaa62cb2819ff6c5a54c110cffb4cd2b261067fda558d93083afea9b04cb8219ff54da864910cffaa6d43240867fdba54d924433fedd2a6c9021bbf6d9a524d60ddfacad2926b06efdb668c955833fecc3464aac19ff68da954910ddfac6d2a42b267fd98695215933fedcb4a90ac99ff6a5a548564cffb4ac9242b267fda5661204433fedd32aa1a419ff6c5a054910affb6ac92c21867fd98694934833fed434ac90219ff6cda564810cffb46d4aa40876fd52685960c33fed42a4c9a219ff6e95264d10cffb74a9326085efdb52896358377eb2b4a492c1bbf58da524960cffb30d112ab057fdb52a582442bfeda862cc041dbf5899558430cffb44caac21867fda8654310833fecc346a0ac19ff65da350560cffb42a1b309057fdb165543482bfed9b30ca2419ff6a1944c520affb else (if i < 5 then 0xe6e19548110bff370d1a40885ff9b864d20442ffcdab46902217fe6d59348110bff36a98240885ff9b0214914c2ffcd810448a617fd6d53160560f7eb04a8b02b077f4b954581583fda98acaa0a81fed4c56250540f7eb0498b02b07bf531601815837fad1262c0ac1dfd2e53160560efeb2a98a42b277f5b94c521593bfad4a6290ac97fd6c45260560bfeb6229322985ff5b10c998582ffad8864c0ac1ff5605314c120bfeb6229b02905ff5b114d91482ffad893098a417fd6c4954c520bfeb6249b029077f5412a531483feac0a6299221ff5545314c910feeb66a8aca887f75b254565443f7adb2a2b1221fbd58d5158910dfeb74a8ac6886ff5ba545624437faa8b4c99221bfd545a664d10dfeaa2d0a64887f755159532443fbaa8acac9a21dfd6c58264430efdb72c12a48877edb960952043bf6c1352a9221dfb609a954810dfdb04d112ab077ed8254993443bf6c12a4c9821dfb6493248564ff9aa6a9260907fcd524c530483bf6a933090221bfb6e9524c120efdb72a92408877ed5264d20443fb6a9aa4982417fb6c5524c120efdb4ac93041877eda1649820c3bf6dab24c1061dfb6e98764810efdb6ed43240877ed876a192043bf6dab50c9021dfb6cda864810efdb6ac13240877edb360992043bf6b9b50c9021dfb6e97364810efdb70a9b240877ed536a192043bf6a9b04c9021dfb6e95364810efdb64a9b240877edb869592043bf6d434ac9021dfb6958264810efdb66d2b240877ecb869592043bf6dc2a4c9021dfb6a15264810efdb66a93240877ecb369592043bf65d2a6c9021fe75513158d40fdbac698ac4a07edd654c532583f6edb262992c1fb758d314c960efbb3098a648877dda94c532583beedca62992c1df76a5314c910efbaa6cc2608877ddb954d304437eed9b4a48a617f76cc5264530efbb3098a609077dd984c530443beedd30ec9821df76d58264c10efbb74c13260877ddb360993043beedc34ec9821df72e1a764c10efbb70d2b260877dda560993043beed934ac9821df76e15364c10efbaa6c13260877ddb254d93043beedc2a4c9821df76e95264c10efbb66a9326086fbd8469521593bdec232aa1a41def5519865120ef7aa8c92c2a077bd5464542582fdeda0a4cc2c17ef6d05260560bf7b6829322b05fbdb40c998582fdeda064c0ac1faf58d415c964ef7b68cc2829077bd985c541503edeb9a82b92c9def6619450520ef7b24b2a82a077bd9565141483f5eb2a84a0ac1def6614250560ef7b2ea1282b07ebd54589615037deaa346b1281bef551a358540fd7acab1282a07ebd6358941503edec3ae6a0a81f6f61d7150540bf7b6a98a82a077bdb560994043bded9b04ca021def6e15365010ef7aa6c13280877bdb254d94043bdedc2a4ca021def6cd5265010befb6a19330b05f7db50c98 else 0x260907fe95264530483ff44c2a498241ffa2a5524c120f7f366c0302b07bf9b2601815837fcc0346a0ac1dfe661935c120eff366cc2609077f9b166130483bfcd830498241dfe661954c120eff330a8a609077f8b566130483bfccc34498241dfe661a14c120eff330c8a60907fd99368131483feca9b3098241ff654d814c120ffb372a9a60907fd9b054d30483feca9b2a98241ff66cd514c120ffb2a6a8a60907fd95368530483feccc26298241ff64c5804c120ffb34a98a60907fd9954c530483fecdca6298241ff6295314c120ff7308aa2e0907fb98450570483fbcaa2a6b8241f7e5d5985c120fbf2e8cc2e0907df9845cd70483efcb9b30b8241f7e611715c120fbf330b8ae0905ff9b566170482ffcdc2a2b82417fe6d1985c120bff370c9ae0905ff9b166170482ffcdcaa8b82417fe6d5935c120bff366a8ae0906ff9a869530482ffcd82a6b82417fe6e5515c120eff330caa408877f99854120442ffcd9a82b8241f7e5cd415c120bff362c9ae0907df97564d70483efcb9b26b8241f7e64d715c120eff30ac9a408877f9b864d204437fcd434098a41bfe6a1a14c120eff350c9a40886ff9a160930483bfccc32690221dfe64d8048110eff36ac9a40886ff9a5681314837fcd2b4298241dfe6959348110eff32ac9a408877f993541204437fc5434098a41bfe295a04c520fef32aa8a60907bf99860530483dfcc130298241efe605804c120bff370d0a60905ff9b829530482ffcdc322982417fe6c9804c120bff3704aa60905ff9b82a530483bfccc260902217fe6d5a14c120bff36a54260905ff9b564530482ffcda930982417fe6cc984c120bff36454260905ff9b325530482ffcd914a982417fe6c4a84c120bff36252a60906ff8ba661304837fc5434298241bfe2e9954c120bff36029b30905ff9b014d814837fc52b4298241ff62cd984c120ffb2a6c8a60905ff9b014d91482ffcd8930982417fe6c4954c120eff172d4260905ff8b960530483fec4c26298241bfe684984c120eff172d2a60907fd8b954d30483bfc5caa2982417fe2e5514c120bff36029302985ff9b0149914c3bfccc12a98241ff6255314c120dff3424aa609077f8b968530483fec5ca6298241bfe2a5a04c520bff36019330b05ff9b00c981583feca995298241bfe6a0a94c120f7f064c0302b07fe9b854920443ff4c1aa490221ffa6a15248110ffd2a4cc240887fe95260120443ff4d9aa490221ffa6e55248110ffd346a9240887fe95264d20443ff4a926090221ff654d804c110ffb262c0260885ff9b54c960442ffcdab26b0221bfe6a1a548110dff350a8240886ff9a868d20443f7cb2a64b0221fbe5959358110f7f302c0260886ff9a84c120443fecc1aa690221ff654d3048110fef30aa9a40885ff9b854d20442ffcdc34a902217f))) else (if i < 9 then (if i < 7 then 0xffeda950c9a417ff6d49864d20bffb6254326905ffcba61d934837fed8b464c241bff2e99360520dff950d3b26906ffca8695934837fe54342c9a417ff6cc9564d20bffb7229b02906ffda1609304837fed0aa4982417ff6e0954c520bffb6a4c262905ffdb52a531482ffed993098a417ff6cc954c520dff950d0262907bfd8260530482ffedab02982417ff6c9814c120bffb66a9260905ffdb814d91482ffed8952a9a41bff14ca960520eff930cab269077fc9865531483bfecb952a9a41dff5c4a954d20eff972a9b229077fc9564d81483bfecc12a98a41dff6e15364810effaa6d43240877fdba54d92043bfe5c34ac9021bff209a524530ffdaa4513229877fca5249914c3ff6d92a6c1221ffb6cd8254910ffdb72c12a4887fedb160952443ff6d8304a9221ffb68d8254910ffdb04d4aa4887fed8268152443ff699342c1221ffb609514c910ffdb04d0a64887fed8254993443ff6c12a498221ffb6e15248110ffdb66a9240887fdda84c532443feed2a6299221ff76e1534c110ffbaa6c1260887fddb254d30443feed8aa698221ff7609314c110ffbaa498a60887f7d5354980443fbea9b40a9221bff6e98564910dffb4ad1b04886ffdba60d924437fed2b52c1221bff68da960910dffb4ad0b04886ffda3685824437fed2b40c1221bff68da060910dffb42d0304885ffdba54d824437fedd304c9a21bff6e9824c110bffb62d0304886ffda868d52442ffed9aa4c0221bff695a64c910dffb4ac1260886ffdba54d804437fea9b50c9221bff54da848110dffb74a9b24886ffdba54d204437fec1b4ac9221bff68da954910bffb62a9300886ffda8681524437fed1b40a9221bff685a054910dffb74a9300886ffda8549934437fedd2a4c9a21bff6e9524c110bffb6a54b04885ffdb3609504437fec2b46c9221bff6a1a14c910dffb4ad0a64885ffdb868532442ffedab4c992217ff6d5a14c910fdfacab1326885ffdb854993442ffe5d30ac9a217ff2e98264d10bff974a9326886ffda24c580443dfec1302982217ff6e1524c110bffb64c0a60885ffdb154930442ffedc2a6c92217ff6e15348110eff972d2b048877fcb968582443bfe5cb40c1221dff544a960910ffd972c12a48877fcb968d52443bfe5caa6c9221dff54d8164420bffb70a9122985ffdb5208914c2ffed910a48a61dff6548224530bff974a9b04087ff18154530483ff8d9aa2b0221ffc6c95158110ffe264a8ac0887ff19354560443ff8c1aa290221ffc6a15148110ffe374a8a40887ff1a354520443ff8c9aa290221ffc2e95148110ffd330a12e0907fe95350970483ff4d42a498241ffa661524c120ffd2a4c0a60907fe9ba54930483ff4d9aa498241ffa6c1524c120ffd364a8a60907fe93260930483ff4a934298241ffa2a1524c120ffd174a9 else (if i < 8 then 0x654c910effb52a8a64887efd6568532583bfecc34299221bff6d5a324960dffb6ad1126b05ffdb314981583bfedd30ac9a21dff6e58564d10effb6ac13268877fdb960993443bfed8b04c9a21dff6c18264d10effb30c0b229877fd95605914c3bfedc2a4c9a21dff6a15264d10effb30a93229877fd5266193443bfea9326c0221dff6e95264d10effb72a93229877fdb954993443bfed8aa4c9a21dff6c15264d10effb0ad13268877fd92605914c3fdeaa262b1281dff551984c520dffb4a98a64b077fdb54c596503bfecaaa898a41dff2d5984c520effb50ca2629077fda565131483bfe98b30a12c1fbf5953158940fdfb6c98ac4a077fdb94c580483bfed4aa898a41fbf595314c960fdfb6c98a64b077fd9868131483bfedcb0498221bff6a18164530effb72c0a609077fd98605304837fed42a4c8a61dff549984c110dffaa4d4122986ffdba549914c3bfedcaa498221bff6e95224530dffb64d2922986ffd52694914c2ffed9152c0a617ff6e45260530bffb7052b22985ffdb52a1914c2ffeda944c8a617ff6c8a564530bff974a93229877fd954c530483bfe4c2a4c8a61dff2e55264530eff92ac0b229877fdb560593083bfedd302c9841dff6cd8164c20effb4ac0b261077fd5360593083dfe59b04c0ac1dff6e58564910effb74c1b248877fdb960d92443bfedc2a6c9221dff54da864910effaa6cc3229077fd5366192443bfedd2a6c9221dff6e55364520effb72a9b248877fd8365592443bfec2b46c9221dff54d9364520eff970c9b229077fd8564d92443bfe5d2a6c9221fef611a548564dffb4a90a64b07efd6369521593bfecc34a90ac9dff655a348564fdfaca90a64b077fd954c9215937fedab4440a617ff6c45260530dffb6ad1122986ffd52688914c37fe42b4448a61ff76e1534c120ffbaa6c1260907fdd5360530483feed92a698241ff76c5534c120ffbaa6a9260907fdcb84c530483fdec3b08a0a41fef6119850520ff7b08caa82907dfd8761173483efec3ae6cc241f7f5d17366120fbfae6cc2e0907bfd87611984837fed3b08cc241bff6a18764d20dffb46c2330906ffdb96a0534837fed8b5029a41bff6858466120dffb62d4126905ffdb824d814837fed3b30a0a41bff6a5845cd20dffb50aa262905ffdb564d814837fe5c34ac9a41bff695984c520bffb6a98b00905ffdb154d704837fed2b0498241eff54d9860520dffaa6d43229077fd53661204437fedd2a6c8a41bff6955364d20effb72a9a40885ffdb528d98482ffe5d2a6cc241bff661a524d20bffb6a49b02906ffdb1694934837fed1b0ea0a41bff6a1944c520dffb4aca262907dfd875cd41483fde5a352a9a41bff6858764d20dff970d1b22907dfd875d593483efec3ae6c9a417ff6e0a564d20bffb704ab26905ffdb72a193482 else 0x376005800c100524022000e4004f0016000580000fff308cc2e0907ff98454d70483ffca9b30b8241ffe6e5535c120fff362a9ae0907ff9b054d70483ffcdc2a2b8241ffe6cd515c120fff2a6a0ae0907ff95364d70483ffc5c326b8241ffe6c13160120fff16ad0262907ff9b560530483ffcdd30298241ffe6cd814c120fff350c0a60907ff9b960530483ffcd930298241ffe661814c120fff360c0a60907ff98260130483ffcc0b0098241ffe695814c120fff32ac0a60907ff8b865530483ffcdc2a298241ffe609514c120fff366a8a60907ff9b254530483ffcd130298241ffe4c5804c120fff150caa60907ff8a560530483ffc4c32a98241ffe261514c120fff14a4c260907ff8b954d70483ffc4ab0298241ffe2a5814c120fff360a9b00887ff9b054980443ffcd8304a8221ffe6d53258110fff360c1260887ff95260130443ffcd9b0a90221ffe6e98548110fff372c2a40887ff9b560d20443ffcdd30690221ffe6e58348110fff370a9a40887ff9536a120443ffca9b3090221ffe54d8048110fff374a9a40887ff9b954d20443ffcd82a690221ffe60da548110fff306caa40887ff98568d20443ffcc2b2690221ffe2e95348110fff172a9a40887ff5814c530483ffa592a2c0ac1ffd0c95160560ffeb64a8ac6887ff58154532443ffaa8b4c99221ffd545a14c910ffdb70a9260907fed5260530483ff6d9aa498241ffb6c5524c120ffd970a9260907fddb54c563503feed2a62992c1ff76d5314c960ff7aa8cba84b07fbd8750941583fdeaa344b1a81fef551a158d40ff7aa8d1ac4a07efda559171583f7ed2ac6b8ac1dff661a55cd60fbfae6cc2e0b07bfdb560981583dfed8304c0ac1bff6e98225560dffb4ac22e2b06ffd8269571583bfecc2a8b9a41bff6a5a54c960effaa6ba3309077fd5366170483bfedcaa6cc241bff68d8225560effb06d4aa4886ffdb8688955837fec13444aac17ff6d43266160bffb6a19302b077fdb960950443dfe5ab04c0ac1bff61da350560effb24d0ac6a077fd5366194483bfedcaa6ca241dff6c55365120fdfacaa12e2b07efd6350971583bfeb9b30a12c1dff661425c560fbfb0ea12e2b06ffda550971583bfe5ab30a12c1dff2e99850960fdf974b2a84b077fd8766141483bfeb9b30a0a41f7f61d7350560effb72a9a829077fd9554d41483bfe5ab30a0a417ff6d53158940dffb4ad0a64b077fd8766193483bfed4b26c0a41dff6619360520effaa6cc3269077fd5365d93483bfecab26c0a41dff54d9564d20eff950cbb269077fca865593482ffedab42992c1fbf695634c960fdfb4ab0a64b077fdb54c996443bfe5cb4a992c17ff6d5314c960dffb4a99242b25ffdb548532583f7edb2a2992c1fbf58d514c960effb30a8a648877fda954532583bfed4b0299221dff6a5)) else (if i < 10 then 0x1a24f1d2736937c4994a4b2524ec90ca4918247a922c6911048652421120b0901247dfa3d7d1e668eed4753a39ed1c1c8dae46a72338519508c4845faa2db9161c8a94451a227b912e8892e447422289106a877a43a0a1b850d02860742e0a15b90a5084e24254a118d0806805641e520e11067c82f84159209e5046681ed40d3a051d021c80d54047a015900207fb03fa19fbc0fd3a7e4a3f0f1f72cfad67d323e489f12cf83e586c3dcc1ed7cf6327ae03d5a1e9ecf49e7a163ce81e690f2a279183c629e194f03e77e63bb61dc98ed5876663b101d6cceaf475413a7d9d2a0e8aa740239ca9ccd4e5de727539111c7a4e3127150387e9c2a8e094701137d21bcdcdd946e6a37121b7acdae26d04365f1b1acd84a6bd235c61ad4cd5b26aa0352d1a850d3346947346d1a21cd09c681533e799df0cea06717336f19a94ccd8660c32e999668cadc650e32641923cc87863f631d818d0cc614576e316898a2cc47061e530cf984fcc20c60b3303d18068bf8e5f672f7d17ad0bcf65e352ef117670bac65d1d2e5e97174b7925b9d2dab96c10b20a5ab12d22167f8b308593e2c8296260b0d858192be995e9caedc570e2b6a9596cac2a55dc2acb15540aa1454762a0494e70a6c65337299b94b5ca4ee521728d5145c4a1d4508a280e93f909f084f17274e9395c9c084dbe26bc1346099a44c72261612f98970c4ad8253c12894938a4972248f922949056478a238811ac08c8645bc22ae1142489864470222210f5c873c433e216f10a60848a41f220c9104c881d8408c20160ff307ef23f191f560f9cc7c5a3df41edd8f6087a923d101e6b8f1a8782e3bc41db88ec4475963a6b1d058e6e072ca391f1c6c8e280708037fa1be70de206e6a36d51b478d98c6c5435f11adc0d5fc6a7234481a240d400698e34811a240d120680433bc19bb0cc8c65ba32a419288c79062d430e318418c0585f862f7017880ba8c5c522de316bb0b3f059d42c70161b8af5c56d42af015480a8585352295614880a35c50d427d6139a89b204c3425a012ad094504968246e120088eb846b62308115408920441e21bc10bb084244138202f0fe787d883e381ed60f4806b4c35a616780b3c0799025de12ef0f15877603b0a1d180e8c073b039661cb30d69859e02cf01335099a8711837e61b860d9986b4c2cf012ef0d2c867e43380196d0c93863ec311c16780c31060a42f92175c0b980584c2dee16b10b3c058fc2c2615c00aa305330290c140c09f004e3426dc1335097784b0c252e123708d1845a8226210eb085f842181fb00f2a0772039dc1cb00e0506d90351419e40c85061282eac16ca0b39056c82ab4149a0a0704da0251c119a087a03f301e800ece073b038781b8c0cd2062302f5016c40af0053f027c8129808c0040d01ea00e6c062802c10137008a00 else (if i < 11 then 0xeb18758c3ac60f2302117d78bcf45d622e7317008b70c5b3e2d7b16918b3fc594e2c6915fb8ae1455f22a8715178a68c515e280913be89af44bfa253d125889094473222f311198869c41661fd90f7f877c43aca1cd90e2686f04369e1a8f0d018650c313a182b0bcf85cb42d4215fb0ab78545c294859d509f284c2c24c9e7fd08ec844cc214e0fe7075f838cc1b4e0d1b0654830dc16ba0ad104fb82544118a083903d681cec0cc205ef02a4812f407fa033d01178068c02620070fff27fcfbfd65fe40fee77f36bf869fbc2fda87eb7bf4a5f978fc5c7e11befa9f6fafb107d5ebe9a9f448f9c47cc5be57df218f8b97c39be0b5efb4f7a17badbdc55ed9ef6967b283d78deb20f5237a683d1f5e86ef3fe79bbbcc91e5a2f28b791c3c7c9e30af1597896bc3d1e190f07578113bf71df2cef6a779f3bb11dcc8ee2b76f2bb6e5dae6ed20740bbb335d90eec4e760abaea1d6c4eb027530ba8a1d3aae98f749e3a3d9d146e843740bb9eddcefce745737fb9ab1cc98e5f972d339519ca00e4c7723a3901dc71ae3477180b8a85c49ce1dc710ab8771c32ce1437085382ddc0e2e02b6ff937e7dbeb2df206f73b7aedbcd0de226ee7b7659ba86dd0a6e48370f5b76cdb496d6e369f1b46cd9f06cd5365f9b2a4d90c6c69a8e61b11ad8546c0735f55af04d73c6b74b59f1aca0d6316afc35661aabed5196a69b5235a8a8d41b69f134e3da692d31d697234aada4e4d22c68f3345b1a24cd0ed685a341859fe8c93d67ddb3d399d8ece8e67243383d9baccd9d66b8b34e199feb2a666632ca9998cccc2d65fa32de996f4970a65a732c2124eccaa865313283d9392c976649eb23a9912ec85e63ff31f158f32c746638031ae98d02c6556301317258b3ac55762823132d893eb2df6233310b58802c3bb61c7b0d252e14c38f61a4b0c417480b9fa6165309dd8462c1eb60d2b04e181fec08560332914147fac0065fe02fde97e68beee5f542f9897c52bdd65eceaf5297a08bcb15e35af095778abb725d9cacb7d654cbaf35d4325c297480b9fa52282e69d72dcb8f45c4a2e09d6fc2b7335b562d8956bd8b5b35ab02d2c968beb3cb59b5acc6165beb2a65936ac90563f6b1c258cb2c4d96214b0de5845ac17d604cafe057cd2bd515e02aed55747ab9255c3aadd756cf2b5c95aa6ad1a5670ab2a158deac3656052b02957a2ab9855afaac9955daaab4554aaa97153dea9a954a4aa3d95146a850540ba9f454f16a738537929ab14ccca62052e6a961d4a82a50852612922548a0a3fd51e228e6146bea2e55149288c943bea17f508fa839940f2a0194fd627d993e409eb34f30278013b5a9d4d4e90a72d138749bda4dca26d3935dc9aa84d31266d1328e99284c712623d307897dc4bbe25cd92e1496d14b4c259492c1895c64ab32544d299a94874a else 0x68250500d802c0241450a20468c060068043822c46c983401fe115206b02da1976ee86b533379bdf03ea01a0a0a9f62fb271a08d126ecc1a0ec9f6ed35f1a20681bbb6f97ed05f3f7a255ed3f406e61bb7cc76800c402b444e41fe013084102180ff07f04508ddb89fc5001a048a2e6781a0308600481fe0fe08a1627201207f804c210509804401fe3de603f82283b3fbd9ec6cf0b6759b396d9c06cdab66b6b33859912560365feb2dc59632ca8d651ab26a5926ec8ab641cb1eb58edec6e3631eb16c58ab2c51b6247b11ad87f2c387617db0a8d8496c20d60e7b05dd823ec0935ff6afebd7e7abecb5f46af8d57b1eb8915ea8af44d7122bcd55e4bae245787ebbe75dc7aec7575beba875d0aae6f57296b8d95c5aae245703eb7ad5b90ad9ed6c1284a15ae5ad4fd6966b45b59daacd0d65a2b25f58e9ac655624684a14250a12845af6b0e55853ac20d6022afd357caabbbd5c92adbd56b2ab2955866aba7559aaaa3d54a2aa515509aa54d51f6a8a35418a9fcd4ecea6f5534ea98454b0aa4f95236a90554746a317516ca8ad54486a1b750bca841d412aa03d4fd8a7c953d669e274edaa74a5396e9c1127f39580d373e9b474d84a6c25352e9a594cf3a65d5320698c54c36a5f852ede96fd4b45a58cd094295f54acea551528d6941349dda4d8d261692b3493aa48dd238a91534856a3fb51e5a8ea14717a368d1a2e8ca54619a2f05166a8ac3451ba26ad127288c74437a1ff50f4a86e5432ca179d0aea851d4262a1285085e83d741b2a0b65049a81a74080a0104ffd27f5d3f689f914fb727d2d3e439f0bcf7ae7b653d799ea6cf45279d13cbc9e41cf12a78573bff9de9cee6a76c33b359d91cebde75973a9f9d334e8b6743739ef9ce1ce62a72a339259c7cce302717738a99c384e112701737ec9be04de1e6e9d37089b67cda266ca136179af5cd6ca6b0d35409a8a4d36e692b345c9a11ccfde679733ac99c6ccdba669f332399824cb966573329a99374c90a642d31f798d8cc5ae626530f998534c18260692fee97d44bdf25e872f0a9768cba625cd92e4096f6cb73a5b112d69969ecb3de59972c9296334b15258512bfc95d24ac0657a12ba495af4ac06567f2b139580cab5655532a8a952f4a8ca53f329c094c3ca56e525f290394654a2465097281293f9c9f524f6b279693bbc9d624e5926f3936a49a064cab261c92f8497464b65257992a6c94ba4a1f24f09268c926248a5241991f6c8e9e4711236991a548cae45ff22c69146c89ba449f2230910248796438d219a90b0c84d6421320dd9052481e2409920208ff3c7eee3f1f1f708fa8c7c623dd91ec08f574793a3c2b1ddc8ed1c75de3a7d1d058e6cc72b638e91c488e07c6f8e376f1b7e8d9c46bca35731a808d2a4686e33c519c38ccbc65ae324b18f98c604625230)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xb173279a24098074ada065aba665500d02a200b707b991abd981a0544016e0f6af799130334ca602dc1ee646af6602c0334194d7b05466ab32278b683281019a2868664dae07016e0f73220622033429402dc1ee646af661ba848005a0f208a142ba82beedbe5ef9e05d03b6659093e06cd6892db17400e81e6b268010408005657b06682a30ef9964408042d17f06682a30ef996394ac14c02b29695ec03f995cc92332a1356bde5a821c503504d5af796a0871403800c0ac0520220509a843821e39d0034a724110200aca880cdc3be65aafe6015951019b877abfe658c02b29595fcaf60d233166573248815844021c300e00602901102201e35411646801121fe02b08a2004e544066e1deaff996366441a05342bf95eccc5995cc920039d7f0060560290110301cc05a050066e6472d413a3818cf80da06ed819794208016805352eb5042576c0ca2d0cba0534e05a4b6844c22842b815d3382662cb50340c065cd155d33280d0284e42180ff1bba014a05601202abbb70620a6a0c4a0ff0880ef120820a50534810e06c95b7344090aba664ce0d9008851d2db5c0032a3feb448032e5a821c3075844422c0fb201dc02136b0a50534a011090053421c402c019422a10e201802740fb1d64c1b396d01984f422c609b045014a148048e6642840f308b27bbb9990a1030c29006205184b42289089d02627a10a07f97bba14809b21f817399906802a02289075844422c306d05241a59a06d9e708d18fced881d80d2cc8843c807a09000b732210f283ac2681161c6530139d71c4c5bb6126e50f0f482411e3802c1b814805dc5141160cd01a80ff33d9a05e62c0c19bb08b100c0db307f04588164066818021c11628180268116180302720fe08b137c20f206966a822c11405901440c40eb015828c22ad02b777b7c5be1cd5045822b0d005903980980a808a34057ddbcde012c23c5df0e70f35597745900ac1a0115446573ae204e4e2c0301209ba8450c07f005047e71213b0889b4ef5c60900174056024eed843d01029c5add42400f208a19340ddb3db571824008f012043d005604e4e2c2402620790450e0310a7843f7c0142ded028c0961484f75c28c09e0a88500b9bb0908450602b08e703f8135bbcc9845ce02408a03e460ed08b05900c00d20870450e0cb08a83482881142849405dc3dccf034006a64cf057024a02e23170f42340354006c01714709280bb87a11accf00d537e0ac180af33c04b08d180c77e1bf0768013a05de50f76c1700790a6ac1009a016804a422252316680252111236ec242114180902280f8180901fc0ff1852c03614c00584a6262da003584a135b3ce1668023c1282804b01210907f900c539809484048062cd000ac2324025809023c1192004809602408f0464a02b009009028011e08c9934004bccf04 else (if i < 14 then 0xc60ae809a21c307300472fe00c00e0560290110403ac21e15d04f10025b9e215c02c2220fe0111c1fc012010902c0169030191d01e012abbc3fc0ca500900700160b707f0074c047b50823c0ca0c602418030012abb81faf3c8d00489c0c20d2543509414407d0241ed4364d00904d80ca58c9d6feb2202d4dd8542228703101941a40264d9b64eb16783100b40ba2536c5e68816c7016d6fc0529bbcc9c450c153ccb0335b279a02d9e608e46200ea64c19bbdc03ee65ab7680a6017622801d20441b1711207f819ca02c06204a40ce40498a182500672024c1181280339046c10388a019c810f081849c0ce408f04450f407c200001a002b00566eeb2611e08ba00140d0099660823011e376cc00002badde64c22e6015f78c1c80358230460dd9306904500c4514ad984a0e00c08a66cca281222b03d813dd507683341b211b3b0f4019dd5076836425211b384a6d6b9bb08a0484a28603004a423611406c9450c06008a046c2445142b6cc2291140300348a0a60848390086409f84dc2539bb28a454c24e7067e0f41fe87a021942000e648a8cd8f56d6b8668805a5009670b3442d007f8050c060cc9b5b4ae057488b0054e57009f66881fe0152809005a07c1809301201d016900e606b00a81f0807327c80b407c408a6e380660db249b21f60fb09c80b4a82b09684000ba401004b4200043260240f01340978174a2d008060ac0ba48b6b5c3b44065016940b5c3d00903fc19c5012804819a0ff01f140300cb009026c0900ce3018b87bd9106680b4bc772a6848013c406681da0c402d06200fcc012cbf82c405757b0a1c53629088c245b7bba0748d68174b4479b0682632fdddbcd81d235af9e0416f833320d050894a8e0d22d06f4403b59e3a026341d8b8d1764c0ba78d244217bb1a2ec9d6cc8900d032f74341dbbad9b64c1a064c802940868624c456800567eeddf8020202b05476800c41114762d2a69bb01680580bb9a0ac9b6cd214deed80b4ece1562853405bbd102e834808759ead0200ca547016f05b7a3bd702e813eb409ce8840c608f014f68005bbd7076817429a901481e029a14a2705805202ddebf76c0ba14d3d7180ba0d28bbf76c0480493c6a2fc013bccf4407bb6062ed0049021e9ae376800bbddb0121e340567c0b1ed811f5c68bbc5000ba04b3c6a4a8914c015c6880bbbd7025d6810153ec580b4b679a06c99a41e0d25b8827421250902dd41e411425f74424074015f69821b5ab08a2032f5dd0d65ed2bb81ad069ef8387a7a80682c32eddd0d6377134011406700740ba999068045589ad02ef7740e8065cccd6881a08007f7753591a0bcf26b7bb9be003a0197333c3d0683401fdddccc85080e80d0bcf04b422892d0047c01408f0889771a088ce14e782145030764c0f807aad166ec1a07007e62c0c010e08 else 0x82b07d84c405a64079534a953890329415008202e831809c53db564c1cc04fcdde68010e02441a18150508033900a95a0088847c876dcd004842221292942019005435602a010e616801182400a8053021cc11705104782220872819427603acd004602221293848415008f02710229588ac51e5c048121304840f01110339022958806403e0a8f9950941c8361260a5922db4011e30061b401144a3809021e05d3818e41f5a0cba00a41fe14d016a16e20a69d004241a4508a03e01a40442002d2ee8fe0818084b39e80584509a01110111804800b47f040c04451a420ac5fe12f201841da1111100120a1143e58062b1158a0a38074e1143c68062aef9a00a58074e01d00656433859960168063bb75bbcca8575614c02e8074615a03282a05f602d281781f60d0cba084861060a3d5d01a07931680074c04501524c72e939302583405a084988b40b4011300e941cd04dce41680057974168034010090ad11881502fb016942b42fb05280b4802909880908361013c9e68003a817d852805a3014851eae99a03c98074c03102a0314252043280dc5f002d1824c22a128033902b536b052822cf6679300e9c05a2be00e819c8147014e6802b40a5aba022cf2601d48b685580c000e810ca122040043c086417b834822408f021941a208f059807408650328075bb615d0ad1417964d0a3f68003e01d00580b40a93970ad2c228024ac456280301000a3807500cbcd00092aee01808a052c03a80498bb803a06720be009605d1918860a01daddf6806061013857421e018052812c28e12839e341c8024cd000ac29601d39e3411e9a0168012eaee14b00ea333c9a000e80b4801b0a3c51c0a200b00e004334199e016a80362c70725682b3c0de0169eca6051005d63c0399a003100b5158a060019c05a420dce4425a40b09f451c03a7b2980602ba114076029528e04b400632d40130ae83b082c0a52a4012d2a0f55656201d40db2a8d81e56e807c00741b66097042602477f08417bb606b20da1881cc500eb0582ba0e6eed84c40d679cb82940960240329483640bcd044001a006500e9fbb60e681582f003e5809012c05690100f1602401b073402c2620bc00f9c0ca01fb7400790c401d415da4ac6dddbb3b85742b4d20dcddb57c01200580900c87d74776c14a15a094012cca36032d02411e1240348174f96d009036427a11400e9982c15cacf6f4426c01d300a52960d0ccf40ad20210e04200752029068660c19a41605284d828a129481a5fc2fe0809360c08c00c07f802c0c404b01731dd100fa0b667a05600c480821003a94a3e68333c0a5025821025277f0d05b33c08402300780a201d4668182d99e08a20aedd16b5b1b00b403aab74305b33d14b9c984d803a7041593404957400e8194d9a055f55d00ca04e283540199a055f55d009)) else (if i < 16 then 0x202d2801afbd59207c36ec22808f398581e4114033900080ef05ec0ac0ce571b564db660f204396c6c553079044410e5ac99420a06111043941b8aac093821c82da8a381b422205d2ce781c809b08a1340a1270a842e41560882826401625601a826c21442b3849c0b24fb04c9024e0590850264890f02d03202280ae2a43e21e11406d900be462040040405a504e80b541f5950a381e40ba7087815844b9954a383000ce02d42a1ab2a2d002902d81126543565428e0a8047810cdddb3db69dc29a120087981d210f0218c5ab14709d82ac18004330296b11a770879e5f32a1203845016c0e90219333e82b25602400fbddc0240402aee0d03cf1e6d802408783c82b4089282a05f0043180d40200ba02780b42000ec3269e6e712a09081e01500672018019a38e08a1340a0339c704509a0418993402283053037c06609e2043c0660db182ec22803306d900193bb08a00cd1a054680c4422a312b4dd0018114019a340c05848a03e40664030004b35a31188a0178c65303da382b760a4cc99340e0d3409528422c08f2e64cd0c5030241007402a6c5846c0f009001f664cf209cc99a181a40bf033941c5a8608a855b54200a3d3853423c9ac984202420bf0339412614d08d81e00ce50308454f7c0ed00e85602220d24664c210503024102280d227f819c99933560348aa60872855bbafaa10a60478210606e0b56b261110a9821cd59308e2e3c5dc0bb0219bbb84733c803b40c22d00a60445011e088855d5421080ab0348e010069023c2220492f77011e02d16805341f01563c68515379000980281f15c4281980300f208a01749db3000002ab175bbcc98348e05007b0b4009042685683b76503cc9823cddb309b562eb7799303e1bb160000055f76b679932a99c23c0bd02e81f081150ae00bb33c029280046806a806780b829799e00612c42340354018cc1e41b04a00a5b4014d016a00a280bccf00a73400100169c10936b0a505340ba508f84440ba088200774d806515df77005679b3cf10ad3dd18a680b405600c7e7ce82298802365d81a42f80219405806208a057c4c4043360f481e0784a68174b0d0051045815608f0219b07a11704e81fc0ce500c03a421e0432774404c00c176775c21e0509d04535205d4158d1c2004008034822208f0249422205417c45000925d07800005434b009f7701779931a526ca7dd7b50d67c5d8450300a733e00a05df77005642b2a5200d20180150334274116302e422a82b0249017282b08a812480d900983ca0560492d6100240d909e8454066601a806005a301ae02403002d200ac1731580691025a57b8ac0348807003040ac0924039e1dc01805009d665805a7038043c05a0db201c021e03506d9015a08f0168c0c601b8a682000ca04f0169d29a0a8032d68009c5ac260f426a0652008010 else (if i < 17 then 0x9b03ef1a043d4664a26c0ff0846340c21b08001d80ba409703f00443868051e22805d20328f6879e04504380ba0ff468040d20cacc91ea226c8d00841828e12c08301191a111407c1c0e679b028040d1a007431ea025a0fd07f84211a00743824428291488566641a0074382f043651407c9019e00ccd5802c8560c488681e10da66c1c6adb280ff8868458f9ab6c1803022c00b6ca03fe21a8556056828e0c00219424494703c043c05a581280b732a0ce08a4e4d71d1ad4033ab411ad08a2e3a228661b303f3620cd083245013c7607843e71c0db08a0278d9a000c03433161143c74450e0e90878278601804c66101173bb06844500ec8cc280440e7393cb682c41a111403b2402213f08a245335b9b103b1db16e36084140c090573638d8d0c5030241400c00000603b73260b303e1eb40aa108441e80905065053018a0760219419680b02e834a04e0cd03282e814a089ccf668010ed6d36f7411600b17b812e2290d04024f3ae27ee204c0f44f802496fb802b07901ea1f60493665805a0cd031052029a6053818f34002d02a02340ca7031c26332d97f0a405340ca702ea2b003a0c106d9421e8ff0668c0f481204883348812048845019a408a034d1a139b08a941d601207c84500ca50a9904c1560ea05715b3f209ce103ee71a90a4681c1f79c2015841502490a3324a71ac094850264a0269c6847c214099284341950d0030022c15060ae034334558b081c2ac11e043403cc224078181b73ba203d65b41a011309e81e4c0631684dc32e88ff0a68194e05809d00e41c80ff0169804c0cd03c843c136506801ea0f50d0089940055bb00ea2185f605dcc9b62c1775b3522b2b66002443154c1e66013043c1d404404d9402412e3b404261a0507c0d4c0ec36ef033a6d21144681678c13607c04510241183168bbaa44608e03e1b6612238180224116180492da11308b0168a01202c04291fe05a2c4002441161819242c0eb45342e4210812815a00c80ce01a830c0c500b4681c09a027027b682b2c1070271c09a0278896659b4013b0838139114706005340ba400583980960b6ade045605671436f4428e0ad0400174c005066012eaef99fcd5835c05610d08a281c40e1cd5821022810d2159efc00cc025d5dd18b0ecade002e0569229ef873862f6017e6549a078af00481fc4d0415940cdbe000d810b3400846cf1188086900202e811882b021942220e104640ac086500203b016502b0219405281b059283d0579a0021811100aa0540132fb0076835670fbbd5b2abd006c24602b05939b28113168010080de005e6f016399f16800fce1046d300480962caaca00f8e03c81b10ac0740d207c2e41b24dc44b62c2100bf088819cb5936c598941505080339946c2e8054021c0ba509084502220bf033941ec2ab08a019c80e32a3823c22 else 0x4f1024085008700b480414761988602b09904c02660d22826c2900491e659af614d0a40348a00c43f043c1b64476043c08854404d952140de015a7091a0105326881044d04058448a02e886a5dd05605d295df35600b88690acb58b80dd6feb4097700c8451056807c819c1f18d021ed0f3c00b09c0438f360ff081e341387ac680b73d00b088a66885610d0859d41e09d040a0ac0ba54d156f105614e04e97bbc99a08884348565016a3fe30502b02e96b560d6086a0ac22c58c1035821b02b021967ab02b468045080272310450956812815981ac11423140ac8da69ef067e35710d08a184ad3ad04d909c228506666ac4c409b08a10acc19fcd104342282d02804822810d4158b40a0273ec9699b565bcccac0ace14e0ce1f64b4d9a20869829850481580749d7f0ae80fc29009b2819332c0cd2a200b5af61480a6a027488b01695101365087a3b008854404d94f5007689b03fc2118d0310492000f802e90adb9c300916b2bb7bd7cd525789a09cd10ecc8ee26226804580ba7729df8b42d5c42cbd6549a010842e363340d30804340b6c7d29f03f32d9955eb9e50f275de5ecaf62bb61466e94ec2d3d9ce1668a7ae5bf2d0134022aaa12ae363348ba039aecc1a602b02043414d70041240005a408502a12280652009f0ee7da02f85348c46acbb85b38758b4ccaf657afddb02fd6b02039950af3414f4775ed017c29a8623694ec2d9c3ce1668ab4006205036b022882b5cf648240ab8d2027422805d3b09413848c8bfc06c0ba609d01e520002d2048023a14d04f1029339c0450194807206c819468168b6a40427c065280a414411504810f3808f0168d04a80f9ce209c10411b0329c18464d02e8c17011d0220eb1799370b042017e067302e022a0491b03c1840e402791b6e41307802b81045307d68015a08002e95cd958b6c982fc0ce571b568005a60f060019cc10609081a4614702402641f60902994cc4a0ad03c0194a64d06101746a6c512810c1840652aa1815008702e900da5000168c06f9e21042812a5140329012a4130850194804f47f8b540ca409d01c920002d201bc2745000169013c14d0480c12a886069024081244230348120408b8255228065220ac17011500e9005206908701d0802905c045403a4049e760411505c8348114405941dc1960560172e850c482b4001017a08c21582b4a02701482f4f420ae04682b4e01b087840411902b06d980aca3616802ac10e05d30537b400567ed106c150602b2a1824802d235b49f216008a0074a00b215831813a07c284f82c4850081c3fc03a6cd8015016715e0219752447f43104640865d49053411e1240219484ba920a482640ce5005829733a4d02158290d2a160482ac4c44d02f7500141001314450a02b0a4a3401104cbb83e80564d00441789a0f8131234082bb8))) else (if i < 21 then (if i < 19 then 0x6ec5a54ca06153cd0564c16c0674054f9d08628d1451eb260b6cd0019d2065e508176b160672d62e38405d08b010cb9a0068564f3161143c74450f877ac982b421007c0339a344060ad9810c8c0f0a38174086443b8340f1c8d008a1426c87708a040d1a00673664c0ba1160219101e0d2c5085340f00673362f376593cd01ed8a0d2329e6ef3400672b62db259bb3e0900220780121ed8f839a0366800ba02d07f810ca23108b03fc0ce402366801fe06720a8422a0671934008d9a002e83fc086608b84473400ff033949a0794cd001741fe043320ac25a1000219101212f02e8d20268043377741950d003a102b79994c225b535a4bbad177741a09eee856c2280ba06801d0c389bee802822919fad5d63020282708b2afba01d805c67eb568270868451054b01aa613bbbddc280a6b41a08cccc6b1341ddc08a03400e87439e6b42140d003a1733211401a83400e8504cce7806a10a2159517610a00e8d20a11303a0cf367a8081a3400e8502a0446280049204b4f5010846801d0b59e2d0665403a40a3cdacc9a7a700e9422208f00e80b48024ac456281a414700e98f1a9a0abb852c03a50148092ae89a03c98074cfe1a0b667808c02e205821003a80a804500f8308a01f040cd08a026c0f842a6568a3400cd08a36ec0e8703056881a007c228960c19bbad10340a103ad104001a001d2a0aeb440d00800074a0bacdd8340228406801e820007c2033422810003e1011e0600064eb7376114302feb1610308a01f0a02906c80b479b302203c01504068030120002d2054c0880f8054132f743d082851005a509644542068d088a14d8e0ed0308151b160f304856cf326906861deaf79960169473c11408680b4980900601742204907b14c03a59ecd50174c026031294c0ba163cd102d80ce8674054c0880a82294c0ba4f0031564c16d9a2033a0018b944a6ae4f32c02deede656f9e94c5251f7ae13b02e91ae0106041140005a50850194a280a8203641d610101690082135295016c80c048000b4714dcca94ac21c409d030120002d201bc2749000169026b058ccab5ec29a10e0541c2b2914054016c815d01f85201364066839003999604d80b5af61480a6a50fc10f0668c27403947600b4136502c04eb01203907203fc05a7087833410004404d94daa058c1e94af3400cd304e810003f0a20278a058abd80e41c80ff0169819a0800878278802004020acdf61310169a290131015e64828090e337080579ab08a10b28593ee100485a010d08a9c8ef39e08a1340801d08a1340605e4d691de73c4d008a190c415005584500f85093817413c11406d950c539e080836c8906088836c611e02ea94e94358b0339814614c0748124805d066840060540888be02800492e70813a08402e853408662a5845003a04322118a54662184750d40d2 else (if i < 20 then 0xd021940fab9c0690174092500ed680a9605d0ab1671b0620158440998f1c38df473a182ad066ec05681c680ac0c411025894295677033a06c0ba6033d9dc20286202194f0319e1dc39de0c402b0809c294bda4cf0406cee8620541c6fc6770120ee22fe05d4cb008eb41062538941fe04380d8174a0780540528086421884a63440373c904ea0c47312aee01fe0a802e94c6dbd205403fc16c04336f480202be054019ca54705404000864054151c21e0432002c1a801c00def6ab400870a5c18926c7084d05a72805d02198a8e08f089010c86e8054054c086490b10042a6067245de34406202e810cb1aa9ce844ab402f8052802c2228031267a3055a00812188056717b01e022206720be103610f02e9021fddbb3ba18826899e08082a109952a382980bb17f08a418813c880b04a4020d925c81f04cd8bcddd64c0f01110339a82c94b0242e4403a5a0b183e72601008893fc0ce780b0aac11e0432034822202d1b62e42d59303c04440ce6263a059b26111047810cd9bb069023c2220432d0581a48ff0248074b4162a38174cee111021980c45086d9810c9216069023c222043281740c5147088810cab7601ae67861002d2be3571203503390c1f81604e810c0ba5307e05813a54702180b6b4005d4105b04bbd1ad0367805a6015934238409d8e436800ba04341a1b04b39303c04040ce63d3c5a8cee0243c68534c686c0b01e015606728d7c29a08f02193b4078d014f76c1cc08f01245dc29a7b654e4eb104a10a3023c08666c5c896384078055819cc14c069023c2020432855b7ae0a80121e5c298616ae05811e0ab021940540d53e58092b1118a0891e5d0bca185012460d2016840460d23c68568092409b955405a30889e5f7ae14c0ab151cc1118b50514f6815602e985aabca05b02000865088ef5c05a5470a2945dc13f0218c5dc14a0218c0218169b5909420002d3269e3671294b5051405af8dad005580ce716a82d8100043205681a55bbad0019ca2f80ab019c75880694628f2e02428060048da08bb9e340ba60ae983c0300a52a3812ccfcb6c4151d3140d22d62004830800e901a407d089010c806500e81777afddb0aeef442b48404d6809751a202e940300a5307d68005604b02e9f33e01003290950560b900e81f7bb9be03cd9e7980d203c04440ce4512dad411e0658bb8174d5a07c6a5dc0ba01d2ae4e2eeda0bc680900ce606904440f014503396b4159ede8983c05a01d3667a726a0f012668005a01d382d81f604318040f5199209b03fc2118d038f040ba15d0339029a0ff094019c8e4d7d4204a1a00822d6cc08815348a00b413c613101740480116c9b644f6c78ddb1dc05a6b50220174c02d0a9d62c0ba0b6033982a602d8d151dcf3605d0339d28e87a0a9b64c13c577401102a602d2194d28ed9363b819c13c else 0x44a5300114206b8e0a983348153066818060581c78334022153285402422512d688411101a88ca7a36166880a999318e400180b609490018813008843c8003090881441271000c23c2404c04c0a8305b049c48130a60802002400e8c13205d01200748616ccb662c6024016854c6000281aaf861286d980082424000142150c3b36024c2523b3600002503b360250004129259b00021211824c004129180002422209851c469220980081a44000034950c34230000242323d05b1615309384a40181030089f316120093824c86be0938008028408b834908c0002211800011e1c9b023c8130001023d00f03281508000093aab06aac001849c62d5949204c0004088824c24e304c36800ba11f2054c0181291854c0181271903c0180110a99014c00c05b04a40225809805d50c26205b1424e00c55602d8800c093843c0224329b6cc252309400002419a220b8246c8130001000212110008222127191e800212119b1cd2441300100cca10f001049c613603e04500a84d1b004c1263000664c402c0120074020400e8043326309480a81279932403c0da02a01f1013002a02e80f824e500000904013cd0000003a400156cc54770d0242129068d0246060080080c338e1849c048216800d4f2e0012011301209d0151025e34801500401c8501560ac20005d200600980101834c1a00652158348a0d20329b1f7ae05d00ee094b411a24804ab662f86c981f00e863c68221210dbb03a15b2606e03036ed75a78e08a1db271a008a01f020606703a1c0ba11500e9ed9b171a25de9f37691104781740ce577438942a607c0339737608f281b64c0ba5281c689b2615303381f0c40fad9a60a3451a002e8074e0c003384001500432bf780973ba3c08441cee062015843d2462329806011e99605b01740ce8804c058ca6a2577402a00ce02d4118a056065404a0580ba02dbed5f82b40a05b3ba173806701695012ee85c99e3805a50313ba0f1a067016950135a03c6c6880ba501684441a40a825ba08c44169c982dab400673c02405b7cf7cba530b7cfeedef44a9402d4a6152ce653912dba016c0670169803898a2c43e5c85c65c995fd0a005d2a3fc1041150481018408a041051c0ba508b03911a034a0158454d29202e82ac1500432baf949a05d182b5b40a4d02e9144b58f9129ba016c0800219d04a0d28d100b40cbbd7ad001750063047819c0ca54a02e9813a14d06901e00ce55129ba244a0ad17d8174ca0f00ed05805a049285680ca02605b1e5c0ce05d385680568094128576fb405d3cb834afc15a0581f41a4b9c02e8124ab9f65083480ba04928896dd158f0338174b1a2ad0017403a48d15680f1a05d2194d0135a0a50834872605d024a013a54702e80b4086501685723854a12a3b6780ba04340e519426770690174092602e951db1e02)) else (if i < 22 then 0x403a2019405a05d1b9b005801d0249005801d0248c05e41208a6f8009002d4159eb27dc24cf8434080550b0077b84049230d8014035064108cc0010338e81e41208a0c2281b1b00740580d2245341dc04e1a0ac014010084105a000a03c03b809e581581e129a5470279605799300c2a184c40b6351b204a82b231668816c61313a4a58e02aee8ce8229a7556028c09c3131003016c0ab02716f9e00c05ca0ac09c5080017405502b01f940553a000601742005eee1517ba26161a1945a0636415d5dc1900783047b326054184782100c81898805411100c100559931310150800001500c070090160040224461284041e43be784dc0c23d1b00a811e00a220ac19e11600510a820e9120ac01410e195041b20e91950733c0d907490c2c02906983288503000047c650808000a101211800c1cc0651d9b00480001c83c04c06502a12b1611e000019481110844400615a1844400611e1d6cc24200008f10a07636012000080000120444759500004846503000564c23c40041422a603b01e8004424303fc1103277da480400012000406a22094e78228301380d402539e23a481a4020027104fc8d03cd809007c574900a804804e200a8d433a00120138a02b81024000ba40060574030110256400a814d18076b4015d02e900180180878c01815d00e80602985c04d63c17237e580400560352483e0084f18c136eca04600826097aa4b4901193040102605809e101182acb005741906c1502055a5d042ac356080d558a128d812e1241836c29a216a80204e6c00e80206286ac509cd80080120f3400080120c03880b0218c0001011007822a06700ec0aca15dcd01ab05a007828bc45b40007639003802d00e817480cbacf007019a01d02e98131bd704d807c0ba50a680e4244390780b734001d02e964d815a00e80980a850b201940a8300e8031558018205680180185561003a00c0290060815a00e00980a8400e00980a83329807004c3168194c048065cd00074c0240060820480b9ce007c1e4502581b4402d0258174640700f96ee05611129ab001801818bc400001d088905b400000e8c21e120dd058202303500002403cca8000240309000000963cca8000a8e01d6d014006024100d000001c18404200076384047636000007460180258a7122d003c0c29a0000908c0c35c602a0444801c3c680b403a400e1f2c05a01d2007404802d18c2804801819e3404801818c2000002b01a9330401d6bf8040999501504a422c05d280740da04e0151022410f1009004c2307b680402d00e082020dc103c81922529a189f9e300ec18c0c6407200740482b1b023d81314700e84a0d40900e81746063cbfa0800184887007004c3453003040022958a0560dc02e8390801802a0444603002a0819011e10008242202a040c410300130241a046078151b else (if i < 23 then 0x50148074b816512d680a8e45128120a8e07800e9631414d1489702d18203c151cae3660b60941a454703c19d24a25c0b151c0f051af8000244373600744a2506920580ba02d28530280901680759424526951db3c078200d428b1c20690558b58f0000488608f4b501946122052881a4024125a905601c1e0590370621817501201dad00090aa4d0150074038d7f03c1800011e1098981e0b6066914a6c0fc07a6888e92c078829a0260908e44b40f009e03e3440b636058274250b0458411506c882421151503f02c02d1d9b00001481d03c290054180b581f8160889301e1111285981e98218000a118160871301e1210000c00050308b04f08503094800022c4c0b0701e1112c53628b995201721a001202e900ca07c00901d21a05000a42157d4538d001e8d5a20a80004228408a00d4400cc04964009c82b2a02411f9a28158174a00c013043c606200620acf1a02609d99f2f83d4158150901290781d1116407fd1dc8f4011211e942d40f2094048a977261890240756c5843480ff45d080060bc1202430d065f00210f4443d051c4002439890e60fa5cd81d21a00dc3086d025073ccd01d01a6695601a20560a90339400012348a0c0c842bbcede7015e0652311c0ca8620a501508e9271b00982b40d22819522a0d308e909ab49213166cc192026300081d62097006847a803a04201a18d003b0194e0f0001047c60570698328681283981d01e8404200a0482b0a680980ca0542c0ac2b40490891204e0630248e42d5a242b402c1fe5312c85821b00b07f941699950550125056504ec85a01609e0251642c04a0868c21a24703a81208406075e8d80a880b293ac80c24058600804305900208407821202c152043284220562421010c00610f22108086005089100aa80b0220c4f7012ccf81f0080500101d81fe074209140000ab17880f08947036d8d85a001d281e141e03c168102b4a5301305340a85052918804c10f23a48c4b6364a3c51c0da606e000244a0f2240c42460021d025d24274921e80620022000a71c2239800c0e8033200092920880139000412303a00cc800a093897261140198e71c83108a049c02e5001049c066114230d80221210749091c23124300088c36001049c606f090880e60310018c0620c30010c0ca10e3d41e78f360d003a040d0e3601d140c611617000e86e9206880e4610808b80e46e6c06880e460d101c8822a108100e02122d003c1027879003080b48e6ccc98446b7655305b18ca6e36507e8d803121605b1ecd9225d1b005caa695305b1c19b4364a9918816c571b00e416c5532044816c11113100b4a111d1b02d84c402d2e0d8f1a0610169022478f03080b48503b1b664c00040158b4003a01008a1405cdc24cf84508466405bf8005c067283128ee07a00180b4a88b80900b00e84017099822 else 0x15582ac11e0573a11083100aca8620a502a0609b831043c681b04dc188609b83104486e6c04d8074609b00e8a30539d43104000565054218821e360b004006a9c200e9672640923100b5f1a50149e4803a360b012173e07800e9405279100e8cc1e0d24cb03540f0573628940f001d239b0100a2)))))
def rootMH11 (i : Nat) : Nat := (if i < 1 then 0x1b60a59a2b00040000a6200b4932c20e80f8c17d000162c2a4f00000001b650034a4e5d2be84044d5c0723c58a03e039888bbc0721b810601fb83841698902d13933d807840a94043244b06b8e2ed1f00122005602000a8041b072eec6423cb24b22101214008907644d40f4ad78a3aa97d34ca820bdc71b63a0a1c1f490ea601042bc1a4bae876c29114068b8d7003408cad8f82ef68e212341f511ed06ae1100200045a04ae085c06b8370136226380b101eb0824281e5f14858087609a102d1311062c0b20162891ab62768a00b201e0087847c4102a1f0629a8c3419e5bd0044d66ad85d30b7003e8cac0c89475064a703d121828ab35208241ac845c9588ee681f6826307aa91940d503ce081842cc1be081a32d611d41b921c536c210b80a7038302bc265561a382706a2451818a833f055e065aa3f110a08fc08480df80a206800f1012081ac603a10286430202b3460b8913bb984b67203cad4a02a344ca08505a998f005820eb40a00c1217ca018d1603a4d274730d24e8048605704a7c062904708a010e022c81cea313003091102a1050209d103d2477033c49b26331224027b46601ccd08c132247640b783522442ebec21fa359624926101aa2b40b36d0f241fd81af06b4c808116a19d03b7683e867a466077e07990974c3297e00f900b9024492e24f56195837a06260f7243849ce51f40f1c01302ce0200808083a3b800061b0807c021d01800000104470020b0e81024a40680c000f11818660c000000000670f400230084858021b01808060081804030e8080006000080e000205c00f806818080001be0020f0201008030492800010e01c10002300c0e0400198400f048311e3c01004ee0a010181804038103c003d8040c313d0001400000086002170000000370001a0200824020b0c800020b001fc00ad0002c0007000d4030401014002003818000e00044081700004001800814020c0003000013b804c60e0e002040005820160100058e60a6b020081c4c008ea000300408b600000700a000040001008040075002b40c040000084350b0c403110d82816130000c3811038100819028080007018000a0001000100b00008000002000060a0000804040b00000250e800003e0600c422f05004bc1f4702910070502000950200406000a80c1800018100800000301a0b000842200000dc0e03000380c110381450490000400010e2200002110000806000240e000924800000780000090880584000b0680606300000a890804404092b02c3c98188000000010000a010181814020080202240281c0e570001400000b81c020400174002d0c80c8c000e00002008d001740500008000f05034be4f2501000090504cd200328182c3d01814003b04088060e000440e1a0100802850787c0a134e8d406330006c141a008046496 else (if i < 2 then 0xc245bc3505a6062c22f029f0727453911f039e04a42d980664a240276020ede100254598c16c9d0a151532127480ad00fb47e9620259401357532110ea37238f740402415a610b068f491890fa920345a50831234240041a80700863848105660c6d84301cd045691809cf02c251fad20c184016bb88c07f04be02f1060c915e23d907e489a00889f442008676d1c81973303222203d91f1cbed7866082d13780e04822022c13d11f767a69072944ca610264a3e5a170139739e8e181de81b2a77205e490b21540858019419dbb5291384030014821b02ee010516581a602306d080ac1352085769d80c499e0008410428c920c105ec0c8c8f2d04d07364e3c06a02d106e8810817a32f00790006418c03ae05bc31e9202a1ec08f803b819a2159412808a02110452635a0412974838fa3220f601a2c48a07e80d8120c826606bf4d7c87f038a07514f5c8f50b6e32acc830158b02857ad47c94a7334905d8eaf40a6105f039200598bbb22138c4eb7014293f000fa0ad81b580fe0696262104d046407440eac20f49ba76ce0846e30025841b406d41bc029c012c03f104b846d904244fe8d7cadc402451b22428146a5f92d041f8015d0346ce240c199d9487c10540c7030f081f02ec1b441ff060b62f0107ab580505275017c03fc020f45089d23abf640921bc1b3999604424fac2240057056a0fc800a9c03606c905c2220160014065f808f8c5a45a20eed093225d446a07a6c3e83b7076411a80c6a30a05d6a6500c0033900d88e1040b823802ae07748830c8a23d001841e8c89865f68cdc1b7a1e972966ffc1468421013c05210c1017f736e0e1e1a20153053724b1a40343d90b66191d62381d055007c503380ca37f40fe509553b40182250a98f342948368c529ae49b74612e8881ceb2d6055728c4058921006da0a50000010c022802fc00301de074e0e059b7847a43149018174a12d0249675821a8363a0e6b2281bb84304370c5a0018a2ba018411c8881b9ca50161019a1b81cb084e9170056434b131a0f3406c000e44b60f7cce621cd26aa4f78089308f11f4222e9de91e696ce0475090010f81f94c8420e83470810050c8f90085037231f11498483016e8ff419900a406028b0c0eca1a1217c09b409f22df12da00b24de00f54522024c017d9a601d407ec024d00b43d403b21dd584b076811a4147034f026cad5a52e00c9022c0005e29a1e520a600211a1134702222ee0a3f91010150c700903027c034b2ba0000a43104fc41150d980f1b0dd2878a4680cf912d26e0da03b9301ba4308407816643de867c01e805540d20224da281ef012800041c40462743a89200000001088e80040d823690066c57d1fc01c2433681c4ca9b9b80531002a0a290cb712e040a244a3e6229c000016313ee00002060000c11a000004001270001 else 0xcc09344b18972644f01ed83cb04ca2d181b2000087b16f3022a93da03420c980ce3c5f971e282918c3be20698c720915a392567e05f54cc8489601ac70c88f81ff01686d70093bb4a28dc1090149201808080fb886b832a02360bf8185209d02a9078c01c40fa04960c311f90433055811d898749c7401088d9131227b054e0ec4a32a3b404a0c9d84ff024648a404c001b82190438c3c021401a804bc0e50238b39003f121a805e2267030c897d23c08fd01d00e85138820126ce029999dba3107cd4d851ab00e28326087d1ec4a73439d6f3c02822ceb34a8c58cad32d503360ee59a349470076478c0639378954c02680558343241c8fde81f529504f20b690de837e91780932495a38c45924b91206b00202e8677d11e019201700b9006f03c1089647bdca711f480e71209219bb4705ad4cf401ac34216260b310ea1229065a8dad130a2c711f04b61d59a38b011e089021b9468b78cc8e6cda004e12e602b91d610ad00ba0b2a0ae846f4828872c1d2934848a20e35643888e665562a45eecbe62789016ac3c894f05e4051416e0074b498088c1709b3f408271911d450ba963804a02018207b0b768a80b6585304a805e81c80a0821c6d09811703ff44760a4017303e1904e913))
def rootMD10 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xc7edb36a15264810f2ed526058265830e3ed526a18264430e3ed52605a960830a7ecca6095264d10d6edc56c8a165830d6ed526c8a165830df4db5549314c120aeedc22e1a624d20d76db854da564810d76db854d5264810f1ed875cda864810d5edb75cda86481097edc86cda56481097edc86cd5264810b6edc62e9536481097eccb54da86481097eccb54d8264810d6dd736d8a954d20c7dd536cca960910cf5db3549a524530b6ddc62e5534c120b6ddc62e5314c120b5ddc72e5314c12097dccb661314c120d75db86955264c10d75db854d5264c1097ddc86e95264c1097ddc86cd5264c1097dccb6958264c1097dccb54d8264c10c7bda86d09564d20a7bdc52a54250560d3bd986d05260560c7bda96d05260530c7bca96d05260560d3bd986d03260560d6bd526d0a165830e6bd652a54250560d73db854d526501097bdc86cd526501097bccb54d8265010c77d546d4a94c520d37d986d43260560c77d536d4a960910d67dc26d4a165830d67d526d4a165830c6fda76d8a366120a6fdc628da16612096fdc62e55366120c6fda76d8a954d20c6fd746d8a954d20c6fd736d8a954d20c6fda86d89564d20d2fd986d89360520c6fda86d89364520e4fda55899758430a5fdc72e9984c520a5fdc728da166120c5fda86dca94c52095fdc72e53160120d1fd986dc9360520c5fda86dc9364520d1fd986dc326056095fdc86cd5265c10c3fd986e83260560c3fdba660536052087fdc86d5a36491087fdc86cda56481087fdc86c8a95056087fdca6e4526053087fdca6e4536052087fdca2e5526053087fdc82e9944c52087fdca2e5536052087fdc82e5a75052087fdc82e5a114d20a5fdc5689975843087fdc56c8a96056087fdcb2a4526056087fdc56c8a950560c6fd546d8a94c52087fdcb6959348110a6fdc62a5a954d2087fdc56cca96091087fdc52e98264d1087fdc92e95360910c6fda56d8a94c520c5fda56dca94c52087fdc52e9984c52087fccb695984c52087fdc52e9944c52087fdc92e9536081095fccb54d8265c10c6fda56d89364520c5fda56dc936452087fdca2e5835491087fdc56c8a958d1096fdc56c8a165830c6fdb66d4a94c520c5fdb76d4a94c520d4fd526dca165830d2fd526e0a165830c6fda46d8a94c520c5fda46dca94c52087fdc12e95365120a6fdc22a56350560a6fdc62a5a94c52096fdc62e55364d20a6fdc62a5a04c520a5fdc72a5a04c52087fcca6e15264d1087fccb6a1934811097bcc96d05260530b79cc36d19850520c7dda72cda466120a7dcc3691a166120ae7dc52e1a624d208efdc62e95366120acfdc72e1a624d208dfdc72e953601108dfdc72e93160110f3d198605314c1209de8cb5cd425c1208fb8ca6d0954c120e675652a55158910c4fdb76d8a94c52083fdc82e5a114d20 else 0xfbd1814c5804c120bfd1c1261314c120bfd1c1255314c120cff1a16c4954c120d7f0b9605514c120ff61a56c95148110ff61835495148110ff61a85495148110ff61c35495148110ff61c95495148110dfe1b36c95148110ff61a35495148110ff615264d5148110ff60ba5495148110fbd1814c5804c110fe71656cd5158110fe71656c95158110fe71654c95158110fe716564d5158110bfb1c42e95148110f3e998549814c120ff4953661524c120ff4953549814c120ff49c954d524c120ff49536c1524c120dfc9b36c9514c120ff4953549a14c120bfc9c2295314c120ff48ba54d524c120fda974661425c120afe9c22a1a04c520afe9c2295a04c520afe9c2295a14c120ff4953549914c120ff48c954d524c120ff49532a5524c120d7d9b5661314c120b7d9c32d5984c120d7d9986cc954c120b7d9c12cd984c120d7d8cb661314c120bbb9c40c98060560bb79c50c98060560b9f9c70c980605609bf9cb0c98060560abf9ca0c98060560b7b9c42d5984c120b7b9c42e5514c120d7b9986d0954c120b6f9c62d5984c120d6f9986d8954c120d3f9b2605804c12097f9c82e5514c12097f8cb661514c12097f8cb661a14c120e3f8ca661814c120c7f9b069ca366120c7f8ba6c5984c120d3f9986c05360520f3d8c3661814c120cfd9b3684954c120bed9c62e5534c1209fd8cb54d984c1209fd9cb255314c1209fd9c32e5514c1209fd9c36c4a54c120bf99c4255314c120bed9c6255314c120bed9c62e5314c1209fd8cb661314c120cfb8ba611545c120af78ca551535c120aef9c02e1a624d208ff9c32e9545c1208ff9c12e9545c120afb9c42a1a04c520cfb9b4684954c120cef9b6684954c120aef9c62a5a04c520adf9c72a1a04c520adf9c72a5a04c52097f8cb6a193481109ef9c62e5514c120d7d9b32e5514c120d7d9532e5514c120d7d9c32e5514c120d7b9c42e5514c120d6f9c62e5514c120c7f9a96c05260530d3f9986c03260560ff498354d5248110ff495354930481108ff9c02e95360910fe95634c56250540f3d598605314c120b7d5c12e1a764c10daf5b25858060560d3f5986d53160560b3f5c82e55160560b3f5c82e53160560a7f5c22a53160560d6f5b6504a94c520d5f5b7504a94c520a7f5c12cda864420d3f5986c45360520c7f5a96c4536052097f5c12e55360520d3f5986c49360520d3f5986c45260560d3f5986c43260560aef5c12e1a624d2097f4c96c45360520fbc582605314c910e6f5632a55158910f3e5526058264430f74da56095264c10f74d536095264c10d7cdba6095264c10d7cdb36095264c10f72d536095265010d7adb36095265010e76d536a1a564810e76d536958264810f56d536095265c10e76d536a15264810c7edb36a1a564810a7edc36958264810d5edb36095265c10) else (if i < 3 then 0x97fdc82e5a354910c7fccb6a15264d10c7fda86d49264530a7fdc52a5a960910a7fdc52a5a160910a7fdc52a5a060910c7fcc56c8a960560c7fda36dd9850520c7fda46e0a94c520c7fda46d4a94c520a7fdc32e99850520a7fdc8695944c520c7fccb6a1944c520c7fccb6959258540c7fccb695944c520a7fcca6c55365120b6fdc62d5985052097fdc82e55350520c7fcb52e99850520e5fd872a57350560a7fdc52a5a94c520a7fccb615a364910a7fdca261954c520c7fd986e8954c520b7bdc42559360520b6fdc62559360520d6fdc36d89564d20b3fdc82559360520a7fdca255936052097fdc82e55364d20a7fdc52a59360520c7fda56cc9864520a7fdc22a5a960530c7fcca6e45260530c7fcca6e45360520c7fca96cc526056097fdc82e95264d10a7fdc82a5a04c52097fdcb261526453097fdc52e98264d1097fdc52e96264d10a7fdc52a5a04c52097fdc22e98564d1097fdc22e96564d10c7fcca6e15264d10a7fcca6d58264d10a7fcca6e15264d10a7fcca615a264d10c7fd512e98264d10d6fd652e96264d10c7fda82e95264d10c7fcba661526453097fcca6d49264530b7bdc42d5984c520d7bd986d0954c520d6fd986d8954c520d5fcc86dca94c52097fccb6a1944c52097fccb695944c520c7fcb52e9984c520af7dc8549a524530af7dc5209a5245308ffdc86d5a2245308ffdc82e952645308ffdcb209a5245308ffdcb215a22453097fdc52e5814c120c7fcba2615264530c7fdba2e55264530c7fcca6d58164c20b6fdc62e5536452097fccb54da86491097fccb54d986452097fccb54d9864910c7fda56c49864d20b7ddc22e5534c110d7dd736c4a954d20b7ddc12e5534c120c7fda76c4a954d20c7fd746c4a954d20c7fd736c4a954d20a7fdc12a5a954d20c7fcba6e95364910a7fcc96d5a220530afddc3215a224530a7fdc9215a224530aefdc6215a224530adfdc7215a224530c7fd956e882245309fdccb54d824c120bdddc72e1314c1209efdc62e95366120aefdc52e1a624d208ffdc82e9954c5208ffccb69d98505208ffdc52e9984c5208ffccb695984c5209bfccb54d98605208ffdcb14ca960520adfdc72a1a04c520a7fcc96c5a814d20a7fdc914ca960520c7fcba261954c520e7bcb42a5a954d20a7fcca660954c52097fccb54da864810ff4d53609524c110ef6d536a15248110afecca6095264d10df5db854d524c1109fdccb54d824c1109fdccb609314c110af7cca54d52601108ffdc22e953601108ffdc52e98264d108ffcca6e15264d10f76d512e58254910d7ecb96c18254910b7ecc968d8254910f75cc954d524c110cfbdc42e95360810ffc152605314c120faf1b35858060560faf1b25858060560bbf1c54c58060560bbf1c10c98060560dfd1b5605314c120fbd198605314c120 else 0xb7f8c96cd514c120d7f9b82e5514c120d7f9c82e5514c120d7f8b9609514c120d7f9b32e5514c120d7f8b96c9514c120d7f9c32e5514c120ff69c854d5248110ff69535499848110ff69535498048110ff69c954d5248110ff69c054d5248110ff68ca54d5248110ff5953549804c110bef9c62e953481109ff8cb54da8481109ff8cb54d98481109ff8cb54d8048110ff68c954d5248110ffc552605314c120f7d598605314c120bfb5c42c95160560bfb5c40c95160560df75c16d43260560bf75c50c95160560faf5c56096160560faf5c06096160560dbf5b56093160560bdf5c70c95160560bbf5c82c95160560bbf5c80c95160560b7f5c32e55160560b7f5c22e55160560bbf5c12d58260560feb5654c56250540dbf5b24c58060560b7f5c52e53160560b7f5c12d5984c520d7f5b8504a94c520d7f5b5504a94c520bbf5c12cd8260560b7f5c1261954c520b7f5c12559360520d7f5986c4954c520aff5c1215a224530ffc5c1609314c910ffc582545314c910fbe582605514c910f3f581544a960910b7edc22d59850960b7edc22615264530b7ecca6095264d10cfedca6c88524530afedc2215a224530ff4d53549814c120bfcdc22e1314c120f76d535499848110eeed526e1a624d20eeed526c5a624d20afedc22a1a04c520cfecca6c5524c120f7ccb9549314c120f5ed875cda864810b7edc82e95364810b7eccb54da864810d7eccb54da864810b7eccb54d8264810d7eccb54d8264810b7edc82cda564810b7edc32e1a564810d7ecca6e15364810d7edb82e95364810fe9d5458d3158940eedda558d314c960b7ddc3261954c520d7dd986cc954c520f75d53549984c110b7ddc82e5314c120b7ddc52e5314c120ddbd846d5715c164bbbdc42d58260560d7bd846c59550d20bbbdc42cd8260560f3bd8461d9850520d7bd846dd9850520e7bd872a54250560eebd5468d6258540b7bccb54d8265010bb7dc52cd8260560f4fd655cd985c160dcfd636d5715c164aefdc3695645c560dcfdb15cd635c160dcfdb558d715c160e5fd736857466120b5fdc55cd985c160d5fd986d5715c164d5fdb35cd985c160d5fd736c5985c120b5fccb5cd985c120a7fccb69d9850520a7fdc52e5a260560a7fdc32e5a260560b9fdc72cd8260560a7fdc52e99850520a7fdc52a5735056097fdc26d5316594097fdc36559360520cefda56d9314c960cefdb558da324960c7fda56e0a94c520a7fdc52e9984c520a7fdca2d5984c520a7fccb695984c52097fdc92e95360810d6fd976d8a954d20d6fdb65c4a954d20c7fd972e9536612097fccb54d985c120c7fdc92e95360810d5fccb54d8265c10c7fda56e09364520e6fd956e1a624d20e6fd956c5a624d2097fdc52e5a360520c7fda86d4a94c520c7fdb86d4a94c520a7fdc82cda564810)) else (if i < 6 then (if i < 5 then 0x6bae174bae685c56b7816caad585a1ab2d1611abe65752adb1589aaf25516a901508a9f05382a5d9479a8b6512aa1d143a28374ff49f2d3e5a7cb4f1c9d4539126c94cd69a69335a6584c3697412d0a5804aa23f90deaa5224a0292a1235a43c481a8f791d0a364466a8c19164a28c449e88810f1a1a642ee8559093a0ea415a81f902ea0203faa7e98fad9f2c3e163b74f6e1e833cc47894ee39de83b8e7660ead9d2c39c272c8e3a9c4637aa7094dfb1bd537683b74dbb9b48364e6be0d569a7034e06520d209a1232906698cd319d5334c6520cbb9948329063f4c60188330a81b1cc0b97f62f725360a6c177c2eb639e8b9d16ef2d105a20b2c96382c1256f8ab995362a0e5360a6c0e7a29525140a28142127ac4e9c9bc131f1dba4bc096092921cf448e49050edd23d246b08b791401fc8440c87110c1214041c47968efe20a0404c7f20fa71eb83cb477f0edd1cf43b7475e0e9b1cf4392c70e0dfb1b9836746b70d3f1a04334c6520c4b18382f7c5d80b3b16182b745570a71146828144ba094511bc224c4320864106a20183e4877e0e661c1036386980cb618b02f785960a7a13c8253843208060ee01bd833e061e0ad813c824a041a07400ad80f4015201b00178000ffe1b2605514c120fbf0cb4c58060560ffd198605314c120ffd1814c5804c120ffd195605314c120ffd0b5605314c120ffd0a5605314c120fbf182605514c120bff1c1295814c120fbf1814c5804c120bff1c1261514c120bff1c1255814c120f7f0b9605514c120bff1c00c95160560fbf0325458060560ffe1836c95148110fef1636c95158110fef1b64c95158110bff1c32e95148110bfe9c154d425c120dfe9b86c9514c120dfe9b36c9514c120bfe9c82e9524c120bfe9c52a1524c120bfe9c3261524c120bfe9c2295814c120bfe9c12a1524c120bfe9c12e9524c120efe8a8549a14c120dfe9b12a1524c120efe8ca549a14c120bfe9c1261524c120dfe8b9549814c120dfe9b2261514c120bfe9c2294984c120bbf9c50c98060560b7f9c82e5514c120bbf9c02cd8260560aff9c0215a224530bfd9c3255814c120bfd9c8295314c120bfd9c8255314c120bfd9c5261314c120bfd9c52e5314c1209ff9c86cd515c120bef9c62e5535c1209ff8cb54d985c120aff9c8295a04c520aff9c8295a14c120cff9b8684954c120aff9c82a5a04c520aff9c52a1a04c520aff9c52a1a14c120cff9b5684984c120aff9c52a5a04c520b7f8cb6159348110bfb9c4255814c120bf79c5261514c120bef9c6255814c120def9c36d8954c120bbf9c8255814c1209ff9cb295814c1209ff9cb255814c1209ff9c82e5514c1209ff9cb261514c1209ff9c52e5814c1209ff9cb294984c120bfd9c12e5534c120b7f8c96d5814c120b7f8c96e1514c120aff9c014ca960520 else 0x7a41a00123056403200ac021c6032803e00f6c6c00eed249cb808a8032c0ff00fc609101fe01f8c03103e00481819cc80824a00e900d411599140074802801fe0668c065003800d033409a022802d007405d0349403d02240668c00e002c0c345200d0050114d3f01e06800570a681a850354abe01386091018801f8c08002c80cd1819a03b0162016900ce029404b04941292d28e052809609282525030c66200b46075bad803b005a4007805100746ff0803c028803a402e40fb00746054108d068005a459b00dd00776b5d8d802d302b5831334007a0251926980d3c52c812ce4c01d2f34007181ff9c9803a5000000d003000b018801305140f84023608400ba3e9b20a5020c0690120a03c016e405805a4018c06d019c02d2015bad000ca3039b04de5d02d00340080301e802282b4168102d0007c0801eb2607584c400a900150570262c4508016a29bde8803a032cb40021eb3c8f76c36000ac04bf6800620444f0127bb60ab009608794060034010e04588052809608d0250401a408404647648ac80d8eeb19b62b2c4cd878b0935ffabe7b8eaaf415d8eb9a56f767ff5b919ffb3ffad6b422eb515673acc144fab1fd610aba756caac8d570aabb54f2a94b3ffa9bd52f62c2548ea8bf50faa07d3eea79b4eb29c5d35ca66d4d26991d336a6054cda991d302a5c34a92941d254a483484a8ead1a6a30b2afa8b95151a27d443e87750cda159422e8355049a06d405680133ff9fdf3e1e7ee4fbb9f513e1e7ba4f459e493b9d9ffbf899d8d3a966e44e769c7338999ffcdf79b91369e6c34d739a89348e6814ce19981327e63f4c6b8b09312a614cc1697cf2b45a234bd467ff2ece5c23c0f96c72cd2582cae490f72b4655f4a9d94dd28fe50f49ef93810ce24c1c33892a924959ffc90491e32342457c89c90f7216a41cc8188fef1f5a2c247c38f291dce3a947238b091c42377c6ce8d3f19fa32ec64a8c6f185a2f3b3ff67ff171a2d2c5848ac7149a282c4e48986d11a251447363a311ce222441587e90f4e1d2436786710c5e17b42d585690a4e13942518461083e0f741cd8359062e0b541498251041e07340c58164cffe04fc070809f00b9ff8bfd079f6fef5fd53f897e98fc3df773ebf7d04f985e7dbe407c22f7f99ffbdc17b40f5fdeaf3d3d7a38f3ede6d3cb9794cf215e2b3c437844f03ddf73bbf7758edf5da73b1f75fceb75d573a557468e84dcf239c37344e605ca93931723ce42dc7538a87192e2a1c43b87470c2e101c0fb7fe6ffcdf3dbde379b6ed8dd2db8e371c6df6d2b9b6d33ff6d72d7f5b45365b63a2d879afeb5dc6b76d6a1acab5826a6ed421a7ab4f567fed389a60b4ae6936d1e9a2cb459688cd0cda0233ff6730ccc597a32b76510c92d90031d16328c5cd1b231526262c409846b050600abf217d3af4e5e0) else (if i < 7 then 0x407d6e7002d2019b3cd007e02e92809017403f00748231482db74272605b00926055805d16f9feedf7a2ae3005a4a60a947019ee77040500b010ca06906100168c035019c40a284020338c15a034b6be017404e280ca00e82ba02e805bbe7fbb7de882b492e4e57f214005d200ba069080d201744014804c41580ba400a404300b405d21f51868010433ea0e4d017408221f5003a21a004110027019c05d182980196b4025d104e02e98063019c05d1b44a03380ba3e74420a680cbad0009e400af1a200b40650174a021805802e8f5a00194403c00d60168c082010c0651803a0338b062019415d0077bd10568c01302b403380ba4012401d01746069009202e8c0d29e34049190167c6803a02e929773e3401d01749de8803a0168c04300b405d1a0c409d80560881032600ac0620440807301be07f8100400ac3260124603e027605280904102c035034802d2009601200ce3009006710048016803a30c20035034802d27340012005a00e9003500b40431809602e8a809c68805d0074803282bb8d1005602e971a2117004b1a344052eb4002580ba512eb1a20174608f000021ed8d93c6ec643101a581e816dcd000ce6047804310025c1e821a1681213266861330348802e803a2f77501201d060687bba03280e84034011401946054026c06802280169682b021001d1dfc3415810800e900bc042001d180fe03708065009001d181040328802201945aedf2e800e8100410700120210708a00f8221ee046034070657355cd100ca01697996034802d03348090005a04f0f99600b40cd1f32d00d805a06693809e6440a818194016813c3034002d027870687355cd100ca016979a202e002d01949ad1013c048005a40348054046c607d818603b005a401740cd101cc05401f601690d7be65401f02a0809a8cac2030c0441019c46801fe47ff32c5004800b02c4015852214d14b4e035bb20c310c0d9012459d002000690c01def5c0e60577996289a1acf2b41c1e803a5d68015ce0f401d2008601a80ba300ac0cd026c600981300448c00ee02780f034002b0348cc53150c02e8c044230c01f045a02b2b01e02f00ca3011c0c60120600c0122005cf3cc3bb1a0603ed13900b4740391a10158c027033409b1801c015f0130a401a0032180cd012d82b181b204d880cd00fc0c300b4809c805a07d81364020806b00b4604f85a002280ca402f001f13200c15898ab6188404f950c02e8c0ff2b405cd000d0431005a402f007f0138604200d007f803a4017e136115a14504a4a01201040328c0632af804e1825a0328802c019440a4810e2031003f1013008a00ca3018414901206063009c202e410800746058806a0480c0b9023401d180ac07f809e30294090009004f20196053807c303540c400fc600c00e6005af3c4680122603b00b100b460 else (if i < 8 then 0x920081000ba3d024251b746c203c810101506c15809c240800100138606680ec02e8c00a00d44e04840240ec6c2048a78de025a251803bc04982c345401351229048700183202c0d000986405f012068004c41b56131009862950daa0668c8d080ac4ee10740f027c5b49141e201943a3600a82007415c100480018a20971b0402b81a6268940b41003c1914c042683c6e36100e28859c0911008068005a303e43104b84a2d024a1615012804d7ae3402680912c4b436088090c4121a0254361014ec04c8d8302440011221403a08029034c442c1016241a80c302c00a9201160498809c963c5204b52423b1c01d1005a03280ba310100d300b46d29b0c4fe78c01d027c4031804c210180630350606980c88a6a2904402d0d00334607a812e21ba00961000c07f880cf03a8472980e22394c119101ea01308097018456c5f326201c486a1000088188001440c40002ca620343877100a202a880510078400080a22202c04310096036880d8080921409c8040124602280aa201080041008b50790160221162500544073840940803a02e8808f58db14700748047ec6c068003a4007003b16c6c00e8048301b5147d8d801d2358e01e0800022ac4037ac2c01c8c0340cf3cc3b81a003811d8b00f04b6380782024c03913b6601d0841200e84b29807425e400391082401c880e508004068880e503440611ec6c1017000117326179b1e3615c6c000541e300c0201700ca02e8c02e007405d1805e00e80ba300b001d1080800e884040074049180ac017805c03280ba0169829c00fc401f80302026003900a8601e0054200e802a100540270804b00a815d1805561289aac0810a1007402410048168080000090404a108c2e0242d298415d000c40009c1e2000402410128b07807038444201000042c08090001746026002022403020017460000098200b79c2101c404008204202c81b1803800600ba30b4002de68005d2000000e0810200d4400e00102c83c200e056ac0805e017003fa0480ba500880260078602a04225080140158802b084c41004c000100000098ac090d4a61c94eb8e00086003500d30330065019002b0348e06680cb2d02b3c016803bde89c0827a841150240804e911804100ba4032bddd8340603a10248680104496800d20337bd10074a016803a02e8ed9e017401d010c94c501a42080406714b418d10a809017409b184c4008bb26ec580ba00ea2283db2005d00b511402d880a9819a012222804d941537ba1e4d026c8237003a20335d93004405d44500b63019a0515b260a980f85c6831a296cd9820074a08a003a20be011401f0603e5c9a08180e8401800cd2ec50d00450a8d000f808a020602e951a2c68005d007497e7eb41de880ca0169415a01940a8bba006700b4c0ad08c481582babcb80ba066efb5bf06b40a033 else 0x26530029809190250680801d0802006909e92004040168580901744032805a00e8c08f2514048017401d2c28b8ca80523568005d00747329803a032b0124305b0d00174602e902403a41a04ba482503c0563020e8090ef9fde882b4300303b36005a2383cf9725307be7f7a22a21c1e49059a2512013512880b604dc47cb8560f05744804840763ea0c06c340074288b80328b02024000101ecd802e803a30174156100207c6803a30074fcb1005a00c0866ce0585c0b60c420353bcf02a0709b874160d02c1d05802d16b275c808065009001dd6808012003a2023c06500747c0b075a0004001d18cd800e00900149066c009001d1805200e0815d08068415880180cf24014803a3007401c1182d9078801800704f3650122d6831a21544a8158882b0dd24c048914c0ecd8104442f1b381e2c058202a681e220482268702c0168c000e03c413109a1c0780a840043809161a002e8806501f18d0180cb86500f806691e920c024a037bba3019407cc340602ea1a0202410d0101901232a0d0056c602b980c2467c10d141a1eee081480324401680ba2a89402e1544a1da4801c16c6c0120805d0))))
def rootMH10 (i : Nat) : Nat := 0x12749b0e54f52acc34140065002963cdd4af10f9084d52b84f400048265ec1d0102340330bc80ecb03831c0092c9d1b308941a06624e1280302a0c80dd25980232908300700c77bc13ae808c000000004bb44407855258000009cd0a0c701206e40c3228ba92a28001d08560008d92dda200010a3a05d07475632cdb0a60b18492807c000000090e8504343720904e1b8030b0ae14b3cbf0d45766ca53bd41112341691a1b1049632c10514b00005c30033444500023801131802c21003402414410c000034000334000018028004604d8c0
def rootMD9 (i : Nat) : Nat := 0x2d080cd0e0d00e653009000747c6882412f2d00bbe7fbd10a88300181003a17cd801204012c3ba480240801a0400c813b178160c01ceb40204c410020101320077c048c31380cc1002f0d942f0ee1005603304034c01580cc1d6530802d003a01746dab0201742000ca0350069806401a45ab3c0194016805d2001d00ba200ca017440194016805d1e5b308065003bdf3fde8900ad005d005a300e800744017400e8bde8805d01a43001601744012c02e8abed7daab5a6b4d55aab48dd150f9d8939274ba94d2492746f8b70e127424802fb5e524e49ced9d124e49cdc12734d69aca9953165e6b0556a7b4ce94d2724e3fc6f4cd17728a4c4780be1361e0230230017fc1d22d5814c530482ff83a452b0298a60905eec750325458060560ddb8e8b8a19300c0ac17b71d50c95160181582f3e3ae192a2c0302b05e7c75ccb4c58060560bbd8ea172c0aa2982415fd0db661814c530483afa3a65cb02a8a609075ec750b9605514c120e9f85cb04c0aa2982417f61d32e95254520442fe93a25d2a6a9260905fd2744c954d524c120cbecd9b905caa29824197d9c870cb9545304832f7370e2172a8a609065ee721c42e5514c120abdcea172d92a29824196f9c8718b9545304832f7388e1972a8a609053ee744ba611545c1208f7ceb196a9b30b82412fb8da7109560530482fcd3ac652a6a92408857da36d535499848110afb46daa6a93009022157d4db661814c5304830fe974e0930caa62907cd9605512e58254910bae6eb972a926298241a76d5132982549934432f5ba865aa6d43240865eb750cb54d8264810cb76eb196a9b50c902196edd632d53609920428f7ba862b6454b02b061ef751c92e95360810c3dee23925d2a6c102186fdc665cba54d984820ff9b6e2974cc2629069af2d1c62a5a954d2083fe6e330dd12a98a4107fcdb72898655314820ff9b4e5930a93229863af719c42e95360810f9e0cc2a4c0a6298241d3d1b5661814c530482e7a3a261b30c0a609074f436d98605314c120bf90ea174a92a2902217e49d632553549304827e91b8a9b30a926090477a744cb5cd425c120cbccd9b885caa29824117d8dc6d5984c5304832f3388e1972a8a609065ae719c42e5514c120
def rootMH9 (i : Nat) : Nat := 0x83951607d9509704409392a0803
def rootMD8 (i : Nat) : Nat := 0x194033401746003a00ba2b56ad5ab569280d5e4751d32e5815453048353d1d874cb9605514c120d5ac759d42e5815453048316add6750cb54da864810c5ab759d432d536099204306bdd6751c92e95360810f4d06d598549814c53048253d0ed6d598605314c120
def rootMH8 (i : Nat) : Nat := 0x961016000
def rootMD7 (i : Nat) : Nat := 0x882584003a002d002e8f8028b587e3acea172c0aa29824134d03f9b566152605314c120
def rootMLevel : Nat → Packing
  | 15 => (1,0,9,0,0,0,0,rootMD15)
  | 14 => (9,1,9,0,0,10,0,rootMD14)
  | 13 => (98,2,9,0,0,14,0,rootMD13)
  | 12 => (588,3,9,0,0,17,0,rootMD12)
  | 11 => (1388,4,9,0,0,17,0,rootMD11)
  | 10 => (583,5,9,0,0,15,0,rootMD10)
  | 9 => (59,6,9,0,0,11,0,rootMD9)
  | 8 => (8,7,9,0,0,7,0,rootMD8)
  | 7 => (2,8,9,0,0,6,0,rootMD7)
  | _ => emptyPacking
def rootMIndex : Nat → Nat → Option (Nat × Nat)
  | 15 => rootLookup 29 61 6 9 4 4 rootMH15
  | 14 => rootLookup 127 257 8 12 7 4 rootMH14
  | 13 => rootLookup 541 1319 10 15 10 4 rootMH13
  | 12 => rootLookup 991 2963 11 16 11 4 rootMH12
  | 11 => rootLookup 457 1063 9 15 10 4 rootMH11
  | 10 => rootLookup 47 127 6 11 6 4 rootMH10
  | 9 => rootLookup 5 11 4 8 3 4 rootMH9
  | 8 => rootLookup 5 7 0 6 1 4 rootMH8
  | _ => fun _ => none
def rootM : Forest := ⟨1535,15,fun j => rootMSamples[j]?.getD (0,0),rootMCols,rootMAutos,rootMLevel,rootMIndex⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb7_0 : block rootM 7 0 2 = true := by
  apply rootGroupsBlock rootM 7 0 [(7,1),(8,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel7 : block rootM 7 0 2=true := rootMb7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb8_0 : block rootM 8 0 8 = true := by
  apply rootGroupsBlock rootM 8 0 [(8,2),(9,6)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel8 : block rootM 8 0 8=true := rootMb8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb9_0 : block rootM 9 0 59 = true := by
  apply rootGroupsBlock rootM 9 0 [(9,12),(10,16),(10,16),(10,15)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel9 : block rootM 9 0 59=true := rootMb9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_0 : block rootM 10 0 86 = true := by
  apply rootGroupsBlock rootM 10 0 [(9,6),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_86 : block rootM 10 86 96 = true := by
  apply rootGroupsBlock rootM 10 86 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_182 : block rootM 10 182 81 = true := by
  apply rootGroupsBlock rootM 10 182 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_263 : block rootM 10 263 96 = true := by
  apply rootGroupsBlock rootM 10 263 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_359 : block rootM 10 359 96 = true := by
  apply rootGroupsBlock rootM 10 359 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_455 : block rootM 10 455 96 = true := by
  apply rootGroupsBlock rootM 10 455 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_551 : block rootM 10 551 32 = true := by
  apply rootGroupsBlock rootM 10 551 [(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel10 : block rootM 10 0 583=true := (@block_merge rootM 10 0 263 320 (@block_merge rootM 10 0 86 177 rootMb10_0 (@block_merge rootM 10 86 96 81 rootMb10_86 rootMb10_182)) (@block_merge rootM 10 263 192 128 (@block_merge rootM 10 263 96 96 rootMb10_263 rootMb10_359) (@block_merge rootM 10 455 96 32 rootMb10_455 rootMb10_551)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_0 : block rootM 11 0 94 = true := by
  apply rootGroupsBlock rootM 11 0 [(9,14),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_94 : block rootM 11 94 92 = true := by
  apply rootGroupsBlock rootM 11 94 [(10,16),(10,16),(10,16),(10,16),(10,12),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_186 : block rootM 11 186 96 = true := by
  apply rootGroupsBlock rootM 11 186 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_282 : block rootM 11 282 96 = true := by
  apply rootGroupsBlock rootM 11 282 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_378 : block rootM 11 378 96 = true := by
  apply rootGroupsBlock rootM 11 378 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_474 : block rootM 11 474 96 = true := by
  apply rootGroupsBlock rootM 11 474 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_570 : block rootM 11 570 96 = true := by
  apply rootGroupsBlock rootM 11 570 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_666 : block rootM 11 666 96 = true := by
  apply rootGroupsBlock rootM 11 666 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_762 : block rootM 11 762 96 = true := by
  apply rootGroupsBlock rootM 11 762 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_858 : block rootM 11 858 93 = true := by
  apply rootGroupsBlock rootM 11 858 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,13)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_951 : block rootM 11 951 96 = true := by
  apply rootGroupsBlock rootM 11 951 [(12,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_1047 : block rootM 11 1047 96 = true := by
  apply rootGroupsBlock rootM 11 1047 [(12,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_1143 : block rootM 11 1143 96 = true := by
  apply rootGroupsBlock rootM 11 1143 [(12,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_1239 : block rootM 11 1239 96 = true := by
  apply rootGroupsBlock rootM 11 1239 [(12,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_1335 : block rootM 11 1335 53 = true := by
  apply rootGroupsBlock rootM 11 1335 [(12,16),(12,16),(12,16),(12,5)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel11 : block rootM 11 0 1388=true := (@block_merge rootM 11 0 666 722 (@block_merge rootM 11 0 282 384 (@block_merge rootM 11 0 94 188 rootMb11_0 (@block_merge rootM 11 94 92 96 rootMb11_94 rootMb11_186)) (@block_merge rootM 11 282 192 192 (@block_merge rootM 11 282 96 96 rootMb11_282 rootMb11_378) (@block_merge rootM 11 474 96 96 rootMb11_474 rootMb11_570))) (@block_merge rootM 11 666 381 341 (@block_merge rootM 11 666 192 189 (@block_merge rootM 11 666 96 96 rootMb11_666 rootMb11_762) (@block_merge rootM 11 858 93 96 rootMb11_858 rootMb11_951)) (@block_merge rootM 11 1047 192 149 (@block_merge rootM 11 1047 96 96 rootMb11_1047 rootMb11_1143) (@block_merge rootM 11 1239 96 53 rootMb11_1239 rootMb11_1335))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_0 : block rootM 12 0 96 = true := by
  apply rootGroupsBlock rootM 12 0 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_96 : block rootM 12 96 92 = true := by
  apply rootGroupsBlock rootM 12 96 [(10,12),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_188 : block rootM 12 188 96 = true := by
  apply rootGroupsBlock rootM 12 188 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_284 : block rootM 12 284 96 = true := by
  apply rootGroupsBlock rootM 12 284 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_380 : block rootM 12 380 96 = true := by
  apply rootGroupsBlock rootM 12 380 [(11,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_476 : block rootM 12 476 96 = true := by
  apply rootGroupsBlock rootM 12 476 [(12,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_572 : block rootM 12 572 16 = true := by
  apply rootGroupsBlock rootM 12 572 [(12,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel12 : block rootM 12 0 588=true := (@block_merge rootM 12 0 284 304 (@block_merge rootM 12 0 96 188 rootMb12_0 (@block_merge rootM 12 96 92 96 rootMb12_96 rootMb12_188)) (@block_merge rootM 12 284 192 112 (@block_merge rootM 12 284 96 96 rootMb12_284 rootMb12_380) (@block_merge rootM 12 476 96 16 rootMb12_476 rootMb12_572)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb13_0 : block rootM 13 0 77 = true := by
  apply rootGroupsBlock rootM 13 0 [(9,5),(10,16),(10,8),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb13_77 : block rootM 13 77 21 = true := by
  apply rootGroupsBlock rootM 13 77 [(11,16),(11,5)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel13 : block rootM 13 0 98=true := (@block_merge rootM 13 0 77 21 rootMb13_0 rootMb13_77)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb14_0 : block rootM 14 0 9 = true := by
  apply rootGroupsBlock rootM 14 0 [(10,9)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel14 : block rootM 14 0 9=true := rootMb14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb15_0 : block rootM 15 0 1 = true := by
  apply rootGroupsBlock rootM 15 0 [(9,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootMlevel15 : block rootM 15 0 1=true := rootMb15_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootMGeom : graphValid rootM (boundsBefore known42879)=true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem rootMTables : checkedTables rootM 15 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootMlevel7
  · exact rootMlevel8
  · exact rootMlevel9
  · exact rootMlevel10
  · exact rootMlevel11
  · exact rootMlevel12
  · exact rootMlevel13
  · exact rootMlevel14
  · exact rootMlevel15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootMImpossible : Impossible false graph 15 inputs.toFinset := by
  have result := index_root (g:=rootM) (m:=1535) (cap:=15) (i:=0) (ws:=inputs) rfl rfl (before_sound known42879 valid42879) rootMGeom rootMTables (by decide +kernel)
  exact (show graphGoal 1535=graph by decide +kernel) ▸ result

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

theorem parentFromModes (exM : Impossible false graph 15 inputs.toFinset)
    (exS : Impossible true graph 14 inputs.toFinset)
    (h : ∃ u k S, k ≤ (if u then 14 else 15) ∧ Live u graph k S ∧ ∀ a ∈ S, a ∈ inputs) : False := by
  obtain ⟨u,k,S,hk,hr,sub⟩ := h
  rw [orbitAllInputs hr sub] at hr
  cases u
  · exact exM k hk hr
  · exact exS k hk hr
end PEqualNP.Outside.L_meta_670.Projection

open PEqualNP.Outside.L_meta_670.Projection

theorem PEqualNP.Outside.L_meta_670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,legal,small,correct⟩
  exact parentFromModes rootMImpossible rootSImpossible (raw_modes C legal (funext correct) small)

